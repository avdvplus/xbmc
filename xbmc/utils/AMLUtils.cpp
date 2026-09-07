/*
 *  Copyright (C) 2011-2018 Team Kodi
 *  This file is part of Kodi - https://kodi.tv
 *
 *  SPDX-License-Identifier: GPL-2.0-or-later
 *  See LICENSES/README.md for more information.
 */

#include <dirent.h>
#include <unistd.h>
#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <charconv>
#include <string>
#include <regex>
#include <chrono>
#include <optional>
#include <vector>
#include <numeric>
#include <cmath>
#include <algorithm>
#include <sstream>
#include <mutex>
#include <atomic>
#include <limits>
#include <cerrno>
#include <cstdint>
#include <pthread.h>
#include <sys/syscall.h>

#include "AMLUtils.h"

#include "application/Application.h"
#include "messaging/ApplicationMessenger.h"
#include "application/ApplicationComponents.h"
#include "application/ApplicationPlayer.h"
#include "cores/DataCacheCore.h"
#include "utils/LogThrottle.h"
#include "utils/log.h"
#include "utils/StringUtils.h"
#include "utils/AudioSyncReset.h"
#include "windowing/GraphicContext.h"
#include "utils/RegExp.h"
#include "filesystem/SpecialProtocol.h"
#include "rendering/RenderSystem.h"
#include "settings/Settings.h"
#include "settings/SettingsComponent.h"
#include "guilib/GUIComponent.h"
#include "guilib/GUIWindowManager.h"
#include "guilib/LocalizeStrings.h"
#include "dialogs/GUIDialogKaiToast.h"
#include "ServiceBroker.h"

#include "settings/DisplaySettings.h"
#include "settings/AdvancedSettings.h"
#include "HDR10PlusConvert.h"

#include "platform/linux/SysfsPath.h"

#include "linux/fb.h"
#include <sys/ioctl.h>
#include <amcodec/codec.h>

static std::atomic<bool> vs10_conversion{false};
static std::atomic<bool> aml_linux_force_422{false};
static std::atomic<bool> aml_hdr10plus_attr_override{false};
bool aml_linux_osd_sdr8 = true;
static std::atomic<bool> s_guiPqIsFinalStage{false};
static std::atomic<bool> aml_bdj_overlay_active{false};
static std::atomic<bool> s_dvDiscSession{false};
static std::atomic<bool> s_dvPlaybackActive{false};
static AVColorPrimaries s_currentColorPrimaries = AVCOL_PRI_UNSPECIFIED;
static std::mutex s_lastDisplayModeMutex;
static std::string s_lastDisplayMode;
static std::recursive_timed_mutex s_dvCoreMutex;
static std::atomic<const char*> s_dvCoreHolder{nullptr};
static std::atomic<int> s_dvCoreHolderTid{0};
static std::atomic<int64_t> s_dvCoreHeldSinceMs{0};
static std::atomic<const char*> s_dvWireStep{nullptr};
static std::atomic<int64_t> s_dvWireStepSinceMs{0};
static std::atomic<bool> s_dvTriggerPending{false};

static std::recursive_timed_mutex s_hdmiWireMutex;
static std::mutex s_cdCsStateMutex;
static std::atomic<const char*> s_hdmiWireHolder{nullptr};
static std::atomic<int> s_hdmiWireHolderTid{0};

static constexpr int64_t kHdmiWireWaitMs = 2000;
static constexpr int64_t kDvWireStepStallMs = 5000;
static constexpr int64_t kDvCoreHoldStallMs = 12000;
static constexpr int64_t kDvTriggerRetryMs = 200;
static constexpr int kDvTriggerRetryGiveUp = 25;

static int64_t aml_steady_ms()
{
  return std::chrono::duration_cast<std::chrono::milliseconds>(
             std::chrono::steady_clock::now().time_since_epoch())
      .count();
}

static int aml_current_tid()
{
  thread_local const int tid = static_cast<int>(syscall(SYS_gettid));
  return tid;
}

static bool aml_dv_core_holder_stalled(int64_t& stepMs, int64_t& heldMs)
{
  const int64_t now = aml_steady_ms();
  const int64_t stepSince = s_dvWireStepSinceMs.load(std::memory_order_relaxed);
  const int64_t heldSince = s_dvCoreHeldSinceMs.load(std::memory_order_relaxed);
  stepMs = stepSince != 0 ? now - stepSince : 0;
  heldMs = heldSince != 0 ? now - heldSince : 0;
  return (stepSince != 0 && stepMs >= kDvWireStepStallMs) ||
         (heldSince != 0 && heldMs >= kDvCoreHoldStallMs);
}

namespace
{
struct fb_vsync_timing_request
{
  int64_t now_ts;
  int64_t last_vsync_ts;
  int64_t next_vsync_ts;
  int64_t period_ns;
  int32_t reserved0;
  int32_t reserved1;
};

#ifndef FBIO_GET_VSYNC_TIMING_64
#define FBIO_GET_VSYNC_TIMING_64 _IOR('F', 0x25, struct fb_vsync_timing_request)
#endif

std::string GetFramebufferDevicePath()
{
  const char* env = getenv("FRAMEBUFFER");
  if (env && env[0] != '\0')
  {
    std::string fb(env);
    auto pos = fb.find("fb");
    if (pos != std::string::npos)
      fb = fb.substr(pos);

    if (fb.rfind("/dev/", 0) == 0)
      return fb;
    return "/dev/" + fb;
  }

  return "/dev/fb0";
}

bool GetFramebufferDevice(int& fbFd, std::string* fbPath)
{
  static std::atomic<int> cachedFd{-1};

  int fd = cachedFd.load(std::memory_order_acquire);
  if (fd >= 0)
  {
    fbFd = fd;
    if (fbPath)
      *fbPath = GetFramebufferDevicePath();
    return true;
  }

  std::string path = GetFramebufferDevicePath();
  fd = open(path.c_str(), O_RDWR | O_CLOEXEC);
  if (fd < 0)
  {
    LOG_THROTTLE_PERIODIC_GENERAL(LOGWARNING, 1000, "failed to open {}: {}", path, strerror(errno));
    return false;
  }

  int expected = -1;
  if (!cachedFd.compare_exchange_strong(expected, fd, std::memory_order_acq_rel))
  {
    close(fd);
    fd = expected;
  }
  else
    logM(LOGINFO, "opened {} fd:{}", path, fd);

  fbFd = fd;
  if (fbPath)
    *fbPath = path;
  return true;
}
}

bool aml_get_vsync_edge(int64_t& lastVsyncTs)
{
  lastVsyncTs = 0;

  static std::atomic<bool> hasEdgeQuery{true};
  if (!hasEdgeQuery.load(std::memory_order_relaxed))
    return false;

  int fbFd{-1};
  if (!GetFramebufferDevice(fbFd, nullptr))
    return false;

  fb_vsync_timing_request req{};
  if (ioctl(fbFd, FBIO_GET_VSYNC_TIMING_64, &req) < 0)
  {
    if (errno == ENOTTY || errno == EINVAL)
    {
      hasEdgeQuery.store(false, std::memory_order_relaxed);
      logM(LOGINFO, "vsync edge query unavailable");
    }
    return false;
  }

  if (req.last_vsync_ts <= 0)
    return false;

  lastVsyncTs = req.last_vsync_ts;
  return true;
}

bool aml_get_time_until_vsync_phase_us(int afterVsyncUs, int& timeUntilPhaseUs)
{
  constexpr int64_t NS_PER_US{1000};

  timeUntilPhaseUs = 0;

  static std::atomic<bool> hasVsyncTiming{true};
  if (!hasVsyncTiming.load(std::memory_order_relaxed))
    return false;

  int fbFd{-1};
  std::string fbPath;
  if (!GetFramebufferDevice(fbFd, &fbPath))
    return false;

  fb_vsync_timing_request req{};
  if (ioctl(fbFd, FBIO_GET_VSYNC_TIMING_64, &req) < 0)
  {
    if (errno == ENOTTY || errno == EINVAL)
    {
      hasVsyncTiming.store(false, std::memory_order_relaxed);
      logM(LOGINFO, "vsync timing ioctl unavailable on {}", fbPath);
    }
    else if (errno != EAGAIN)
      logM(LOGERROR, "ioctl failed on {}: {}", fbPath, strerror(errno));
    return false;
  }

  if (req.now_ts <= 0 || req.last_vsync_ts <= 0 || req.next_vsync_ts <= 0)
    return false;

  int64_t periodNs = req.period_ns;
  if (periodNs <= 0)
  {
    if (req.next_vsync_ts <= req.last_vsync_ts)
      return false;

    periodNs = req.next_vsync_ts - req.last_vsync_ts;
  }

  int64_t phaseNs = std::max<int64_t>(0, static_cast<int64_t>(afterVsyncUs) * NS_PER_US);
  if (phaseNs >= periodNs) phaseNs %= periodNs;

  int64_t targetNs = req.last_vsync_ts + phaseNs;
  if (targetNs <= req.now_ts)
  {
    const int64_t elapsedNs = req.now_ts - targetNs;
    targetNs += (elapsedNs / periodNs + 1) * periodNs;
  }

  const int64_t deltaNs = targetNs - req.now_ts;
  timeUntilPhaseUs = static_cast<int>(std::max<int64_t>(
      0, std::min<int64_t>(deltaNs / NS_PER_US, std::numeric_limits<int>::max())));

  return true;
}

class CDVCoreGuard
{
public:
  enum class Acquire
  {
    Wait,
    Abortable,
    TryOnce,
  };

  explicit CDVCoreGuard(const char* tag, Acquire mode = Acquire::Wait) : m_tag(tag)
  {
    if (mode == Acquire::Wait && CServiceBroker::GetAppMessenger()->IsProcessThread())
      mode = Acquire::Abortable;

    const auto t0 = std::chrono::steady_clock::now();
    int64_t nextLogMs = 5000;
    for (;;)
    {
      const auto budget = (mode == Acquire::Wait) ? std::chrono::milliseconds(5000)
                                                  : std::chrono::milliseconds(500);
      if (mode == Acquire::TryOnce)
      {
        if (s_dvCoreMutex.try_lock())
          break;
        return;
      }
      if (s_dvCoreMutex.try_lock_for(budget))
        break;

      const int64_t waitedMs = std::chrono::duration_cast<std::chrono::milliseconds>(
                                   std::chrono::steady_clock::now() - t0)
                                   .count();
      const char* holder = s_dvCoreHolder.load(std::memory_order_relaxed);
      const char* step = s_dvWireStep.load(std::memory_order_relaxed);
      const int holderTid = s_dvCoreHolderTid.load(std::memory_order_relaxed);
      int64_t stepMs = 0;
      int64_t heldMs = 0;
      const bool stalled = aml_dv_core_holder_stalled(stepMs, heldMs);

      if (mode == Acquire::Abortable && stalled)
      {
        logM(LOGERROR,
             "DV-core lock: {} ABANDONED after {}ms - holder {} tid={} stalled in wire step {} for "
             "{}ms (held {}ms); continuing without the lock to keep the UI alive",
             m_tag, waitedMs, holder ? holder : "<unknown>", holderTid, step ? step : "<none>",
             stepMs, heldMs);
        return;
      }

      if (waitedMs >= nextLogMs)
      {
        logM(LOGERROR,
             "DV-core lock: {} blocked {}ms (held by {} tid={} for {}ms, wire step {} for {}ms)",
             m_tag, waitedMs, holder ? holder : "<unknown>", holderTid, heldMs,
             step ? step : "<none>", stepMs);
        nextLogMs = waitedMs + (waitedMs >= 30000 ? 60000 : 5000);
      }
    }
    m_owns = true;
    m_diag = CServiceBroker::GetLogging().CanLogComponent(LOGVIDEO);
    if (m_diag)
    {
      const auto waitMs = std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - t0).count();
      if (waitMs > 50)
        logComponentM(LOGDEBUG, LOGVIDEO, "DV-core lock convoy: {} waited {}ms", m_tag, waitMs);
    }
    m_prevHolder = s_dvCoreHolder.exchange(m_tag, std::memory_order_relaxed);
    m_outermost = (s_lockDepth++ == 0);
    if (m_outermost)
    {
      s_dvCoreHeldSinceMs.store(aml_steady_ms(), std::memory_order_relaxed);
      s_dvCoreHolderTid.store(aml_current_tid(), std::memory_order_relaxed);
    }
    if (m_diag && m_outermost)
      m_acquired = std::chrono::steady_clock::now();
  }
  ~CDVCoreGuard()
  {
    if (!m_owns)
      return;
    --s_lockDepth;
    if (m_diag && m_outermost)
    {
      const auto heldMs = std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - m_acquired).count();
      if (heldMs > 100)
        logComponentM(LOGDEBUG, LOGVIDEO, "DV-core lock: {} held {}ms", m_tag, heldMs);
    }
    if (m_outermost)
    {
      s_dvCoreHeldSinceMs.store(0, std::memory_order_relaxed);
      s_dvCoreHolderTid.store(0, std::memory_order_relaxed);
    }
    s_dvCoreHolder.store(m_prevHolder, std::memory_order_relaxed);
    s_dvCoreMutex.unlock();
  }
  bool Owns() const { return m_owns; }
  CDVCoreGuard(const CDVCoreGuard&) = delete;
  CDVCoreGuard& operator=(const CDVCoreGuard&) = delete;
private:
  static thread_local int s_lockDepth;
  const char* m_tag;
  const char* m_prevHolder{nullptr};
  bool m_owns{false};
  bool m_diag{false};
  bool m_outermost{false};
  std::chrono::steady_clock::time_point m_acquired{};
};
thread_local int CDVCoreGuard::s_lockDepth = 0;

CAmlHdmiWireGuard::CAmlHdmiWireGuard(const char* tag)
{
  const bool diag = CServiceBroker::GetLogging().CanLogComponent(LOGVIDEO);
  const int64_t t_wait = diag ? aml_steady_ms() : 0;
  const char* blocker = diag ? s_hdmiWireHolder.load(std::memory_order_relaxed) : nullptr;
  const int blockerTid = diag ? s_hdmiWireHolderTid.load(std::memory_order_relaxed) : 0;
  if (s_hdmiWireMutex.try_lock_for(std::chrono::milliseconds(kHdmiWireWaitMs)))
  {
    m_owns = true;
    m_prevHolder = s_hdmiWireHolder.exchange(tag, std::memory_order_relaxed);
    m_prevHolderTid = s_hdmiWireHolderTid.exchange(aml_current_tid(), std::memory_order_relaxed);
    if (diag && blocker && blockerTid && blockerTid != aml_current_tid())
    {
      const int64_t waited = aml_steady_ms() - t_wait;
      if (waited > 0)
        logComponentM(LOGDEBUG, LOGVIDEO, "HDMI wire: {} acquired after {}ms behind {}", tag,
                      waited, blocker);
    }
    return;
  }

  static int64_t s_nextLogMs = 0;
  const int64_t now = aml_steady_ms();
  if (now >= s_nextLogMs)
  {
    s_nextLogMs = now + 5000;
    const char* holder = s_hdmiWireHolder.load(std::memory_order_relaxed);
    logM(LOGERROR,
         "HDMI wire: {} proceeding unserialised after {}ms - still held by {}",
         tag, kHdmiWireWaitMs, holder ? holder : "<unknown>");
  }
}

CAmlHdmiWireGuard::~CAmlHdmiWireGuard()
{
  if (!m_owns)
    return;
  s_hdmiWireHolder.store(m_prevHolder, std::memory_order_relaxed);
  s_hdmiWireHolderTid.store(m_prevHolderTid, std::memory_order_relaxed);
  s_hdmiWireMutex.unlock();
}

CAmlDvWireStep::CAmlDvWireStep(const char* tag)
  : m_prevTag(s_dvWireStep.exchange(tag, std::memory_order_relaxed)),
    m_prevSinceMs(s_dvWireStepSinceMs.exchange(aml_steady_ms(), std::memory_order_relaxed))
{
}

CAmlDvWireStep::~CAmlDvWireStep()
{
  s_dvWireStep.store(m_prevTag, std::memory_order_relaxed);
  s_dvWireStepSinceMs.store(m_prevSinceMs, std::memory_order_relaxed);
}

static void aml_display_mode_round_trip(const char* fn);

static std::shared_ptr<CSettings> settings()
{
  return CServiceBroker::GetSettingsComponent()->GetSettings();
}

int aml_dv_osd_max_nits()
{
  if (aml_bdj_overlay_active)
    return 2000;
  return settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_MODE_ON_LUMINANCE);
}

bool aml_dv_bdj_overlay_visible()
{
  return aml_bdj_overlay_active;
}

static void aml_dv_reset_osd_max()
{
  aml_dv_set_osd_max(aml_dv_osd_max_nits());
}

void aml_set_bdj_overlay_active(bool active)
{
  aml_bdj_overlay_active = active;
  aml_dv_reset_osd_max();
}

std::string aml_get_plane_state_diag()
{
  auto readTrim = [](const char* p) -> std::string {
    CSysfsPath s{p};
    if (!s.Exists())
      return "N/A";
    std::string v = s.Get<std::string>().value_or("");
    while (!v.empty() && (v.back() == '\n' || v.back() == ' ' || v.back() == '\r' || v.back() == '\t'))
      v.pop_back();
    return v.empty() ? "empty" : v;
  };
  std::ostringstream os;
  os << "disable_video="   << readTrim("/sys/class/video/disable_video")
     << " fb0_blank="      << readTrim("/sys/class/graphics/fb0/blank")
     << " fb1_blank="      << readTrim("/sys/class/graphics/fb1/blank")
     << " graphic_max="    << readTrim("/sys/module/amdolby_vision/parameters/dolby_vision_graphic_max")
     << " hdmi_hdr="       << readTrim("/sys/class/amhdmitx/amhdmitx0/hdmi_hdr_status")
     << " disp_mode="      << readTrim("/sys/class/amhdmitx/amhdmitx0/disp_mode")
     << " dv_mode="        << static_cast<int>(aml_dv_mode())
     << " bdj_active="     << (aml_bdj_overlay_active ? 1 : 0);
  return os.str();
}

static void aml_dv_toggle_frame(unsigned int mode)
{
  CAmlDvWireStep step("toggle_frame");
  CSysfsPath dolby_vision_flags{"/sys/module/amdolby_vision/parameters/dolby_vision_flags"};
  if (dolby_vision_flags.Exists())
  {
    dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() | FLAG_TOGGLE_FRAME);
    CLog::Log(LOGDEBUG, "AMLUtils::{} - Toggle Frame - start - for mode [{}]", __FUNCTION__, aml_dv_output_mode_to_string(mode));
    std::chrono::time_point<std::chrono::system_clock> now(std::chrono::system_clock::now());
    while(true) {
      if ((dolby_vision_flags.Get<unsigned int>().value() & FLAG_TOGGLE_FRAME) == 0) {
        CLog::Log(LOGDEBUG, "AMLUtils::{} - Toggle Frame - done - for mode [{}]", __FUNCTION__, aml_dv_output_mode_to_string(mode));
        break;
      }
      if ((std::chrono::system_clock::now() - now) >= std::chrono::milliseconds(3000)) {
        CLog::Log(LOGDEBUG, "AMLUtils::{} - Toggle Frame - wait time elapsed - for mode [{}]", __FUNCTION__, aml_dv_output_mode_to_string(mode));
        dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_TOGGLE_FRAME));
        logM(LOGWARNING, "Toggle Frame - force-cleared stuck FLAG_TOGGLE_FRAME after timeout");
        break;
      }
      usleep(10000); // wait 10ms
    }
  }
}

static void aml_dv_wait_dv_std_vsif_packet()
{
  // Wait for DV Std vsif packet being sent on HDMI.
  CSysfsPath hdmi_pkt{"/sys/kernel/debug/amhdmitx/hdmi_pkt"};
  if (hdmi_pkt.Exists())
  {
    const auto t_start = std::chrono::steady_clock::now();
    logM(LOGDEBUG, "aml_dv_wait_dv_std_vsif_packet - start");
    while(true) {
      std::string valstr = hdmi_pkt.Get<std::string>().value();
      if (valstr.find("DV STD hdmitx_parsing_vsifpkt") != std::string::npos) {
        const auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(
            std::chrono::steady_clock::now() - t_start).count();
        logM(LOGDEBUG, "aml_dv_wait_dv_std_vsif_packet TIMING: done elapsed={}ms", ms);
        break;
      }
      if ((std::chrono::steady_clock::now() - t_start) >= std::chrono::milliseconds(3000)) {
        logM(LOGDEBUG, "aml_dv_wait_dv_std_vsif_packet TIMING: timeout elapsed=3000ms");
        break;
      }
      usleep(10000); // wait 10ms
    }
  }
}

void aml_reset_audio_from_vs10_change()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  advancedSettings->SetAlgoForReset(2);
}

void aml_set_audio_ddr_urgent(bool enable)
{
  CSysfsPath urgent{"/sys/class/aml_ddr/urgent"};
  if (!urgent.Exists())
    return;
  urgent.Set(std::string(enable ? "80 4" : "80 0"));
}

static bool aml_kodi_restore_cd_cs()
{
  bool was_active;
  bool clear_linux_flag;
  {
    std::lock_guard<std::mutex> cdcs(s_cdCsStateMutex);
    was_active = aml_linux_force_422 || aml_hdr10plus_attr_override;
    clear_linux_flag = aml_linux_force_422;
    aml_linux_force_422 = false;
    aml_hdr10plus_attr_override = false;
  }

  if (clear_linux_flag)
  {
    CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_aml_linux_force_422", false);
    logM(LOGINFO, "CSysfsPath(xbmc_aml_linux_force_422, 0)");
  }

  if (was_active)
    logM(LOGINFO, "clear_linux_flag={:d}", clear_linux_flag);

  return was_active;
}

bool aml_kodi_set_cd_cs(int cd_cs_type)
{
  if (cd_cs_type == 2 && aml_hdr10plus_attr_override.load(std::memory_order_relaxed))
    return false;

  bool prev_override;
  bool new_override;
  bool linux_flag_changed;
  bool linux_flag_value;
  bool hdr10plus_value;
  bool hdr10plus_changed;
  int dv_type_value = -1;
  int dv_vp_value = -1;
  {
    std::unique_lock<std::mutex> cdcs(s_cdCsStateMutex, std::defer_lock);
    if (cd_cs_type == 2)
    {
      if (!cdcs.try_lock())
        return false;
    }
    else
      cdcs.lock();
    prev_override = aml_linux_force_422 || aml_hdr10plus_attr_override;
    const bool prev_linux_flag = aml_linux_force_422;
    const bool prev_hdr10plus = aml_hdr10plus_attr_override;

    switch (cd_cs_type)
    {
      case 1:
      {
        enum DV_TYPE dv_type(static_cast<DV_TYPE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE)));
        unsigned int dv_vp(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VIDEO_PROCESSOR));
        dv_type_value = static_cast<int>(dv_type);
        dv_vp_value = static_cast<int>(dv_vp);
        aml_linux_force_422 =
            (dv_vp == 2) || (dv_vp == 3) ||
            ((dv_vp == 0) && (dv_type == DV_TYPE_PLAYER_LED_HDR2)) ||
            ((dv_vp == 0) && (dv_type == DV_TYPE_PLAYER_LED_LLDV));
        break;
      }
      case 2:
      {
        if (CServiceBroker::GetDataCacheCore().GetVideoHdrType() == StreamHdrType::HDR_TYPE_HDR10PLUS)
          aml_hdr10plus_attr_override = true;
        break;
      }
      default:
        return false;
    }

    linux_flag_value = aml_linux_force_422;
    hdr10plus_value = aml_hdr10plus_attr_override;
    linux_flag_changed = (linux_flag_value != prev_linux_flag);
    hdr10plus_changed = (hdr10plus_value != prev_hdr10plus);
    new_override = aml_linux_force_422 || aml_hdr10plus_attr_override;
  }

  if (linux_flag_changed)
  {
    CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_aml_linux_force_422", linux_flag_value);
    logM(LOGINFO, "CSysfsPath(xbmc_aml_linux_force_422, {:d})", linux_flag_value);
  }

  if (hdr10plus_changed)
    logM(LOGINFO, "aml_hdr10plus_attr_override={:d}", hdr10plus_value);

  if (cd_cs_type == 1 && (linux_flag_changed || new_override != prev_override))
    logM(LOGINFO, "dv_type={} dv_vp={} linux_flag_value={}", dv_type_value, dv_vp_value,
         linux_flag_value);

  if (new_override != prev_override)
  {
    const auto t_wire = std::chrono::steady_clock::now();
    logM(LOGINFO,
         "cd_cs_type={} prev_override={} new_override={} linux_flag_value={} "
         "hdr10plus_value={}",
         cd_cs_type, prev_override, new_override, linux_flag_value, hdr10plus_value);
    if (new_override)
    {
      CAmlHdmiWireGuard wire(__FUNCTION__);
      if (aml_is_force_422_override_active())
      {
        CSysfsPath("/sys/class/amhdmitx/amhdmitx0/attr", ",422,12bit");
        logM(LOGINFO, "CSysfsPath(amhdmitx0/attr, ,422,12bit)");
        aml_display_mode_round_trip(__FUNCTION__);
      }
    }
    else
    {
      write_current_resolution_ini();
      logM(LOGINFO, "write_current_resolution_ini()");
    }
    const auto wire_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - t_wire).count();
    logM(LOGDEBUG, "aml_kodi_set_cd_cs TIMING: type={} new_override={} prev_override={} wire_work={}ms",
         cd_cs_type, new_override, prev_override, wire_ms);
    return true;
  }

  return false;
}

bool aml_is_force_422_override_active()
{
  return aml_linux_force_422 || aml_hdr10plus_attr_override;
}

static unsigned int aml_vs10_by_hdrtype(StreamHdrType hdrType, unsigned int bitDepth);

bool aml_dv_player_led_output_active(StreamHdrType hdrType, unsigned int bitDepth)
{
  if (aml_dv_mode() == DV_MODE_OFF)
    return false;
  const enum DV_TYPE type = aml_dv_type();
  if ((type != DV_TYPE_PLAYER_LED_LLDV) && (type != DV_TYPE_PLAYER_LED_HDR) &&
      (type != DV_TYPE_PLAYER_LED_HDR2))
    return false;
  const bool hdr10_output =
      ((type == DV_TYPE_PLAYER_LED_HDR) || (type == DV_TYPE_PLAYER_LED_HDR2));
  const unsigned int mode = aml_vs10_by_hdrtype(hdrType, bitDepth);
  if (mode == DOLBY_VISION_OUTPUT_MODE_IPT || mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL)
    return true;
  if (!aml_is_dv_enable())
    return false;
  const unsigned int live = aml_dv_dolby_vision_mode();
  return (live == DOLBY_VISION_OUTPUT_MODE_IPT || live == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
          (hdr10_output && (live == DOLBY_VISION_OUTPUT_MODE_HDR10)));
}

bool aml_dv_eotf_override_active()
{
  if (!aml_is_dv_enable())
    return false;
  const enum DV_TYPE current_dv_type = aml_dv_type();
  const unsigned int current_dv_mode = aml_dv_dolby_vision_mode();
  const bool engine_in_ipt =
      (current_dv_mode == DOLBY_VISION_OUTPUT_MODE_IPT ||
       current_dv_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL);
  return engine_in_ipt && (current_dv_type == DV_TYPE_DISPLAY_LED ||
                           current_dv_type == DV_TYPE_PLAYER_LED_LLDV);
}

unsigned int aml_dv_dolby_vision_mode()
{
  CSysfsPath dolby_vision_mode{"/sys/module/amdolby_vision/parameters/dolby_vision_mode"};
  if (dolby_vision_mode.Exists())
    return dolby_vision_mode.Get<unsigned int>().value();
  else
    return DOLBY_VISION_OUTPUT_MODE_BYPASS;
}

static void aml_apply_pq_input_state(StreamHdrType hdrType, unsigned int bitDepth = 0,
                                     std::optional<unsigned int> override_mode = std::nullopt)
{
  aml_set_linux_osd_sdr8(hdrType, bitDepth, override_mode);

  const bool engine_on_after = override_mode.has_value()
      ? (override_mode.value() != DOLBY_VISION_OUTPUT_MODE_BYPASS)
      : aml_is_dv_enable();
  aml_set_osd_pq_bypass(engine_on_after ? StreamHdrType::HDR_TYPE_NONE : hdrType);
}

static void aml_apply_pq_output_state(StreamHdrType hdrType, unsigned int bitDepth = 0,
                                      std::optional<unsigned int> override_mode = std::nullopt)
{
  aml_set_transfer_pq(hdrType, bitDepth, override_mode);

  aml_set_osd_pq_bypass(aml_is_dv_enable() ? StreamHdrType::HDR_TYPE_NONE : hdrType);
}

void aml_dv_set_vs10_mode(unsigned int mode, StreamHdrType hdrType, bool force)
{
  enum DV_TYPE dv_type(static_cast<DV_TYPE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE)));
  if ((dv_type == DV_TYPE_VS10_ONLY) ||
      (hdrType == StreamHdrType::HDR_TYPE_HDR10PLUS))
    return;

  if (mode != DOLBY_VISION_OUTPUT_MODE_BYPASS &&
      !CServiceBroker::GetDataCacheCore().IsVideoHwDecoder())
  {
    logM(LOGINFO, "aml_dv_set_vs10_mode: refusing VS10 mode {} for software-decoded video (no hardware video layer)",
         aml_dv_output_mode_to_string(mode));
    CGUIDialogKaiToast::QueueNotification(CGUIDialogKaiToast::Info,
                                          g_localizeStrings.Get(60344),
                                          g_localizeStrings.Get(60345));
    return;
  }

  const auto t_vs10_start = std::chrono::steady_clock::now();

  if (mode == DOLBY_VISION_OUTPUT_MODE_SDR10 &&
      hdrType == StreamHdrType::HDR_TYPE_NONE &&
      s_currentColorPrimaries == AVCOL_PRI_BT2020)
  {
    logM(LOGDEBUG, "SDR BT.2020 detected, forcing VS10 SDR10 to BYPASS to preserve gamut");
    mode = DOLBY_VISION_OUTPUT_MODE_BYPASS;
  }

  unsigned int existing_mode = aml_dv_dolby_vision_mode();

  auto is_dv_output = [](unsigned int m) {
    return m == DOLBY_VISION_OUTPUT_MODE_IPT || m == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL;
  };
  if (mode != DOLBY_VISION_OUTPUT_MODE_BYPASS && aml_is_dv_enable() &&
      (mode == existing_mode || (is_dv_output(mode) && is_dv_output(existing_mode))))
  {
    logM(LOGDEBUG, "aml_dv_set_vs10_mode: engine already converting at mode {} - no-op", aml_dv_output_mode_to_string(mode));
    return;
  }

  aml_apply_pq_input_state(hdrType, 0, mode);

  if (mode != DOLBY_VISION_OUTPUT_MODE_BYPASS)
  {
    if (force)
      vs10_conversion = true;
    else if ((existing_mode == mode) || ((mode == DOLBY_VISION_OUTPUT_MODE_IPT) && (hdrType == StreamHdrType::HDR_TYPE_DOLBYVISION)))
      vs10_conversion = false;
    else
      vs10_conversion = true;

    aml_dv_on(mode, force);
  }
  else if (aml_is_dv_enable()) // DV BYPASS, and it is on - then switch it off.
  {
    aml_dv_off();
  }

  aml_apply_pq_output_state(hdrType, 0, mode);

  const auto vs10_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_vs10_start).count();
  logComponentM(LOGDEBUG, LOGVIDEO, "aml_dv_set_vs10_mode TIMING: total={}ms mode={} hdrType={}",
       vs10_ms, aml_dv_output_mode_to_string(mode), static_cast<int>(hdrType));
}

void aml_dv_wait_video_off(int timeout)
{
  // Wait for dv_video_on to unset.
  CSysfsPath dv_video_on{"/sys/class/amdolby_vision/dv_video_on"};
  CSysfsPath dolby_vision_enable{"/sys/module/amdolby_vision/parameters/dolby_vision_enable"};
  if (dv_video_on.Exists())
  {
    CLog::Log(LOGDEBUG, "AMLUtils::{} - DV Video Off - start", __FUNCTION__);
    std::chrono::time_point<std::chrono::system_clock> now(std::chrono::system_clock::now());
    while(true) {
      if (dv_video_on.Get<int>().value() == 0) {
        CLog::Log(LOGDEBUG, "AMLUtils::{} - DV Video Off - done", __FUNCTION__);
        break;
      }
      if (dolby_vision_enable.Exists() &&
          StringUtils::EqualsNoCase(dolby_vision_enable.Get<std::string>().value(), "N")) {
        CLog::Log(LOGDEBUG, "AMLUtils::{} - DV Video Off - skip (engine disabled)", __FUNCTION__);
        break;
      }
      if ((std::chrono::system_clock::now() - now) >= std::chrono::seconds(timeout)) {
        CLog::Log(LOGDEBUG, "AMLUtils::{} - DV Video Off - wait time elapsed", __FUNCTION__);
        break;
      }
      usleep(10000); // wait 10ms
    }
  }
}

static constexpr unsigned int kAmlMpeg2DecControlKeepProgFrame = 0x0040;

static std::optional<unsigned int> aml_read_dec_control(CSysfsPath& path)
{
  const auto raw = path.Get<std::string>();
  if (!raw.has_value())
    return std::nullopt;

  unsigned int value = 0;
  const char* const last = raw->data() + raw->size();
  const auto parsed = std::from_chars(raw->data(), last, value);
  if (parsed.ec != std::errc() || parsed.ptr != last)
    return std::nullopt;

  return value;
}

void aml_set_mpeg2_keep_progressive(bool enable)
{
  CSysfsPath dec_control{"/sys/module/amvdec_mmpeg12/parameters/dec_control"};
  if (!dec_control.Exists())
  {
    logM(LOGWARNING, "mpeg2 keep-progressive {} - dec_control node absent", enable);
    return;
  }

  const auto current = aml_read_dec_control(dec_control);
  if (!current.has_value())
  {
    logM(LOGERROR, "mpeg2 keep-progressive {} - dec_control unreadable, leaving it alone", enable);
    return;
  }

  const unsigned int flags = current.value();
  const unsigned int updated = enable ? (flags | kAmlMpeg2DecControlKeepProgFrame)
                                      : (flags & ~kAmlMpeg2DecControlKeepProgFrame);
  dec_control.Set(updated);

  const auto readback = aml_read_dec_control(dec_control);
  if (!readback.has_value())
  {
    logM(LOGERROR, "mpeg2 keep-progressive {} - dec_control {} -> {} written, readback failed",
         enable, flags, updated);
    return;
  }
  if (readback.value() != updated)
  {
    logM(LOGERROR, "mpeg2 keep-progressive {} - dec_control {} -> {} MISMATCH, readback {}",
         enable, flags, updated, readback.value());
    return;
  }

  logComponentM(LOGDEBUG, LOGVIDEO, "mpeg2 keep-progressive {} - dec_control {} -> {} {}",
                enable, flags, updated, (flags == updated) ? "nochange" : "applied");
}

int aml_blackout_policy(int new_blackout)
{
  CSysfsPath blackout_policy{"/sys/class/video/blackout_policy"};
  if (blackout_policy.Exists())
  {
    int existing_blackout = blackout_policy.Get<int>().value();
    blackout_policy.Set(new_blackout);
    logComponentM(LOGDEBUG, LOGVIDEO, "blackout_policy {} -> {}", existing_blackout, new_blackout);
    return existing_blackout;
  }
  return 0;
}

int aml_osd_blank(int fbIndex, int blankMode)
{
  const std::string blankPath = StringUtils::Format("/sys/class/graphics/fb{}/blank", fbIndex);
  CSysfsPath osd_blank{blankPath};
  if (osd_blank.Exists())
  {
    const int existingBlank = osd_blank.Get<int>().value();
    osd_blank.Set(blankMode);
    return existingBlank;
  }

  return 0;
}

static unsigned int aml_vs10_by_hdrtype(StreamHdrType hdrType, unsigned int bitDepth)
{
  unsigned int vs10_mode = DOLBY_VISION_OUTPUT_MODE_BYPASS;
  switch (hdrType)
  {
    case StreamHdrType::HDR_TYPE_NONE:
      if (bitDepth == 10)
        vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_SDR10);
      else
        vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_SDR8);
      break;
    case StreamHdrType::HDR_TYPE_HDR10:
      vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_HDR10);
      break;
    case StreamHdrType::HDR_TYPE_HDR10PLUS:
      vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_HDR10PLUS);
      break;
    case StreamHdrType::HDR_TYPE_HLG:
    case StreamHdrType::HDR_TYPE_HDR_VIVID:
      vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_HDRHLG);
      break;
    case StreamHdrType::HDR_TYPE_DOLBYVISION:
      vs10_mode = aml_vs10_by_setting(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_DV);
      break;
  }

  return vs10_mode;
}

static void aml_dv_trigger_update_resolution(StreamHdrType hdrType)
{
  auto& components = CServiceBroker::GetAppComponents();
  const auto appPlayer = components.GetComponent<CApplicationPlayer>();
  appPlayer->TriggerUpdateResolutionHdr(hdrType);
}

int aml_get_cpufamily_id()
{
  static int aml_cpufamily_id = -1;
  if (aml_cpufamily_id == -1)
  {
    std::ifstream cpuinfo("/proc/cpuinfo");
    std::regex re(".*: (.*)$");

    for (std::string line; std::getline(cpuinfo, line);)
    {
      if (line.find("Serial") != std::string::npos)
      {
        std::smatch match;

        if (std::regex_match(line, match, re) && match.size() == 2)
        {
          std::ssub_match value = match[1];
          std::string cpu_family = value.str().substr(0, 2);
          aml_cpufamily_id = std::stoi(cpu_family, nullptr, 16);
          break;
        }
      }
    }
  }
  return aml_cpufamily_id;
}

bool aml_display_connected()
{
  CSysfsPath hpd_state{"/sys/class/amhdmitx/amhdmitx0/hpd_state"};
  if (hpd_state.Exists())
    return (hpd_state.Get<int>().value_or(0) == 1);
  return false;
}

bool aml_display_support_hdr_pq()
{
  bool support = false;
  CSysfsPath hdr_cap{"/sys/class/amhdmitx/amhdmitx0/hdr_cap"};
  if (hdr_cap.Exists())
  {
    std::string valstr = hdr_cap.Get<std::string>().value();
    support = (valstr.find("SMPTE ST 2084: 1") != std::string::npos);
  }
  return support;
}

bool aml_display_support_hdr_hlg()
{
  bool support = false;
  CSysfsPath hdr_cap{"/sys/class/amhdmitx/amhdmitx0/hdr_cap"};
  if (hdr_cap.Exists())
  {
    std::string valstr = hdr_cap.Get<std::string>().value();
    support = (valstr.find("Hybrid Log-Gamma: 1") != std::string::npos);
  }
  return support;
}

bool aml_display_support_hdr10plus()
{
  bool support = false;
  CSysfsPath hdr_cap{"/sys/class/amhdmitx/amhdmitx0/hdr_cap"};
  if (hdr_cap.Exists())
    support = (hdr_cap.Get<std::string>().value().find("HDR10Plus Supported: 1") != std::string::npos);
  return support;
}

AMLHdmiAudioCaps aml_get_hdmi_audio_caps()
{
  AMLHdmiAudioCaps caps;

  CSysfsPath aud_cap{"/sys/class/amhdmitx/amhdmitx0/aud_cap"};
  if (!aud_cap.Exists())
    return caps;
  const std::string cap = aud_cap.Get<std::string>().value();
  caps.valid = true;

  auto findLine = [&cap](const char* token) -> std::string {
    const std::size_t tlen = std::char_traits<char>::length(token);
    std::size_t pos = 0;
    while (pos < cap.size())
    {
      const std::size_t eol = cap.find('\n', pos);
      std::string line = cap.substr(pos, eol == std::string::npos ? std::string::npos : eol - pos);
      const std::size_t nb = line.find_first_not_of(" \t");
      if (nb != std::string::npos && line.compare(nb, tlen, token) == 0)
        return line;
      if (eol == std::string::npos)
        break;
      pos = eol + 1;
    }
    return {};
  };
  auto chanOf = [](const std::string& line) -> int {
    if (line.empty())
      return 0;
    const std::size_t chp = line.find(" ch");
    if (chp == std::string::npos || chp == 0)
      return -1;
    const char d = line[chp - 1];
    return (d >= '0' && d <= '9') ? (d - '0') : -1;
  };

  const std::string pcmLine = findLine("PCM");
  caps.pcm_ch = chanOf(pcmLine);
  caps.pcm_192k = caps.pcm_ch != 0 && pcmLine.find("192") != std::string::npos;
  caps.truehd_ch = chanOf(findLine("MAT,"));
  std::string ddpLine = findLine("Dolby_Digital+");
  if (ddpLine.empty())
    ddpLine = findLine("Dobly_Digital+");
  caps.ddp_ch = chanOf(ddpLine);
  caps.ddp_atmos = caps.ddp_ch != 0 && ddpLine.find("ATMOS") != std::string::npos;
  caps.ac3_ch = chanOf(findLine("AC-3"));
  caps.dtshd_ch = chanOf(findLine("DTS-HD"));
  caps.dts_ch = chanOf(findLine("DTS,"));
  return caps;
}

bool aml_display_support_dv_ll()
{
  int support_ll = 0;
  CRegExp regexp;
  regexp.RegComp("LL_YCbCr_422_12BIT");
  std::string valstr;
  CSysfsPath dv_cap{"/sys/devices/virtual/amhdmitx/amhdmitx0/dv_cap"};
  if (dv_cap.Exists())
  {
    valstr = dv_cap.Get<std::string>().value();
    support_ll = (regexp.RegFind(valstr) >= 0) ? 1 : 0;
  }

  return support_ll;
}

bool aml_display_support_dv_std()
{
  int support_std = 0;
  CRegExp regexp;
  regexp.RegComp("DV_RGB_444_8BIT");
  std::string valstr;
  CSysfsPath dv_cap{"/sys/devices/virtual/amhdmitx/amhdmitx0/dv_cap"};
  if (dv_cap.Exists())
  {
    valstr = dv_cap.Get<std::string>().value();
    support_std = (regexp.RegFind(valstr) >= 0) ? 1 : 0;
  }
  return support_std;
}

bool aml_display_support_dv()
{
  int support_dv = 0;
  CRegExp regexp;
  regexp.RegComp("The Rx don't support DolbyVision");
  std::string valstr;
  CSysfsPath dv_cap{"/sys/devices/virtual/amhdmitx/amhdmitx0/dv_cap"};
  if (dv_cap.Exists())
  {
    valstr = dv_cap.Get<std::string>().value();
    support_dv = (regexp.RegFind(valstr) >= 0) ? 0 : 1;
  }
  return support_dv;
}

bool aml_display_support_3d()
{
  static int support_3d = -1;

  if (support_3d == -1)
  {
    CSysfsPath amhdmitx0_support_3d{"/sys/class/amhdmitx/amhdmitx0/support_3d"};
    if (amhdmitx0_support_3d.Exists())
      support_3d = amhdmitx0_support_3d.Get<int>().value();
    else
      support_3d = 0;

    CLog::Log(LOGDEBUG, "AMLUtils: display support 3D: {}", bool(!!support_3d));
  }

  return (support_3d == 1);
}

bool aml_display_support_12bit(int force_cs)
{
  CSysfsPath dc_cap{"/sys/class/amhdmitx/amhdmitx0/dc_cap"};
  if (!dc_cap.Exists())
    return false;
  std::string valstr = dc_cap.Get<std::string>().value();
  switch (force_cs)
  {
    case 1: return valstr.find("rgb,12bit") != std::string::npos;
    case 2: return valstr.find("420,12bit") != std::string::npos;
    case 3: return valstr.find("422,12bit") != std::string::npos;
    case 4: return valstr.find("444,12bit") != std::string::npos;
    default: return (valstr.find("444,12bit") != std::string::npos) &&
                    (valstr.find("422,12bit") != std::string::npos);
  }
}

static bool aml_support_vcodec_profile(const char *regex)
{
  int profile = 0;
  CRegExp regexp;
  regexp.RegComp(regex);
  std::string valstr;
  CSysfsPath vcodec_profile{"/sys/class/amstream/vcodec_profile"};
  if (vcodec_profile.Exists())
  {
    valstr = vcodec_profile.Get<std::string>().value();
    profile = (regexp.RegFind(valstr) >= 0) ? 1 : 0;
  }

  return profile;
}

bool aml_support_hevc()
{
  static int has_hevc = -1;

  if (has_hevc == -1)
      has_hevc = aml_support_vcodec_profile("\\bhevc\\b:");

  return (has_hevc == 1);
}

bool aml_support_hevc_4k2k()
{
  static int has_hevc_4k2k = -1;

  if (has_hevc_4k2k == -1)
    has_hevc_4k2k = aml_support_vcodec_profile("\\bhevc\\b:(?!\\;).*(4k|8k)");

  return (has_hevc_4k2k == 1);
}

bool aml_support_hevc_8k4k()
{
  static int has_hevc_8k4k = -1;

  if (has_hevc_8k4k == -1)
    has_hevc_8k4k = aml_support_vcodec_profile("\\bhevc\\b:(?!\\;).*8k");

  return (has_hevc_8k4k == 1);
}

bool aml_support_hevc_10bit()
{
  static int has_hevc_10bit = -1;

  if (has_hevc_10bit == -1)
    has_hevc_10bit = aml_support_vcodec_profile("\\bhevc\\b:(?!\\;).*10bit");

  return (has_hevc_10bit == 1);
}

AML_SUPPORT_H264_4K2K aml_support_h264_4k2k()
{
  static AML_SUPPORT_H264_4K2K has_h264_4k2k = AML_SUPPORT_H264_4K2K_UNINIT;

  if (has_h264_4k2k == AML_SUPPORT_H264_4K2K_UNINIT)
  {
    has_h264_4k2k = AML_NO_H264_4K2K;

    if (aml_support_vcodec_profile("\\bh264\\b:4k"))
      has_h264_4k2k = AML_HAS_H264_4K2K_SAME_PROFILE;
    else if (aml_support_vcodec_profile("\\bh264_4k2k\\b:"))
      has_h264_4k2k = AML_HAS_H264_4K2K;
  }
  return has_h264_4k2k;
}

bool aml_support_vp9()
{
  static int has_vp9 = -1;

  if (has_vp9 == -1)
    has_vp9 = aml_support_vcodec_profile("\\bvp9\\b:(?!\\;).*compressed");

  return (has_vp9 == 1);
}

bool aml_support_av1()
{
  static int has_av1 = -1;

  if (has_av1 == -1)
    has_av1 = aml_support_vcodec_profile("\\bav1\\b:(?!\\;).*compressed");

  return (has_av1 == 1);
}

bool aml_support_dolby_vision()
{
  static int support_dv = -1;

  if (support_dv == -1)
  {
    CSysfsPath support_info{"/sys/class/amdolby_vision/support_info"};
    support_dv = 0;
    if (support_info.Exists())
    {
      support_dv = (int)((support_info.Get<int>().value() & 7) == 7);
      if (support_dv == 1) {
        CSysfsPath ko_info{"/sys/class/amdolby_vision/ko_info"};
        if (ko_info.Exists())
          CLog::Log(LOGDEBUG, "Amlogic Dolby Vision info: {}", ko_info.Get<std::string>().value().c_str());
      }
    }
  }

  return (support_dv == 1);
}

bool aml_dolby_vision_enabled()
{
  static int dv_enabled = -1;
  bool dv_user_enabled(aml_dv_mode() != DV_MODE_OFF);

  if (dv_enabled == -1)
    dv_enabled = (!!aml_support_dolby_vision());

  return ((dv_enabled && !!dv_user_enabled) == 1);
}

std::string aml_dv_output_mode_to_string(unsigned int mode)
{
  std::string mode_string = "Unknown";
  switch (mode) {
    case DOLBY_VISION_OUTPUT_MODE_IPT:
      mode_string = "0-IPT";
      break;
    case DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL:
      mode_string = "1-IPT Tunnel";
      break;
    case DOLBY_VISION_OUTPUT_MODE_HDR10:
      mode_string = "2-HDR10";
      break;
    case DOLBY_VISION_OUTPUT_MODE_SDR10:
      mode_string = "3-SDR10";
      break;
    case DOLBY_VISION_OUTPUT_MODE_BYPASS:
      mode_string = "5-Bypass";
      break;
  }
  return mode_string;
}

std::string aml_dv_mode_to_string(enum DV_MODE mode)
{
  std::string mode_string = "Unknown";
  switch (mode) {
    case DV_MODE::DV_MODE_ON:
      mode_string = "0-On";
      break;
    case DV_MODE::DV_MODE_ON_DEMAND:
      mode_string = "1-On Demand";
      break;
    case DV_MODE::DV_MODE_OFF:
      mode_string = "2-Off";
      break;
  }
  return mode_string;
}

std::string aml_dv_type_to_string(enum DV_TYPE type)
{
  std::string type_string = "Unknown";
  switch (type) {
    case DV_TYPE::DV_TYPE_DISPLAY_LED:
      type_string = "0-Display Led (DV-Std)";
      break;
    case DV_TYPE::DV_TYPE_PLAYER_LED_LLDV:
      type_string = "1-Player Led (DV-LL)";
      break;
    case DV_TYPE::DV_TYPE_PLAYER_LED_HDR:
      type_string = "2-Player Led (HDR)";
      break;
    case DV_TYPE::DV_TYPE_VS10_ONLY:
      type_string = "3-VS10 Only";
      break;
    case DV_TYPE::DV_TYPE_PLAYER_LED_HDR2:
      type_string = "4-Player Led (HDR2)";
      break;
  }
  return type_string;
}

void aml_apply_hdr10_overrides()
{
  const bool limiter = settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_HDR10_LIMITER);
  const int max_lum = limiter ? settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_HDR10_MAX_LUMINANCE) : 0;
  const int max_cll = limiter ? settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_HDR10_MAX_CLL) : 0;
  CSysfsPath("/sys/module/hdmitx20/parameters/xbmc_hdr10_max_lum_override", static_cast<unsigned int>(max_lum));
  CSysfsPath("/sys/module/hdmitx20/parameters/xbmc_hdr10_max_cll_override", static_cast<unsigned int>(max_cll));
  CServiceBroker::GetDataCacheCore().SetHdr10Overrides(static_cast<uint32_t>(max_lum),
                                                       static_cast<uint32_t>(max_cll));
  logComponentM(LOGDEBUG, LOGVIDEO, "aml_apply_hdr10_overrides: max_lum={} max_cll={}",
                max_lum, max_cll);
}

bool aml_dv_vs10_converting()
{
  return vs10_conversion.load(std::memory_order_relaxed);
}

bool aml_dv_refresh_vs10_converting(StreamHdrType hdrType, unsigned int bitDepth)
{
  const unsigned int stream_vs10_mode = aml_vs10_by_hdrtype(hdrType, bitDepth);
  const bool converting =
      (stream_vs10_mode != DOLBY_VISION_OUTPUT_MODE_BYPASS) &&
      ((hdrType != StreamHdrType::HDR_TYPE_DOLBYVISION) ||
       (stream_vs10_mode == DOLBY_VISION_OUTPUT_MODE_SDR10) ||
       (stream_vs10_mode == DOLBY_VISION_OUTPUT_MODE_HDR10));
  vs10_conversion = converting;
  return converting;
}

bool aml_dv_vsvdb_v1_enabled()
{
  return CServiceBroker::GetSettingsComponent()->GetAdvancedSettings()->m_dvVsvdbV1Enabled;
}

void aml_dv_write_vsvdb_policy()
{
  CSysfsPath xbmc_dv_vsvdb_v1{"/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_v1"};
  if (xbmc_dv_vsvdb_v1.Exists())
    xbmc_dv_vsvdb_v1.Set(aml_dv_vsvdb_v1_enabled());
  else
    logM(LOGERROR, "aml_dv_write_vsvdb_policy: xbmc_dv_vsvdb_v1 is missing, the kernel VSVDB policy is unmanaged");
}

void set_vsvdb_payload_ver(enum DV_TYPE dv_type, int max_lum_nits_value, int source_max_pq)
{
  static thread_local bool inRecompute = false;
  if (inRecompute)
    return;
  inRecompute = true;

  // cs == 4 (EPSON LS12000, ported from Pannal PR #25) always forces V2 -- its
  // custom/hardcoded coordinates are only handled by CalculateVSVDBPayload_2.
  int cs(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VSVDB_CS));
  if (!aml_dv_vsvdb_v1_enabled() ||
      (cs == 4) ||
      (dv_type == DV_TYPE_DISPLAY_LED) ||
      (max_lum_nits_value < 400) ||
      ((max_lum_nits_value > 6450) && (source_max_pq == 4095)))
    CalculateVSVDBPayload_2(dv_type);
  else
    CalculateVSVDBPayload();

  inRecompute = false;
}

unsigned int aml_dv_on(unsigned int mode, bool force)
{
  CDVCoreGuard dvlock(__FUNCTION__);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_on: skipped, the DV-core lock holder is stalled");
    return mode;
  }
  const auto t_on_start = std::chrono::steady_clock::now();

  bool dv_source_level_5(settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_STD_SOURCE_LEVEL_5));
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5", dv_source_level_5);

  bool dv_source_level_5_osdst(settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_STD_SOURCE_LEVEL_5_OSDST));
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5_osd_st", dv_source_level_5_osdst);

  const int dv_l5_subs_signal_mode_val = dv_source_level_5 ? aml_dv_l5_subs_signal_mode() : 0;
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5_subs_st", dv_l5_subs_signal_mode_val > 0);

  unsigned int xbmc_dv_vsvdb_source_lum_limit_num = 0;
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_source_lum_limit_num", xbmc_dv_vsvdb_source_lum_limit_num);

  xbmc_dv_cap::dv_ver_i = 0;
  aml_get_dv_cap();
  enum DV_COLORIMETRY colorimetry = DV_COLORIMETRY_AMLOGIC;
  if (xbmc_dv_cap::dv_ver_i == 2) colorimetry = DV_COLORIMETRY_REMOVE;
  CSysfsPath("/sys/module/hdmitx20/parameters/dovi_tv_led_bt2020", (colorimetry == DV_COLORIMETRY_BT2020NC) ? 'Y' : 'N');
  CSysfsPath("/sys/module/hdmitx20/parameters/dovi_tv_led_no_colorimetry", (colorimetry == DV_COLORIMETRY_REMOVE) ? 'Y' : 'N');

  DOVIStreamMetadata dovi_stream_metadata;
  dovi_stream_metadata = CServiceBroker::GetDataCacheCore().GetVideoDoViStreamMetadata();
  int source_max_pq = static_cast<int>(dovi_stream_metadata.source_max_pq);
  enum DV_TYPE dv_type(static_cast<DV_TYPE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE)));
  int max_lum_nits_value(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VSVDB_MAX_LUM));

  bool dv_type_vp_auto(settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE_VP_AUTO));
  unsigned int dv_vp(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VIDEO_PROCESSOR));

  if (vs10_conversion || (dv_vp != 0) || (dv_type == DV_TYPE_DISPLAY_LED) || (max_lum_nits_value < max_pq_to_nits(source_max_pq)))
    dv_type_vp_auto = false;

  if (dv_type_vp_auto)
  {
    switch (dv_type)
    {
      case DV_TYPE_PLAYER_LED_HDR:
        dv_vp = 1;
        break;
      case DV_TYPE_PLAYER_LED_HDR2:
        dv_vp = 2;
        break;
      case DV_TYPE_PLAYER_LED_LLDV:
        dv_vp = 3;
        break;
      default:
        break;
    }
  }

  const RESOLUTION_INFO res = CDisplaySettings::GetInstance().GetResolutionInfo(
      CDisplaySettings::GetInstance().GetCurrentResolution());
  const bool is_display_4k_50_60 = kernel_display_is_4k_50_60();
  if (is_display_4k_50_60 && ((dv_vp == 4) || (dv_vp == 5)))
  {
    if (dv_vp == 4) dv_vp = 6;
    else if (dv_vp == 5) dv_vp = 7;
  }

  if (vs10_conversion && (dv_vp != 0))
  {
    switch (dv_vp)
    {
      case 1:
        dv_type = DV_TYPE_PLAYER_LED_HDR;
        break;
      case 2:
        dv_type = DV_TYPE_PLAYER_LED_HDR2;
        break;
      case 3:
        dv_type = DV_TYPE_PLAYER_LED_LLDV;
        break;
      case 4:
        dv_type = DV_TYPE_PLAYER_LED_LLDV;
        break;
      case 6:
        dv_type = DV_TYPE_PLAYER_LED_LLDV;
        break;
      default:
        break;
    }
    dv_vp = 0;
    vs10_conversion = false;
  }
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vp", dv_vp);

  unsigned int dv_vp_tm(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VIDEO_PROCESSOR_TM));
  dv_vp_tm = 4;
  CSysfsPath dvprofile{"/sys/module/amdolby_vision/parameters/xbmc_dv_profile"};
  if (dvprofile.Exists())
  {
    unsigned int dv_profile = dvprofile.Get<unsigned int>().value();
    if ((dv_vp != 0) && (dv_vp_tm > 3) && (dv_profile == 5)) dv_vp_tm = 3;
    if ((dv_vp != 0) && (dv_vp_tm > 2) && ((dv_vp == 5) || (dv_vp == 7))) dv_vp_tm = 2;
  }
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vp_tm", dv_vp_tm);

  if (dv_vp > 2) dv_type = DV_TYPE_PLAYER_LED_LLDV;
  else if (dv_vp == 1) dv_type = DV_TYPE_PLAYER_LED_HDR;
  else if (dv_vp == 2) dv_type = DV_TYPE_PLAYER_LED_HDR2;
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_type", static_cast<unsigned int>(dv_type));

  const bool wire_reloaded_by_set_cd_cs = aml_kodi_set_cd_cs(1);

  const bool dv_mode_is_ipt = (mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
                                mode == DOLBY_VISION_OUTPUT_MODE_IPT);
  bool dv_deep_color = settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_PREFER_12BIT)
                    && (dv_mode_is_ipt
                        || aml_display_support_12bit(
                             settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_FORCE_CS)));
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_deep_color", dv_deep_color);
  logComponentM(LOGDEBUG, LOGVIDEO, "prefer.12bit setting={} dv_mode_is_ipt={} edid_12bit={} -> xbmc_dv_deep_color={}",
                settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_PREFER_12BIT),
                dv_mode_is_ipt, aml_display_support_12bit(), dv_deep_color);

  aml_dv_set_sdr_source_max_nits(aml_dv_sdr_boost_param());

  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_for_dv_ll", ((dv_type == DV_TYPE_PLAYER_LED_HDR) || (dv_type == DV_TYPE_PLAYER_LED_HDR2)) ? 'Y' : 'N');
  unsigned int xbmc_dv_hdr10_for_dv_ll_inject_num = 0;
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_for_dv_ll_inject_num", xbmc_dv_hdr10_for_dv_ll_inject_num);

  bool dv_dolby_vsvdb_inject(settings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_VSVDB_INJECT));
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_inject", dv_dolby_vsvdb_inject);
  unsigned int xbmc_dv_vsvdb_inject_num = 0;
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_inject_num", xbmc_dv_vsvdb_inject_num);

  set_vsvdb_payload_ver(dv_type, max_lum_nits_value, source_max_pq);

  std::string dv_dolby_vsvdb_payload(settings()->GetString(CSettings::SETTING_COREELEC_AMLOGIC_DV_VSVDB_PAYLOAD));
  if ((dv_vp != 0) && (dv_vp_tm > 1))
    dv_dolby_vsvdb_payload = "27FE012E5699AA";
  else if ((dv_vp != 0) && (dv_vp_tm == 1))
    dv_dolby_vsvdb_payload = "27FE012D5699AA";
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_payload", dv_dolby_vsvdb_payload);

  // setup display led or player led
  CSysfsPath dolby_vision_flags{"/sys/module/amdolby_vision/parameters/dolby_vision_flags"};
  CSysfsPath dolby_vision_ll_policy{"/sys/module/amdolby_vision/parameters/dolby_vision_ll_policy"};

  if (dolby_vision_flags.Exists() && dolby_vision_ll_policy.Exists())
  {
     // Display Led (DV-Std)
    if (dv_type == DV_TYPE_DISPLAY_LED)
    {
      dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_FORCE_RGB_OUTPUT));
      dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_FORCE_DOVI_LL));
      dolby_vision_ll_policy.Set(DOLBY_VISION_LL_DISABLE);
    }
    // Player Led (DV-LL and HDR) or VS10 Only.
    else
    {
      if ((dv_vp == 5) || (dv_vp == 7))
      {
        dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() | FLAG_FORCE_DOVI_LL);
        dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() | FLAG_FORCE_RGB_OUTPUT);
        dolby_vision_ll_policy.Set(DOLBY_VISION_LL_RGB444);
      }
      else
      {
        dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_FORCE_RGB_OUTPUT));
        dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() | FLAG_FORCE_DOVI_LL);
        dolby_vision_ll_policy.Set(DOLBY_VISION_LL_YUV422);
      }
    }
  }

  // switch mode to IPT Tunnel if IPT and type is DV_TYPE_DISPLAY_LED.
  if ((mode == DOLBY_VISION_OUTPUT_MODE_IPT) && (dv_type == DV_TYPE_DISPLAY_LED)) 
    mode = DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL;

  // change mode and enable.
  unsigned int existing_mode = aml_dv_dolby_vision_mode();
  bool modeChange(force || (existing_mode != mode));
  CLog::Log(LOGDEBUG, "AMLUtils::{} - mode change [{}], existing mode [{}], this mode [{}]", __FUNCTION__, modeChange, aml_dv_output_mode_to_string(existing_mode), aml_dv_output_mode_to_string(mode));

  const bool was_ipt = (existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
                        existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT);
  const bool will_be_ipt = (mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
                            mode == DOLBY_VISION_OUTPUT_MODE_IPT);
  if (modeChange && !will_be_ipt && !wire_reloaded_by_set_cd_cs)
  {
    std::string fmt_attr;
    {
      CAmlHdmiWireGuard wire(__FUNCTION__);
      fmt_attr = compute_bandwidth_safe_fmt_attr(res);
      CSysfsPath("/sys/class/amhdmitx/amhdmitx0/attr", fmt_attr);
    }
    logM(LOGDEBUG, "aml_dv_on - bandwidth-safe wire fmt_attr pre-write before non-IPT mode change ({}): [{}]",
         was_ipt ? "IPT-exit" : "non-IPT entry", fmt_attr);
  }

  if (modeChange) CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_mode", mode);
  CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_policy", DOLBY_VISION_FORCE_OUTPUT_MODE);
  CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_enable", "Y");

  if (modeChange)
  {
    aml_dv_toggle_frame(mode);

    // Re-trigger update resolution when mode IPT Tunnel and in Display Led (DV-Std).
    // Work around CD 12 bit issue for DV-Std shoule be CD 8 bit.
    // Wait for Dolby VSIF being output before trigging the update resolution so logic has correct input to work from.
    // The update resolution will cause the hdmi mode switch logic in the kernel to set the colour bit depth correctly in DV-Std.
    if ((mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL) && (dv_type == DV_TYPE_DISPLAY_LED))
      aml_dv_wait_dv_std_vsif_packet();

    if ((mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL) || (mode == DOLBY_VISION_OUTPUT_MODE_IPT))
    {
      aml_dv_trigger_update_resolution(StreamHdrType::HDR_TYPE_DOLBYVISION); // Required for 60Hz VS10 > DV.
      aml_dv_display_auto_now();
    }
  }

  if (!wire_reloaded_by_set_cd_cs &&
      !(dv_type == DV_TYPE_DISPLAY_LED &&
        (mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
         mode == DOLBY_VISION_OUTPUT_MODE_IPT)))
    write_current_resolution_ini();

  const auto on_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_on_start).count();
  logM(LOGDEBUG, "aml_dv_on TIMING: total={}ms mode={} dv_type={} wire_reloaded_by_set_cd_cs={} modeChange={}",
       on_ms, aml_dv_output_mode_to_string(mode), static_cast<int>(dv_type),
       wire_reloaded_by_set_cd_cs, modeChange);
  return mode;
}

static void aml_dv_clear_stream_metadata()
{
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_profile", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_el_type", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_cll", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_fall", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_lum", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_min_lum", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_source_max_pq", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_source_min_pq", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_cll", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_fall", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_lum", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_min_lum", 0);
  CServiceBroker::GetDataCacheCore().SetDvLevel6Limits(0, 0);
}

void aml_dv_off(bool restoreFollows)
{
  CDVCoreGuard dvlock(__FUNCTION__);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_off: skipped, the DV-core lock holder is stalled");
    return;
  }
  const auto t_off_start = std::chrono::steady_clock::now();

  // change mode and disable.
  unsigned int existing_mode = aml_dv_dolby_vision_mode();
  bool modeChange(existing_mode != DOLBY_VISION_OUTPUT_MODE_BYPASS);

  CLog::Log(LOGDEBUG, "AMLUtils::{} - mode change [{}], existing mode [{}], this mode [{}]", 
    __FUNCTION__, modeChange,
    aml_dv_output_mode_to_string(existing_mode), 
    aml_dv_output_mode_to_string(DOLBY_VISION_OUTPUT_MODE_BYPASS));

  CSysfsPath dolby_vision_flags{"/sys/module/amdolby_vision/parameters/dolby_vision_flags"};
  CSysfsPath dolby_vision_ll_policy{"/sys/module/amdolby_vision/parameters/dolby_vision_ll_policy"};
  if (dolby_vision_flags.Exists() && dolby_vision_ll_policy.Exists())
  {
    dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_FORCE_RGB_OUTPUT));
    dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_FORCE_DOVI_LL));
    dolby_vision_flags.Set(dolby_vision_flags.Get<unsigned int>().value() & ~(FLAG_TOGGLE_FRAME));
    dolby_vision_ll_policy.Set(DOLBY_VISION_LL_DISABLE);
  }

  CSysfsPath amdolby_vision_debug{"/sys/class/amdolby_vision/debug"};
  if (amdolby_vision_debug.Exists()) CSysfsPath("/sys/class/amdolby_vision/debug", "enable_fel 0");
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vp", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vp_tm", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_for_dv_ll", 'N');
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_for_dv_ll_inject_num", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_inject", false);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_inject_num", 0);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_vsvdb_payload", std::string{});
  aml_dv_write_vsvdb_policy();
  aml_dv_clear_stream_metadata();

  // First allow system to reset to follow source, then turn off DV.
  {
    CAmlDvWireStep step("dv_policy_follow");
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_policy", DOLBY_VISION_FOLLOW_SOURCE);
  }
  if (modeChange) aml_dv_toggle_frame(DOLBY_VISION_OUTPUT_MODE_BYPASS);
  {
    CAmlDvWireStep step("dv_enable_N");
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_enable", "N");
  }

  // Finally reset back to bypass for consistency.
  {
    CAmlDvWireStep step("dv_policy_force");
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_policy", DOLBY_VISION_FORCE_OUTPUT_MODE);
  }
  if (modeChange)
  {
    CAmlDvWireStep step("dv_mode_bypass");
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_mode", DOLBY_VISION_OUTPUT_MODE_BYPASS);
  }

  const StreamHdrType source_hdr = CServiceBroker::GetDataCacheCore().GetVideoHdrType();
  CServiceBroker::GetWinSystem()->GetGfxContext().SetHDRType(source_hdr);

  enum DV_TYPE dv_type(static_cast<DV_TYPE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE)));
  const bool was_ipt = (existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL ||
                        existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT);
  const bool restoreWillWrite =
      restoreFollows && (aml_linux_force_422 || aml_hdr10plus_attr_override);
  if (was_ipt && dv_type == DV_TYPE_DISPLAY_LED)
  {
    if (!restoreWillWrite)
      write_current_resolution_ini();
  }
  else if (aml_linux_force_422 && was_ipt)
  {
    aml_dv_display_auto_now();
    if (!restoreWillWrite)
      write_current_resolution_ini();
  }

  const auto off_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_off_start).count();
  logM(LOGDEBUG, "aml_dv_off TIMING: total={}ms modeChange={} existing_mode={} restoreFollows={} wireWriteSkipped={}",
       off_ms, modeChange, aml_dv_output_mode_to_string(existing_mode), restoreFollows,
       restoreWillWrite);
}

void aml_dv_open(StreamHdrType hdrType, unsigned int bitDepth, AVColorPrimaries colorPrimaries, bool swDecoded)
{
  s_dvPlaybackActive = true;

  CDVCoreGuard dvlock(__FUNCTION__);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_open: skipped, the DV-core lock holder is stalled");
    return;
  }
  const auto t_open_start = std::chrono::steady_clock::now();

  s_currentColorPrimaries = colorPrimaries;

  const unsigned int stream_vs10_mode = aml_vs10_by_hdrtype(hdrType, bitDepth);
  if (stream_vs10_mode != DOLBY_VISION_OUTPUT_MODE_IPT &&
      stream_vs10_mode != DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL)
    aml_dv_clear_stream_metadata();

  aml_dv_refresh_vs10_converting(hdrType, bitDepth);

  enum DV_MODE dv_mode(aml_dv_mode());
  if (s_dvDiscSession)
  {
    const bool outputDovi = !swDecoded &&
                            (dv_mode == DV_MODE_ON || dv_mode == DV_MODE_ON_DEMAND) &&
                            (stream_vs10_mode == DOLBY_VISION_OUTPUT_MODE_IPT ||
                             stream_vs10_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL);
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_vsif_hold", outputDovi ? 1 : 0);
    logM(LOGDEBUG, "aml_dv_open - disc session VSIF hold={} (hdrType={} vs10_mode={})",
         outputDovi, static_cast<int>(hdrType), stream_vs10_mode);
  }
  CLog::Log(LOGDEBUG, "AMLUtils::{} - Checking DV for DV mode: [{}], DV type: [{}]", __FUNCTION__, aml_dv_mode_to_string(dv_mode), aml_dv_type_to_string(aml_dv_type()));
  if (dv_mode == DV_MODE_ON || dv_mode == DV_MODE_ON_DEMAND)
  {
    if (swDecoded)
    {
      logM(LOGINFO, "aml_dv_open: software-decoded video, forcing VS10 Bypass (no hardware video layer)");
      aml_apply_pq_input_state(hdrType, bitDepth, DOLBY_VISION_OUTPUT_MODE_BYPASS);
      if (aml_is_dv_enable())
        aml_dv_off();
      else
        write_current_resolution_ini();
      aml_apply_pq_output_state(hdrType, bitDepth, DOLBY_VISION_OUTPUT_MODE_BYPASS);
      return;
    }

    if (stream_vs10_mode == DOLBY_VISION_OUTPUT_MODE_SDR10 &&
        hdrType == StreamHdrType::HDR_TYPE_NONE &&
        colorPrimaries == AVCOL_PRI_BT2020)
    {
      logM(LOGDEBUG, "SDR BT.2020 detected, bypassing VS10 SDR10 to preserve gamut");
      aml_apply_pq_input_state(hdrType, bitDepth, DOLBY_VISION_OUTPUT_MODE_BYPASS);
      if (aml_is_dv_enable())
        aml_dv_off();
      else
        write_current_resolution_ini();
      aml_apply_pq_output_state(hdrType, bitDepth, DOLBY_VISION_OUTPUT_MODE_BYPASS);
      const auto open_ms_early = std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - t_open_start).count();
      logM(LOGDEBUG, "aml_dv_open TIMING: total={}ms hdrType={} bitDepth={} exit=SDR_BT2020_BYPASS",
           open_ms_early, static_cast<int>(hdrType), bitDepth);
      return;
    }

    unsigned int vs10_mode = stream_vs10_mode;
    aml_apply_pq_input_state(hdrType, bitDepth, vs10_mode);

    if (vs10_mode != DOLBY_VISION_OUTPUT_MODE_BYPASS)
    {
      if (dv_mode == DV_MODE_ON_DEMAND)
        aml_dv_reset_osd_max();
      vs10_mode = aml_dv_on(vs10_mode);
    }
    else if (aml_is_dv_enable() && vs10_mode == DOLBY_VISION_OUTPUT_MODE_BYPASS) // DV BYPASS, and it is on - then switch it off.
      aml_dv_off();
    else
      write_current_resolution_ini();

    bool content_is_dv(hdrType == StreamHdrType::HDR_TYPE_DOLBYVISION);
    CLog::Log(LOGDEBUG, "AMLUtils::{} - DV is [{}], requested with vs10 mode: [{}], set for: [{}]",  __FUNCTION__, aml_is_dv_enable(), aml_dv_output_mode_to_string(vs10_mode), content_is_dv ? "content" : "mapping");
  }
  else
  {
    aml_apply_pq_input_state(hdrType, bitDepth);
    write_current_resolution_ini();
  }

  aml_apply_pq_output_state(hdrType, bitDepth);

  const auto open_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_open_start).count();
  logM(LOGDEBUG, "aml_dv_open TIMING: total={}ms hdrType={} bitDepth={} dv_mode={} dv_engaged={}",
       open_ms, static_cast<int>(hdrType), bitDepth,
       static_cast<int>(dv_mode), aml_is_dv_enable());
}

void aml_dv_close()
{
  s_dvPlaybackActive = false;

  CDVCoreGuard dvlock(__FUNCTION__);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_close: skipped, the DV-core lock holder is stalled");
    return;
  }
  const auto t_close_start = std::chrono::steady_clock::now();

  s_currentColorPrimaries = AVCOL_PRI_UNSPECIFIED;

  unsigned int existing_mode = aml_dv_dolby_vision_mode();
  if ((aml_dv_mode() == DV_MODE_ON) && ((existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT) || (existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL)))
  {
    aml_apply_pq_input_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
    aml_apply_pq_output_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
    const auto close_ms_early = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - t_close_start).count();
    logM(LOGDEBUG, "aml_dv_close TIMING: total={}ms existing_mode={} dv_mode={} exit=DV_ON_IPT_keep",
         close_ms_early, aml_dv_output_mode_to_string(existing_mode), static_cast<int>(aml_dv_mode()));
    return;
  }

  if (s_dvDiscSession && aml_is_dv_enable() && (aml_dv_mode() == DV_MODE_ON_DEMAND) &&
      ((existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT) || (existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL)))
  {
    aml_apply_pq_input_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
    aml_apply_pq_output_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
    aml_dv_reset_osd_max();
    const auto close_ms_keep = std::chrono::duration_cast<std::chrono::milliseconds>(
        std::chrono::steady_clock::now() - t_close_start).count();
    logM(LOGDEBUG, "aml_dv_close TIMING: total={}ms existing_mode={} dv_mode={} exit=disc_session_keep",
         close_ms_keep, aml_dv_output_mode_to_string(existing_mode), static_cast<int>(aml_dv_mode()));
    return;
  }

  if (aml_dv_mode() != DV_MODE_ON)
    aml_apply_pq_input_state(StreamHdrType::HDR_TYPE_NONE, 0);

  if (aml_is_dv_enable() && (aml_dv_mode() == DV_MODE_ON_DEMAND))
    aml_dv_off(true);
  else if (CServiceBroker::GetDataCacheCore().GetVideoHdrType() != StreamHdrType::HDR_TYPE_NONE &&
           aml_dv_mode() != DV_MODE_ON)
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_enable", "N");

  if (aml_kodi_restore_cd_cs() && !aml_is_dv_enable())
  {
    write_current_resolution_ini();
    logM(LOGINFO, "write_current_resolution_ini()");
  }

  if (aml_dv_mode() != DV_MODE_ON)
    aml_apply_pq_output_state(StreamHdrType::HDR_TYPE_NONE, 0);

  aml_dv_start();

  const auto close_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_close_start).count();
  logM(LOGDEBUG, "aml_dv_close TIMING: total={}ms existing_mode={} dv_mode={} dv_engaged_after={}",
       close_ms, aml_dv_output_mode_to_string(existing_mode), static_cast<int>(aml_dv_mode()), aml_is_dv_enable());
}

bool aml_dv_playback_active()
{
  return s_dvPlaybackActive;
}

void aml_dv_restore_gui_osd_max()
{
  if (aml_dv_mode() != DV_MODE_ON)
    return;

  CDVCoreGuard dvlock(__FUNCTION__, CDVCoreGuard::Acquire::Abortable);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_restore_gui_osd_max: skipped, the DV-core lock holder is stalled");
    return;
  }

  if (!aml_is_dv_enable() || aml_dv_playback_active())
  {
    logM(LOGDEBUG, "aml_dv_restore_gui_osd_max: skipped, dv_engaged={} playback_active={}",
         aml_is_dv_enable(), aml_dv_playback_active());
    return;
  }

  aml_dv_reset_osd_max();
  logM(LOGDEBUG, "aml_dv_restore_gui_osd_max: GUI OSD luminance restored");
}

void aml_dv_set_osd_max(int max)
{
  static std::mutex osdMaxLock;
  static int lastMax = -1;
  std::lock_guard<std::mutex> lock(osdMaxLock);
  if (max == lastMax)
    return;
  lastMax = max;
  // Set the OSD DV graphic max.
  CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_graphic_max", max);
}

int aml_dv_sdr_boost_param()
{
  int mode = settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_SDR_BOOST);
  if (mode == 2)
    return settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_VS10_SDR_SRC_MAX_NITS);
  return mode;
}

void aml_dv_set_sdr_source_max_nits(int value)
{
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_sdr_src_max_nits", value);
}

bool aml_is_dv_enable()
{
  CSysfsPath dolby_vision_enable{"/sys/module/amdolby_vision/parameters/dolby_vision_enable"};
  return (dolby_vision_enable.Exists() && StringUtils::EqualsNoCase(dolby_vision_enable.Get<std::string>().value(), "Y"));
}

static void aml_display_mode_round_trip(const char* fn)
{
  CAmlDvWireStep step("mode_round_trip");
  CSysfsPath display_mode{"/sys/class/display/mode"};
  if (!display_mode.Exists()) return;
  CAmlHdmiWireGuard wire(__FUNCTION__);
  const std::string cur = display_mode.Get<std::string>().value_or("");
  if (cur != "null" && !cur.empty())
  {
    display_mode.Set(cur);
    return;
  }
  std::lock_guard<std::mutex> lk(s_lastDisplayModeMutex);
  if (!s_lastDisplayMode.empty() && s_lastDisplayMode != "null")
  {
    logM(LOGWARNING,
         "display/mode read as '{}' during round-trip from {} — recovering to last-known [{}]",
         cur.empty() ? "(empty)" : cur, fn, s_lastDisplayMode);
    display_mode.Set(s_lastDisplayMode);
  }
  else
  {
    logM(LOGWARNING,
         "display/mode read as '{}' during round-trip from {} — no last-known mode to recover to; skipping write",
         cur.empty() ? "(empty)" : cur, fn);
  }
}

void aml_dv_display_trigger()
{
  CDVCoreGuard dvlock(__FUNCTION__, CDVCoreGuard::Acquire::Abortable);
  if (!dvlock.Owns())
  {
    s_dvTriggerPending.store(true, std::memory_order_relaxed);
    return;
  }
  if (aml_is_dv_enable())
    aml_display_mode_round_trip(__FUNCTION__);
}

void aml_dv_display_trigger_tick()
{
  if (!s_dvTriggerPending.load(std::memory_order_relaxed))
    return;

  static int64_t s_nextAttemptMs = 0;
  static int s_deferredAttempts = 0;
  const int64_t now = aml_steady_ms();
  if (now < s_nextAttemptMs)
    return;
  s_nextAttemptMs = now + kDvTriggerRetryMs;

  {
    CDVCoreGuard dvlock(__FUNCTION__, CDVCoreGuard::Acquire::TryOnce);
    if (dvlock.Owns())
    {
      s_dvTriggerPending.store(false, std::memory_order_relaxed);
      s_deferredAttempts = 0;
      if (aml_is_dv_enable())
        aml_display_mode_round_trip(__FUNCTION__);
      return;
    }
  }

  if (++s_deferredAttempts < kDvTriggerRetryGiveUp)
    return;

  s_deferredAttempts = 0;
  s_dvTriggerPending.store(false, std::memory_order_relaxed);
  const char* holder = s_dvCoreHolder.load(std::memory_order_relaxed);
  logM(LOGWARNING,
       "DV display trigger: DV-core lock still held by {} after {}ms deferred, re-asserting the "
       "display mode without it",
       holder ? holder : "<unknown>", kDvTriggerRetryMs * kDvTriggerRetryGiveUp);
  if (aml_is_dv_enable())
    aml_display_mode_round_trip(__FUNCTION__);
}

void aml_dv_display_auto_now()
{
  // hdmi tx store attr "now" - will trigger set_disp_mode_auto.
  CAmlDvWireStep step("attr_now");
  CAmlHdmiWireGuard wire(__FUNCTION__);
  CSysfsPath attr{"/sys/class/amhdmitx/amhdmitx0/attr"};
  if (attr.Exists()) attr.Set("now");
}

void aml_dv_start()
{
  if (aml_dv_mode() != DV_MODE_ON)
    return;

  CDVCoreGuard dvlock(__FUNCTION__);
  if (!dvlock.Owns())
  {
    logM(LOGERROR, "aml_dv_start: skipped, the DV-core lock holder is stalled");
    return;
  }
  aml_dv_reset_osd_max();
  aml_apply_pq_input_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
  aml_dv_on(DOLBY_VISION_OUTPUT_MODE_IPT);
  aml_apply_pq_output_state(StreamHdrType::HDR_TYPE_NONE, 0, DOLBY_VISION_OUTPUT_MODE_IPT);
}

void aml_dv_set_subtitles(bool visible)
{
  static int s_lastSubtitles = -1;
  const int val = visible ? 1 : 0;
  if (val == s_lastSubtitles)
    return;
  logComponentM(LOGDEBUG, LOGVIDEO, "dolby_vision_subtitles {} -> {}", s_lastSubtitles, val);
  s_lastSubtitles = val;
  CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_subtitles", val);
}

int aml_dv_l5_subs_signal_mode()
{
  const auto s = settings();
  if (!s)
    return 1;
  return s->GetInt(CSettings::SETTING_SUBTITLES_DOLBYVISION_L5_SIGNAL_MODE);
}

void aml_dv_push_l5_flags()
{
  const auto s = settings();
  if (!s)
    return;

  const bool dv_source_level_5 = s->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_STD_SOURCE_LEVEL_5);
  const bool dv_source_level_5_osdst = s->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DV_STD_SOURCE_LEVEL_5_OSDST);
  const int dv_l5_subs_signal_mode_val = dv_source_level_5 ? aml_dv_l5_subs_signal_mode() : 0;

  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5", dv_source_level_5);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5_osd_st", dv_source_level_5_osdst);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_meta_level_5_subs_st", dv_l5_subs_signal_mode_val > 0);
}

void aml_dv_set_xbmc_osd(bool osd_active)
{
  const int osd_state = osd_active ? 1 : 0;
  static int last_osd_active = -1;
  if (osd_state == last_osd_active) return;
  last_osd_active = osd_state;

  CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_xbmc_osd", osd_active);
}

enum DV_MODE aml_dv_mode()
{
  return static_cast<DV_MODE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_MODE));
}

enum DV_TYPE aml_dv_type()
{
  return static_cast<DV_TYPE>(settings()->GetInt(CSettings::SETTING_COREELEC_AMLOGIC_DV_TYPE));
}

unsigned int aml_vs10_by_setting(const std::string setting)
{
  return static_cast<unsigned int>(settings()->GetInt(setting));
}

void aml_dv_enable_fel() 
{
  CSysfsPath("/sys/class/amdolby_vision/debug", "enable_fel 1");  
}

void aml_hevc_nal_skip_policy(const int value) 
{
  CSysfsPath("/sys/module/amvdec_h265/parameters/nal_skip_policy", value);  
}

void aml_set_osd_pq_bypass(StreamHdrType hdrType)
{
  const bool enable = ((hdrType == StreamHdrType::HDR_TYPE_HDR10) ||
                       (hdrType == StreamHdrType::HDR_TYPE_HDR10PLUS));

  s_guiPqIsFinalStage.store(enable, std::memory_order_relaxed);

  CSysfsPath("/sys/module/am_vecm/parameters/osd_pq_bypass", enable);
  logComponentM(LOGDEBUG, LOGVIDEO, "am_vecm osd_pq_bypass [{}], gui shader is final transfer stage [{}]",
       enable ? "enabled" : "disabled", enable ? "yes" : "no");
}

bool aml_gui_pq_is_final_stage()
{
  return s_guiPqIsFinalStage.load(std::memory_order_relaxed);
}

void aml_set_linux_osd_sdr8(StreamHdrType hdrType, unsigned int bitDepth,
                            std::optional<unsigned int> override_mode)
{
  const unsigned int vs10_mode =
      override_mode.value_or(aml_vs10_by_hdrtype(hdrType, bitDepth));

  bool sdr8;
  if (vs10_mode == DOLBY_VISION_OUTPUT_MODE_BYPASS)
    sdr8 = (hdrType == StreamHdrType::HDR_TYPE_NONE) ||
           (hdrType == StreamHdrType::HDR_TYPE_HLG) ||
           (hdrType == StreamHdrType::HDR_TYPE_HDR_VIVID);
  else if (vs10_mode == DOLBY_VISION_OUTPUT_MODE_SDR10)
    sdr8 = true;
  else
    sdr8 = false;

  aml_linux_osd_sdr8 = sdr8;
  CSysfsPath("/sys/module/amdolby_vision/parameters/aml_linux_osd_sdr8", aml_linux_osd_sdr8);
  logComponentM(LOGDEBUG, LOGVIDEO, "amdolby_vision aml_linux_osd_sdr8 [{}]", sdr8 ? "true" : "false");
}

void aml_set_transfer_pq(StreamHdrType hdrType, unsigned int bitDepth,
                         std::optional<unsigned int> override_mode)
{
  // Configure GUI/OSD for HDR PQ when display is in HDR PQ mode
  bool hdr_display(CServiceBroker::GetWinSystem()->IsHDRDisplay() || aml_display_support_dv());
  bool dv_on(aml_is_dv_enable());
  bool hdr(false);

  if (hdr_display) // Only relevant with an hdr_display
  {
    // TODO: any need to test display supports each hdr content (inc fallback) specifically?
    hdr = ((hdrType != StreamHdrType::HDR_TYPE_NONE) &&
           (hdrType != StreamHdrType::HDR_TYPE_HLG) &&
           (hdrType != StreamHdrType::HDR_TYPE_HDR_VIVID));

    // Check for vs10 up or down mapping.
    if (dv_on) {
      unsigned int vs10_mode = override_mode.value_or(aml_vs10_by_hdrtype(hdrType, bitDepth));
      hdr = (((vs10_mode == DOLBY_VISION_OUTPUT_MODE_BYPASS) && hdr) ||
              (vs10_mode <= DOLBY_VISION_OUTPUT_MODE_HDR10));
    }
  }

  CLog::Log(LOGDEBUG, "AMLUtils::{} - {}DV support, {}, HDR type is {}, transfer PQ is {}",
          __FUNCTION__,
          aml_support_dolby_vision() ? "" : "no ",
          dv_on ? "enabled" : "disabled",
          CStreamDetails::HdrTypeToString(hdrType),
          hdr ? "set" : "not set");

  CServiceBroker::GetWinSystem()->GetGfxContext().SetTransferPQ(hdr);

  const bool hlg_output = hdr_display &&
                          (hdrType == StreamHdrType::HDR_TYPE_HLG ||
                           hdrType == StreamHdrType::HDR_TYPE_HDR_VIVID) &&
                          !dv_on;
  if (hlg_output)
    CServiceBroker::GetWinSystem()->GetGfxContext().SetGuiHdr(GuiHdr::HDR);
}

static StreamHdrType aml_get_final_hdr_type(StreamHdrType hdrType, unsigned int bitDepth)
{
  if ((hdrType == StreamHdrType::HDR_TYPE_NONE) || !aml_is_dv_enable())
    return hdrType;

  switch (aml_vs10_by_hdrtype(hdrType, bitDepth))
  {
    case DOLBY_VISION_OUTPUT_MODE_IPT:
    case DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL:
      return StreamHdrType::HDR_TYPE_DOLBYVISION;
    case DOLBY_VISION_OUTPUT_MODE_HDR10:
      return StreamHdrType::HDR_TYPE_HDR10;
    case DOLBY_VISION_OUTPUT_MODE_SDR10:
      return StreamHdrType::HDR_TYPE_NONE;
    case DOLBY_VISION_OUTPUT_MODE_BYPASS:
    default:
      return hdrType;
  }
}

StreamHdrType aml_get_output_hdr_type(StreamHdrType sourceType)
{
  if (!aml_is_dv_enable())
    return sourceType;

  switch (aml_dv_dolby_vision_mode())
  {
    case DOLBY_VISION_OUTPUT_MODE_HDR10:
      return StreamHdrType::HDR_TYPE_HDR10;
    case DOLBY_VISION_OUTPUT_MODE_IPT:
    case DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL:
      return StreamHdrType::HDR_TYPE_DOLBYVISION;
    case DOLBY_VISION_OUTPUT_MODE_SDR10:
      return StreamHdrType::HDR_TYPE_NONE;
    default:
      return sourceType;
  }
}

static bool aml_dv_has_hdr10_graphics(const DOVIStreamInfo& doviStreamInfo)
{
  if (!doviStreamInfo.has_config)
    return false;

  switch (doviStreamInfo.dovi.dv_profile)
  {
    case 7:
      return true;
    case 8:
    case 10:
      return doviStreamInfo.dovi.dv_bl_signal_compatibility_id == 1 ||
             doviStreamInfo.dovi.dv_bl_signal_compatibility_id == 6;
    default:
      return false;
  }
}

static bool aml_has_hdr10_graphics(StreamHdrType hdrType)
{
  switch (hdrType)
  {
    case StreamHdrType::HDR_TYPE_HDR10:
    case StreamHdrType::HDR_TYPE_HDR10PLUS:
      return true;
    case StreamHdrType::HDR_TYPE_DOLBYVISION:
      return aml_dv_has_hdr10_graphics(
          CServiceBroker::GetDataCacheCore().GetVideoDoViStreamInfo());
    default:
      return false;
  }
}

static GuiHdr aml_gui_hdr(StreamHdrType hdrType, unsigned int bitDepth)
{
  if (aml_has_hdr10_graphics(hdrType))
    return GuiHdr::HDR_PQ;

  if ((hdrType != StreamHdrType::HDR_TYPE_NONE) ||
      (aml_get_final_hdr_type(hdrType, bitDepth) != StreamHdrType::HDR_TYPE_NONE))
    return GuiHdr::HDR;

  return GuiHdr::SDR;
}

static void aml_set_gui_hdr(StreamHdrType hdrType, unsigned int bitDepth)
{
  const GuiHdr guiHdr = aml_gui_hdr(hdrType, bitDepth);
  CServiceBroker::GetWinSystem()->GetGfxContext().SetGuiHdr(guiHdr);
}

bool aml_has_frac_rate_policy()
{
  static int has_frac_rate_policy = -1;

  if (has_frac_rate_policy == -1)
  {
    CSysfsPath amhdmitx0_frac_rate_policy{"/sys/class/amhdmitx/amhdmitx0/frac_rate_policy"};
    has_frac_rate_policy = static_cast<int>(amhdmitx0_frac_rate_policy.Exists());
  }

  return (has_frac_rate_policy == 1);
}

void aml_video_mute(bool mute)
{
  static int _mute = -1;

  if (_mute == -1 || (_mute != !!mute))
  {
    _mute = !!mute;
    CSysfsPath("/sys/class/amhdmitx/amhdmitx0/vid_mute", _mute);
    CLog::Log(LOGDEBUG, "AMLUtils::{} - {} video", __FUNCTION__, mute ? "mute" : "unmute");
  }
}

void aml_set_audio_passthrough(bool passthrough)
{
  CSysfsPath("/sys/class/audiodsp/digital_raw", (passthrough ? 2 : 0));
}

void aml_set_3d_video_mode(unsigned int mode, bool framepacking_support, int view_mode)
{
  int fd;
  if ((fd = open("/dev/amvideo", O_RDWR)) >= 0)
  {
    if (ioctl(fd, AMSTREAM_IOC_SET_3D_TYPE, mode) != 0)
      CLog::Log(LOGERROR, "AMLUtils::{} - unable to set 3D video mode 0x%x", __FUNCTION__, mode);
    close(fd);

    CSysfsPath("/sys/module/amvideo/parameters/framepacking_support", framepacking_support ? 1 : 0);
    CSysfsPath("/sys/module/amvdec_h264mvc/parameters/view_mode", view_mode);
  }
}

void aml_probe_hdmi_audio()
{
  // Audio {format, channel, freq, cce}
  // {1, 7, 7f, 7}
  // {7, 5, 1e, 0}
  // {2, 5, 7, 0}
  // {11, 7, 7e, 1}
  // {10, 7, 6, 0}
  // {12, 7, 7e, 0}

  int fd = open("/sys/class/amhdmitx/amhdmitx0/edid", O_RDONLY);
  if (fd >= 0)
  {
    char valstr[1024] = {0};

    read(fd, valstr, sizeof(valstr) - 1);
    valstr[strlen(valstr)] = '\0';
    close(fd);

    std::vector<std::string> probe_str = StringUtils::Split(valstr, "\n");

    for (std::vector<std::string>::const_iterator i = probe_str.begin(); i != probe_str.end(); ++i)
    {
      if (i->find("Audio") == std::string::npos)
      {
        for (auto j = i + 1; j != probe_str.end(); ++j)
        {
          if      (j->find("{1,")  != std::string::npos)
            printf(" PCM found {1,\n");
          else if (j->find("{2,")  != std::string::npos)
            printf(" AC3 found {2,\n");
          else if (j->find("{3,")  != std::string::npos)
            printf(" MPEG1 found {3,\n");
          else if (j->find("{4,")  != std::string::npos)
            printf(" MP3 found {4,\n");
          else if (j->find("{5,")  != std::string::npos)
            printf(" MPEG2 found {5,\n");
          else if (j->find("{6,")  != std::string::npos)
            printf(" AAC found {6,\n");
          else if (j->find("{7,")  != std::string::npos)
            printf(" DTS found {7,\n");
          else if (j->find("{8,")  != std::string::npos)
            printf(" ATRAC found {8,\n");
          else if (j->find("{9,")  != std::string::npos)
            printf(" One_Bit_Audio found {9,\n");
          else if (j->find("{10,") != std::string::npos)
            printf(" Dolby found {10,\n");
          else if (j->find("{11,") != std::string::npos)
            printf(" DTS_HD found {11,\n");
          else if (j->find("{12,") != std::string::npos)
            printf(" MAT found {12,\n");
          else if (j->find("{13,") != std::string::npos)
            printf(" ATRAC found {13,\n");
          else if (j->find("{14,") != std::string::npos)
            printf(" WMA found {14,\n");
          else
            break;
        }
        break;
      }
    }
  }
}

int aml_axis_value(AML_DISPLAY_AXIS_PARAM param)
{
  std::string axis;
  int value[8];

  CSysfsPath display_axis{"/sys/class/display/axis"};
  if (display_axis.Exists())
    axis = display_axis.Get<std::string>().value();

  sscanf(axis.c_str(), "%d %d %d %d %d %d %d %d", &value[0], &value[1], &value[2], &value[3], &value[4], &value[5], &value[6], &value[7]);

  return value[param];
}

bool aml_display_is_widescreen()
{
  bool is_widescreen = true;
  CSysfsPath edid{"/sys/class/amhdmitx/amhdmitx0/edid"};

  if (edid.Exists())
  {
    auto valstr = edid.Get<std::string>();
    size_t pos = valstr ? valstr->find("size(mm):") : std::string::npos;
    if (pos != std::string::npos)
    {
      int width_mm = 0, height_mm = 0;
      if (sscanf(valstr->c_str() + pos, "size(mm): %d x %d", &width_mm, &height_mm) == 2 &&
          width_mm > 0 && height_mm > 0)
      {
        float ratio = static_cast<float>(width_mm) / height_mm;
        is_widescreen = ratio > 1.65f;
        logM(LOGDEBUG, "display {} widescreen ({}x{}mm)", is_widescreen ? "is" : "is not",
             width_mm, height_mm);
      }
    }
  }

  return is_widescreen;
}

bool aml_mode_to_resolution(const char *mode, RESOLUTION_INFO &res)
{
  res.iWidth = 0;
  res.iHeight= 0;

  if(!mode)
    return false;

  const bool nativeGui = CServiceBroker::GetSettingsComponent()->GetSettings()->GetBool(CSettings::SETTING_COREELEC_AMLOGIC_DISABLEGUISCALING);
  std::string fromMode = mode;
  StringUtils::Trim(fromMode);
  // strips, for example, 720p* to 720p
  // the * indicate the 'native' mode of the display
  if (StringUtils::EndsWith(fromMode, "*"))
    fromMode.erase(fromMode.size() - 1);

  if (StringUtils::EqualsNoCase(fromMode, "panel"))
  {
    res.iWidth = aml_axis_value(AML_DISPLAY_AXIS_PARAM_WIDTH);
    res.iHeight= aml_axis_value(AML_DISPLAY_AXIS_PARAM_HEIGHT);
    res.iScreenWidth = aml_axis_value(AML_DISPLAY_AXIS_PARAM_WIDTH);
    res.iScreenHeight= aml_axis_value(AML_DISPLAY_AXIS_PARAM_HEIGHT);
    res.fRefreshRate = 60;
    res.dwFlags = D3DPRESENTFLAG_PROGRESSIVE;
  }
  else if (StringUtils::EqualsNoCase(fromMode, "4k2ksmpte") || StringUtils::EqualsNoCase(fromMode, "smpte24hz"))
  {
    res.iWidth = nativeGui ? 4096 : 1920;
    res.iHeight= nativeGui ? 2160 : 1080;
    res.iScreenWidth = 4096;
    res.iScreenHeight= 2160;
    res.fRefreshRate = 24;
    res.dwFlags = D3DPRESENTFLAG_PROGRESSIVE;
  }
  else
  {
    int width = 0, height = 0, rrate = 60;
    char smode[2] = { 0 };

    if (sscanf(fromMode.c_str(), "%dx%dp%dhz", &width, &height, &rrate) == 3)
    {
      *smode = 'p';
    }
    else if (sscanf(fromMode.c_str(), "%d%1[ip]%dhz", &height, smode, &rrate) >= 2)
    {
      switch (height)
      {
        case 480:
        case 576:
          width = 720;
          break;
        case 720:
          width = 1280;
          break;
        case 1080:
          width = 1920;
          break;
        case 2160:
          width = 3840;
          break;
      }
    }
    else if (sscanf(fromMode.c_str(), "%dcvbs", &height) == 1)
    {
      width = 720;
      *smode = 'i';
      rrate = (height == 576) ? 50 : 60;
    }
    else if (sscanf(fromMode.c_str(), "4k2k%d", &rrate) == 1)
    {
      width = 3840;
      height = 2160;
      *smode = 'p';
    }
    else
    {
      return false;
    }

    res.iWidth = nativeGui ? width : std::min(width, 1920);
    res.iHeight= nativeGui ? height : std::min(height, 1080);
    res.iScreenWidth = width;
    res.iScreenHeight = height;
    res.dwFlags = (*smode == 'p') ? D3DPRESENTFLAG_PROGRESSIVE : D3DPRESENTFLAG_INTERLACED;

    switch (rrate)
    {
      case 23:
      case 29:
      case 59:
        res.fRefreshRate = (float)((rrate + 1)/1.001f);
        break;
      default:
        res.fRefreshRate = (float)rrate;
        break;
    }
  }

  res.bFullScreen   = true;
  res.iSubtitles    = (int)(0.965 * res.iHeight);
  res.fPixelRatio   = 1.0f;
  if (res.iScreenWidth == 720 && (res.iScreenHeight == 480 || res.iScreenHeight == 576))
  {
    const bool is4x3 = fromMode.find("cvbs") != std::string::npos ||
                       fromMode.find("_4x3") != std::string::npos ||
                       !aml_display_is_widescreen();
    res.fPixelRatio = (is4x3 ? (4.0f / 3.0f) : (16.0f / 9.0f)) *
                      res.iScreenHeight / res.iScreenWidth;
  }
  res.strId         = fromMode;
  res.strMode       = StringUtils::Format("{:d}x{:d} @ {:.2f}{} - Full Screen",
                                          res.iScreenWidth, res.iScreenHeight, res.fRefreshRate,
                                          res.dwFlags & D3DPRESENTFLAG_INTERLACED ? "i" : "");

  if (fromMode.find("FramePacking") != std::string::npos)
  {
    res.iBlanking = res.iScreenHeight == 1080 ? 45 : 30;
    res.dwFlags |= D3DPRESENTFLAG_MODE3DFP;
  }

  if (fromMode.find("TopBottom") != std::string::npos)
    res.dwFlags |= D3DPRESENTFLAG_MODE3DTB;

  if (fromMode.find("SidebySide") != std::string::npos)
    res.dwFlags |= D3DPRESENTFLAG_MODE3DSBS;

  return ((res.iWidth > 0) && (res.iHeight > 0));
}

bool aml_get_native_resolution(RESOLUTION_INFO &res)
{
  std::string mode;
  CSysfsPath display_mode{"/sys/class/display/mode"};
  if (display_mode.Exists())
    mode = display_mode.Get<std::string>().value();
  bool result = aml_mode_to_resolution(mode.c_str(), res);

  if (aml_has_frac_rate_policy())
  {
    int fractional_rate = 0;
    CSysfsPath frac_rate_policy{"/sys/class/amhdmitx/amhdmitx0/frac_rate_policy"};
    if (frac_rate_policy.Exists())
      fractional_rate = frac_rate_policy.Get<int>().value();
    if (fractional_rate == 1)
      res.fRefreshRate /= 1.001f;
  }

  return result;
}

bool aml_set_native_resolution(const RESOLUTION_INFO &res, std::string framebuffer_name,
  const int stereo_mode, bool force_mode_switch)
{
  bool result = false;

  aml_handle_display_stereo_mode(stereo_mode);
  result = aml_set_display_resolution(res, framebuffer_name, force_mode_switch);
  if (stereo_mode != RENDER_STEREO_MODE_OFF)
    CSysfsPath("/sys/class/amhdmitx/amhdmitx0/phy", 1);


  aml_handle_scale(res);

  return result;
}

bool aml_probe_resolutions(std::vector<RESOLUTION_INFO> &resolutions)
{
  std::string valstr, addstr;

  CSysfsPath user_dcapfile{CSpecialProtocol::TranslatePath("special://home/userdata/disp_cap")};

  if (!user_dcapfile.Exists())
  {
    CSysfsPath dcapfile{"/sys/class/amhdmitx/amhdmitx0/disp_cap"};
    if (dcapfile.Exists())
      valstr = dcapfile.Get<std::string>().value();
    else
      return false;

    CSysfsPath vesa{"/flash/vesa.enable"};
    if (vesa.Exists())
    {
      CSysfsPath vesa_cap{"/sys/class/amhdmitx/amhdmitx0/vesa_cap"};
      if (vesa_cap.Exists())
      {
        addstr = vesa_cap.Get<std::string>().value();
        valstr += "\n" + addstr;
      }
    }

    CSysfsPath custom_mode{"/sys/class/amhdmitx/amhdmitx0/custom_mode"};
    if (custom_mode.Exists())
    {
      addstr = custom_mode.Get<std::string>().value();
      valstr += "\n" + addstr;
    }

    CSysfsPath user_daddfile{CSpecialProtocol::TranslatePath("special://home/userdata/disp_add")};
    if (user_daddfile.Exists())
    {
      addstr = user_daddfile.Get<std::string>().value();
      valstr += "\n" + addstr;
    }
  }
  else
    valstr = user_dcapfile.Get<std::string>().value();

  if (aml_display_support_3d())
  {
    CSysfsPath user_dcapfile_3d{CSpecialProtocol::TranslatePath("special://home/userdata/disp_cap_3d")};
    if (!user_dcapfile_3d.Exists())
    {
      CSysfsPath dcapfile3d{"/sys/class/amhdmitx/amhdmitx0/disp_cap_3d"};
      if (dcapfile3d.Exists())
      {
        addstr = dcapfile3d.Get<std::string>().value();
        valstr += "\n" + addstr;
      }
    }
    else
      valstr = user_dcapfile_3d.Get<std::string>().value();
  }

  std::vector<std::string> probe_str = StringUtils::Split(valstr, "\n");

  resolutions.clear();
  RESOLUTION_INFO res;
  for (std::vector<std::string>::const_iterator i = probe_str.begin(); i != probe_str.end(); ++i)
  {
    if (((StringUtils::StartsWith(i->c_str(), "4k2k")) && (aml_support_h264_4k2k() > AML_NO_H264_4K2K)) || !(StringUtils::StartsWith(i->c_str(), "4k2k")))
    {
      if (aml_mode_to_resolution(i->c_str(), res))
        resolutions.push_back(res);

      if (aml_has_frac_rate_policy())
      {
        // Add fractional frame rates: 23.976, 29.97 and 59.94 Hz
        switch ((int)res.fRefreshRate)
        {
          case 24:
          case 30:
          case 60:
            res.fRefreshRate /= 1.001f;
            res.strMode       = StringUtils::Format("{:d}x{:d} @ {:.2f}{} - Full Screen", res.iScreenWidth, res.iScreenHeight, res.fRefreshRate,
              res.dwFlags & D3DPRESENTFLAG_INTERLACED ? "i" : "");
            resolutions.push_back(res);
            break;
        }
      }
    }
  }
  return resolutions.size() > 0;
}

bool aml_set_display_resolution(const RESOLUTION_INFO &res, std::string framebuffer_name,
  bool force_mode_switch)
{
  const auto t_setdr_start = std::chrono::steady_clock::now();

  std::string mode = res.strId.c_str();
  std::string cur_mode;
  std::string pre_mode;
  std::string custom_mode;
  std::vector<std::string> _mode = StringUtils::Split(mode, ' ');
  std::string mode_options;

  if (_mode.size() > 1)
  {
    mode = _mode[0];
    unsigned int i = 1;
    while(i < (_mode.size() - 1))
    {
      if (i > 1)
        mode_options.append(" ");
      mode_options.append(_mode[i]);
      i++;
    }
    CLog::Log(LOGDEBUG, "{}: try to set mode: {} ({})", __FUNCTION__, mode.c_str(), mode_options.c_str());
  }
  else
    CLog::Log(LOGDEBUG, "{}: try to set mode: {}", __FUNCTION__, mode.c_str());

  CAmlHdmiWireGuard wire(__FUNCTION__);

  CSysfsPath display_mode{"/sys/class/display/mode"};
  if (display_mode.Exists())
    cur_mode = display_mode.Get<std::string>().value();
  pre_mode = cur_mode;

  CSysfsPath amhdmitx0_custom_mode{"/sys/class/amhdmitx/amhdmitx0/custom_mode"};
  if (amhdmitx0_custom_mode.Exists())
    custom_mode = amhdmitx0_custom_mode.Get<std::string>().value();

  if (custom_mode == mode)
  {
    mode = "custombuilt";
  }

  if (aml_has_frac_rate_policy())
  {
    int fractional_rate = (res.fRefreshRate == floor(res.fRefreshRate)) ? 0 : 1;
    int cur_fractional_rate = fractional_rate;
    CSysfsPath amhdmitx0_frac_rate_policy{"/sys/class/amhdmitx/amhdmitx0/frac_rate_policy"};
    if (amhdmitx0_frac_rate_policy.Exists())
    {
      const auto cur = amhdmitx0_frac_rate_policy.Get<int>();
      if (cur.has_value())
        cur_fractional_rate = cur.value();
    }

    if ((cur_fractional_rate != fractional_rate) || force_mode_switch)
    {
      cur_mode = "null";
      if (display_mode.Exists())
      {
        CAmlDvWireStep step("mode_null");
        display_mode.Set(cur_mode);
      }
      if (amhdmitx0_frac_rate_policy.Exists())
      {
        CAmlDvWireStep step("frac_rate");
        amhdmitx0_frac_rate_policy.Set(fractional_rate);
      }
    }
  }

  if (cur_mode != mode)
  {
    if (display_mode.Exists())
    {
      const bool dv_on = aml_is_dv_enable();
      const bool target_is_4k_50_60 = (res.iScreenWidth >= 3840 &&
                                        res.iScreenHeight >= 2160 &&
                                        res.fRefreshRate >= 49.9f);
      const bool dv_eotf_override = aml_dv_eotf_override_active();
      if (!dv_on || (target_is_4k_50_60 && !dv_eotf_override))
      {
        CSysfsPath attr_path{"/sys/class/amhdmitx/amhdmitx0/attr"};
        const std::string prev_attr = attr_path.Exists() ? attr_path.Get<std::string>().value() : "";
        const std::string fmt_attr = compute_bandwidth_safe_fmt_attr(res);
        {
          CAmlDvWireStep step("attr_pre");
          attr_path.Set(fmt_attr);
        }
        if (dv_on && target_is_4k_50_60)
          logM(LOGDEBUG, "aml_set_display_resolution - DV-on bandwidth-safe attr pre-write before 4K@50/60 mode change: was=[{}] new=[{}] {}",
               prev_attr, fmt_attr, (prev_attr != fmt_attr) ? "CHANGED" : "unchanged");
      }
      else if (dv_on && target_is_4k_50_60 && dv_eotf_override)
      {
        logM(LOGDEBUG, "aml_set_display_resolution - 4K@50/60 with DV EOTF override active (DV-Std/LL): SKIP attr pre-write to avoid amvecm vs kernel-forced-wire mismatch");
      }
      const auto t_dm_start = std::chrono::steady_clock::now();
      {
        CAmlDvWireStep step("mode_target");
        display_mode.Set(mode);
      }
      const auto dm_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
          std::chrono::steady_clock::now() - t_dm_start).count();
      logM(LOGDEBUG, "aml_set_display_resolution - display_mode.Set({}) took {}ms (cur_mode_was={})",
           mode, dm_ms, pre_mode);
    }
  }

  if (mode != "null" && !mode.empty())
  {
    std::lock_guard<std::mutex> lk(s_lastDisplayModeMutex);
    s_lastDisplayMode = mode;
  }

  aml_set_framebuffer_resolution(res, framebuffer_name);

  const auto setdr_ms = std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - t_setdr_start).count();
  logComponentM(LOGDEBUG, LOGVIDEO, "aml_set_display_resolution TIMING: total={}ms mode={} cur_mode_was={} dv_on={} 4k_50_60={}",
       setdr_ms, mode, pre_mode, aml_is_dv_enable(),
       (res.iScreenWidth >= 3840 && res.iScreenHeight >= 2160 && res.fRefreshRate >= 49.9f));
  return true;
}

void aml_handle_scale(const RESOLUTION_INFO &res)
{
  if (res.iScreenWidth > res.iWidth && res.iScreenHeight > res.iHeight)
    aml_enable_freeScale(res);
  else
    aml_disable_freeScale();
}

void aml_handle_display_stereo_mode(const int stereo_mode)
{
  static int kernel_stereo_mode = -1;

  if (kernel_stereo_mode == -1)
  {
    CSysfsPath _kernel_stereo_mode{"/sys/class/amhdmitx/amhdmitx0/stereo_mode"};
    if (_kernel_stereo_mode.Exists())
      kernel_stereo_mode = _kernel_stereo_mode.Get<int>().value();
  }

  if (kernel_stereo_mode != stereo_mode)
  {
    std::string command = "3doff";
    switch (stereo_mode)
    {
      case RENDER_STEREO_MODE_SPLIT_VERTICAL:
        command = "3dlr";
        break;
      case RENDER_STEREO_MODE_SPLIT_HORIZONTAL:
        command = "3dtb";
        break;
      case RENDER_STEREO_MODE_HARDWAREBASED:
        command = "3dfp";
        break;
      default:
        // nothing - command is already initialised to "3doff"
        break;
    }

    CLog::Log(LOGDEBUG, "AMLUtils::{} setting new mode: {}", __FUNCTION__, command);
    {
      CAmlHdmiWireGuard wire(__FUNCTION__);
      CSysfsPath("/sys/class/amhdmitx/amhdmitx0/config", command);
    }
    kernel_stereo_mode = stereo_mode;
  }
}

void aml_enable_freeScale(const RESOLUTION_INFO &res)
{
  char fsaxis_str[256] = {0};
  sprintf(fsaxis_str, "0 0 %d %d", res.iWidth-1, res.iHeight-1);
  char waxis_str[256] = {0};
  sprintf(waxis_str, "0 0 %d %d", res.iScreenWidth-1, res.iScreenHeight-1);

  CSysfsPath("/sys/class/graphics/fb0/free_scale", 0);
  CSysfsPath("/sys/class/graphics/fb0/free_scale_axis", fsaxis_str);
  CSysfsPath("/sys/class/graphics/fb0/window_axis", waxis_str);
  CSysfsPath("/sys/class/graphics/fb0/free_scale", 0x10001);
}

void aml_disable_freeScale()
{
  // turn off frame buffer freescale
  CSysfsPath("/sys/class/graphics/fb0/free_scale", 0);
  CSysfsPath("/sys/class/graphics/fb1/free_scale", 0);
}

void aml_set_framebuffer_resolution(const RESOLUTION_INFO &res, std::string framebuffer_name)
{
  aml_set_framebuffer_resolution(res.iWidth, res.iHeight, framebuffer_name);
}

void aml_set_framebuffer_resolution(unsigned int width, unsigned int height, std::string framebuffer_name)
{
  int fd0;
  std::string framebuffer = "/dev/" + framebuffer_name;

  if ((fd0 = open(framebuffer.c_str(), O_RDWR)) >= 0)
  {
    struct fb_var_screeninfo vinfo;
    if (ioctl(fd0, FBIOGET_VSCREENINFO, &vinfo) == 0)
    {
      if (width != vinfo.xres || height != vinfo.yres)
      {
        vinfo.xres = width;
        vinfo.yres = height;
        vinfo.xres_virtual = width;
        vinfo.yres_virtual = height * 2;
        vinfo.bits_per_pixel = 32;
        vinfo.activate = FB_ACTIVATE_ALL;
        ioctl(fd0, FBIOPUT_VSCREENINFO, &vinfo);
      }
    }
    close(fd0);
  }
}

bool aml_read_reg(const std::string &reg, uint32_t &reg_val)
{
  CSysfsPath paddr{"/sys/kernel/debug/aml_reg/paddr"};
  if (paddr.Exists())
  {
    paddr.Set(reg);
    std::string val = paddr.Get<std::string>().value();

    CRegExp regexp;
    regexp.RegComp("\\[0x(?<reg>.+)\\][\\s]+=[\\s]+(?<val>.+)");
    if (regexp.RegFind(val) == 0)
    {
      std::string match;
      if (regexp.GetNamedSubPattern("reg", match))
      {
        if (match == reg)
        {
          if (regexp.GetNamedSubPattern("val", match))
          {
            try
            {
              reg_val = std::stoul(match, nullptr, 16);
              return true;
            }
            catch (...) {}
          }
        }
      }
    }
  }
  return false;
}

bool aml_has_capability_ignore_alpha()
{
  // 4.9 seg faults on access to /sys/kernel/debug/aml_reg/paddr and since we are CE it's always AML
  return true;
}

bool aml_set_reg_ignore_alpha()
{
  if (aml_has_capability_ignore_alpha())
  {
    CSysfsPath fb0_debug{"/sys/class/graphics/fb0/debug"};
    if (fb0_debug.Exists())
    {
      fb0_debug.Set("write 0x1a2d 0x7fc0");
      return true;
    }
  }
  return false;
}

bool aml_unset_reg_ignore_alpha()
{
  if (aml_has_capability_ignore_alpha())
  {
    CSysfsPath fb0_debug{"/sys/class/graphics/fb0/debug"};
    if (fb0_debug.Exists())
    {
      fb0_debug.Set("write 0x1a2d 0x3fc0");
      return true;
    }
  }
  return false;
}

struct FpsData {
  unsigned int input_fps;
  unsigned int output_fps;
  std::chrono::steady_clock::time_point timestamp;
};

struct FpsInfo {
  unsigned int avg_input_fps;
  unsigned int avg_output_fps;
  unsigned int avg_drop_fps;
};

struct FormattedFpsInfo {
  std::string basic_info;
  std::string drop_info;
};

FpsInfo gather_fps_data() {

  static std::vector<FpsData> fps_history;
  static const std::chrono::seconds HISTORY_DURATION(1);
  static const std::chrono::milliseconds SAMPLE_INTERVAL(100);
  static std::chrono::steady_clock::time_point last_sample_time;
  static bool sample_valid = false;
  static unsigned int cached_input_fps = 0;
  static unsigned int cached_output_fps = 0;

  auto now = std::chrono::steady_clock::now();
  bool sample_updated = false;

  if (!sample_valid || (now - last_sample_time) >= SAMPLE_INTERVAL) {
    CSysfsPath fps_info{"/sys/class/video/fps_info"};
    if (fps_info.Exists()) {

      std::string input = fps_info.Get<std::string>().value();
      unsigned int input_fps, output_fps;
      std::istringstream iss(input);

      if ((iss.ignore(std::numeric_limits<std::streamsize>::max(), ':') && iss >> std::hex >> input_fps) &&
          (iss.ignore(std::numeric_limits<std::streamsize>::max(), ':') && iss >> std::hex >> output_fps)) {
        cached_input_fps = input_fps;
        cached_output_fps = output_fps;
        sample_valid = true;
        sample_updated = true;
      }
    }

    last_sample_time = now;
  }

  if (sample_valid && sample_updated) {
    fps_history.push_back({cached_input_fps, cached_output_fps, now});
  }

  fps_history.erase(
    std::remove_if(
        fps_history.begin(), fps_history.end(),
        [&now](const FpsData& data) {
          return (now - data.timestamp) > HISTORY_DURATION;
        }
      ), fps_history.end()
  );

  if (!fps_history.empty()) {
    double avg_input_fps = 0;
    double avg_output_fps = 0;
    double avg_drop_fps = 0;

    for (const auto& data : fps_history) {
      avg_input_fps += data.input_fps;
      avg_output_fps += data.output_fps;
    }

    avg_input_fps /= fps_history.size();
    avg_output_fps /= fps_history.size();
    avg_drop_fps = (avg_input_fps > avg_output_fps) ? (avg_input_fps - avg_output_fps) : 0.0;

    return {
      static_cast<unsigned int>(avg_input_fps + 0.5),
      static_cast<unsigned int>(avg_output_fps + 0.5),
      static_cast<unsigned int>(avg_drop_fps + 0.5)
    };
  }

  return {0, 0, 0};
}

FormattedFpsInfo format_fps_info() {

  FpsInfo info = gather_fps_data();

  // Format basic info
  static int rotation_index = 0;
  const char rotation_chars[] = {'|', '/', '-', '\\'};

  static std::chrono::steady_clock::time_point last_update = std::chrono::steady_clock::now();
  const std::chrono::milliseconds UPDATE_INTERVAL(100);

  std::ostringstream basic_info;
  basic_info << std::fixed << std::setprecision(0) << std::setfill('0')
              << std::setw(3) << info.avg_input_fps << " - "
              << std::setw(3) << info.avg_output_fps << " - "
              << std::setw(3) << info.avg_drop_fps;

  auto now = std::chrono::steady_clock::now();
  if ((now - last_update) >= UPDATE_INTERVAL) {
    rotation_index = (rotation_index + 1) % 4;
    last_update = now;
  }

  basic_info << " " << rotation_chars[rotation_index];

  // Format drop info
  static unsigned int lowest_avg_output_fps = 0;
  static std::chrono::steady_clock::time_point last_drop_time;
  const std::chrono::seconds HOLD_PERIOD(3);
  static std::string drop_info = "";

  if (info.avg_output_fps < info.avg_input_fps) {
      if (lowest_avg_output_fps == 0 || info.avg_output_fps < lowest_avg_output_fps) {
          lowest_avg_output_fps = info.avg_output_fps;
          last_drop_time = now;
      } else if (now - last_drop_time >= HOLD_PERIOD) {
          lowest_avg_output_fps = info.avg_output_fps;
          last_drop_time = now;
      }
      drop_info = std::to_string(lowest_avg_output_fps);
  } else {
      if (lowest_avg_output_fps != 0 && now - last_drop_time >= HOLD_PERIOD) {
          lowest_avg_output_fps = 0;
          drop_info = "";
      }
  }

  return {basic_info.str(), drop_info};
}

std::string aml_video_fps_info() {
  return format_fps_info().basic_info;
}

std::string aml_video_fps_drop() {
  return format_fps_info().drop_info;
}

void aml_dv_set_disc_session(bool active)
{
  s_dvDiscSession = active;
  if (!active)
  {
    const unsigned int existing_mode = aml_dv_dolby_vision_mode();
    if (aml_is_dv_enable() && (aml_dv_mode() == DV_MODE_ON_DEMAND) &&
        ((existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT) || (existing_mode == DOLBY_VISION_OUTPUT_MODE_IPT_TUNNEL)))
    {
      logM(LOGDEBUG, "aml_dv_set_disc_session - disc session ended with DV engine kept alive, tearing down");
      aml_dv_off();
      aml_apply_pq_input_state(StreamHdrType::HDR_TYPE_NONE, 0);
      aml_apply_pq_output_state(StreamHdrType::HDR_TYPE_NONE, 0);
    }
    CSysfsPath("/sys/module/amdolby_vision/parameters/dolby_vision_vsif_hold", 0);
    logM(LOGDEBUG, "aml_dv_set_disc_session - disc session ended, VSIF hold released");
  }
  else
    logM(LOGDEBUG, "aml_dv_set_disc_session - disc session active");
}

unsigned int aml_dv_video_processor_mode()
{
  CSysfsPath dv_vp{"/sys/module/amdolby_vision/parameters/xbmc_dv_vp"};
  if (dv_vp.Exists())
    return dv_vp.Get<unsigned int>().value_or(0);
  return 0;
}

void aml_dv_send_md_levels() {
  DOVIStreamMetadata dovi_stream_metadata;
  dovi_stream_metadata = CServiceBroker::GetDataCacheCore().GetVideoDoViStreamMetadata();
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_source_max_pq", dovi_stream_metadata.source_max_pq);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_source_min_pq", dovi_stream_metadata.source_min_pq);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_lum", dovi_stream_metadata.level6_max_lum);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_min_lum", dovi_stream_metadata.level6_min_lum);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_cll", dovi_stream_metadata.level6_max_cll);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_md_level_6_max_fall", dovi_stream_metadata.level6_max_fall);
  CServiceBroker::GetDataCacheCore().SetDvLevel6Limits(dovi_stream_metadata.level6_max_cll,
                                                       dovi_stream_metadata.level6_max_lum);
}

void aml_dv_send_hdr10_data() {
  HDRStaticMetadataInfo hdrStaticMetadataInfo;
  hdrStaticMetadataInfo = CServiceBroker::GetDataCacheCore().GetVideoHDRStaticMetadataInfo();
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_lum", hdrStaticMetadataInfo.max_lum);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_min_lum", hdrStaticMetadataInfo.min_lum);
  // CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_colour_primaries", hdrStaticMetadataInfo.colour_primaries);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_cll", hdrStaticMetadataInfo.max_cll);
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_hdr10_max_fall", hdrStaticMetadataInfo.max_fall);
}

void aml_dv_send_el_type() {
  DOVIStreamInfo dovi_stream_info;
  dovi_stream_info = CServiceBroker::GetDataCacheCore().GetVideoDoViStreamInfo();
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_el_type", dovi_stream_info.dovi_el_type);
}

void aml_dv_send_profile(int dvprofile) {
  CSysfsPath("/sys/module/amdolby_vision/parameters/xbmc_dv_profile", static_cast<unsigned int>(dvprofile));
}

void aml_reset_audio_from_player_open()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  if (aml_get_cpufamily_id() == AML_G12B)
    advancedSettings->SetAlgoForReset(2);
  else
    advancedSettings->SetAlgoForReset(3);
}

void aml_reset_audio_from_player_pause()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  advancedSettings->SetAlgoForReset(2);
}

void aml_reset_audio_from_window_home()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  advancedSettings->SetAlgoForReset(2);
}

void aml_reset_audio_from_play_from_beginning()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  if (aml_get_cpufamily_id() == AML_G12B)
    advancedSettings->SetAlgoForReset(2);
  else
    advancedSettings->SetAlgoForReset(3);
}

void aml_reset_audio_from_play_from_resume()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSync(true);
  advancedSettings->SetResetSeek(true);
  advancedSettings->SetLastResetTime(0.0);
  advancedSettings->SetAlgoForReset(1);
}

void aml_reset_from_subtitle_change()
{
  auto* advancedSettings = &CAudioSyncReset::GetInstance();
  advancedSettings->SetResetSyncSub(true);
  advancedSettings->SetResetSeekSub(true);
  advancedSettings->SetLastResetTimeSub(0.0);
  advancedSettings->SetAlgoForResetSub(99);
}

void aml_get_dv_cap()
{
  if (!aml_display_support_dv())
    return;

  CSysfsPath dv_cap{"/sys/devices/virtual/amhdmitx/amhdmitx0/dv_cap"};
  if (!dv_cap.Exists())
    return;

  const std::string valstr = dv_cap.Get<std::string>().value();
  if (valstr.find("Rx: ") == std::string::npos)
    return;

  auto field = [&valstr](const std::string& key, const std::string& suffix, int& out) {
    const size_t start = valstr.find(key);
    if (start == std::string::npos)
      return;
    const size_t from = start + key.length();
    const size_t end = valstr.find(suffix, from);
    if ((end == std::string::npos) || (end <= from))
      return;
    out = std::stoi(valstr.substr(from, end - from));
  };

  const std::string ver_key = "VSVDB Version: V";
  const size_t ver_pos = valstr.find(ver_key);
  if (ver_pos != std::string::npos)
    xbmc_dv_cap::dv_ver_i = std::stoi(valstr.substr(ver_pos + ver_key.length(), 1));

  int vsvdb_length = 0;
  field("Length: ", "\n", vsvdb_length);
  xbmc_dv_cap::dv_len_i = vsvdb_length + 1;

  const std::string vsvdb_key = "VSVDB: ";
  const size_t vsvdb_pos = valstr.find(vsvdb_key);
  if (vsvdb_pos != std::string::npos)
    xbmc_dv_cap::dv_vsvdb_s = valstr.substr(vsvdb_pos + vsvdb_key.length(), xbmc_dv_cap::dv_len_i * 2);

  field("tmaxLUM: ", "nti", xbmc_dv_cap::dv_max_v1_i);
  field("tmaxPQ: ", "pqi", xbmc_dv_cap::dv_max_v2_i);
  field("Rx: ", "rxi", xbmc_dv_cap::dv_rx_i);
  field("Ry: ", "ryi", xbmc_dv_cap::dv_ry_i);
  field("Gx: ", "gxi", xbmc_dv_cap::dv_gx_i);
  field("Gy: ", "gyi", xbmc_dv_cap::dv_gy_i);
  field("Bx: ", "bxi", xbmc_dv_cap::dv_bx_i);
  field("By: ", "byi", xbmc_dv_cap::dv_by_i);

  if (xbmc_dv_cap::dv_ver_i == 0)
  {
    xbmc_dv_cap::dv_rx_i = xbmc_dv_cap::dv_rx_i >> 4;
    xbmc_dv_cap::dv_ry_i = xbmc_dv_cap::dv_ry_i >> 4;
    xbmc_dv_cap::dv_gx_i = xbmc_dv_cap::dv_gx_i >> 4;
    xbmc_dv_cap::dv_gy_i = xbmc_dv_cap::dv_gy_i >> 4;
    xbmc_dv_cap::dv_bx_i = xbmc_dv_cap::dv_bx_i >> 4;
    xbmc_dv_cap::dv_by_i = xbmc_dv_cap::dv_by_i >> 4;
  }
}

namespace
{
std::mutex s_governorMutex;
bool s_governorsSet = false;
std::vector<std::pair<std::string, std::string>> s_savedGovernors;
std::optional<std::string> s_savedMaliMinFreq;
}

void aml_set_perf_governors_for_playback()
{
  std::lock_guard<std::mutex> lock(s_governorMutex);
  if (s_governorsSet)
    return;

  {
    CSysfsPath minFreq{"/sys/class/mpgpu/min_freq"};
    CSysfsPath maxFreq{"/sys/class/mpgpu/max_freq"};
    if (minFreq.Exists() && maxFreq.Exists())
    {
      auto curMin = minFreq.Get<std::string>();
      auto curMax = maxFreq.Get<std::string>();
      if (curMin.has_value() && curMax.has_value() && *curMin != *curMax)
      {
        try
        {
          minFreq.Set(*curMax);
          s_savedMaliMinFreq = *curMin;
          logM(LOGINFO,
               "Set /sys/class/mpgpu/min_freq = {} (was {}) to lock Mali GPU at max performance bin",
               *curMax, *curMin);
        }
        catch (...)
        {
        }
      }
    }
  }

  DIR* dirp = opendir("/sys/class/devfreq");
  if (!dirp)
    return;

  struct dirent* entry;
  while ((entry = readdir(dirp)) != nullptr)
  {
    std::string name = entry->d_name;
    if (name == "." || name == "..")
      continue;

    bool relevant = false;
    for (const auto& key : {"gpu", "bifrost", "mali", "dmc", "ddr"})
    {
      if (name.find(key) != std::string::npos)
      {
        relevant = true;
        break;
      }
    }
    if (!relevant)
      continue;

    const std::string governorPath = "/sys/class/devfreq/" + name + "/governor";
    CSysfsPath gov{governorPath};
    if (!gov.Exists())
      continue;

    auto current = gov.Get<std::string>();
    if (!current.has_value() || *current == "performance")
      continue;

    try
    {
      gov.Set(std::string{"performance"});
      s_savedGovernors.emplace_back(governorPath, *current);
      logM(LOGINFO, "Set {} governor performance (was {})", governorPath, *current);
    }
    catch (...)
    {
    }
  }
  closedir(dirp);

  if (!s_savedGovernors.empty() || s_savedMaliMinFreq.has_value())
    s_governorsSet = true;
}

void aml_restore_governors_after_playback()
{
  std::lock_guard<std::mutex> lock(s_governorMutex);
  if (!s_governorsSet)
    return;

  if (s_savedMaliMinFreq.has_value())
  {
    try
    {
      CSysfsPath{"/sys/class/mpgpu/min_freq"}.Set(*s_savedMaliMinFreq);
      logM(LOGINFO, "Restored /sys/class/mpgpu/min_freq to {}", *s_savedMaliMinFreq);
    }
    catch (...)
    {
    }
    s_savedMaliMinFreq.reset();
  }

  for (const auto& [path, original] : s_savedGovernors)
  {
    try
    {
      CSysfsPath{path}.Set(original);
      logM(LOGINFO, "Restored {} governor to {}", path, original);
    }
    catch (...)
    {
    }
  }
  s_savedGovernors.clear();
  s_governorsSet = false;
}
