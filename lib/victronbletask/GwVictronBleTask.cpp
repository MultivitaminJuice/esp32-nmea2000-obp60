#ifdef ESP32

#include "GwVictronBleTask.h"

#if !defined(DISABLE_VICTRON_BLE)

#include <NimBLEDevice.h>
#include <NimBLEScan.h>
#include <NimBLEAdvertisedDevice.h>
#include <esp_heap_caps.h>
#include <esp_bt.h>
#include <esp_err.h>
#include "mbedtls/aes.h"
#include "GwMessage.h"
#include "GwBoatData.h"
#if defined(BOARD_OBP60S3) || defined(BOARD_OBP40S3)
#include "obp60task.h"
#endif

static const size_t MIN_FREE_INTERNAL = 30000; // 30KB: stabiler fuer BLE-Init
static bool s_nimbleInitialized = false;
static bool s_taskRunning = false;
static bool s_btClassicReleased = false;
static uint32_t s_lastAdvSeenMs = 0;
static uint32_t s_lastMatchMs = 0;
static uint32_t s_lastRxMs = 0;
static uint32_t s_advSeenCount = 0;
static uint32_t s_matchCount = 0;
static uint32_t s_rxCount = 0;
static uint8_t s_lastRxType = 0;
static char s_lastAdvMac[18] = {0};
static char s_lastMatchMac[18] = {0};
static char s_lastRxMac[18] = {0};
static char s_currentMatchMac[18] = {0};
static uint32_t s_aesBackoffUntilMs = 0;
static uint32_t s_lastAesBackoffLogMs = 0;
static uint8_t s_lastPlain[16] = {0};
static uint8_t s_lastPlainLen = 0;
static uint8_t s_lastPlainType = 0;
static uint32_t s_lastRxSeq = 0;

static void hexEncode(const uint8_t* in, size_t len, char* out, size_t outSize) {
  static const char* kHex = "0123456789abcdef";
  if (!out || outSize < (len * 2 + 1)) return;
  for (size_t i = 0; i < len; ++i) {
    out[i * 2] = kHex[(in[i] >> 4) & 0x0f];
    out[i * 2 + 1] = kHex[in[i] & 0x0f];
  }
  out[len * 2] = '\0';
}

static void copyMac(char* dst, const String& mac) {
  if (!dst) return;
  const String m = mac.length() ? mac : String();
  strncpy(dst, m.c_str(), 17);
  dst[17] = '\0';
}

static void logBleSummary(GwLog* log, uint32_t nowMs) {
  const uint32_t advAge = s_lastAdvSeenMs ? (uint32_t)(nowMs - s_lastAdvSeenMs) : 0;
  const uint32_t matchAge = s_lastMatchMs ? (uint32_t)(nowMs - s_lastMatchMs) : 0;
  const uint32_t rxAge = s_lastRxMs ? (uint32_t)(nowMs - s_lastRxMs) : 0;
  log->logDebug(
    GwLog::LOG,
    "BLE summary: adv=%lu age=%lums mac=%s | match=%lu age=%lums mac=%s | rx=%lu age=%lums mac=%s type=0x%02x",
    (unsigned long)s_advSeenCount, (unsigned long)advAge, s_lastAdvMac[0] ? s_lastAdvMac : "-",
    (unsigned long)s_matchCount, (unsigned long)matchAge, s_lastMatchMac[0] ? s_lastMatchMac : "-",
    (unsigned long)s_rxCount, (unsigned long)rxAge, s_lastRxMac[0] ? s_lastRxMac : "-",
    (unsigned int)s_lastRxType
  );
  USBSerial.printf(
    "VIC: summary adv=%lu age=%lums mac=%s | match=%lu age=%lums mac=%s | rx=%lu age=%lums mac=%s type=0x%02x\n",
    (unsigned long)s_advSeenCount, (unsigned long)advAge, s_lastAdvMac[0] ? s_lastAdvMac : "-",
    (unsigned long)s_matchCount, (unsigned long)matchAge, s_lastMatchMac[0] ? s_lastMatchMac : "-",
    (unsigned long)s_rxCount, (unsigned long)rxAge, s_lastRxMac[0] ? s_lastRxMac : "-",
    (unsigned int)s_lastRxType
  );
  USBSerial.flush();
}

bool victronBleIsInitialized() {
  return s_nimbleInitialized;
}

bool victronBleTaskRunning() {
  return s_taskRunning;
}

static inline bool parseHexNibble(char c, uint8_t& out) {
  if (c >= '0' && c <= '9') { out = (uint8_t)(c - '0'); return true; }
  if (c >= 'a' && c <= 'f') { out = (uint8_t)(c - 'a' + 10); return true; }
  if (c >= 'A' && c <= 'F') { out = (uint8_t)(c - 'A' + 10); return true; }
  return false;
}

static bool parseHexBytes(const String& hex, uint8_t* out, size_t outLen) {
  String s = hex;
  s.trim();
  if (s.length() != (int)(outLen * 2)) return false;
  for (size_t i = 0; i < outLen; i++) {
    uint8_t hi, lo;
    if (!parseHexNibble(s[2*i], hi)) return false;
    if (!parseHexNibble(s[2*i+1], lo)) return false;
    out[i] = (uint8_t)((hi << 4) | lo);
  }
  return true;
}

static String bytesToHex(const uint8_t* buf, size_t len) {
  static const char* kHex = "0123456789abcdef";
  String out;
  out.reserve((int)(len * 2));
  for (size_t i = 0; i < len; i++) {
    out += kHex[(buf[i] >> 4) & 0x0f];
    out += kHex[buf[i] & 0x0f];
  }
  return out;
}

static String maskKey(const String& key) {
  const int n = key.length();
  if (n <= 4) return String("***");
  return key.substring(0, 2) + String("...") + key.substring(n - 2);
}

static String normalizeMac(const String& s) {
  String t = s;
  t.trim();
  String raw;
  raw.reserve(12);
  for (int i = 0; i < t.length(); i++) {
    char c = t[i];
    if (c == ':' || c == '-') continue;
    if (c >= 'A' && c <= 'F') c = (char)(c - 'A' + 'a');
    if (!((c >= '0' && c <= '9') || (c >= 'a' && c <= 'f'))) {
      return String();
    }
    raw += c;
  }
  if (raw.length() != 12) return String();
  return raw;
}

// Bit-Extractor: LSB-first über Byte-Stream
static uint32_t getBitsLE(const uint8_t* buf, uint16_t startBit, uint8_t bitLen) {
  uint32_t v = 0;
  for (uint8_t i = 0; i < bitLen; i++) {
    uint16_t bit = startBit + i;
    uint8_t b = (buf[bit / 8] >> (bit % 8)) & 0x01;
    v |= ((uint32_t)b << i);
  }
  return v;
}

static uint32_t readBitsLEAdvance(const uint8_t* buf, uint16_t& bitPos, uint8_t bitLen) {
  const uint32_t v = getBitsLE(buf, bitPos, bitLen);
  bitPos = (uint16_t)(bitPos + bitLen);
  return v;
}

static int32_t signExtend(uint32_t v, uint8_t bits) {
  // bits: 1..32
  if (bits == 32) return (int32_t)v;
  uint32_t m = 1u << (bits - 1);
  return (int32_t)((v ^ m) - m);
}

// AES-CTR decrypt (mbedTLS)
static bool victronDecryptCtr(
  const uint8_t key[16],
  const uint8_t nonce2[2],
  const uint8_t* enc, size_t len,
  uint8_t* out
){
  mbedtls_aes_context ctx;
  mbedtls_aes_init(&ctx);
  if (mbedtls_aes_setkey_enc(&ctx, key, 128) != 0) {
    mbedtls_aes_free(&ctx);
    return false;
  }

  // CTR IV/nonce_counter block:
  // Victron: nonce/dataCounter ist 2 Byte, LSB-first übertragen -> so übernehmen.
  uint8_t nonce_counter[16] = {0};
  nonce_counter[0] = nonce2[0];
  nonce_counter[1] = nonce2[1];

  size_t nc_off = 0;
  uint8_t stream_block[16] = {0};

  int rc = mbedtls_aes_crypt_ctr(&ctx, len, &nc_off, nonce_counter, stream_block, enc, out);
  mbedtls_aes_free(&ctx);
  return rc == 0;
}

// Provider für dynamische BoatData Items
class SimpleProvider : public GwBoatItemNameProvider {
  String n;
  String f;
  unsigned long inv;
public:
  SimpleProvider(const String& name, const String& fmt, unsigned long invalidMs)
    : n(name), f(fmt), inv(invalidMs) {}
  String getBoatItemName() override { return n; }
  String getBoatItemFormat() override { return f; }
  unsigned long getInvalidTime() override { return inv; }
};

// Thread-safe write into boatData via main-thread request
class SetBoatDataRequest : public GwMessage {
  GwApi* api;
  int sourceId;
public:
  struct Entry {
    String name;
    String fmt;
    double value;
    unsigned long invalidMs;
  };
  std::vector<Entry> entries;

  SetBoatDataRequest(GwApi* api, int sourceId)
    : GwMessage(F("victron set boat data")), api(api), sourceId(sourceId) {}

protected:
  void processImpl() override {
    GwBoatData* bd = api->getBoatData();
    for (auto& e : entries) {
      SimpleProvider p(e.name, e.fmt, e.invalidMs);
      bd->update<double>(e.value, sourceId, &p);
    }
  }
};

struct VictronDeviceCfg {
  NimBLEAddress mac;
  bool hasMac = false;
  String macRaw;
  uint8_t key[16] = {0};
  bool hasKey = false;
};

struct VictronConfiguredDevice {
  String slotName;
  String type;
  uint8_t expectedRecordType = 0x00;
  VictronDeviceCfg cfg;
};

static bool parseMac(const String& s, NimBLEAddress& out) {
  const String raw = normalizeMac(s);
  if (raw.length() != 12) return false;

  String fmt;
  fmt.reserve(17);
  for (int i = 0; i < 12; i += 2) {
    if (i > 0) fmt += ':';
    fmt += raw[i];
    fmt += raw[i + 1];
  }

  // Type wird bei Vergleich nicht genutzt; Adresse kann public/random sein.
  std::string macStr = std::string(fmt.c_str());
  out = NimBLEAddress(macStr, BLE_ADDR_PUBLIC);
  return true;
}

static VictronDeviceCfg loadDevice(GwApi* api, const String& macCfgName, const String& keyCfgName) {
  VictronDeviceCfg d;
  auto* cfg = api->getConfig();

  String mac = cfg->getConfigItem(macCfgName, true)->asString();
  String key = cfg->getConfigItem(keyCfgName, true)->asString();

  if (parseMac(mac, d.mac)) {
    d.hasMac = true;
    d.macRaw = normalizeMac(mac);
  } else if (mac.length() > 0) {
    api->getLogger()->logDebug(GwLog::ERROR, "Victron MAC invalid: %s", mac.c_str());
  }
  if (parseHexBytes(key, d.key, 16)) d.hasKey = true;

  return d;
}

static uint8_t expectedRecordTypeFromType(const String& type) {
  if (type == "solar") return 0x01;
  if (type == "shunt") return 0x02;
  if (type == "inverter") return 0x03;
  if (type == "dcdc") return 0x04;
  if (type == "smartLithium") return 0x05;
  if (type == "inverterRs") return 0x06;
  if (type == "acCharger") return 0x08;
  if (type == "smartBatteryProtect") return 0x09;
  if (type == "lynxBms") return 0x0A;
  if (type == "multiRs") return 0x0B;
  if (type == "veBus") return 0x0C;
  if (type == "dcEnergyMeter") return 0x0D;
  if (type == "orionXs") return 0x0F;
  return 0x00;
}

static void addDeviceIfValid(std::vector<VictronConfiguredDevice>& out,
                             const String& slotName,
                             const String& type,
                             const VictronDeviceCfg& cfg) {
  if (!cfg.hasMac || !cfg.hasKey) return;
  for (auto& d : out) {
    if (d.cfg.macRaw == cfg.macRaw) return;
  }
  VictronConfiguredDevice d;
  d.slotName = slotName;
  d.type = type;
  d.expectedRecordType = expectedRecordTypeFromType(type);
  d.cfg = cfg;
  out.push_back(d);
}

static std::vector<VictronConfiguredDevice> loadConfiguredDevices(GwApi* api) {
  std::vector<VictronConfiguredDevice> out;
  auto* cfg = api->getConfig();

  for (int i = 1; i <= 4; ++i) {
    const String typeName = cfg->getConfigItem("vicDev" + String(i) + "Type", true)->asString();
    if (typeName == "off" || typeName.length() == 0) continue;
    const String macName = "vicDev" + String(i) + "Mac";
    const String keyName = "vicDev" + String(i) + "Key";
    VictronDeviceCfg dev = loadDevice(api, macName, keyName);
    addDeviceIfValid(out, "dev" + String(i), typeName, dev);
  }

  return out;
}

// --- Parser: SmartShunt (0x02) / SmartSolar (0x01)
static void parseBatteryMonitor_02(const uint8_t* plain16, GwLog* log, std::vector<SetBoatDataRequest::Entry>& out) {
  // Spec-basierte Bit-Offsets (Victron Extra Manufacturer Data):
  // https://communityarchive.victronenergy.com/storage/attachments/extra-manufacturer-data-2022-12-14.pdf
  // Hinweis: Battery Monitor (0x02) verwendet Bitfelder; NA-Werte werden übersprungen.
  const uint16_t ttg_raw = (uint16_t)getBitsLE(plain16, 32, 16);
  const uint16_t vbatt_raw = (uint16_t)getBitsLE(plain16, 48, 16);
  const uint32_t i_raw_u = getBitsLE(plain16, 98, 22);
  const uint16_t soc_raw = (uint16_t)getBitsLE(plain16, 140, 10);

  const bool has_ttg = ttg_raw != 0xFFFF;
  const bool has_v = vbatt_raw != 0x7FFF;
  const bool has_i = i_raw_u != 0x3FFFFF;
  const bool has_soc = soc_raw != 0x03FF;

  const double ttg_min = has_ttg ? (double)ttg_raw : 0.0;
  const double vbatt = has_v ? (double)signExtend(vbatt_raw, 16) * 0.01 : 0.0;
  const double ibatt = has_i ? (double)signExtend(i_raw_u, 22) * 0.001 : 0.0;
  const double soc = has_soc ? (double)soc_raw * 0.1 : 0.0;

  if (has_v)   out.push_back({"VSH_V",   "formatFixed1", vbatt, 10000});
  if (has_i)   out.push_back({"VSH_I",   "formatFixed1", ibatt, 10000});
  if (has_soc) out.push_back({"VSHSOC",  "formatFixed1", soc,   15000});
  if (has_ttg) out.push_back({"VSHTTG",  "formatFixed0", ttg_min, 15000});

  static uint32_t lastSpecLogMs = 0;
  static uint32_t lastUsbLogMs = 0;
  const uint32_t nowMs = millis();
  if ((uint32_t)(nowMs - lastSpecLogMs) > 5000) {
    log->logDebug(
      GwLog::LOG,
      "Victron Shunt raw: ttg=0x%04x v=0x%04x i=0x%06x soc=0x%03x",
      (unsigned)ttg_raw, (unsigned)vbatt_raw, (unsigned)i_raw_u, (unsigned)soc_raw
    );
    lastSpecLogMs = nowMs;
  }
  if ((uint32_t)(nowMs - lastUsbLogMs) > 5000) {
    USBSerial.printf("VIC: shunt v=%.2f i=%.3f soc=%.1f ttg=%.0f\n",
                     vbatt, ibatt, soc, ttg_min);
    USBSerial.flush();
    lastUsbLogMs = nowMs;
  }

  log->logDebug(GwLog::DEBUG,
                "Victron Shunt: V=%s I=%s SOC=%s TTG=%s",
                has_v ? String(vbatt, 2).c_str() : "-",
                has_i ? String(ibatt, 3).c_str() : "-",
                has_soc ? String(soc, 1).c_str() : "-",
                has_ttg ? String((int)ttg_min).c_str() : "-");
}

static void parseSolarCharger_01(const uint8_t* plain16, GwLog* log, std::vector<SetBoatDataRequest::Entry>& out) {
  // Spec-basiertes Layout (Instant Readout, Solar Charger):
  // Byte 0: device_state
  // Byte 1: charger_error
  // Byte 2..3: battery_voltage_centi (LE, 0.01V, NA=0x7FFF)
  // Byte 4..5: battery_current_deci (LE, 0.1A, NA=0x7FFF)
  // Byte 6..7: yield_today_centikwh (LE, 0.01kWh, NA=0xFFFF)
  // Byte 8..9: pv_power_w (LE, 1W, NA=0xFFFF)
  // Byte 10..11: load_current_deci (LE, 9 bit, NA=0x1FF)
  const uint8_t dev_state = plain16[0];
  const uint8_t err_code = plain16[1];

  const uint16_t vbatt_raw = (uint16_t)plain16[2] | ((uint16_t)plain16[3] << 8);
  const uint16_t ibatt_raw = (uint16_t)plain16[4] | ((uint16_t)plain16[5] << 8);
  const uint16_t yld_raw = (uint16_t)plain16[6] | ((uint16_t)plain16[7] << 8);
  const uint16_t pv_raw = (uint16_t)plain16[8] | ((uint16_t)plain16[9] << 8);
  const uint16_t load_raw = (uint16_t)plain16[10] | (((uint16_t)plain16[11] & 0x01) << 8);

  const bool has_v = vbatt_raw != 0x7FFF;
  const bool has_i = ibatt_raw != 0x7FFF;
  const bool has_y = yld_raw != 0xFFFF;
  const bool has_pv = pv_raw != 0xFFFF;
  const bool has_load = load_raw != 0x01FF;

  const double vbatt = has_v ? (double)signExtend(vbatt_raw, 16) * 0.01 : 0.0;
  const double ibatt = has_i ? (double)signExtend(ibatt_raw, 16) * 0.1 : 0.0;
  const double yield_kwh = has_y ? (double)yld_raw * 0.01 : 0.0;
  const double pv_w = has_pv ? (double)pv_raw * 1.0 : 0.0;
  const double load_a = has_load ? (double)load_raw * 0.1 : 0.0;

  if (has_v)  out.push_back({"VSO_V", "formatFixed1", vbatt,     10000});
  if (has_i)  out.push_back({"VSO_I", "formatFixed1", ibatt,     10000});
  if (has_pv) out.push_back({"VSO_P", "formatFixed0", pv_w,      10000});
  if (has_y)  out.push_back({"VSO_Y", "formatFixed1", yield_kwh, 30000});

  static uint32_t lastSpecLogMs = 0;
  static uint32_t lastUsbLogMs = 0;
  const uint32_t nowMs = millis();
  if ((uint32_t)(nowMs - lastSpecLogMs) > 5000) {
    log->logDebug(
      GwLog::LOG,
      "Victron Solar raw: state=0x%02x err=0x%02x v=0x%04x i=0x%04x y=0x%04x pv=0x%04x load=0x%03x",
      (unsigned)dev_state, (unsigned)err_code,
      (unsigned)vbatt_raw, (unsigned)ibatt_raw,
      (unsigned)yld_raw, (unsigned)pv_raw, (unsigned)load_raw
    );
    lastSpecLogMs = nowMs;
  }
  if ((uint32_t)(nowMs - lastUsbLogMs) > 5000) {
    USBSerial.printf("VIC: solar v=%.2f i=%.1f pv=%.0f y=%.2f\n",
                     vbatt, ibatt, pv_w, yield_kwh);
    USBSerial.flush();
    lastUsbLogMs = nowMs;
  }

  log->logDebug(GwLog::DEBUG,
                "Victron Solar: state=%u err=%u V=%s I=%s PV=%sW Y=%skWh Load=%sA",
                (unsigned)dev_state, (unsigned)err_code,
                has_v ? String(vbatt, 2).c_str() : "-",
                has_i ? String(ibatt, 1).c_str() : "-",
                has_pv ? String((int)pv_w).c_str() : "-",
                has_y ? String(yield_kwh, 2).c_str() : "-",
                has_load ? String(load_a, 1).c_str() : "-");
}

static bool ensureBits(size_t encLen, uint16_t needBits, GwLog* log, const char* tag) {
  const uint16_t haveBits = (uint16_t)(encLen * 8);
  if (haveBits < needBits) {
    log->logDebug(GwLog::LOG, "Victron drop: %s needs %u bits, have %u",
                  tag, (unsigned)needBits, (unsigned)haveBits);
    return false;
  }
  return true;
}

static void parseInverter_03(const uint8_t* plain, size_t encLen, GwLog* log,
                             std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 82, log, "inverter")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t alarm = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t vb_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t ac_apparent = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t ac_v_raw = (uint16_t)readBitsLEAdvance(plain, b, 15);
  const uint16_t ac_i_raw = (uint16_t)readBitsLEAdvance(plain, b, 11);

  const double vb = (double)vb_raw * 0.01;
  const double ac_v = (double)ac_v_raw * 0.01;
  const double ac_i = (double)ac_i_raw * 0.1;

  out.push_back({"VIC_INV_VBATT", "formatFixed0", vb, 4000});
  out.push_back({"VIC_INV_AC_V", "formatFixed0", ac_v, 4000});
  out.push_back({"VIC_INV_AC_I", "formatFixed0", ac_i, 4000});
  out.push_back({"VIC_INV_AC_VA", "formatFixed0", (double)ac_apparent, 4000});
  out.push_back({"VIC_INV_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_INV_ALARM", "formatFixed0", (double)alarm, 8000});
}

static void parseDcdc_04(const uint8_t* plain, size_t encLen, GwLog* log,
                         std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 80, log, "dcdc")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t vin_raw = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t vout_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint32_t off_reason = readBitsLEAdvance(plain, b, 32);

  out.push_back({"VIC_DCDC_VIN", "formatFixed0", (double)vin_raw * 0.01, 4000});
  out.push_back({"VIC_DCDC_VOUT", "formatFixed0", (double)vout_raw * 0.01, 4000});
  out.push_back({"VIC_DCDC_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_DCDC_ERR", "formatFixed0", (double)err, 8000});
  out.push_back({"VIC_DCDC_OFF", "formatFixed0", (double)off_reason, 8000});
}

static void parseSmartLithium_05(const uint8_t* plain, size_t encLen, GwLog* log,
                                 std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 127, log, "smart_lithium")) return;
  uint16_t b = 0;
  const uint32_t bms_flags = readBitsLEAdvance(plain, b, 32);
  const uint16_t err = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t cell1 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell2 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell3 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell4 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell5 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell6 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell7 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t cell8 = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t vb_raw = (uint16_t)readBitsLEAdvance(plain, b, 12);
  const uint8_t bal = (uint8_t)readBitsLEAdvance(plain, b, 4);
  const uint16_t temp_raw = (uint16_t)readBitsLEAdvance(plain, b, 7);

  out.push_back({"VIC_LI_FLAGS", "formatFixed0", (double)bms_flags, 8000});
  out.push_back({"VIC_LI_ERR", "formatFixed0", (double)err, 8000});
  out.push_back({"VIC_LI_VBATT", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_LI_BAL", "formatFixed0", (double)bal, 8000});
  out.push_back({"VIC_LI_TEMP", "formatFixed0", (double)temp_raw, 8000});
  out.push_back({"VIC_LI_CELL1", "formatFixed0", (double)cell1 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL2", "formatFixed0", (double)cell2 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL3", "formatFixed0", (double)cell3 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL4", "formatFixed0", (double)cell4 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL5", "formatFixed0", (double)cell5 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL6", "formatFixed0", (double)cell6 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL7", "formatFixed0", (double)cell7 * 0.01, 8000});
  out.push_back({"VIC_LI_CELL8", "formatFixed0", (double)cell8 * 0.01, 8000});
}

static void parseInverterRs_06(const uint8_t* plain, size_t encLen, GwLog* log,
                               std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 96, log, "inverter_rs")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const int16_t vb_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t ib_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t pv_raw = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t yld_raw = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t ac_out = (int16_t)readBitsLEAdvance(plain, b, 16);

  out.push_back({"VIC_IRS_VBATT", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_IRS_IBATT", "formatFixed0", (double)ib_raw * 0.1, 4000});
  out.push_back({"VIC_IRS_PV_W", "formatFixed0", (double)pv_raw, 4000});
  out.push_back({"VIC_IRS_Y_KWH", "formatFixed0", (double)yld_raw * 0.01, 20000});
  out.push_back({"VIC_IRS_AC_OUT_W", "formatFixed0", (double)ac_out, 4000});
  out.push_back({"VIC_IRS_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_IRS_ERR", "formatFixed0", (double)err, 8000});
}

static void parseAcCharger_08(const uint8_t* plain, size_t encLen, GwLog* log,
                              std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 104, log, "ac_charger")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t v1 = (uint16_t)readBitsLEAdvance(plain, b, 13);
  const uint16_t i1 = (uint16_t)readBitsLEAdvance(plain, b, 11);
  const uint16_t v2 = (uint16_t)readBitsLEAdvance(plain, b, 13);
  const uint16_t i2 = (uint16_t)readBitsLEAdvance(plain, b, 11);
  const uint16_t v3 = (uint16_t)readBitsLEAdvance(plain, b, 13);
  const uint16_t i3 = (uint16_t)readBitsLEAdvance(plain, b, 11);
  const uint16_t temp = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t ac_i = (uint16_t)readBitsLEAdvance(plain, b, 9);

  out.push_back({"VIC_AC_V1", "formatFixed0", (double)v1 * 0.01, 4000});
  out.push_back({"VIC_AC_I1", "formatFixed0", (double)i1 * 0.1, 4000});
  out.push_back({"VIC_AC_V2", "formatFixed0", (double)v2 * 0.01, 4000});
  out.push_back({"VIC_AC_I2", "formatFixed0", (double)i2 * 0.1, 4000});
  out.push_back({"VIC_AC_V3", "formatFixed0", (double)v3 * 0.01, 4000});
  out.push_back({"VIC_AC_I3", "formatFixed0", (double)i3 * 0.1, 4000});
  out.push_back({"VIC_AC_TEMP", "formatFixed0", (double)temp, 8000});
  out.push_back({"VIC_AC_I", "formatFixed0", (double)ac_i * 0.1, 4000});
  out.push_back({"VIC_AC_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_AC_ERR", "formatFixed0", (double)err, 8000});
}

static void parseSmartBatteryProtect_09(const uint8_t* plain, size_t encLen, GwLog* log,
                                        std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 120, log, "smart_batt_protect")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t out_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t alarm = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t warn = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t vin_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t vout_raw = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint32_t off_reason = readBitsLEAdvance(plain, b, 32);

  out.push_back({"VIC_SBP_VIN", "formatFixed0", (double)vin_raw * 0.01, 4000});
  out.push_back({"VIC_SBP_VOUT", "formatFixed0", (double)vout_raw * 0.01, 4000});
  out.push_back({"VIC_SBP_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_SBP_OUT", "formatFixed0", (double)out_state, 8000});
  out.push_back({"VIC_SBP_ERR", "formatFixed0", (double)err, 8000});
  out.push_back({"VIC_SBP_ALARM", "formatFixed0", (double)alarm, 8000});
  out.push_back({"VIC_SBP_WARN", "formatFixed0", (double)warn, 8000});
  out.push_back({"VIC_SBP_OFF", "formatFixed0", (double)off_reason, 8000});
}

static void parseLynxSmartBms_0A(const uint8_t* plain, size_t encLen, GwLog* log,
                                 std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 127, log, "lynx_bms")) return;
  uint16_t b = 0;
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t ttg = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t vb_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t ib_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t io_status = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint32_t warn = readBitsLEAdvance(plain, b, 18);
  const uint16_t soc = (uint16_t)readBitsLEAdvance(plain, b, 10);
  const int32_t cons_ah = signExtend(readBitsLEAdvance(plain, b, 20), 20);
  const uint16_t temp = (uint16_t)readBitsLEAdvance(plain, b, 7);

  out.push_back({"VIC_LBMS_V", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_LBMS_I", "formatFixed0", (double)ib_raw * 0.1, 4000});
  out.push_back({"VIC_LBMS_SOC", "formatFixed0", (double)soc * 0.1, 8000});
  out.push_back({"VIC_LBMS_TTG", "formatFixed0", (double)ttg, 8000});
  out.push_back({"VIC_LBMS_TEMP", "formatFixed0", (double)temp, 8000});
  out.push_back({"VIC_LBMS_IO", "formatFixed0", (double)io_status, 8000});
  out.push_back({"VIC_LBMS_WARN", "formatFixed0", (double)warn, 8000});
  out.push_back({"VIC_LBMS_CONS_AH", "formatFixed0", (double)cons_ah * 0.1, 8000});
  out.push_back({"VIC_LBMS_ERR", "formatFixed0", (double)err, 8000});
}

static void parseMultiRs_0B(const uint8_t* plain, size_t encLen, GwLog* log,
                            std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 112, log, "multi_rs")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const int16_t ib_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t vb_raw = (uint16_t)readBitsLEAdvance(plain, b, 14);
  const uint8_t ac_in = (uint8_t)readBitsLEAdvance(plain, b, 2);
  const int16_t ac_in_p = (int16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t ac_out_p = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t pv_p = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t yld = (uint16_t)readBitsLEAdvance(plain, b, 16);

  out.push_back({"VIC_MRS_V", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_MRS_I", "formatFixed0", (double)ib_raw * 0.1, 4000});
  out.push_back({"VIC_MRS_AC_IN_P", "formatFixed0", (double)ac_in_p, 4000});
  out.push_back({"VIC_MRS_AC_OUT_P", "formatFixed0", (double)ac_out_p, 4000});
  out.push_back({"VIC_MRS_PV_W", "formatFixed0", (double)pv_p, 4000});
  out.push_back({"VIC_MRS_Y_KWH", "formatFixed0", (double)yld * 0.01, 20000});
  out.push_back({"VIC_MRS_AC_IN", "formatFixed0", (double)ac_in, 8000});
  out.push_back({"VIC_MRS_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_MRS_ERR", "formatFixed0", (double)err, 8000});
}

static void parseVeBus_0C(const uint8_t* plain, size_t encLen, GwLog* log,
                          std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 102, log, "ve_bus")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t ve_err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const int16_t ib_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t vb_raw = (uint16_t)readBitsLEAdvance(plain, b, 14);
  const uint8_t ac_in = (uint8_t)readBitsLEAdvance(plain, b, 2);
  const int32_t ac_in_p = signExtend(readBitsLEAdvance(plain, b, 19), 19);
  const int32_t ac_out_p = signExtend(readBitsLEAdvance(plain, b, 19), 19);
  const uint8_t alarm = (uint8_t)readBitsLEAdvance(plain, b, 2);
  const uint16_t temp = (uint16_t)readBitsLEAdvance(plain, b, 7);
  const uint16_t soc = (uint16_t)readBitsLEAdvance(plain, b, 7);

  out.push_back({"VIC_VEBUS_V", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_VEBUS_I", "formatFixed0", (double)ib_raw * 0.1, 4000});
  out.push_back({"VIC_VEBUS_AC_IN_P", "formatFixed0", (double)ac_in_p, 4000});
  out.push_back({"VIC_VEBUS_AC_OUT_P", "formatFixed0", (double)ac_out_p, 4000});
  out.push_back({"VIC_VEBUS_AC_IN", "formatFixed0", (double)ac_in, 8000});
  out.push_back({"VIC_VEBUS_ALARM", "formatFixed0", (double)alarm, 8000});
  out.push_back({"VIC_VEBUS_TEMP", "formatFixed0", (double)temp, 8000});
  out.push_back({"VIC_VEBUS_SOC", "formatFixed0", (double)soc, 8000});
  out.push_back({"VIC_VEBUS_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_VEBUS_ERR", "formatFixed0", (double)ve_err, 8000});
}

static void parseDcEnergyMeter_0D(const uint8_t* plain, size_t encLen, GwLog* log,
                                 std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 88, log, "dc_energy_meter")) return;
  uint16_t b = 0;
  const int16_t mode = (int16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t vb_raw = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t alarm = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const int16_t aux = (int16_t)readBitsLEAdvance(plain, b, 16);
  const uint8_t aux_type = (uint8_t)readBitsLEAdvance(plain, b, 2);
  const int32_t ib_raw = signExtend(readBitsLEAdvance(plain, b, 22), 22);

  out.push_back({"VIC_DCM_V", "formatFixed0", (double)vb_raw * 0.01, 4000});
  out.push_back({"VIC_DCM_I", "formatFixed0", (double)ib_raw * 0.001, 4000});
  out.push_back({"VIC_DCM_MODE", "formatFixed0", (double)mode, 8000});
  out.push_back({"VIC_DCM_ALARM", "formatFixed0", (double)alarm, 8000});
  out.push_back({"VIC_DCM_AUX", "formatFixed0", (double)aux * 0.01, 8000});
  out.push_back({"VIC_DCM_AUXT", "formatFixed0", (double)aux_type, 8000});
}

static void parseOrionXs_0F(const uint8_t* plain, size_t encLen, GwLog* log,
                           std::vector<SetBoatDataRequest::Entry>& out) {
  if (!ensureBits(encLen, 112, log, "orion_xs")) return;
  uint16_t b = 0;
  const uint8_t dev_state = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint8_t err = (uint8_t)readBitsLEAdvance(plain, b, 8);
  const uint16_t vout = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t iout = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t vin = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint16_t iin = (uint16_t)readBitsLEAdvance(plain, b, 16);
  const uint32_t off_reason = readBitsLEAdvance(plain, b, 32);

  out.push_back({"VIC_ORX_VOUT", "formatFixed0", (double)vout * 0.01, 4000});
  out.push_back({"VIC_ORX_IOUT", "formatFixed0", (double)iout * 0.1, 4000});
  out.push_back({"VIC_ORX_VIN", "formatFixed0", (double)vin * 0.01, 4000});
  out.push_back({"VIC_ORX_IIN", "formatFixed0", (double)iin * 0.1, 4000});
  out.push_back({"VIC_ORX_STATE", "formatFixed0", (double)dev_state, 8000});
  out.push_back({"VIC_ORX_ERR", "formatFixed0", (double)err, 8000});
  out.push_back({"VIC_ORX_OFF", "formatFixed0", (double)off_reason, 8000});
}

// Victron frame decode (minimal):
// - data[0] must be 0x10 (Instant Readout/Manufacturer specific)
// - recordType in data[4] (0x01 solar, 0x02 battery monitor, ...)
// - nonce bytes data[5], data[6]
// - encrypted payload starts at data[8] (direct manufacturer payload)
enum class VictronDeviceType {
  Solar,
  Shunt
};

static void handleVictronFrame(
  GwApi* api,
  const VictronDeviceCfg& dev,
  const char* slotName,
  uint8_t expectedRecordType,
  const uint8_t* data, size_t len
){
  GwLog* log = api->getLogger();
  if (!dev.hasMac || !dev.hasKey) return;
  static uint32_t lastDropLogMs = 0;
  const uint32_t nowMsDrop = millis();
  const bool allowDropLog = (uint32_t)(nowMsDrop - lastDropLogMs) > 5000;

  if (s_aesBackoffUntilMs != 0) {
    if ((int32_t)(nowMsDrop - s_aesBackoffUntilMs) < 0) {
      if ((uint32_t)(nowMsDrop - s_lastAesBackoffLogMs) > 5000) {
        log->logDebug(GwLog::LOG, "Victron decrypt backoff active");
        s_lastAesBackoffLogMs = nowMsDrop;
      }
      return;
    }
    s_aesBackoffUntilMs = 0;
  }

  if (len < 12) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG, "Victron drop: short len=%u", (unsigned)len);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }
  if (data[0] != 0x10) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG, "Victron drop: bad header=0x%02x len=%u",
                    data[0], (unsigned)len);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }

  // Spec-konformes Layout (siehe esphome-victron_ble):
  // [0]=0x10 (Product Advertisement)
  // [1]=manufacturer_record_length
  // [2..3]=product_id (LE)
  // [4]=record_type
  // [5..6]=data_counter (LSB/MSB)
  // [7]=encryption_key_0 (bindkey byte 0)
  // [8..]=ciphertext (bis 16 Byte)
  if (len < 8) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG, "Victron drop: short base len=%u", (unsigned)len);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }

  const uint8_t manufacturerLen = data[1];
  const uint16_t productId = (uint16_t)data[2] | ((uint16_t)data[3] << 8);
  const uint8_t recordType = data[4];
  const uint8_t keyCheck = data[7];

  if (keyCheck != dev.key[0]) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG,
                    "Victron drop: keyCheck mismatch got=0x%02x expect=0x%02x pid=0x%04x",
                    (unsigned)keyCheck, (unsigned)dev.key[0], (unsigned)productId);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }

  size_t nonceOff = 5;
  size_t encStart = 8;
  size_t encLen = len - encStart;

  if (len < 8 || nonceOff + 1 >= len || encStart >= len) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG, "Victron drop: no enc payload len=%u", (unsigned)len);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }
  const uint8_t nonce2[2] = { data[nonceOff], data[nonceOff + 1] };
  if (expectedRecordType != 0x00 && recordType != expectedRecordType && allowDropLog) {
    log->logDebug(GwLog::LOG,
                  "Victron warn: slot=%s expected rt=0x%02x got=0x%02x",
                  slotName ? slotName : "-", expectedRecordType, recordType);
    lastDropLogMs = nowMsDrop;
  }
  if (len < 24 && allowDropLog) {
    const uint16_t dataCounter = (uint16_t)nonce2[0] | ((uint16_t)nonce2[1] << 8);
    log->logDebug(GwLog::LOG,
                  "Victron base frame slot=%s len=%u mlen=%u pid=0x%04x rt=0x%02x encStart=%u encLen=%u nonceOff=%u ctr=%u",
                  slotName ? slotName : "-",
                  (unsigned)len, (unsigned)manufacturerLen, (unsigned)productId,
                  (unsigned)recordType, (unsigned)encStart, (unsigned)encLen,
                  (unsigned)nonceOff, (unsigned)dataCounter);
    lastDropLogMs = nowMsDrop;
  }
  const uint8_t* enc = data + encStart;
  if (encLen > 16) encLen = 16;

  uint8_t plain[16] = {0};
  if (!victronDecryptCtr(dev.key, nonce2, enc, encLen, plain)) {
    log->logDebug(GwLog::ERROR,
                  "Victron decrypt failed len=%u rt=0x%02x nonce=%02x%02x",
                  (unsigned)len, recordType, nonce2[0], nonce2[1]);
    s_aesBackoffUntilMs = nowMsDrop + 2000;
    return;
  }

  s_lastRxMs = millis();
  s_lastRxType = recordType;
  s_rxCount++;
  strncpy(s_lastRxMac, s_currentMatchMac, sizeof(s_lastRxMac) - 1);
  s_lastRxMac[sizeof(s_lastRxMac) - 1] = '\0';
  {
    const size_t copyLen = encLen > sizeof(s_lastPlain) ? sizeof(s_lastPlain) : encLen;
    if (copyLen > 0) {
      memcpy(s_lastPlain, plain, copyLen);
      s_lastPlainLen = (uint8_t)copyLen;
      s_lastPlainType = recordType;
      s_lastRxSeq++;
    }
  }

  std::vector<SetBoatDataRequest::Entry> entries;
  entries.reserve(12);

  auto parseByType = [&](uint8_t type) {
    switch (type) {
      case 0x01:
        parseSolarCharger_01(plain, log, entries);
        break;
      case 0x02:
        parseBatteryMonitor_02(plain, log, entries);
        break;
      case 0x03:
        parseInverter_03(plain, encLen, log, entries);
        break;
      case 0x04:
        parseDcdc_04(plain, encLen, log, entries);
        break;
      case 0x05:
        parseSmartLithium_05(plain, encLen, log, entries);
        break;
      case 0x06:
        parseInverterRs_06(plain, encLen, log, entries);
        break;
      case 0x08:
        parseAcCharger_08(plain, encLen, log, entries);
        break;
      case 0x09:
        parseSmartBatteryProtect_09(plain, encLen, log, entries);
        break;
      case 0x0A:
        parseLynxSmartBms_0A(plain, encLen, log, entries);
        break;
      case 0x0B:
        parseMultiRs_0B(plain, encLen, log, entries);
        break;
      case 0x0C:
        parseVeBus_0C(plain, encLen, log, entries);
        break;
      case 0x0D:
        parseDcEnergyMeter_0D(plain, encLen, log, entries);
        break;
      case 0x0F:
        parseOrionXs_0F(plain, encLen, log, entries);
        break;
      default:
        break;
    }
  };

  const uint8_t parseType = expectedRecordType != 0x00 ? expectedRecordType : recordType;
  parseByType(parseType);
  if (entries.empty() && parseType != recordType) {
    parseByType(recordType);
  }
  if (entries.empty()) {
    if (allowDropLog) {
      log->logDebug(GwLog::LOG, "Victron warn: no data parsed rt=0x%02x exp=0x%02x len=%u",
                    recordType, expectedRecordType, (unsigned)len);
      lastDropLogMs = nowMsDrop;
    }
    return;
  }

  // Throttled "RX ok" marker so we can see BLE data flow without DEBUG spam
  static uint32_t lastRxLogMs = 0;
  const uint32_t nowMsRx = millis();
  if ((uint32_t)(nowMsRx - lastRxLogMs) > 5000) {
    const String plainHex = bytesToHex(plain, sizeof(plain));
    // Single-line log reduces interleaving/partial output on busy UART.
    log->logDebug(
      GwLog::LOG,
      "VIC: RX type=0x%02x len=%u encStart=%u nonce=%02x%02x plain=%s",
      recordType,
      (unsigned)len,
      (unsigned)encStart,
      nonce2[0],
      nonce2[1],
      plainHex.c_str()
    );
    log->flush();
    lastRxLogMs = nowMsRx;
  }

  // BoatData schreiben (Main-Thread)
  SetBoatDataRequest* r = new SetBoatDataRequest(api, api->getSourceId());
  r->entries = std::move(entries);
  if (api->getQueue()->sendAndWait(r, 2000) != GwRequestQueue::MSG_OK) {
    log->logDebug(GwLog::ERROR, "Victron set boatData request not handled");
  }
  r->unref();
}

// NimBLE advertised device callback
class VictronScanCallbacks : public NimBLEScanCallbacks {
  GwApi* api;
  std::vector<VictronConfiguredDevice> devices;
  bool listAll;
  uint32_t lastResetMs = 0;
public:
  VictronScanCallbacks(GwApi* api, const std::vector<VictronConfiguredDevice>& devices, bool listAll)
    : api(api), devices(devices), listAll(listAll) {
    }

  void onResult(const NimBLEAdvertisedDevice* d) override {
    // MAC match
    const NimBLEAddress a = d->getAddress();
    const String aRaw = normalizeMac(String(a.toString().c_str()));
    bool isMatch = false;
    const VictronConfiguredDevice* matches[4] = {nullptr, nullptr, nullptr, nullptr};
    size_t matchCount = 0;
    for (const auto& dev : devices) {
      if (dev.cfg.hasMac && aRaw.length() == 12 && aRaw == dev.cfg.macRaw) {
        isMatch = true;
        if (matchCount < 4) {
          matches[matchCount++] = &dev;
        }
      }
    }

    // manufacturer data
    std::string md = d->getManufacturerData();
    if (md.size() == 0) return;

    const uint8_t* b = (const uint8_t*)md.data();
    size_t n = md.size();

    if (listAll) {
      const uint32_t nowMsList = millis();
      if (lastResetMs == 0) lastResetMs = nowMsList;
      if ((uint32_t)(nowMsList - lastResetMs) > 60000) {
        lastResetMs = nowMsList;
      }
    }

    // If we see any Victron-like payload, track summary counters
    static uint32_t lastSeenLogMs = 0;
    const uint32_t nowMsSeen = millis();
    const bool hasVictronCompany = (n >= 2 && b[0] == 0xE1 && b[1] == 0x02);
    const bool victronLike = hasVictronCompany || (b[0] == 0x10) || (n >= 3 && b[2] == 0x10);
    if (victronLike && (listAll || isMatch)) {
      s_lastAdvSeenMs = nowMsSeen;
      s_advSeenCount++;
      copyMac(s_lastAdvMac, String(a.toString().c_str()));
    }
    if (victronLike && listAll && (uint32_t)(nowMsSeen - lastSeenLogMs) > 5000) {
      lastSeenLogMs = nowMsSeen;
    }

    if (!isMatch) return;

    if (!isMatch) return;

    s_lastMatchMs = nowMsSeen;
    s_matchCount++;
    copyMac(s_lastMatchMac, String(a.toString().c_str()));
    copyMac(s_currentMatchMac, String(a.toString().c_str()));

    // manche Stacks liefern Company ID (2B) vorne mit — häufig 0x02E1 (Victron)
    if (hasVictronCompany && n > 2) {
      b += 2;
      n -= 2;
    }

    // Robust: Header (0x10) in den ersten Bytes suchen und darauf ausrichten.
    if (n >= 12 && b[0] != 0x10) {
      size_t searchMax = n > 12 ? std::min((size_t)6, n - 12) : 0;
      size_t headerOffset = (size_t)-1;
      for (size_t i = 1; i <= searchMax; ++i) {
        if (b[i] == 0x10) { headerOffset = i; break; }
      }
      if (headerOffset != (size_t)-1) {
        b += headerOffset;
        n -= headerOffset;
      }
    }

    if (n < 12 || b[0] != 0x10) return;

    for (size_t i = 0; i < matchCount; ++i) {
      const auto* dev = matches[i];
      if (!dev) continue;
      handleVictronFrame(api, dev->cfg, dev->slotName.c_str(), dev->expectedRecordType, b, n);
    }
  }
};

void victronBleInit(GwApi* api) {
  // Früher BLE-Init, bevor speicherintensive Tasks/Subsysteme starten
  GwLog* log = api->getLogger();
  auto* cfg = api->getConfig();
  log->logDebug(GwLog::LOG, "victronBleInit");

  const bool enable = cfg->getConfigItem("vicEnable", true)->asBoolean();
  if (!enable) {
    log->logDebug(GwLog::LOG, "victronBleInit: disabled (vicEnable=false)");
    return;
  }

  auto devices = loadConfiguredDevices(api);
  for (const auto& d : devices) {
    log->logDebug(GwLog::LOG, "Victron cfg: slot=%s type=%s mac=%s key=%s",
                  d.slotName.c_str(), d.type.c_str(),
                  d.cfg.macRaw.c_str(), maskKey(bytesToHex(d.cfg.key, 16)).c_str());
  }
  if (devices.empty()) {
    log->logDebug(GwLog::LOG, "victronBleInit: no devices configured");
    return;
  }

  if (s_nimbleInitialized) return;

  size_t largestInternal = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
  size_t freeInternal = heap_caps_get_free_size(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
  size_t freeTotal = heap_caps_get_free_size(MALLOC_CAP_DEFAULT);
  log->logDebug(GwLog::LOG, "BLE_INIT: early check - freeInternal=%u, largestInternal=%u, freeTotal=%u",
                (unsigned)freeInternal, (unsigned)largestInternal, (unsigned)freeTotal);

  if (largestInternal < MIN_FREE_INTERNAL) {
    log->logDebug(GwLog::LOG, "BLE_INIT: early init skipped (largestInternal=%u < %u)",
                  (unsigned)largestInternal, (unsigned)MIN_FREE_INTERNAL);
    return;
  }

  log->logDebug(GwLog::LOG, "BLE_INIT: early init");
  NimBLEDevice::init("");
  NimBLEDevice::setPower(ESP_PWR_LVL_P9); // max power for better range
  s_nimbleInitialized = true;
}

void victronBleTask(GwApi* api) {
  GwLog* log = api->getLogger();
  auto* cfg = api->getConfig();
  s_taskRunning = true;
  {
    const uint32_t freeInternal = heap_caps_get_free_size(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
    const uint32_t largestInternal = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
    USBSerial.printf("VIC: task start freeInternal=%u largestInternal=%u\n",
                     (unsigned)freeInternal, (unsigned)largestInternal);
    USBSerial.flush();
  }
  log->logDebug(GwLog::LOG, "Victron BLE: task start");
  log->logDebug(GwLog::LOG, "Victron BLE cfg: enable=%d scanMs=%d active=%d listAll=%d",
                cfg->getConfigItem("vicEnable", true)->asBoolean() ? 1 : 0,
                cfg->getConfigItem("vicScanMs", true)->asInt(),
                cfg->getConfigItem("vicActiveScan", true)->asBoolean() ? 1 : 0,
                cfg->getConfigItem("vicBleListAll", true)->asBoolean() ? 1 : 0);
  {
    const UBaseType_t hwm = uxTaskGetStackHighWaterMark(NULL);
    log->logDebug(GwLog::LOG, "Victron BLE: stack HWM=%u words (%u bytes)",
                  (unsigned)hwm, (unsigned)(hwm * sizeof(uint32_t)));
  }

  const bool enable = cfg->getConfigItem("vicEnable", true)->asBoolean();
  if (!enable) {
    log->logDebug(GwLog::LOG, "Victron BLE disabled");
    log->logDebug(GwLog::LOG, "Victron BLE: task exit (disabled)");
    s_taskRunning = false;
    vTaskDelete(NULL);
    return;
  }

#if defined(BOARD_OBP60S3) || defined(BOARD_OBP40S3)
  // Wait until OBP60 reaches the point before keyboard/sensor tasks
  const uint32_t waitBleStart = millis();
  while (!obp60BleReady() && (millis() - waitBleStart) < 5000) {
    delay(100);
  }
  log->logDebug(GwLog::LOG, "Victron BLE: wait OBP60 BLE ready=%d",
                obp60BleReady() ? 1 : 0);
  USBSerial.printf("VIC: wait OBP60 BLE ready=%d\n", obp60BleReady() ? 1 : 0);
  USBSerial.flush();
#endif
  const int scanIntervalMs = cfg->getConfigItem("vicScanMs", true)->asInt();

  auto devices = loadConfiguredDevices(api);
  for (const auto& d : devices) {
    log->logDebug(GwLog::LOG, "Victron cfg: slot=%s type=%s mac=%s key=%s",
                  d.slotName.c_str(), d.type.c_str(),
                  d.cfg.macRaw.c_str(), maskKey(bytesToHex(d.cfg.key, 16)).c_str());
  }
  if (devices.empty()) {
    log->logDebug(GwLog::LOG, "No Victron devices configured, stopping task");
    log->logDebug(GwLog::LOG, "Victron BLE: task exit (no devices)");
    s_taskRunning = false;
    vTaskDelete(NULL);
    return;
  }

  if (!s_nimbleInitialized) {
  // Warten bis genug interner RAM frei ist (NimBLE braucht ~20KB zusammenhängend)
  int waitCount = 0;
  size_t largestInternal = 0;
  
  while (true) {
    largestInternal = heap_caps_get_largest_free_block(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
    size_t freeInternal = heap_caps_get_free_size(MALLOC_CAP_INTERNAL | MALLOC_CAP_8BIT);
    size_t freeTotal = heap_caps_get_free_size(MALLOC_CAP_DEFAULT);
    
    if (waitCount % 10 == 0) { // alle 10 Sekunden loggen
      log->logDebug(GwLog::LOG, "BLE_INIT: waiting for RAM - freeInternal=%u, largestInternal=%u, freeTotal=%u", 
                    (unsigned)freeInternal, (unsigned)largestInternal, (unsigned)freeTotal);
        USBSerial.printf("VIC: wait RAM freeInternal=%u largestInternal=%u freeTotal=%u\n",
                         (unsigned)freeInternal, (unsigned)largestInternal, (unsigned)freeTotal);
        USBSerial.flush();
    }
    
    if (largestInternal >= MIN_FREE_INTERNAL) {
      log->logDebug(GwLog::LOG, "BLE_INIT: enough RAM available, initializing BLE");
        USBSerial.println("VIC: BLE init start");
        USBSerial.flush();
      break;
    }
    
    if (waitCount++ > 60) { // max 60 Sekunden warten
        log->logDebug(GwLog::ERROR, "BLE_INIT: timeout waiting for RAM, retrying");
        waitCount = 0;
        delay(10000); // kurze Pause, dann erneut warten
        continue;
    }
    
    delay(1000); // 1 Sekunde warten
  }

    if (!s_btClassicReleased) {
      esp_err_t rc = esp_bt_controller_mem_release(ESP_BT_MODE_CLASSIC_BT);
      log->logDebug(GwLog::LOG, "Victron BLE: release Classic BT memory rc=%d", (int)rc);
      USBSerial.printf("VIC: release Classic BT rc=%d\n", (int)rc);
      USBSerial.flush();
      s_btClassicReleased = true;
    }

  NimBLEDevice::init("");
  NimBLEDevice::setPower(ESP_PWR_LVL_P9); // max power for better range
    s_nimbleInitialized = true;
    log->logDebug(GwLog::LOG, "Victron BLE: NimBLE init done");
    USBSerial.println("VIC: BLE init done");
    USBSerial.flush();
  }

#if defined(BOARD_OBP60S3) || defined(BOARD_OBP40S3)
  // Start scanning only after OBP60 created its auxiliary tasks (reduces init peaks overlap)
  const uint32_t waitTasksStart = millis();
  while (!obp60TasksReady() && (millis() - waitTasksStart) < 15000) {
    delay(200);
  }
  log->logDebug(GwLog::LOG, "Victron BLE: wait OBP60 tasks=%d",
                obp60TasksReady() ? 1 : 0);
  USBSerial.printf("VIC: wait OBP60 tasks=%d\n", obp60TasksReady() ? 1 : 0);
  USBSerial.flush();
#endif

  USBSerial.println("VIC: scan setup");
  USBSerial.flush();
  NimBLEScan* scan = NimBLEDevice::getScan();
  // Scanner schlank halten (puffer klein halten spart RAM)
  const int maxResultsNormal = 4;
  const int maxResultsListAll = 8;
  const int maxResultsAggressive = 8;
  const int scanIntervalNormal = 300;
  const int scanWindowNormal = 30;
  const int scanIntervalListAll = 200;
  const int scanWindowListAll = 50;
  const int scanIntervalAggressive = 160;
  const int scanWindowAggressive = 60;
  scan->setMaxResults(maxResultsNormal);      // nur wenige Ergebnisse puffern
  scan->clearResults();        // alte Ergebnisse verwerfen
  // Scan-Callbacks registrieren (wird von NimBLE verwaltet)
  const bool listAll = cfg->getConfigItem("vicBleListAll", true)->asBoolean();
  // Wir wollen wiederholte Advertisements sehen (Telemetry), daher Duplicates erlauben.
  scan->setScanCallbacks(new VictronScanCallbacks(api, devices, listAll), true);
  const bool activeScan = cfg->getConfigItem("vicActiveScan", true)->asBoolean();
  if (listAll) {
    // Debug: aggressiver Scan, aber Puffer klein halten
    scan->setMaxResults(maxResultsListAll);
    scan->setActiveScan(true);
    scan->setInterval(scanIntervalListAll);
    scan->setWindow(scanWindowListAll);
    scan->setDuplicateFilter(false);
    log->logDebug(GwLog::LOG, "BLE scan cfg: active=1 interval=%d window=%d max=%d",
                  scanIntervalListAll, scanWindowListAll, maxResultsListAll);
  } else {
    scan->setActiveScan(activeScan);
    scan->setInterval(scanIntervalNormal);
    scan->setWindow(scanWindowNormal);
    scan->setDuplicateFilter(false);
    log->logDebug(GwLog::LOG, "BLE scan cfg: active=%d interval=%d window=%d",
                  activeScan ? 1 : 0, scanIntervalNormal, scanWindowNormal);
  }

  log->logDebug(GwLog::LOG, "Victron BLE scan start");
  USBSerial.println("VIC: scan start");
  USBSerial.flush();
  static uint32_t lastSummaryMs = 0;
  static uint32_t lastStackMs = 0;
  static uint32_t lastScanLogMs = 0;
  static int lastScanCount = -1;
  static uint32_t lastPlainLogMs = 0;
  static uint32_t lastRxSeqLogged = 0;
  if (listAll) {
    // Debug: dauerhaft scannen und regelmäßig Ergebnisse ausgeben
    if (!scan->start(0, false)) {
      log->logDebug(GwLog::ERROR, "BLE scan start failed");
      USBSerial.println("VIC: scan start failed");
      USBSerial.flush();
    }
    while (true) {
      delay(5000);
      const uint32_t nowMs = millis();
      if ((uint32_t)(nowMs - lastSummaryMs) > 10000) {
        logBleSummary(log, nowMs);
        lastSummaryMs = nowMs;
      }
      if (s_lastRxSeq != lastRxSeqLogged && (uint32_t)(nowMs - lastPlainLogMs) > 5000) {
        char hexbuf[33];
        const size_t hexLen = s_lastPlainLen > 8 ? 8 : s_lastPlainLen;
        hexEncode(s_lastPlain, hexLen, hexbuf, sizeof(hexbuf));
        USBSerial.printf("VIC: last plain rt=0x%02x len=%u hex=%s\n",
                         (unsigned)s_lastPlainType, (unsigned)s_lastPlainLen, hexbuf);
        USBSerial.flush();
        lastPlainLogMs = nowMs;
        lastRxSeqLogged = s_lastRxSeq;
      }
      if ((uint32_t)(nowMs - lastStackMs) > 10000) {
        const UBaseType_t hwm = uxTaskGetStackHighWaterMark(NULL);
        log->logDebug(GwLog::LOG, "Victron BLE: stack HWM=%u words (%u bytes)",
                      (unsigned)hwm, (unsigned)(hwm * sizeof(uint32_t)));
        lastStackMs = nowMs;
      }
      if (!scan->isScanning()) {
        log->logDebug(GwLog::ERROR, "BLE scan stopped unexpectedly, restarting");
        scan->start(0, true);
      }
      NimBLEScanResults results = scan->getResults();
      const int count = results.getCount();
      if (count != lastScanCount || (uint32_t)(nowMs - lastScanLogMs) > 10000) {
        log->logDebug(GwLog::LOG, "BLE scan running results=%d", count);
        USBSerial.printf("VIC: scan running results=%d\n", count);
        USBSerial.flush();
        lastScanLogMs = nowMs;
        lastScanCount = count;
      }
      const int maxList = std::min(10, count);
      for (int i = 0; i < maxList; i++) {
        const NimBLEAdvertisedDevice* dev = results.getDevice(i);
        if (!dev) continue;
        log->logDebug(GwLog::LOG, "BLE dev %s rssi=%d",
                      dev->getAddress().toString().c_str(),
                      dev->getRSSI());
      }
      // Free scan result storage to keep heap low
      scan->clearResults();
    }
  } else {
    int noAdvStreak = 0;
  while (true) {
      const uint32_t nowMs = millis();
      if ((uint32_t)(nowMs - lastSummaryMs) > 10000) {
        logBleSummary(log, nowMs);
        lastSummaryMs = nowMs;
      }
      if (s_lastRxSeq != lastRxSeqLogged && (uint32_t)(nowMs - lastPlainLogMs) > 5000) {
        char hexbuf[33];
        const size_t hexLen = s_lastPlainLen > 8 ? 8 : s_lastPlainLen;
        hexEncode(s_lastPlain, hexLen, hexbuf, sizeof(hexbuf));
        USBSerial.printf("VIC: last plain rt=0x%02x len=%u hex=%s\n",
                         (unsigned)s_lastPlainType, (unsigned)s_lastPlainLen, hexbuf);
        USBSerial.flush();
        lastPlainLogMs = nowMs;
        lastRxSeqLogged = s_lastRxSeq;
      }
      if ((uint32_t)(nowMs - lastStackMs) > 10000) {
        const UBaseType_t hwm = uxTaskGetStackHighWaterMark(NULL);
        log->logDebug(GwLog::LOG, "Victron BLE: stack HWM=%u words (%u bytes)",
                      (unsigned)hwm, (unsigned)(hwm * sizeof(uint32_t)));
        lastStackMs = nowMs;
      }
      // Blockierender Scan für scanIntervalMs Millisekunden
      NimBLEScanResults results = scan->getResults((uint32_t)std::max(1, scanIntervalMs), false);
      const int count = results.getCount();
      if (count != lastScanCount || (uint32_t)(nowMs - lastScanLogMs) > 10000) {
        log->logDebug(GwLog::LOG, "BLE scan done results=%d", count);
        USBSerial.printf("VIC: scan done results=%d\n", count);
        USBSerial.flush();
        lastScanLogMs = nowMs;
        lastScanCount = count;
      }
      if (count == 0) {
        noAdvStreak++;
      } else {
        noAdvStreak = 0;
      }
      // Free scan result storage to keep heap low
      scan->clearResults();
      if (noAdvStreak >= 3) {
        noAdvStreak = 0;
        log->logDebug(GwLog::ERROR, "BLE scan results=0 for multiple rounds, retry with aggressive scan");
        scan->setMaxResults(maxResultsAggressive);
        scan->setActiveScan(true);
        scan->setInterval(scanIntervalAggressive);
        scan->setWindow(scanWindowAggressive);
        scan->setDuplicateFilter(false);
        NimBLEScanResults aggressiveResults = scan->getResults(2000, false);
        const int aggressiveCount = aggressiveResults.getCount();
        log->logDebug(GwLog::LOG, "BLE aggressive scan results=%d", aggressiveCount);
        scan->clearResults();
        scan->setMaxResults(maxResultsNormal);
        scan->setActiveScan(activeScan);
        scan->setInterval(scanIntervalNormal);
        scan->setWindow(scanWindowNormal);
        scan->setDuplicateFilter(false);
      }
    delay(50);
    }
  }
}

#endif // !DISABLE_VICTRON_BLE
#endif // ESP32
