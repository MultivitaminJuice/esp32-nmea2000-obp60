#pragma once
#include "GwApi.h"

// Für OBP60 S3 build-guards: wenn du willst, kannst du das enger fassen.
// Oft existieren Defines wie BOARD_OBP60S3 / HARDWARE_V21 – variiert je nach Env.
#ifdef ESP32

#if defined(DISABLE_VICTRON_BLE)
inline void victronBleTask(GwApi* api) { (void)api; }
inline void victronBleInit(GwApi* api) { (void)api; }
inline bool victronBleIsInitialized() { return false; }
inline bool victronBleTaskRunning() { return false; }
DECLARE_CAPABILITY(victronBle, false);
#else
void victronBleTask(GwApi* api);
void victronBleInit(GwApi* api);
bool victronBleIsInitialized();
bool victronBleTaskRunning();

// Stack größer, BLE + AES + NimBLE Callback brauchen Luft
// Start after OBP60Task so its large stack can be allocated first
DECLARE_USERTASK_PARAM(victronBleTask, 10000, 100);
// BLE init will be handled inside victronBleTask to avoid early heap pressure
// DECLARE_INITFUNCTION(victronBleInit);

// optional: Capability, damit du Config-Items filtern kannst
DECLARE_CAPABILITY(victronBle, true);
#endif

#endif
