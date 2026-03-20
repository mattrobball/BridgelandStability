// Lean compiler output
// Module: BridgelandStability.Deformation.PPhiAbelian
// Imports: public import Init public import BridgelandStability.StabilityCondition public import BridgelandStability.StabilityFunction public import BridgelandStability.IntervalCategory public import BridgelandStability.TStructure.HeartAbelian
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_StabilityCondition(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_StabilityFunction(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_IntervalCategory(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_TStructure_HeartAbelian(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_PPhiAbelian(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_StabilityCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_StabilityFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_IntervalCategory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_TStructure_HeartAbelian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
