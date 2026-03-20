// Lean compiler output
// Module: BridgelandStability
// Imports: public import Init public import BridgelandStability.Deformation.BoundaryTriangles public import BridgelandStability.Deformation.HomVanishing public import BridgelandStability.Deformation.IntervalSelection public import BridgelandStability.Deformation.Lemma77 public import BridgelandStability.Deformation.MDQ public import BridgelandStability.Deformation.MDQKernel public import BridgelandStability.Deformation.PPhiAbelian public import BridgelandStability.Deformation.PhaseArithmetic public import BridgelandStability.Deformation.PhaseConfinement public import BridgelandStability.Deformation.PhiPlusReduction public import BridgelandStability.Deformation.Pullback public import BridgelandStability.Deformation.Setup public import BridgelandStability.Deformation.StrictSES public import BridgelandStability.Deformation.TStructure public import BridgelandStability.Deformation.Theorem71 public import BridgelandStability.Deformation.WPhase public import BridgelandStability.DeformationTheorem public import BridgelandStability.EulerForm public import BridgelandStability.GrothendieckGroup public import BridgelandStability.HeartEquivalence public import BridgelandStability.IntervalCategory public import BridgelandStability.NumericalStability public import BridgelandStability.NumericalStabilityManifold public import BridgelandStability.PostnikovTower public import BridgelandStability.Slicing public import BridgelandStability.StabilityCondition public import BridgelandStability.StabilityFunction public import BridgelandStability.Strict public import BridgelandStability.TStructure.AbelianSubcategory public import BridgelandStability.TStructure.HeartAbelian
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
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_BoundaryTriangles(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_HomVanishing(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_IntervalSelection(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_Lemma77(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_MDQ(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_MDQKernel(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_PPhiAbelian(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_PhaseArithmetic(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_PhaseConfinement(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_PhiPlusReduction(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_Pullback(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_Setup(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_StrictSES(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_TStructure(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_Theorem71(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Deformation_WPhase(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_DeformationTheorem(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_EulerForm(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_GrothendieckGroup(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_HeartEquivalence(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_IntervalCategory(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_NumericalStability(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_NumericalStabilityManifold(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_PostnikovTower(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Slicing(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_StabilityCondition(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_StabilityFunction(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_Strict(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_TStructure_AbelianSubcategory(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_TStructure_HeartAbelian(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_BoundaryTriangles(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_HomVanishing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_IntervalSelection(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_Lemma77(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_MDQ(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_MDQKernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_PPhiAbelian(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_PhaseArithmetic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_PhaseConfinement(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_PhiPlusReduction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_Pullback(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_Setup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_StrictSES(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_TStructure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_Theorem71(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Deformation_WPhase(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_DeformationTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_EulerForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_GrothendieckGroup(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_HeartEquivalence(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_IntervalCategory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_NumericalStability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_NumericalStabilityManifold(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_PostnikovTower(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Slicing(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_StabilityCondition(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_StabilityFunction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_Strict(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_TStructure_AbelianSubcategory(builtin);
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
