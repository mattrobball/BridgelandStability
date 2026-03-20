// Lean compiler output
// Module: BridgelandStability.EulerForm
// Imports: public import Init public import BridgelandStability.NumericalStability public import Mathlib.CategoryTheory.Triangulated.Yoneda public import Mathlib.CategoryTheory.Linear.Yoneda public import Mathlib.CategoryTheory.Shift.Linear public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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
lean_object* initialize_BridgelandStability_BridgelandStability_NumericalStability(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Triangulated_Yoneda(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Linear_Yoneda(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Shift_Linear(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ModuleCat(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_FiniteDimensional_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability_EulerForm(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_NumericalStability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Triangulated_Yoneda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Linear_Yoneda(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Shift_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ModuleCat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_FiniteDimensional_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
