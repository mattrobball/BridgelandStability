// Lean compiler output
// Module: BridgelandStability.StabilityFunction
// Imports: public import Init public import Mathlib.CategoryTheory.Abelian.Basic public import Mathlib.CategoryTheory.Abelian.Exact public import Mathlib.CategoryTheory.Subobject.Lattice public import Mathlib.CategoryTheory.Subobject.ArtinianObject public import Mathlib.CategoryTheory.Subobject.NoetherianObject public import Mathlib.CategoryTheory.Simple public import Mathlib.Algebra.Homology.ShortComplex.ShortExact public import Mathlib.Analysis.SpecialFunctions.Complex.Arg public import Mathlib.Order.Minimal public import Mathlib.Data.Fintype.Lattice
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
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Abelian_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Abelian_Exact(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_Lattice(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_ArtinianObject(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_NoetherianObject(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Simple(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ShortExact(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Arg(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Order_Minimal(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Fintype_Lattice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability_StabilityFunction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Abelian_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Abelian_Exact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_Lattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_ArtinianObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_NoetherianObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Simple(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ShortExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Complex_Arg(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Order_Minimal(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Fintype_Lattice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
