// Lean compiler output
// Module: BridgelandStability.Strict
// Imports: public import Init public import Mathlib.CategoryTheory.Abelian.Basic public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback public import Mathlib.Algebra.Homology.ShortComplex.ShortExact public import Mathlib.CategoryTheory.Subobject.Basic public import Mathlib.CategoryTheory.Subobject.ArtinianObject public import Mathlib.CategoryTheory.Subobject.NoetherianObject
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
lean_object* lp_mathlib_CategoryTheory_Subobject_mk___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_CategoryTheory_Subobject_lift___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
lean_inc(x_4);
x_9 = lean_apply_1(x_7, x_4);
x_10 = lean_apply_3(x_8, x_4, x_2, x_5);
x_11 = lp_mathlib_CategoryTheory_Subobject_mk___redArg(x_3, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg___lam__0), 6, 3);
lean_closure_set(x_5, 0, x_2);
lean_closure_set(x_5, 1, x_3);
lean_closure_set(x_5, 2, x_1);
x_6 = lp_mathlib_CategoryTheory_Subobject_lift___redArg(x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___redArg(x_4, x_5, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lp_BridgelandStability___private_BridgelandStability_Strict_0__CategoryTheory_subobjectImageOfFaithfulPreservesMono(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
return x_11;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Abelian_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Limits_Shapes_Pullback_HasPullback(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ShortExact(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_ArtinianObject(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_CategoryTheory_Subobject_NoetherianObject(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability_Strict(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Abelian_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Limits_Shapes_Pullback_HasPullback(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Homology_ShortComplex_ShortExact(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_ArtinianObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_CategoryTheory_Subobject_NoetherianObject(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
