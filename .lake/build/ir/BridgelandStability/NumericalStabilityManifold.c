// Lean compiler output
// Module: BridgelandStability.NumericalStabilityManifold
// Imports: public import Init public import BridgelandStability.DeformationTheorem public import BridgelandStability.EulerForm public import BridgelandStability.NumericalStability public import Mathlib.Analysis.Normed.Module.Connected public import Mathlib.Geometry.Manifold.Complex public import Mathlib.Topology.Algebra.Module.FiniteDimension public import Mathlib.Topology.Connected.TotallyDisconnected public import Mathlib.Topology.IsLocalHomeomorph public import Mathlib.Topology.LocalAtTarget
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
lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_K_u2080_instAddCommGroup(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_QuotientAddGroup_mk___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_AddMonoidHom_comp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lp_BridgelandStability_CategoryTheory_Triangulated_K_u2080_instAddCommGroup(lean_box(0), x_1, lean_box(0), x_2, x_3, lean_box(0), x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_closure((void*)(lp_mathlib_QuotientAddGroup_mk___boxed), 4, 3);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, x_5);
lean_closure_set(x_7, 2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lp_BridgelandStability_CategoryTheory_Triangulated_K_u2080_instAddCommGroup(lean_box(0), x_2, lean_box(0), x_4, x_5, lean_box(0), x_7);
x_10 = lean_box(0);
x_11 = lean_alloc_closure((void*)(lp_mathlib_QuotientAddGroup_mk___boxed), 4, 3);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_BridgelandStability_CategoryTheory_Triangulated_numericalQuotientMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_box(0);
x_5 = lean_alloc_closure((void*)(lp_mathlib_QuotientAddGroup_mk___boxed), 4, 3);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_1);
lean_closure_set(x_5, 2, x_4);
x_6 = lp_mathlib_AddMonoidHom_comp___redArg(x_2, x_5);
x_7 = lean_apply_1(x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lp_BridgelandStability_CategoryTheory_Triangulated_K_u2080_instAddCommGroup(lean_box(0), x_1, lean_box(0), x_2, x_3, lean_box(0), x_4);
x_6 = lean_alloc_closure((void*)(lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg___lam__0), 3, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___redArg(x_2, x_4, x_5, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lp_BridgelandStability_CategoryTheory_Triangulated_precomposeNumericalQuotient(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___redArg(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc_ref(x_13);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_BridgelandStability_CategoryTheory_Triangulated_ComponentTopologicalLinearLocalModel_ambientNumericalChargeMap(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_2(x_2, x_1, lean_box(0));
return x_3;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lean_apply_2(x_12, x_11, lean_box(0));
return x_13;
}
}
LEAN_EXPORT lean_object* lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = lp_BridgelandStability___private_BridgelandStability_NumericalStabilityManifold_0__CategoryTheory_Triangulated_componentZMap_match__1_splitter(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
return x_13;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_DeformationTheorem(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_EulerForm(uint8_t builtin);
lean_object* initialize_BridgelandStability_BridgelandStability_NumericalStability(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Normed_Module_Connected(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Geometry_Manifold_Complex(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Algebra_Module_FiniteDimension(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_Connected_TotallyDisconnected(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_IsLocalHomeomorph(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Topology_LocalAtTarget(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_BridgelandStability_BridgelandStability_NumericalStabilityManifold(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_DeformationTheorem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_EulerForm(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_BridgelandStability_BridgelandStability_NumericalStability(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Normed_Module_Connected(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Geometry_Manifold_Complex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Algebra_Module_FiniteDimension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_Connected_TotallyDisconnected(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_IsLocalHomeomorph(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Topology_LocalAtTarget(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
