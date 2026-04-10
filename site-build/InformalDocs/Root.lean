import VersoManual
import InformalDocs.PostnikovTower.Defs
import InformalDocs.GrothendieckGroup
import InformalDocs.EulerForm.Basic
import InformalDocs.ExtensionClosure
import InformalDocs.QuasiAbelian.Basic
import InformalDocs.TStructure
import InformalDocs.IntervalCategory
import InformalDocs.StabilityFunction
import InformalDocs.Slicing
import InformalDocs.NumericalStability.Defs
import InformalDocs.NumericalStabilityManifold
import InformalDocs.HeartEquivalence
import InformalDocs.StabilityCondition
import InformalDocs.Deformation
import InformalDocs.ForMathlib

open Verso.Genre Manual

set_option maxHeartbeats 800000

#doc (Manual) "Bridgeland Stability Conditions" =>

Inspired by Douglas's work on Π-stability in string theory, Bridgeland stability conditions allow one to extract a complex manifold from a triangulated category. A stability condition pairs a central charge — a group homomorphism from the Grothendieck group to the complex numbers — with a slicing of the category into semistable objects of each phase. Bridgeland's main theorem is that the space of all such conditions is itself a complex manifold, with local charts given by the central charge. The theory has since become one of the most active areas in modern mathematics. It provides infrastructure for wall-crossing in birational geometry, Donaldson-Thomas theory, and the study of moduli spaces of sheaves on surfaces and threefolds.

*About this formalization*

This site documents a machine-checked proof of the complex manifold theorem, formalized in Lean 4 using Mathlib. All Lean code is written by AI agents guided by human mathematicians — no human writes proof scripts. The formalization covers Sections 2–7 of Bridgeland's _Stability conditions on triangulated categories_ (Annals of Mathematics, 2007), working in class-map generality as in Bayer–Macrì–Stellari and Bayer–Lahoz–Macrì–Nuer–Perry–Stellari.

*Paper alignment*

The table below lists every definition, lemma, and theorem from the paper that currently has an exact formal analog.

*Why trust a proof written by AI?*

Two independent checks. First, every logical step is verified by Lean's kernel — a small, fixed type checker that accepts or rejects proofs regardless of how they were produced. The kernel guarantees the arguments are correct. Second, the [Comparator Manual](comparator/) lists the definitions the result depends on, paired with their informal mathematical meanings, so you can audit whether the formal statements faithfully capture the mathematics. Auto-generated [API documentation](api/BridgelandStability.html) is also available.

*Contributing*

Each declaration is paired with an informal description and, where available, a proof sketch. Passing the type checker is necessary but not sufficient: the formalization aims for Mathlib quality, with correct abstractions, reusable lemmas, and proofs that could survive code review and upstreaming. If you see a mathematical inaccuracy, a missing generalization, a cleaner definition, or — if you know Lean — a better proof strategy, each declaration has a link to open an issue. Describe what you think should happen and start a discussion. Once we figure out what needs to change, AI agents will do the rest.

{include 0 InformalDocs.PostnikovTower.Defs}

{include 0 InformalDocs.GrothendieckGroup}

{include 0 InformalDocs.EulerForm.Basic}

{include 0 InformalDocs.ExtensionClosure}

{include 0 InformalDocs.QuasiAbelian.Basic}

{include 0 InformalDocs.TStructure}

{include 0 InformalDocs.IntervalCategory}

{include 0 InformalDocs.StabilityFunction}

{include 0 InformalDocs.Slicing}

{include 0 InformalDocs.NumericalStability.Defs}

{include 0 InformalDocs.NumericalStabilityManifold}

{include 0 InformalDocs.HeartEquivalence}

{include 0 InformalDocs.StabilityCondition}

{include 0 InformalDocs.Deformation}

{include 0 InformalDocs.ForMathlib}
