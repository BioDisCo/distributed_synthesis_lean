/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Model
import DistributedSynthesis.Formalizations.GraphAdversaries.HolesIff

/-! # Nowhere denseness characterizes decidable LTL synthesis

For each fixed omega-regular adversary, synthesis is computable exactly when
its geometric image is nowhere dense in [0,1], with its relative topology.
Equivalently, there are open holes at every scale. Input streams remain unrestricted.
The result permits X. The negative direction already holds with singleton
inputs and does not require omega-regularity. The positive solver is primitive
recursive in the instance; the adversary and its finite bounds are fixed.
-/
namespace DistributedSynthesis.GraphAdversaries

/-- Fix an omega-regular set `A` of allowed graph sequences. There is an algorithm
deciding realizability of finite LTL instances over `A` if and only if every
nonempty relatively open subset of `[0,1]` contains a nonempty relatively open
subset disjoint from the geometric image of `A`. The instance specifies finite,
nonempty input and output alphabets; the two private input streams are unrestricted. -/
theorem realizable_computable_iff_geometric_holes
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ GeometricHoles A :=
  Characterisation.WithInputs.realizable_computable_iff_geometric_holes A regular

/-- For a fixed omega-regular graph adversary, LTL realizability is computable
exactly when the closure of its geometric image has empty interior in `[0,1]`.
Both closure and interior are taken in the relative topology on `[0,1]`. -/
theorem realizable_computable_iff_interior_closure_empty
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ interior (closure (geometricMap '' A)) = ∅ :=
  Characterisation.WithInputs.realizable_computable_iff_interior_closure_empty A regular

/-- For each fixed omega-regular graph adversary, LTL realizability is computable
exactly when its geometric image is nowhere dense in `[0,1]`. The topology is
the relative topology on the interval, and private input streams are unrestricted. -/
theorem realizable_computable_iff_nowhere_dense
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ IsNowhereDense (geometricMap '' A) :=
  realizable_computable_iff_interior_closure_empty A regular

/-- For each fixed omega-regular adversary with geometric holes, there is a
primitive-recursive Boolean function that returns true exactly on its realizable
instances. The adversary is fixed; the encoded formula, truth table, and finite
input and output alphabets are arguments of the solver. -/
theorem holes_primitive_recursive_solver
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ solve : Instance → Bool, Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i :=
  Characterisation.WithInputs.holes_primitive_recursive_solver A regular holes

/-- A fixed omega-regular adversary with nowhere dense geometric image admits
a primitive-recursive Boolean solver on finite synthesis instances. -/
theorem nowhere_dense_primitive_recursive_solver
    (A : Set (Nat → Graph)) (regular : OmegaRegular A)
    (nowhereDense : IsNowhereDense (geometricMap '' A)) :
    ∃ solve : Instance → Bool, Primrec solve ∧ ∀ i, solve i = true ↔ Realizable A i :=
  holes_primitive_recursive_solver A regular
    ((geometricHoles_iff_isNowhereDense A).mpr nowhereDense)

/-- If the geometric image of an adversary lacks holes in some nonempty open
region, no algorithm decides LTL realizability over that adversary. This
direction requires no omega-regularity assumption. -/
theorem no_geometric_holes_undecidable
    (A : Set (Nat → Graph)) (noHoles : ¬ GeometricHoles A) :
    ¬ ComputablePred (Realizable A) :=
  Characterisation.WithInputs.no_geometric_holes_undecidable A noHoles

/-- If an adversary's geometric image is not nowhere dense, LTL realizability
is undecidable. This direction requires no omega-regularity assumption. -/
theorem not_nowhere_dense_undecidable
    (A : Set (Nat → Graph)) (notNowhereDense : ¬ IsNowhereDense (geometricMap '' A)) :
    ¬ ComputablePred (Realizable A) :=
  no_geometric_holes_undecidable A
    (fun holes => notNowhereDense ((geometricHoles_iff_isNowhereDense A).mp holes))

namespace SingletonInputs

/-- The same characterization holds when each process has only one possible
input value. For a fixed omega-regular adversary, synthesis of finite-output
LTL specifications is computable exactly when its geometric image has holes. -/
theorem realizable_computable_iff_geometric_holes
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ GeometricHoles A :=
  Characterisation.realizable_computable_iff_geometric_holes A regular

/-- The nowhere-denseness characterization also holds with singleton inputs. -/
theorem realizable_computable_iff_nowhere_dense
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) :
    ComputablePred (Realizable A) ↔ IsNowhereDense (geometricMap '' A) :=
  (realizable_computable_iff_geometric_holes A regular).trans
    (geometricHoles_iff_isNowhereDense A)

end SingletonInputs
end DistributedSynthesis.GraphAdversaries
