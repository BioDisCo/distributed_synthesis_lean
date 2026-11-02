/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefEpochAbstractions
import Mathlib.Data.Fintype.Pi

/-!
# Regular-test basis to finite repair

This file packages `prop:regulartestbasistorepair`: a finite regular-test basis
induces a finite truth-vector quotient of typed paths, and its stated closure
fields provide the four semantic repair clauses used by the paper.
-/

namespace DistributedSynthesis

open Classical

universe u v w

/-- The finite atom of a path induced by the truth values of all basis tests. -/
abbrev RegularTestTruthAtom
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType) :=
  basis.test -> Bool

/-- The basis-test truth vector of a typed path. -/
noncomputable def regularTestTruthVector
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path : TypedPath EdgeType) :
    RegularTestTruthAtom basis :=
  fun test => decide (path ∈ basis.language test)

/-- A finite regular-test basis has only finitely many truth atoms. -/
@[reducible] noncomputable def regularTestTruthAtomFintype
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) :
    Fintype (RegularTestTruthAtom basis) := by
  letI := basis.testFinite
  letI : DecidableEq basis.test := Classical.decEq _
  infer_instance

/-- A finite quotient of typed paths induced by a finite regular-test basis. -/
structure FiniteRegularTestTruthQuotient
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) where
  Atom : Type w
  atomFinite : Fintype Atom
  encode : TypedPath EdgeType -> Atom

attribute [instance] FiniteRegularTestTruthQuotient.atomFinite

/-- The four repair clauses required by Proposition `prop:finitecongruencerepair`. -/
structure RegularTestBasisRepairClauses
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) where
  quotient : FiniteRegularTestTruthQuotient basis
  determinesPathData : basis.determinesPathData
  privateInputUpdateClosed : basis.predecessorClosed
  closingMapWellDefined : ∀ boundaryState, basis.boundaryClosed boundaryState
  rightCongruenceForContinuations : basis.continuationClosed

/--
Pointwise path equivalence induced by a finite regular-test basis: two paths
satisfy exactly the same basis tests.
-/
def RegularTestBasisPathEquivalent
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path path' : TypedPath EdgeType) : Prop :=
  ∀ test, (path ∈ basis.language test ↔ path' ∈ basis.language test)

/-- Regular-test basis path equivalence is reflexive. -/
theorem RegularTestBasisPathEquivalent.refl
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path : TypedPath EdgeType) :
    RegularTestBasisPathEquivalent basis path path := by
  intro test
  rfl

/-- Regular-test basis path equivalence is symmetric. -/
theorem RegularTestBasisPathEquivalent.symm
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq : RegularTestBasisPathEquivalent basis path path') :
    RegularTestBasisPathEquivalent basis path' path := by
  intro test
  exact (heq test).symm

/-- Regular-test basis path equivalence is transitive. -/
theorem RegularTestBasisPathEquivalent.trans
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path₁ path₂ path₃ : TypedPath EdgeType}
    (hleft : RegularTestBasisPathEquivalent basis path₁ path₂)
    (hright : RegularTestBasisPathEquivalent basis path₂ path₃) :
    RegularTestBasisPathEquivalent basis path₁ path₃ := by
  intro test
  exact (hleft test).trans (hright test)

/--
The truth-vector quotient is exactly equality of all basis-test outcomes.
This is the finite quotient used in `prop:regulartestbasistorepair`.
-/
theorem regularTestTruthVector_eq_iff
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path path' : TypedPath EdgeType) :
    regularTestTruthVector basis path = regularTestTruthVector basis path' ↔
      RegularTestBasisPathEquivalent basis path path' := by
  constructor
  · intro h test
    have htest := congrFun h test
    by_cases hpath : path ∈ basis.language test
    · by_cases hpath' : path' ∈ basis.language test
      · exact ⟨fun _ => hpath', fun _ => hpath⟩
      · simp [regularTestTruthVector, hpath, hpath'] at htest
    · by_cases hpath' : path' ∈ basis.language test
      · simp [regularTestTruthVector, hpath, hpath'] at htest
      · exact ⟨fun h => False.elim (hpath h), fun h => False.elim (hpath' h)⟩
  · intro h
    funext test
    specialize h test
    by_cases hpath : path ∈ basis.language test
    · have hpath' : path' ∈ basis.language test := h.1 hpath
      simp [regularTestTruthVector, hpath, hpath']
    · have hpath' : ¬ path' ∈ basis.language test := by
        intro hpath'
        exact hpath (h.2 hpath')
      simp [regularTestTruthVector, hpath, hpath']

/-- Convert regular-test basis path equivalence to truth-vector equality. -/
theorem regularTestTruthVector_eq_of_pathEquivalent
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq : RegularTestBasisPathEquivalent basis path path') :
    regularTestTruthVector basis path = regularTestTruthVector basis path' :=
  (regularTestTruthVector_eq_iff basis path path').mpr heq

/-- Convert truth-vector equality to regular-test basis path equivalence. -/
theorem regularTestBasisPathEquivalent_of_truthVector_eq
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq : regularTestTruthVector basis path = regularTestTruthVector basis path') :
    RegularTestBasisPathEquivalent basis path path' :=
  (regularTestTruthVector_eq_iff basis path path').mp heq

/--
Proposition `prop:regulartestbasistorepair`, finite-index core: a finite
regular-test basis produces a finite quotient of typed paths by basis-test
truth values.
-/
theorem regular_test_basis_to_finite_truth_quotient
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) :
    Nonempty (FiniteRegularTestTruthQuotient basis) := by
  refine ⟨{
    Atom := RegularTestTruthAtom basis
    atomFinite := regularTestTruthAtomFintype basis
    encode := regularTestTruthVector basis
  }⟩

/--
Canonical repair clauses obtained from the truth-vector quotient of a finite
regular-test basis.

Use this named object when later proofs need to rewrite the repair atom back to
`regularTestTruthVector` rather than destructing the `Nonempty` proof below.
-/
noncomputable def regularTestBasisRepairClausesOfTruthVector
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) :
    RegularTestBasisRepairClauses basis where
  quotient := {
    Atom := RegularTestTruthAtom basis
    atomFinite := regularTestTruthAtomFintype basis
    encode := regularTestTruthVector basis
  }
  determinesPathData := basis.determinesPathData_proof
  privateInputUpdateClosed := basis.predecessorClosed_proof
  closingMapWellDefined := basis.boundaryClosed_proof
  rightCongruenceForContinuations := basis.continuationClosed_proof

/-- The canonical repair quotient encodes paths by their truth vector. -/
@[simp] theorem regularTestBasisRepairClausesOfTruthVector_encode
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType)
    (path : TypedPath EdgeType) :
    (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
      regularTestTruthVector basis path :=
  rfl

/--
For the canonical repair quotient, equality of repair atoms is exactly equality
of all basis-test outcomes.
-/
theorem regularTestBasisRepairClausesOfTruthVector_encode_eq_iff
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path path' : TypedPath EdgeType) :
    (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
        (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path' ↔
      RegularTestBasisPathEquivalent basis path path' := by
  exact regularTestTruthVector_eq_iff basis path path'

/-- Convert regular-test basis path equivalence to canonical repair-atom equality. -/
theorem regularTestBasisRepairClausesOfTruthVector_repairAtom_eq_of_pathEquivalent
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq : RegularTestBasisPathEquivalent basis path path') :
    (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
      (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path' :=
  (regularTestBasisRepairClausesOfTruthVector_encode_eq_iff basis path path').mpr heq

/-- Convert canonical repair-atom equality to regular-test basis path equivalence. -/
theorem regularTestBasisPathEquivalent_of_repairAtom_eq
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq :
      (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
        (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path') :
    RegularTestBasisPathEquivalent basis path path' :=
  (regularTestBasisRepairClausesOfTruthVector_encode_eq_iff basis path path').mp heq

/--
For the canonical repair quotient, truth-vector equality is exactly repair-atom
equality.
-/
theorem regularTestBasisRepairClausesOfTruthVector_truthVector_eq_iff
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis boundary EdgeType)
    (path path' : TypedPath EdgeType) :
    regularTestTruthVector basis path = regularTestTruthVector basis path' ↔
      (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
        (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path' := by
  rfl

/-- Convert canonical truth-vector equality to repair-atom equality. -/
theorem regularTestBasisRepairClausesOfTruthVector_repairAtom_eq_of_truthVector_eq
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq : regularTestTruthVector basis path = regularTestTruthVector basis path') :
    (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
      (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path' :=
  (regularTestBasisRepairClausesOfTruthVector_truthVector_eq_iff basis path path').mp heq

/-- Convert canonical repair-atom equality to truth-vector equality. -/
theorem regularTestBasisRepairClausesOfTruthVector_truthVector_eq_of_repairAtom_eq
    {boundary : Type u} {EdgeType : Type v}
    {basis : FiniteRegularTestBasis boundary EdgeType}
    {path path' : TypedPath EdgeType}
    (heq :
      (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path =
        (regularTestBasisRepairClausesOfTruthVector basis).quotient.encode path') :
    regularTestTruthVector basis path = regularTestTruthVector basis path' :=
  (regularTestBasisRepairClausesOfTruthVector_truthVector_eq_iff basis path path').mpr heq

/--
Proposition `prop:regulartestbasistorepair`: a finite regular-test basis produces
the finite truth-vector quotient and carries the four repair clauses needed by
the finite-congruence target.
-/
theorem regular_test_basis_implies_repair_clauses
    {boundary : Type u} {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} boundary EdgeType) :
    Nonempty (RegularTestBasisRepairClauses basis) := by
  exact ⟨regularTestBasisRepairClausesOfTruthVector basis⟩

end DistributedSynthesis
