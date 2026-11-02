/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmRegulartestdecidability

/-!
# Saturation termination gives a finite regular-test basis

This file packages `prop:saturationbasis`: if a regular-test saturation stage
is stable and boundary-complete, then the stage tests form a finite regular-test
basis, and the regular-test decision theorem applies.
-/

namespace DistributedSynthesis

universe u v w x y z q

/-- Boundary-completeness and closure evidence for a stabilized saturation stage. -/
structure StabilizedSaturationBasisCertificate
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    (sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂)
    (n : Nat) where
  stable : sat.StableAt n
  determinesPathData : Prop
  predecessorClosed : Prop
  boundaryClosed : Boundary -> Prop
  continuationClosed : Prop
  determinesPathData_proof : determinesPathData
  predecessorClosed_proof : predecessorClosed
  boundaryClosed_proof : ∀ boundaryState, boundaryClosed boundaryState
  continuationClosed_proof : continuationClosed

/-- The stabilized stage of a saturation sequence, viewed as a finite regular-test basis. -/
def stabilizedSaturationBasis
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    FiniteRegularTestBasis.{w, v, max u v w x y z} Boundary EdgeType where
  test := sat.stageTest n
  testFinite := sat.stageFinite n
  language := sat.stageLanguage n
  determinesPathData := cert.determinesPathData
  predecessorClosed := cert.predecessorClosed
  boundaryClosed := cert.boundaryClosed
  continuationClosed := cert.continuationClosed
  determinesPathData_proof := cert.determinesPathData_proof
  predecessorClosed_proof := cert.predecessorClosed_proof
  boundaryClosed_proof := cert.boundaryClosed_proof
  continuationClosed_proof := cert.continuationClosed_proof

/--
The stabilized basis carries the path-data proof supplied by the saturation
certificate.
-/
theorem stabilizedSaturationBasis_determinesPathData
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    (stabilizedSaturationBasis cert).determinesPathData :=
  cert.determinesPathData_proof

/--
The stabilized basis carries the predecessor-closure proof supplied by the
saturation certificate.
-/
theorem stabilizedSaturationBasis_predecessorClosed
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    (stabilizedSaturationBasis cert).predecessorClosed :=
  cert.predecessorClosed_proof

/--
The stabilized basis carries each boundary-closure proof supplied by the
saturation certificate.
-/
theorem stabilizedSaturationBasis_boundaryClosed
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (boundaryState : Boundary) :
    (stabilizedSaturationBasis cert).boundaryClosed boundaryState :=
  cert.boundaryClosed_proof boundaryState

/--
The stabilized basis carries the continuation-closure proof supplied by the
saturation certificate.
-/
theorem stabilizedSaturationBasis_continuationClosed
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    (stabilizedSaturationBasis cert).continuationClosed :=
  cert.continuationClosed_proof

/--
Canonical repair clauses for the stabilized saturation basis.

This keeps the finite-congruence repair handoff tied to the truth-vector
quotient of the stabilized basis, rather than to an anonymous `Nonempty`
witness.
-/
noncomputable def stabilizedSaturationBasisRepairClauses
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    RegularTestBasisRepairClauses (stabilizedSaturationBasis cert) :=
  regularTestBasisRepairClausesOfTruthVector (stabilizedSaturationBasis cert)

/-- The stabilized canonical repair quotient encodes paths by truth vectors. -/
@[simp] theorem stabilizedSaturationBasisRepairClauses_encode
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path : TypedPath EdgeType) :
    (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
      regularTestTruthVector (stabilizedSaturationBasis cert) path :=
  rfl

/--
For the stabilized basis, equality of truth-vector atoms is exactly equality
of all stabilized basis-test outcomes.
-/
theorem stabilizedSaturationBasisTruthVector_eq_iff
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    regularTestTruthVector (stabilizedSaturationBasis cert) path =
        regularTestTruthVector (stabilizedSaturationBasis cert) path' ↔
      ∀ test,
        (path ∈ (stabilizedSaturationBasis cert).language test ↔
          path' ∈ (stabilizedSaturationBasis cert).language test) := by
  exact regularTestTruthVector_eq_iff (stabilizedSaturationBasis cert) path path'

/--
For the stabilized canonical repair quotient, equality of repair atoms is
exactly equality of all stabilized basis-test outcomes.
-/
theorem stabilizedSaturationBasisRepairClauses_encode_eq_iff
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
        (stabilizedSaturationBasisRepairClauses cert).quotient.encode path' ↔
      ∀ test,
        (path ∈ (stabilizedSaturationBasis cert).language test ↔
          path' ∈ (stabilizedSaturationBasis cert).language test) := by
  exact
    regularTestBasisRepairClausesOfTruthVector_encode_eq_iff
      (stabilizedSaturationBasis cert) path path'

/--
Path equivalence induced by the stabilized saturation basis: two paths satisfy
exactly the same stabilized basis tests.
-/
def StabilizedSaturationBasisPathEquivalent
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) : Prop :=
  ∀ test,
    (path ∈ (stabilizedSaturationBasis cert).language test ↔
      path' ∈ (stabilizedSaturationBasis cert).language test)

/-- Stabilized basis path equivalence is reflexive. -/
theorem StabilizedSaturationBasisPathEquivalent.refl
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path : TypedPath EdgeType) :
    StabilizedSaturationBasisPathEquivalent cert path path := by
  intro test
  rfl

/-- Stabilized basis path equivalence is symmetric. -/
theorem StabilizedSaturationBasisPathEquivalent.symm
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq : StabilizedSaturationBasisPathEquivalent cert path path') :
    StabilizedSaturationBasisPathEquivalent cert path' path := by
  intro test
  exact (heq test).symm

/-- Stabilized basis path equivalence is transitive. -/
theorem StabilizedSaturationBasisPathEquivalent.trans
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path₁ path₂ path₃ : TypedPath EdgeType}
    (hleft : StabilizedSaturationBasisPathEquivalent cert path₁ path₂)
    (hright : StabilizedSaturationBasisPathEquivalent cert path₂ path₃) :
    StabilizedSaturationBasisPathEquivalent cert path₁ path₃ := by
  intro test
  exact (hleft test).trans (hright test)

/--
The stabilized path-equivalence predicate is the generic regular-test basis
path equivalence for `stabilizedSaturationBasis cert`.
-/
theorem stabilizedSaturationBasisPathEquivalent_iff_regularTestBasisPathEquivalent
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    StabilizedSaturationBasisPathEquivalent cert path path' ↔
      RegularTestBasisPathEquivalent (stabilizedSaturationBasis cert) path path' := by
  rfl

/--
The stabilized basis path-equivalence predicate is exactly equality of
truth-vector atoms.
-/
theorem stabilizedSaturationBasisPathEquivalent_iff_truthVector_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    StabilizedSaturationBasisPathEquivalent cert path path' ↔
      regularTestTruthVector (stabilizedSaturationBasis cert) path =
        regularTestTruthVector (stabilizedSaturationBasis cert) path' := by
  exact (stabilizedSaturationBasisTruthVector_eq_iff cert path path').symm

/-- Convert stabilized same-tests equivalence to truth-vector equality. -/
theorem stabilizedSaturationBasis_truthVector_eq_of_pathEquivalent
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq : StabilizedSaturationBasisPathEquivalent cert path path') :
    regularTestTruthVector (stabilizedSaturationBasis cert) path =
      regularTestTruthVector (stabilizedSaturationBasis cert) path' :=
  (stabilizedSaturationBasisPathEquivalent_iff_truthVector_eq cert path path').mp heq

/--
If typed-path length factors through the stabilized truth-vector atom, then
stabilized path equivalence preserves typed-path length.
-/
theorem stabilizedSaturationBasis_pathLength_eq_of_truthVector_factor
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    (pathLengthOfTruth :
      RegularTestTruthAtom (stabilizedSaturationBasis cert) -> Nat)
    (pathLength_factor :
      ∀ path : TypedPath EdgeType,
        path.length =
          pathLengthOfTruth
            (regularTestTruthVector (stabilizedSaturationBasis cert) path))
    {path path' : TypedPath EdgeType}
    (heq : StabilizedSaturationBasisPathEquivalent cert path path') :
    path.length = path'.length := by
  have htruth :=
    stabilizedSaturationBasis_truthVector_eq_of_pathEquivalent heq
  calc
    path.length =
        pathLengthOfTruth
          (regularTestTruthVector (stabilizedSaturationBasis cert) path) := by
          exact pathLength_factor path
    _ =
        pathLengthOfTruth
          (regularTestTruthVector (stabilizedSaturationBasis cert) path') := by
          exact congrArg pathLengthOfTruth htruth
    _ = path'.length := by
          exact (pathLength_factor path').symm

/--
A finite truth-vector atom cannot globally determine the length of every typed
path as soon as the edge alphabet is inhabited.  Any length decoder used in an
unbounded path argument therefore has to be local to a generated or bounded path
family, or has to use a richer quotient than the finite truth atom.
-/
theorem regularTestTruthVector_no_global_pathLength_factor
    {Boundary : Type u}
    {EdgeType : Type v}
    (basis : FiniteRegularTestBasis.{u, v, w} Boundary EdgeType)
    [Inhabited EdgeType]
    (pathLengthOfTruth : RegularTestTruthAtom basis -> Nat)
    (pathLength_factor :
      ∀ path : TypedPath EdgeType,
        path.length =
          pathLengthOfTruth (regularTestTruthVector basis path)) :
    False := by
  classical
  letI := regularTestTruthAtomFintype basis
  let edge : EdgeType := default
  let encode :
      Fin (Fintype.card (RegularTestTruthAtom basis) + 1) ->
        RegularTestTruthAtom basis :=
    fun i => regularTestTruthVector basis (List.replicate i.val edge)
  have hInjective : Function.Injective encode := by
    intro i j hij
    have hi := pathLength_factor (List.replicate i.val edge)
    have hj := pathLength_factor (List.replicate j.val edge)
    have hlen :
        (List.replicate i.val edge).length =
          (List.replicate j.val edge).length := by
      calc
        (List.replicate i.val edge).length =
            pathLengthOfTruth
              (regularTestTruthVector basis (List.replicate i.val edge)) := by
          exact hi
        _ =
            pathLengthOfTruth
              (regularTestTruthVector basis (List.replicate j.val edge)) := by
          simpa [encode] using congrArg pathLengthOfTruth hij
        _ = (List.replicate j.val edge).length := by
          exact hj.symm
    exact Fin.ext (by simpa using hlen)
  have hcard :
      Fintype.card (Fin (Fintype.card (RegularTestTruthAtom basis) + 1)) ≤
        Fintype.card (RegularTestTruthAtom basis) :=
    Fintype.card_le_of_injective encode hInjective
  have hbad :
      Fintype.card (RegularTestTruthAtom basis) + 1 ≤
        Fintype.card (RegularTestTruthAtom basis) := by
    simpa using hcard
  exact Nat.not_succ_le_self _ hbad

/--
Specialized impossibility result for stabilized saturation bases: the finite
stabilized truth atom cannot determine all typed-path lengths globally on an
inhabited edge alphabet.
-/
theorem stabilizedSaturationBasis_no_global_pathLength_factor
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    [Inhabited EdgeType]
    (pathLengthOfTruth :
      RegularTestTruthAtom (stabilizedSaturationBasis cert) -> Nat)
    (pathLength_factor :
      ∀ path : TypedPath EdgeType,
        path.length =
          pathLengthOfTruth
            (regularTestTruthVector (stabilizedSaturationBasis cert) path)) :
    False :=
  regularTestTruthVector_no_global_pathLength_factor
    (stabilizedSaturationBasis cert) pathLengthOfTruth pathLength_factor

/-- Convert truth-vector equality to stabilized same-tests equivalence. -/
theorem stabilizedSaturationBasis_pathEquivalent_of_truthVector_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq :
      regularTestTruthVector (stabilizedSaturationBasis cert) path =
        regularTestTruthVector (stabilizedSaturationBasis cert) path') :
    StabilizedSaturationBasisPathEquivalent cert path path' :=
  (stabilizedSaturationBasisPathEquivalent_iff_truthVector_eq cert path path').mpr heq

/--
The stabilized basis path-equivalence predicate is exactly equality of
canonical repair atoms.
-/
theorem stabilizedSaturationBasisPathEquivalent_iff_repairAtom_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    StabilizedSaturationBasisPathEquivalent cert path path' ↔
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path' := by
  exact (stabilizedSaturationBasisRepairClauses_encode_eq_iff cert path path').symm

/-- Convert stabilized same-tests equivalence to canonical repair-atom equality. -/
theorem stabilizedSaturationBasis_repairAtom_eq_of_pathEquivalent
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq : StabilizedSaturationBasisPathEquivalent cert path path') :
    (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path' :=
  (stabilizedSaturationBasisPathEquivalent_iff_repairAtom_eq cert path path').mp heq

/-- Convert canonical repair-atom equality to stabilized same-tests equivalence. -/
theorem stabilizedSaturationBasis_pathEquivalent_of_repairAtom_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq :
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
        (stabilizedSaturationBasisRepairClauses cert).quotient.encode path') :
    StabilizedSaturationBasisPathEquivalent cert path path' :=
  (stabilizedSaturationBasisPathEquivalent_iff_repairAtom_eq cert path path').mpr heq

/--
For the stabilized canonical repair quotient, truth-vector equality is exactly
repair-atom equality.
-/
theorem stabilizedSaturationBasis_truthVector_eq_iff_repairAtom_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n)
    (path path' : TypedPath EdgeType) :
    regularTestTruthVector (stabilizedSaturationBasis cert) path =
        regularTestTruthVector (stabilizedSaturationBasis cert) path' ↔
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
        (stabilizedSaturationBasisRepairClauses cert).quotient.encode path' := by
  exact
    regularTestBasisRepairClausesOfTruthVector_truthVector_eq_iff
      (stabilizedSaturationBasis cert) path path'

/-- Convert stabilized truth-vector equality to canonical repair-atom equality. -/
theorem stabilizedSaturationBasis_repairAtom_eq_of_truthVector_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq :
      regularTestTruthVector (stabilizedSaturationBasis cert) path =
        regularTestTruthVector (stabilizedSaturationBasis cert) path') :
    (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path' :=
  (stabilizedSaturationBasis_truthVector_eq_iff_repairAtom_eq cert path path').mp heq

/-- Convert stabilized canonical repair-atom equality to truth-vector equality. -/
theorem stabilizedSaturationBasis_truthVector_eq_of_repairAtom_eq
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    {cert : StabilizedSaturationBasisCertificate sat n}
    {path path' : TypedPath EdgeType}
    (heq :
      (stabilizedSaturationBasisRepairClauses cert).quotient.encode path =
        (stabilizedSaturationBasisRepairClauses cert).quotient.encode path') :
    regularTestTruthVector (stabilizedSaturationBasis cert) path =
      regularTestTruthVector (stabilizedSaturationBasis cert) path' :=
  (stabilizedSaturationBasis_truthVector_eq_iff_repairAtom_eq cert path path').mpr heq

/-- Proposition `prop:saturationbasis`: a stable boundary-complete saturation stage yields a basis. -/
theorem saturation_stabilization_gives_test_basis
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    sat.StableAt n ∧
      Nonempty (FiniteRegularTestBasis.{w, v, max u v w x y z} Boundary EdgeType) := by
  exact ⟨cert.stable, ⟨stabilizedSaturationBasis cert⟩⟩

/--
Stabilized saturation also supplies the canonical finite repair clauses for
the stabilized basis.
-/
theorem saturation_stabilization_gives_canonical_repair_clauses
    {Alphabet : Type u} {EdgeType : Type v} {Boundary : Type w}
    {In₁ : Type x} {In₂ : Type y}
    {sat : RegularTestSaturation.{u, v, w, x, y, z} Alphabet EdgeType Boundary In₁ In₂}
    {n : Nat}
    (cert : StabilizedSaturationBasisCertificate sat n) :
    sat.StableAt n ∧
      Nonempty (RegularTestBasisRepairClauses (stabilizedSaturationBasis cert)) := by
  exact ⟨cert.stable, ⟨stabilizedSaturationBasisRepairClauses cert⟩⟩

/--
Decision wrapper for the stabilized-basis route: once the two stabilized bases
are packaged in a regular-test route certificate, decidability follows from
`thm:regulartestdecidability`.
-/
theorem saturation_basis_route_to_decidability
    {Automaton : Type q} {Realizable : Prop}
    (cert : RegularTestRouteDecisionCertificate Automaton Realizable) :
    Nonempty (Decidable Realizable) := by
  exact regular_test_route_decidable_nonempty cert

/--
Named decision extractor for the stabilized-basis route.
-/
noncomputable def saturation_basis_route_decidable
    {Automaton : Type q} {Realizable : Prop}
    (cert : RegularTestRouteDecisionCertificate Automaton Realizable) :
    Decidable Realizable :=
  regular_test_route_decidable cert

end DistributedSynthesis
