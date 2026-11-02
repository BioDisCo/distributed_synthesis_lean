/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSummaryWindowRelationalClosure
import DistributedSynthesis.Formalizations.Proposition.PropJournalatomsreversalclosure

/-!
# Candidate-set reversal closure

Step 4 of the set route: carry the saturated candidate set through the
reversal-closure certificate.

Refined atoms become finite *sets* of summary-window atoms
(`SummaryWindowAtomSet`); a path's own refined atom is the singleton of
its window atom, so refinement of the base atoms is inherited pointwise.
At a direct reversal the handoff maps a candidate set to the union of the
saturated successor images of its members (`setHandoff`), which is
well-defined by the set-level pullback bound and *functional by
construction* -- determinism is free at the set granularity, which is the
entire point of simultaneous saturation.  Coverage
(`setHandoff_covers`) states that the real continuation's atom always
lies in the carried candidate set: if the old path's atom is a carried
candidate and the continuation is any relational output, its atom is in
the handoff of the set.

`summaryWindowSetClosureCertificate` packages all of this as a
`JournalAtomsReversalClosureCertificate` whose `Prop` fields are the
actual proved statements (window compatibility of the base atoms and the
set-level simultaneous saturation), with no unnamed certificate fields.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

section SetClosure

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
variable [∀ d, Fintype (EdgeType d)]

/-- Candidate-set atoms: finite sets of refined summary-window atoms. -/
abbrev SummaryWindowAtomSet (d : Proc) : Type (max u v) :=
  Finset (SummaryWindowAtom S radius d)

/-- The pointwise closing tuple of a candidate atom inside a set tuple. -/
def setTupleAt {d : Proc}
    (tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d)
    (atom : SummaryWindowAtom S radius d) :
    DirectReversalTuple (SummaryWindowAtom S radius) In₁ In₂ Out₁ Out₂ d :=
  ⟨atom, tuple.bits, tuple.letter⟩

variable (rel : SummaryWindowReversalRel S radius
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

open Classical in
/-- The saturated successor image of one candidate atom: the image of any
representative path, empty if the atom is unrealized. -/
noncomputable def atomSuccessors {d : Proc}
    (tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d)
    (atom : SummaryWindowAtom S radius d) :
    Finset (SummaryWindowAtom S radius d.other) :=
  if h : ∃ old : TypedPath (EdgeType d),
      SummaryWindowAtom.ofPath S radius d old = atom then
    summaryWindowRelAtomImageFinset S radius rel d
      (setTupleAt S radius tuple atom) h.choose
  else ∅

/-- Any relational output of a path lands in the successors of the path's
own atom: the representative choice is irrelevant by set-level
saturation. -/
theorem mem_atomSuccessors_of_rel
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)} {out : TypedPath (EdgeType d.other)}
    (hmem : out ∈ rel d
      (setTupleAt S radius tuple (SummaryWindowAtom.ofPath S radius d old))
      old) :
    SummaryWindowAtom.ofPath S radius d.other out ∈
      atomSuccessors S radius rel tuple
        (SummaryWindowAtom.ofPath S radius d old) := by
  unfold atomSuccessors
  have hex : ∃ p : TypedPath (EdgeType d),
      SummaryWindowAtom.ofPath S radius d p =
        SummaryWindowAtom.ofPath S radius d old := ⟨old, rfl⟩
  rw [dif_pos hex,
    summaryWindowRelAtomImageFinset_eq_of_atom_eq S radius rel hpullback
      hradius (tuple := setTupleAt S radius tuple
        (SummaryWindowAtom.ofPath S radius d old)) hex.choose_spec,
    mem_summaryWindowRelAtomImageFinset]
  exact mem_summaryWindowRelAtomImage S radius rel hmem

/-- The set-level direct-reversal handoff: the union of the saturated
successor images of the carried candidates. -/
noncomputable def setHandoff {d : Proc}
    (tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d) :
    SummaryWindowAtomSet S radius d.other := by
  classical
  exact tuple.atom.biUnion (atomSuccessors S radius rel tuple)

/-- **Coverage**: the real continuation's atom is covered.  If the old
path's atom is a carried candidate and the continuation is any relational
output at that candidate's closing tuple, then the continuation's atom
lies in the handoff of the candidate set. -/
theorem setHandoff_covers
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)} {out : TypedPath (EdgeType d.other)}
    (hatom : SummaryWindowAtom.ofPath S radius d old ∈ tuple.atom)
    (hmem : out ∈ rel d
      (setTupleAt S radius tuple (SummaryWindowAtom.ofPath S radius d old))
      old) :
    SummaryWindowAtom.ofPath S radius d.other out ∈
      setHandoff S radius rel tuple := by
  classical
  unfold setHandoff
  refine Finset.mem_biUnion.mpr
    ⟨SummaryWindowAtom.ofPath S radius d old, hatom, ?_⟩
  exact mem_atomSuccessors_of_rel S radius rel hpullback hradius hmem

/-- Set-level successor tests: the old path carries one of the tuple's
candidates and the proposed target is the set handoff. -/
noncomputable def setHandoffTests :
    HandoffTests EdgeType (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ where
  successorTest d tuple target :=
    { old |
      SummaryWindowAtom.ofPath S radius d old ∈ tuple.atom ∧
        target = setHandoff S radius rel tuple }

/-- Determinism is free at the set granularity: the only successful
target is the set handoff itself. -/
theorem setHandoffTests_unique :
    AtMostOneHandoffSuccessor (setHandoffTests S radius rel) := by
  rintro d tuple target₁ target₂ ⟨old₁, _, htarget₁⟩ ⟨old₂, _, htarget₂⟩
  exact htarget₁.trans htarget₂.symm

/-- The set-level finite handoff. -/
noncomputable def setFiniteHandoff :
    FiniteDirectReversalHandoff (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ :=
  finiteDirectReversalHandoffOf (setHandoffTests S radius rel)
    (fun _ tuple => setHandoff S radius rel tuple)

/-- The set-level handoff satisfies its semantic invariant. -/
theorem setFiniteHandoff_invariant :
    (setFiniteHandoff S radius rel).invariant := by
  refine handoff_exclusion_check_implies_invariant
    (setHandoffTests S radius rel)
    (fun _ tuple => setHandoff S radius rel tuple) ?_
  rintro d tuple target hne old ⟨_, htarget⟩
  exact hne htarget

/-- The set-level functional closing extension. -/
noncomputable def setDirectClosing :
    FunctionalDirectClosingExtension EdgeType (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ :=
  functionalDirectClosingFromSuccessors (setHandoffTests S radius rel)

theorem setDirectClosing_functional :
    (setDirectClosing S radius rel).functionalOnReachable :=
  setHandoffTests_unique S radius rel

/--
**The candidate-set reversal-closure certificate.**  Refined atoms are
finite candidate sets of summary-window atoms; a path's refined atom is
the singleton of its window atom; the handoff is the saturated union.
Both semantic `Prop` fields carry the actual proved statements: the
window compatibility of the base atoms and set-level simultaneous
saturation.
-/
noncomputable def summaryWindowSetClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible (S d) radius (baseAtomOf d))
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate EdgeType BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation where
  RefinedAtom := SummaryWindowAtomSet S radius
  refinedFinite d := by
    classical
    infer_instance
  baseAtomOf := baseAtomOf
  refinedAtomOf d path := {SummaryWindowAtom.ofPath S radius d path}
  continuationOf := continuationOf
  baseSound := baseSound
  refinedRefinesBase d old new h :=
    compatible d old new
      (SummaryWindowAtom.raw_eq_of_eq S radius (Finset.singleton_inj.mp h))
  refinedRegular d :=
    Nonempty (Fintype (SummaryWindowAtomSet S radius d))
  enrichedSummaryWindowCompatible :=
    ∀ d, SummaryWindowCompatible (S d) radius (baseAtomOf d)
  simultaneousClosureStabilizes :=
    ∀ (d : Proc)
      (tuple : DirectReversalTuple (SummaryWindowAtom S radius)
        In₁ In₂ Out₁ Out₂ d)
      (old new : TypedPath (EdgeType d)),
      SummaryWindowAtom.ofPath S radius d old =
          SummaryWindowAtom.ofPath S radius d new ->
        summaryWindowRelAtomImageFinset S radius rel d tuple old =
          summaryWindowRelAtomImageFinset S radius rel d tuple new
  directClosing := setDirectClosing S radius rel
  finiteHandoff := setFiniteHandoff S radius rel
  refinedRegular_proof d := ⟨by
    classical
    infer_instance⟩
  enrichedSummaryWindowCompatible_proof := compatible
  simultaneousClosureStabilizes_proof := fun d tuple old new hatom =>
    summaryWindowRelAtomImageFinset_eq_of_atom_eq S radius rel hpullback
      hradius (tuple := tuple) hatom

end SetClosure

end DistributedSynthesis
