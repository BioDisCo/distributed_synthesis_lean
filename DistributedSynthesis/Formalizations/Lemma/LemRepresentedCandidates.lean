/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemRangeHull

/-!
# Reverse coverage: represented candidates are preserved

The generic discharge of the "spurious hull paths are harmless"
obligation.  The candidate-set handoff internally chooses arbitrary
(possibly spurious hull) representatives; these lemmas show the choice
never introduces a candidate atom lacking a *genuine* iterated model
representative.

* `mem_atomSuccessors_iff_exists_rel_of_representative` (**reverse
  coverage**): for a represented source atom, membership in
  `atomSuccessors` is EQUIVALENT to being the atom of an actual
  relational output of that representative -- the forward direction by
  the chosen-representative pullback equality, the reverse by the
  existing coverage.
* `IterativelyReachable`: the genuine model paths -- initial paths
  closed under substitution outputs.  Every such path lies in the
  regular hull (`rangeHull_of_iterativelyReachable`), which is the
  remaining half of model fact 1 at the abstract level.
* `setHandoff_preserves_representedCandidates`: if every atom of a
  candidate set has an iteratively reachable representative, so does
  every atom of its handoff (for any relation whose outputs of genuine
  paths are genuine -- e.g. `reachRel`, whose outputs are substitution
  outputs).

Consequence for the witness semantics: along handoffs from represented
candidate sets, every candidate atom carries a genuine representative,
so an `EntryRestartExchange` failure surfacing through the certificate
is automatically located on a represented candidate -- the guarded
negative witness -- while failures on merely spurious hull
representatives cannot influence any represented candidate set.
-/

namespace DistributedSynthesis

universe u v w x y z r s

/-! ### Reverse coverage at one atom -/

section ReverseCoverage

variable {EdgeType : Proc -> Type u}
  (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)

variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
variable [∀ d, Fintype (EdgeType d)]

variable (rel : SummaryWindowReversalRel S radius
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/-- **Reverse coverage**: for a represented source atom, membership in
the saturated successor set is exactly being the atom of an actual
relational output of that representative. -/
theorem mem_atomSuccessors_iff_exists_rel_of_representative
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d}
    {old : TypedPath (EdgeType d)}
    {atom' : SummaryWindowAtom S radius d.other} :
    atom' ∈ atomSuccessors S radius rel tuple
        (SummaryWindowAtom.ofPath S radius d old) ↔
      ∃ out ∈ rel d
          (setTupleAt S radius tuple (SummaryWindowAtom.ofPath S radius d old))
          old,
        SummaryWindowAtom.ofPath S radius d.other out = atom' := by
  unfold atomSuccessors
  have hex : ∃ p : TypedPath (EdgeType d),
      SummaryWindowAtom.ofPath S radius d p =
        SummaryWindowAtom.ofPath S radius d old := ⟨old, rfl⟩
  rw [dif_pos hex,
    summaryWindowRelAtomImageFinset_eq_of_atom_eq S radius rel hpullback
      hradius (tuple := setTupleAt S radius tuple
        (SummaryWindowAtom.ofPath S radius d old)) hex.choose_spec,
    mem_summaryWindowRelAtomImageFinset]
  exact Set.mem_image _ _ _

end ReverseCoverage

/-! ### Genuine paths and represented candidate sets -/

section Represented

variable {EdgeType : Proc -> Type u} {Label : Type r}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type r}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (Init : (d : Proc) -> TypedPath (EdgeType d) -> Prop)

/-- The genuine model paths: initial paths, closed under substitution
outputs. -/
inductive IterativelyReachable : (d : Proc) -> TypedPath (EdgeType d) -> Prop
  | initial {d : Proc} {path : TypedPath (EdgeType d)} :
      Init d path -> IterativelyReachable d path
  | step {d : Proc} {old : TypedPath (EdgeType d)} {param : Param d}
      {out : TypedPath (EdgeType (d.other))} :
      IterativelyReachable d old ->
      out ∈ (schemeAt d param).SuccessorWords old ->
      IterativelyReachable d.other out

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → Fintype (EdgeType d)]
    [(d : Proc) → DecidableEq (EdgeType d)] [(d : Proc) → Fintype (Param d)]
    [(d : Proc) → DecidableEq (Param d)] in
/-- Every genuine path lies in the regular hull: the abstract half of
model fact 1. -/
theorem rangeHull_of_iterativelyReachable {d : Proc}
    {path : TypedPath (EdgeType d)}
    (h : IterativelyReachable schemeAt Init d path) :
    RangeHull schemeAt Init d path := by
  cases h with
  | initial h => exact mem_rangeHull_of_init schemeAt Init h
  | step hold hout => exact mem_rangeHull_of_successorWords schemeAt Init hout

variable (S : (d : Proc) -> PathSummarySemigroup.{u, v} (EdgeType d))
  (radius : Nat)
variable {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
variable (rel : SummaryWindowReversalRel S radius
  (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))

/-- A candidate set is represented if every atom in it is the atom of
some genuine path. -/
def RepresentedCandidates {d : Proc}
    (candidates : SummaryWindowAtomSet S radius d) : Prop :=
  ∀ atom ∈ candidates, ∃ path : TypedPath (EdgeType d),
    IterativelyReachable schemeAt Init d path ∧
      SummaryWindowAtom.ofPath S radius d path = atom

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → DecidableEq (EdgeType d)]
    [(d : Proc) → Fintype (Param d)] [(d : Proc) → DecidableEq (Param d)] in
/-- **Handoffs preserve represented candidates**: for any relation
whose outputs of genuine paths are genuine, the handoff of a
represented candidate set is represented.  The internally chosen
spurious hull representatives never introduce an atom without a
genuine iterated representative. -/
theorem setHandoff_preserves_representedCandidates
    (hpullback : ∀ d tuple,
      SummaryWindowRelSetPullbackBoundAt radius (S d) (S d.other)
        (rel d tuple))
    (hradius : endpointPullbackBound radius ≤ radius)
    (hrelStep : ∀ (d : Proc)
      (tuple : DirectReversalTuple (SummaryWindowAtom S radius)
        In₁ In₂ Out₁ Out₂ d)
      (old : TypedPath (EdgeType d)) (out : TypedPath (EdgeType (d.other))),
      IterativelyReachable schemeAt Init d old ->
      out ∈ rel d tuple old ->
      IterativelyReachable schemeAt Init d.other out)
    {d : Proc}
    {tuple : DirectReversalTuple (SummaryWindowAtomSet S radius)
      In₁ In₂ Out₁ Out₂ d}
    (hrep : RepresentedCandidates schemeAt Init S radius tuple.atom) :
    RepresentedCandidates schemeAt Init S radius
      (setHandoff S radius rel tuple) := by
  intro atom' hatom'
  classical
  simp only [setHandoff, Finset.mem_biUnion] at hatom'
  obtain ⟨atom, hatom, hsucc⟩ := hatom'
  obtain ⟨path, hreach, hofPath⟩ := hrep atom hatom
  rw [<- hofPath] at hsucc
  obtain ⟨out, hout, hout'⟩ :=
    (mem_atomSuccessors_iff_exists_rel_of_representative S radius rel
      hpullback hradius).mp hsucc
  exact ⟨out, hrelStep d _ path out hreach hout, hout'⟩

/-- The `hrelStep` discharge for the relativized relation: `reachRel`
outputs of genuine paths are genuine, since they are substitution
outputs. -/
theorem reachRel_step_iterativelyReachable
    (Reach : (d : Proc) -> TypedPath (EdgeType d) -> Prop)
    (base : (d : Proc) -> PathSummarySemigroup.{u, max u r} (EdgeType d))
    (radiusR : Nat)
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d)
    (d : Proc)
    (tuple : DirectReversalTuple
      (SummaryWindowAtom (saturationLevel schemeAt base radiusR 1) radiusR)
      In₁ In₂ Out₁ Out₂ d)
    (old : TypedPath (EdgeType d)) (out : TypedPath (EdgeType (d.other)))
    (hreach : IterativelyReachable schemeAt Init d old)
    (hmem : out ∈ reachRel Reach schemeAt base radiusR paramOf d tuple old) :
    IterativelyReachable schemeAt Init d.other out :=
  IterativelyReachable.step hreach hmem.2

end Represented

end DistributedSynthesis
