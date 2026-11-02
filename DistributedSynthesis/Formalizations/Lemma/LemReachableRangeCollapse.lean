/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemRangeDetermination

/-!
# The reachability-relative collapse and the restart exchange

`RangeDetermination` quantified over arbitrary typed paths, but the
model's entry-restart argument only speaks about reachable,
strategy-generated histories.  This file makes the whole positive route
reachability-relative, parameterized by an abstract predicate family
`Reach`:

* **The model input** is `EntryRestartExchange`: equal base window
  codes of two substituted words of *reachable* paths induce a
  boundary-preserving, code-preserving exchange between ALL locally
  uniform substitutions of the two words -- the all-labelings restart
  isomorphism (in the exchange form that set equality needs).  It
  implies `RangeDeterminationOn Reach`
  (`rangeDeterminationOn_of_entryRestartExchange`).
* **The relative collapse** mirrors the global one: range
  determination on reachable paths gives `SummaryDeterminesOn` at
  level one and `SaturationStabilizesAtOn Reach 1`.
* **Back to the global certificate with no relativized closure stack**:
  the substitution relation is relativized instead (`reachRel` --
  unreachable paths get the empty successor set), and reachability is
  required to be carried by the base monitors
  (`ReachWindowDetermined`: base summaries determine `Reach`; concretely
  discharged by adding the regular reachability monitor to the enriched
  base family).  Then window-equal paths agree on reachability, so the
  relativized relation satisfies the *global* set pullback bound at the
  stable level (`reachRel_setPullbackBoundAt`): reachable pairs by the
  relative stabilization and the one-round bound, unreachable pairs
  trivially.  Unreachable atoms are thereby completed with empty
  handoffs; coverage for real (reachable) continuations goes through
  the reachable branch.

`entryRestartClosureCertificate` is the end-to-end positive arrow:
restart exchange + reachability-carrying lawful compatible base =>
the full `JournalAtomsReversalClosureCertificate`.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

section ReachableCollapse

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (Reach : (d : Proc) -> TypedPath (EdgeType d) -> Prop)
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (radius : Nat)

/-- Range determination on reachable paths: outputs of reachable paths
with equal base window codes have equal cross-side base profiles. -/
def RangeDeterminationOn : Prop :=
  ∀ (d : Proc) (pu pv : Param d) (u v : TypedPath (EdgeType d))
    (out out' : TypedPath (EdgeType d.other)),
    Reach d u -> Reach d v ->
    out ∈ (schemeAt d pu).SuccessorWords u ->
    out' ∈ (schemeAt d pv).SuccessorWords v ->
    finiteSummaryWindowAbstraction (base d.other) radius out =
      finiteSummaryWindowAbstraction (base d.other) radius out' ->
    ∀ param' : Param d.other,
      letI : DecidableEq (base d.other.other).Summary := Classical.decEq _
      pathSummaryValue
          (windowProfileSemigroup (schemeAt d.other param')
            (base d.other.other) radius) out =
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d.other param')
            (base d.other.other) radius) out'

/--
**The all-labelings restart isomorphism, exchange form**: equal base
window codes of two substituted words of reachable paths let every
locally uniform substitution of the one be answered by a substitution
of the other with the same boundary labels and the same base window
code.  This is the decisive model lemma: it is strictly stronger than
any acceptance/replay fact about one selected folded continuation.
-/
def EntryRestartExchange : Prop :=
  ∀ (d : Proc) (pu pv : Param d) (u v : TypedPath (EdgeType d))
    (out out' : TypedPath (EdgeType d.other)),
    Reach d u -> Reach d v ->
    out ∈ (schemeAt d pu).SuccessorWords u ->
    out' ∈ (schemeAt d pv).SuccessorWords v ->
    finiteSummaryWindowAbstraction (base d.other) radius out =
      finiteSummaryWindowAbstraction (base d.other) radius out' ->
    ∀ (param' : Param d.other) (left right : Label)
      (w : TypedPath (EdgeType d.other.other)),
      (schemeAt d.other param').LocalFrom left out w right ->
        ∃ w', (schemeAt d.other param').LocalFrom left out' w' right ∧
          finiteSummaryWindowAbstraction (base d.other.other) radius w' =
            finiteSummaryWindowAbstraction (base d.other.other) radius w

omit [(d : Proc) → Fintype (Param d)] [(d : Proc) → DecidableEq (Param d)] in
/-- The restart exchange yields range determination on reachable
paths. -/
theorem rangeDeterminationOn_of_entryRestartExchange
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hex : EntryRestartExchange Reach schemeAt base radius) :
    RangeDeterminationOn Reach schemeAt base radius := by
  intro d pu pv u v out out' hu hv hout hout' hcode param'
  letI : DecidableEq (base d.other.other).Summary := Classical.decEq _
  exact windowProfileValue_eq_of_exchange (schemeAt d.other param')
    (base d.other.other) radius (hbase d.other.other)
    (fun left right w hw =>
      hex d pu pv u v out out' hu hv hout hout' hcode param' left right w hw)
    (fun left right w hw =>
      hex d pv pu v u out' out hv hu hout' hout hcode.symm param' left right
        w hw)

/-- Level-`k` values determine level-`k + 1` values, on reachable
paths. -/
def SummaryDeterminesOn (k : Nat) : Prop :=
  ∀ (d : Proc) (old new : TypedPath (EdgeType d)),
    Reach d old -> Reach d new ->
    pathSummaryValue (saturationLevel schemeAt base radius k d) old =
        pathSummaryValue (saturationLevel schemeAt base radius k d) new ->
      pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) old =
        pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) new

/-- Stabilization on reachable paths. -/
def SaturationStabilizesAtOn (k : Nat) : Prop :=
  ∀ (d : Proc) (bound : Nat) (old new : TypedPath (EdgeType d)),
    Reach d old -> Reach d new ->
    summaryWindowAbstraction (saturationLevel schemeAt base radius k d)
        bound old =
      summaryWindowAbstraction (saturationLevel schemeAt base radius k d)
        bound new ->
    summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
        bound old =
      summaryWindowAbstraction (saturationLevel schemeAt base radius (k + 1) d)
        bound new

theorem saturationStabilizesAtOn_of_summaryDeterminesOn
    {k : Nat} (h : SummaryDeterminesOn Reach schemeAt base radius k) :
    SaturationStabilizesAtOn Reach schemeAt base radius k := by
  intro d bound old new hro hrn hwindow
  have hsummary := congrArg SummaryWindowValue.summary hwindow
  have hpref := congrArg SummaryWindowValue.pref hwindow
  have hsuff := congrArg SummaryWindowValue.suff hwindow
  simp only [summaryWindowAbstraction] at hsummary hpref hsuff ⊢
  simp only [SummaryWindowValue.mk.injEq]
  exact ⟨h d old new hro hrn hsummary, hpref, hsuff⟩

/-- **The relative collapse at level one**: range determination on
reachable paths gives summary determination at level one on reachable
paths. -/
theorem summaryDeterminesOn_one_of_rangeDeterminationOn
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hrange : RangeDeterminationOn Reach schemeAt base radius) :
    SummaryDeterminesOn Reach schemeAt base radius 1 := by
  intro d u v hru hrv h1
  obtain ⟨hb, hp0⟩ :=
    (saturationLevel_succ_value_eq_iff schemeAt base radius 0 d u v).mp h1
  refine (saturationLevel_succ_value_eq_iff schemeAt base radius 1 d u v).mpr
    ⟨hb, fun param => ?_⟩
  letI : DecidableEq
      (saturationLevel schemeAt base radius 1 d.other).Summary :=
    Classical.decEq _
  letI : DecidableEq
      (saturationLevel schemeAt base radius 0 d.other).Summary :=
    Classical.decEq _
  letI : DecidableEq (base d.other).Summary := Classical.decEq _
  have key : ∀ p q : TypedPath (EdgeType d), Reach d p -> Reach d q ->
      pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) p =
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) q ->
      ∀ (left right : Label) (out : TypedPath (EdgeType d.other)),
        (schemeAt d param).LocalFrom left p out right ->
          ∃ out', (schemeAt d param).LocalFrom left q out' right ∧
            finiteSummaryWindowAbstraction
                (saturationLevel schemeAt base radius 1 d.other) radius
                out' =
              finiteSummaryWindowAbstraction
                (saturationLevel schemeAt base radius 1 d.other) radius
                out := by
    intro p q hrp hrq hpq left right out hlocal
    have hmem : finiteSummaryWindowAbstraction
        (saturationLevel schemeAt base radius 0 d.other) radius out ∈
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) p
          left right :=
      ((schemeAt d param).mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil _ radius)
          (finiteSummaryWindowAbstraction_append _ radius (hbase d.other))
          p left right _).mpr ⟨out, hlocal, rfl⟩
    rw [hpq] at hmem
    obtain ⟨out', hlocal', heq0⟩ :=
      ((schemeAt d param).mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil _ radius)
          (finiteSummaryWindowAbstraction_append _ radius (hbase d.other))
          q left right _).mp hmem
    refine ⟨out', hlocal', ?_⟩
    have hb0 : pathSummaryValue (base d.other) out' =
        pathSummaryValue (base d.other) out := congrArg Prod.fst heq0
    have hpre := congrArg (fun value => value.2.1) heq0
    have hsuf := congrArg (fun value => value.2.2) heq0
    have hval1 : pathSummaryValue
        (saturationLevel schemeAt base radius 1 d.other) out' =
        pathSummaryValue (saturationLevel schemeAt base radius 1 d.other)
          out := by
      refine (saturationLevel_succ_value_eq_iff schemeAt base radius 0
        d.other out' out).mpr ⟨hb0, fun param' => ?_⟩
      exact hrange d param param q p out' out hrq hrp
        ⟨left, right, hlocal'⟩ ⟨left, right, hlocal⟩ heq0 param'
    exact Prod.ext hval1 (Prod.ext hpre hsuf)
  exact windowProfileValue_eq_of_exchange (schemeAt d param)
    (saturationLevel schemeAt base radius 1 d.other) radius
    (saturationLevel_lawful schemeAt base radius hbase 1 d.other)
    (key u v hru hrv (hp0 param)) (key v u hrv hru (hp0 param).symm)

/-! ### Back to the global certificate -/

/-- Reachability is carried by the base monitors: base summaries
determine `Reach`.  Concretely discharged by adding the regular
reachability monitor to the enriched base family. -/
def ReachWindowDetermined : Prop :=
  ∀ (d : Proc) (u v : TypedPath (EdgeType d)),
    pathSummaryValue (base d) u = pathSummaryValue (base d) v ->
      (Reach d u ↔ Reach d v)

variable {In₁ : Type v} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/-- The reachability-relativized substitution relation: unreachable
paths get the empty successor set. -/
def reachRel
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d) :
    SummaryWindowReversalRel (saturationLevel schemeAt base radius 1) radius
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) :=
  fun d tuple old =>
    { out | Reach d old ∧
        out ∈ (schemeAt d
          (paramOf d tuple.bits tuple.letter)).SuccessorWords old }

/-- **The relativized relation satisfies the global pullback bound at
the stable level**: window-equal paths agree on reachability, reachable
pairs exchange by the relative stabilization and the one-round bound,
and unreachable pairs have empty images. -/
theorem reachRel_setPullbackBoundAt
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hdet : ReachWindowDetermined Reach base)
    (hstab : SaturationStabilizesAtOn Reach schemeAt base radius 1)
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d)
    (d : Proc)
    (tuple : DirectReversalTuple
      (SummaryWindowAtom (saturationLevel schemeAt base radius 1) radius)
      In₁ In₂ Out₁ Out₂ d) :
    SummaryWindowRelSetPullbackBoundAt radius
      (saturationLevel schemeAt base radius 1 d)
      (saturationLevel schemeAt base radius 1 d.other)
      (reachRel Reach schemeAt base radius paramOf d tuple) := by
  intro old₁ old₂ hwindow
  have hval := congrArg SummaryWindowValue.summary hwindow
  simp only [summaryWindowAbstraction] at hval
  have hbval := saturationLevel_refines_base schemeAt base radius hbase 1 d
    old₁ old₂ hval
  have hiff := hdet d old₁ old₂ hbval
  by_cases hr : Reach d old₁
  · have hr₂ : Reach d old₂ := hiff.mp hr
    have hset₁ : reachRel Reach schemeAt base radius paramOf d tuple old₁ =
        (schemeAt d (paramOf d tuple.bits tuple.letter)).SuccessorWords
          old₁ :=
      Set.ext fun _ => ⟨And.right, fun h => ⟨hr, h⟩⟩
    have hset₂ : reachRel Reach schemeAt base radius paramOf d tuple old₂ =
        (schemeAt d (paramOf d tuple.bits tuple.letter)).SuccessorWords
          old₂ :=
      Set.ext fun _ => ⟨And.right, fun h => ⟨hr₂, h⟩⟩
    rw [hset₁, hset₂]
    exact saturationLevel_round_bound schemeAt base radius hbase 1 d
      (paramOf d tuple.bits tuple.letter) (endpointPullbackBound radius)
      (hstab d (endpointPullbackBound radius) old₁ old₂ hr hr₂ hwindow)
  · have hr₂ : ¬ Reach d old₂ := fun h => hr (hiff.mpr h)
    have hset₁ : reachRel Reach schemeAt base radius paramOf d tuple old₁ =
        (∅ : Set (TypedPath (EdgeType d.other))) :=
      Set.ext fun _ => ⟨fun h => (hr h.1).elim, fun h => h.elim⟩
    have hset₂ : reachRel Reach schemeAt base radius paramOf d tuple old₂ =
        (∅ : Set (TypedPath (EdgeType d.other))) :=
      Set.ext fun _ => ⟨fun h => (hr₂ h.1).elim, fun h => h.elim⟩
    rw [hset₁, hset₂]

/--
**The reachability-relative reversal-closure certificate**: relative
stabilization at level one plus reachability carried by the base give
the full certificate over the relativized relation.  Unreachable atoms
are completed with empty handoffs; real continuations are covered
through the reachable branch.
-/
noncomputable def reachableRangeClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hdet : ReachWindowDetermined Reach base)
    (hstab : SaturationStabilizesAtOn Reach schemeAt base radius 1)
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d)
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible (base d) radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate EdgeType BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  summaryWindowSetClosureCertificate
    (saturationLevel schemeAt base radius 1) radius
    (reachRel Reach schemeAt base radius paramOf)
    baseAtomOf continuationOf baseSound
    (fun d =>
      summaryWindowCompatible_saturationLevel schemeAt base radius hbase
        compatible 1 d)
    (fun d tuple =>
      reachRel_setPullbackBoundAt Reach schemeAt base radius hbase hdet
        hstab paramOf d tuple)
    hradius

/--
**The end-to-end positive arrow**: the all-labelings restart exchange
on reachable paths, with reachability carried by a lawful compatible
base, yields the full reversal-closure certificate.
-/
noncomputable def entryRestartClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hdet : ReachWindowDetermined Reach base)
    (hex : EntryRestartExchange Reach schemeAt base radius)
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d)
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible (base d) radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate EdgeType BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  reachableRangeClosureCertificate Reach schemeAt base radius hbase hdet
    (saturationStabilizesAtOn_of_summaryDeterminesOn Reach schemeAt base
      radius
      (summaryDeterminesOn_one_of_rangeDeterminationOn Reach schemeAt base
        radius hbase
        (rangeDeterminationOn_of_entryRestartExchange Reach schemeAt base
          radius hbase hex)))
    paramOf baseAtomOf continuationOf baseSound compatible hradius

end ReachableCollapse

end DistributedSynthesis
