/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemConcreteEntryRestartExchange

/-!
# The finite entry quotient needed by the restart construction

`entryMonitors` in `LemConcreteEntryRestartExchange` was deliberately left as
an unstructured parameter.  This file gives it its exact mathematical meaning.
For a path inside a side-`d` epoch, its continuation behaviour is the finite
set of concrete summary-window codes obtainable from every closing parameter
and boundary-label pair.  The paper's `M_A × Q_d` entry state must be a right
congruence for these sets.

The main result, `automatonEntryRestartExchange_of_entryRightCongruence`, proves
that this right-congruence law is precisely sufficient for the all-labelings
restart exchange.  The other half is unconditional: because the concrete base
contains the entry monitor transition monoid, equality of concrete codes
already forces equality of the selected entry-monitor state.  Thus no extra
"code exposes the entry" hypothesis remains.

This separates the genuine model theorem from plumbing:

* monitor enrichment proves that equal codes have the same finite entry state;
* the `M_A × Q_d` right congruence says that equal entry states have the same
  continuation-code sets;
* set membership chooses the required matching continuation.

The history-level same-`θ` interchange theorem proves acceptance of a selected
paired replay.  It does not imply the right-congruence below, which quantifies
over every local labeling and preserves the full finite code.  Bridging that
gap is exactly the existence/construction theorem for the epoch quotient
`Q_d`, not a consequence of acceptance alone.
-/

namespace DistributedSynthesis

universe u

section ConcreteRightCongruence

variable {Alphabet In₁ In₂ Out₁ Out₂ : Type u}
variable [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Fintype (BoundaryLabel Out₁ Out₂)]
variable [DecidableEq (BoundaryLabel Out₁ Out₂)]
variable (A : DetParityAutomaton.{u, u} Alphabet) [DecidableEq A.State]
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)
variable (S₀ : PathSummarySemigroup.{u, u} (AutomatonEdgeType A.State))
variable (entryMonitors : Proc ->
  DeterministicMonitorFamily.{u, u, u} (AutomatonEdgeType A.State))

/-- Select the `M_A × Q_d` entry/ack coordinate from the entry-monitor
family.  Additional entry monitors may coexist in the family. -/
abbrev EntryMonitorIndex :=
  (d : Proc) -> (entryMonitors d).index

/-- The finite set of concrete codes of same-boundary continuations of `old`
under one fixed closing parameter. -/
def continuationCodeSet (radius : Nat) (d : Proc)
    (param : ReversalClosingParam In₁ In₂)
    (left right : BoundaryLabel Out₁ Out₂)
    (old : TypedPath (AutomatonEdgeType A.State)) :
    Set (FiniteSummaryWindowValue
      (concreteBase A letter S₀ entryMonitors d.other).Summary
      (AutomatonEdgeType A.State) radius) :=
  { code | ∃ out,
      (automatonSchemeFamily A letter d param).LocalFrom left old out right ∧
      finiteSummaryWindowAbstraction
        (concreteBase A letter S₀ entryMonitors d.other) radius out = code }

/-- The run state of the selected entry monitor after reading a path. -/
def entryMonitorState
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (d : Proc) (path : TypedPath (AutomatonEdgeType A.State)) :
    (entryMonitors d).state (entryIndex d) :=
  runMonitor (entryMonitors d) (entryIndex d) path

omit [DecidableEq In₁] [DecidableEq In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq (BoundaryLabel Out₁ Out₂)] [DecidableEq A.State] in
/-- The concrete monitor sum restricts to the selected entry-monitor run. -/
theorem runMonitor_concreteFamily_entry
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (d : Proc) (path : TypedPath (AutomatonEdgeType A.State)) :
    runMonitor (concreteMonitorFamily A letter entryMonitors d)
        (Sum.inl (Sum.inl (entryIndex d))) path =
      entryMonitorState (A := A) entryMonitors entryIndex d path :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq (BoundaryLabel Out₁ Out₂)] [DecidableEq A.State] in
/-- **Code exposure is automatic.**  Equality of concrete codes forces
equality of the selected `M_A × Q_d` entry/ack monitor state.  This uses the
whole transition function stored by `monitorTransitionSemigroup`, evaluated at
the monitor's initial state. -/
theorem concreteCode_determines_entryMonitorState
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat) (d : Proc)
    {u v : TypedPath (AutomatonEdgeType A.State)}
    (hcode : finiteSummaryWindowAbstraction
        (concreteBase A letter S₀ entryMonitors d) radius u =
      finiteSummaryWindowAbstraction
        (concreteBase A letter S₀ entryMonitors d) radius v) :
    entryMonitorState (A := A) entryMonitors entryIndex d u =
      entryMonitorState (A := A) entryMonitors entryIndex d v := by
  have hsummary := congrArg Prod.fst hcode
  dsimp only [finiteSummaryWindowAbstraction] at hsummary
  rw [show concreteBase A letter S₀ entryMonitors d =
      S₀.prod (monitorTransitionSemigroup
        (concreteMonitorFamily A letter entryMonitors d)) from rfl,
    PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsummary
  have hmonitor := congrArg Prod.snd hsummary
  dsimp only at hmonitor
  have happ := congrFun
    (congrFun hmonitor (Sum.inl (Sum.inl (entryIndex d))))
    ((entryMonitors d).init (entryIndex d))
  rw [monitorTransition_value, monitorTransition_value] at happ
  exact happ

/-- **The paper's finite entry-quotient obligation.**  On regular-hull paths,
equality of the selected entry state implies equality of all continuation-code
sets, for every next closing input and both threaded boundary labels.

This is Definition `def:epochcongruence`(iv), specialized to the concrete code
consumed by the reversal closure. -/
def AutomatonEntryRightCongruence
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop) : Prop :=
  ∀ (d : Proc) (old old' : TypedPath (AutomatonEdgeType A.State)),
    RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P) d old ->
    RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P) d old' ->
    entryMonitorState (A := A) entryMonitors entryIndex d old =
      entryMonitorState (A := A) entryMonitors entryIndex d old' ->
    ∀ (param : ReversalClosingParam In₁ In₂)
      (left right : BoundaryLabel Out₁ Out₂),
      continuationCodeSet A letter S₀ entryMonitors radius d param
          left right old =
        continuationCodeSet A letter S₀ entryMonitors radius d param
          left right old'

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- Membership is exactly the existence of a same-boundary continuation with
the requested concrete code. -/
theorem mem_continuationCodeSet_iff
    (radius : Nat) (d : Proc) (param : ReversalClosingParam In₁ In₂)
    (left right : BoundaryLabel Out₁ Out₂)
    (old : TypedPath (AutomatonEdgeType A.State))
    (code : FiniteSummaryWindowValue
      (concreteBase A letter S₀ entryMonitors d.other).Summary
      (AutomatonEdgeType A.State) radius) :
    code ∈ continuationCodeSet A letter S₀ entryMonitors radius d param
        left right old ↔
      ∃ out,
        (automatonSchemeFamily A letter d param).LocalFrom
          left old out right ∧
        finiteSummaryWindowAbstraction
          (concreteBase A letter S₀ entryMonitors d.other) radius out = code :=
  Iff.rfl

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- **Right congruence closes the all-labelings exchange.** -/
theorem automatonEntryRestartExchange_of_entryRightCongruence
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop)
    (hcong : AutomatonEntryRightCongruence A letter S₀ entryMonitors
      entryIndex radius P) :
    AutomatonEntryRestartExchange A letter S₀ entryMonitors radius P := by
  unfold AutomatonEntryRightCongruence at hcong
  intro d pu pv u v out out' hu hv hout hout' hcode param left right w hw
  have hreachOut :
      RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P)
        d.other out :=
    mem_rangeHull_of_successorWords
      (automatonSchemeFamily A letter) (singleEdgeInit A P) hout
  have hreachOut' :
      RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P)
        d.other out' :=
    mem_rangeHull_of_successorWords
      (automatonSchemeFamily A letter) (singleEdgeInit A P) hout'
  have hentry := concreteCode_determines_entryMonitorState
    A letter S₀ entryMonitors entryIndex radius d.other hcode
  have hsets := hcong d.other out out' hreachOut hreachOut' hentry
    param left right
  let code := finiteSummaryWindowAbstraction
    (concreteBase A letter S₀ entryMonitors d.other.other) radius w
  have hmem : code ∈ continuationCodeSet A letter S₀ entryMonitors radius
      d.other param left right out := ⟨w, hw, rfl⟩
  have hmem' : code ∈ continuationCodeSet A letter S₀ entryMonitors radius
      d.other param left right out' := by
    rw [← hsets]
    exact hmem
  rcases hmem' with ⟨w', hw', hcode'⟩
  exact ⟨w', hw', hcode'⟩

/-! ### The exact obstruction to a finite entry quotient -/

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- A valid entry quotient must separate any two reachable hull paths whose
continuation-code sets differ.  This is the useful converse direction when
testing a proposed `Q_d`: a difference in one closing parameter/boundary pair
forces different finite entry states. -/
theorem entryMonitorState_ne_of_continuationCodeSet_ne
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop)
    (hcong : AutomatonEntryRightCongruence A letter S₀ entryMonitors
      entryIndex radius P)
    (d : Proc) (old old' : TypedPath (AutomatonEdgeType A.State))
    (hold : RangeHull (automatonSchemeFamily A letter)
      (singleEdgeInit A P) d old)
    (hold' : RangeHull (automatonSchemeFamily A letter)
      (singleEdgeInit A P) d old')
    (param : ReversalClosingParam In₁ In₂)
    (left right : BoundaryLabel Out₁ Out₂)
    (hne : continuationCodeSet A letter S₀ entryMonitors radius d param
        left right old ≠
      continuationCodeSet A letter S₀ entryMonitors radius d param
        left right old') :
    entryMonitorState (A := A) entryMonitors entryIndex d old ≠
      entryMonitorState (A := A) entryMonitors entryIndex d old' := by
  intro hstate
  exact hne (hcong d old old' hold hold' hstate param left right)

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- **Infinite distinguishability refutes every fixed finite selected entry
state.**  If a sequence of hull paths is pairwise separated by some concrete
continuation-code test, pigeonhole forces two of them into the same finite
entry state, contradicting right congruence.

This is the guarded negative target for the global mathematics.  Merely
exhibiting increasing syntactic/profile depth is insufficient; one needs the
pairwise concrete continuation separation quantified below. -/
theorem not_automatonEntryRightCongruence_of_infinite_distinguishable
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop)
    (d : Proc)
    (path : Nat -> TypedPath (AutomatonEdgeType A.State))
    (hreach : ∀ n, RangeHull (automatonSchemeFamily A letter)
      (singleEdgeInit A P) d (path n))
    (hsep : ∀ i j, i ≠ j ->
      ∃ (param : ReversalClosingParam In₁ In₂)
        (left right : BoundaryLabel Out₁ Out₂),
        continuationCodeSet A letter S₀ entryMonitors radius d param
            left right (path i) ≠
          continuationCodeSet A letter S₀ entryMonitors radius d param
            left right (path j)) :
    ¬ AutomatonEntryRightCongruence A letter S₀ entryMonitors
      entryIndex radius P := by
  intro hcong
  letI : Fintype ((entryMonitors d).state (entryIndex d)) :=
    (entryMonitors d).stateFinite (entryIndex d)
  obtain ⟨i, j, hij, hstate⟩ :=
    Finite.exists_ne_map_eq_of_infinite
      (fun n => entryMonitorState (A := A) entryMonitors entryIndex d (path n))
  obtain ⟨param, left, right, hne⟩ := hsep i j hij
  exact hne (hcong d (path i) (path j) (hreach i) (hreach j) hstate
    param left right)

/-- End-to-end closure package from the finite entry right congruence. -/
noncomputable def entryRestartClosureCertificate_of_entryRightCongruence
    {BaseAtom : Proc -> Type u} {Continuation : Proc -> Type u}
    (entryIndex : EntryMonitorIndex (A := A) entryMonitors)
    (radius : Nat) (P : Proc -> AutomatonEdgeType A.State -> Prop)
    (hlaw : PathSummaryLawful S₀)
    (hcong : AutomatonEntryRightCongruence A letter S₀ entryMonitors
      entryIndex radius P)
    (baseAtomOf : (d : Proc) ->
      TypedPath (AutomatonEdgeType A.State) -> BaseAtom d)
    (continuationOf : (d : Proc) ->
      TypedPath (AutomatonEdgeType A.State) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible
      (concreteBase A letter S₀ entryMonitors d) radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate
      (fun _ => AutomatonEdgeType A.State) BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  entryRestartClosureCertificate_of_concreteExchange A letter S₀ entryMonitors
    radius P hlaw
    (automatonEntryRestartExchange_of_entryRightCongruence
      A letter S₀ entryMonitors entryIndex radius P hcong)
    baseAtomOf continuationOf baseSound compatible hradius

end ConcreteRightCongruence

end DistributedSynthesis
