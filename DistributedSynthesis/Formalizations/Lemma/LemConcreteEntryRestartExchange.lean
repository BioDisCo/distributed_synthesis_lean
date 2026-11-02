/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHullInstantiation
import DistributedSynthesis.Formalizations.Lemma.LemRepresentedCandidates

/-!
# The concrete entry-restart target

The single concrete instantiation of the positive route.  All generic
layers are consumed here; what remains is exactly one theorem.

* `DeterministicMonitorFamily.sum` -- the family combinator; runs
  restrict definitionally (`runMonitor_sum_inl`/`_inr`).
* `concreteMonitorFamily` -- per side: the `M_A x Q_d` entry monitors
  and the acknowledgement-bit monitor (the `entryMonitors` parameter,
  whose exact content is part of the exchange construction), combined
  with `singleEdgeMonitor` and `rangeWordMonitor`.
* `concreteBase` -- the enriched base
  `enrichedBaseSemigroup S₀ (concreteMonitorFamily ...)`.
* `concreteBase_reachWindowDetermined` -- `ReachWindowDetermined` for
  the regular hull at the concrete base, discharged by the recognizer
  assembly with the two recognizers of the family.
* `AutomatonEntryRestartExchange` -- **the exact remaining theorem**:
  `EntryRestartExchange` for the concrete scheme family on the regular
  hull at the concrete base.
* `entryRestartClosureCertificate_of_concreteExchange` -- the package:
  every field discharged except the exchange itself.

Attack plan for the exchange, by cases on the two hull witnesses of
the sources: Init/Init is a finite single-edge calculation; Init/Range
and Range/Init are the spurious mixed-depth cases to TEST FIRST (the
likeliest place for the regular hull to be too broad); Range/Range is
the genuine restart construction -- unpack both range witnesses into
threaded three-edge blocks and mirror every continuation labeling
using equality of the entry monitors and the fresh acknowledgement
bit.  Failure classification per the recorded trichotomy: a failure on
an `IterativelyReachable` path is a genuine negative witness; a
hull-only failure means the regular hull is too coarse.
-/

namespace DistributedSynthesis

universe u v w v' r

/-! ### The monitor-family combinator -/

section Sum

variable {EdgeType : Type u}

/-- The sum of two deterministic monitor families. -/
def DeterministicMonitorFamily.sum
    (F G : DeterministicMonitorFamily.{u, v, w} EdgeType) :
    DeterministicMonitorFamily.{u, v, w} EdgeType where
  index := F.index ⊕ G.index
  indexFinite := by
    letI := F.indexFinite
    letI := G.indexFinite
    infer_instance
  state
    | Sum.inl i => F.state i
    | Sum.inr j => G.state j
  stateFinite
    | Sum.inl i => F.stateFinite i
    | Sum.inr j => G.stateFinite j
  init
    | Sum.inl i => F.init i
    | Sum.inr j => G.init j
  step
    | Sum.inl i => F.step i
    | Sum.inr j => G.step j

@[simp]
theorem runMonitor_sum_inl (F G : DeterministicMonitorFamily.{u, v, w} EdgeType)
    (i : F.index) (w : List EdgeType) :
    runMonitor (F.sum G) (Sum.inl i) w = runMonitor F i w :=
  rfl

@[simp]
theorem runMonitor_sum_inr (F G : DeterministicMonitorFamily.{u, v, w} EdgeType)
    (j : G.index) (w : List EdgeType) :
    runMonitor (F.sum G) (Sum.inr j) w = runMonitor G j w :=
  rfl

end Sum

/-! ### The concrete family, base, and target -/

section Concrete

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

/-- The concrete initial paths: single edges satisfying a per-side
initial-edge predicate. -/
def singleEdgeInit (P : Proc -> AutomatonEdgeType A.State -> Prop) :
    (d : Proc) -> TypedPath (AutomatonEdgeType A.State) -> Prop :=
  fun d w => ∃ e, w = [e] ∧ P d e

/-- The concrete monitor family: the `M_A x Q_d` entry and
acknowledgement monitors (the `entryMonitors` parameter), the
single-edge initial recognizer, and the range-word recognizer. -/
noncomputable def concreteMonitorFamily (d : Proc) :
    DeterministicMonitorFamily.{u, u, u} (AutomatonEdgeType A.State) :=
  ((entryMonitors d).sum singleEdgeMonitor).sum (rangeWordMonitor A letter)

/-- The concrete enriched base. -/
noncomputable def concreteBase :
    (d : Proc) ->
      PathSummarySemigroup.{u, u} (AutomatonEdgeType A.State) :=
  fun d =>
    enrichedBaseSemigroup S₀ (concreteMonitorFamily A letter entryMonitors d)

omit [DecidableEq In₁] [DecidableEq In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq (BoundaryLabel Out₁ Out₂)] [DecidableEq A.State] in
theorem concreteBase_lawful (hlaw : PathSummaryLawful S₀) (d : Proc) :
    PathSummaryLawful (concreteBase A letter S₀ entryMonitors d) :=
  enrichedBaseSemigroup_lawful S₀
    (concreteMonitorFamily A letter entryMonitors d) hlaw

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- `ReachWindowDetermined` for the regular hull at the concrete base:
discharged by the recognizer assembly with the family's two
recognizers. -/
theorem concreteBase_reachWindowDetermined
    (P : Proc -> AutomatonEdgeType A.State -> Prop) :
    ReachWindowDetermined
      (RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P))
      (concreteBase A letter S₀ entryMonitors) := by
  apply rangeHull_reachWindowDetermined_of_recognizers
    (automatonSchemeFamily A letter) (fun _ => S₀)
    (concreteMonitorFamily A letter entryMonitors) (singleEdgeInit A P)
  · intro d
    exact ⟨Sum.inl (Sum.inr PUnit.unit),
      fun st => ∃ e, st = some (some e) ∧ P d e,
      fun w => singleEdgeMonitor_recognizes (P d) w⟩
  · intro e
    exact ⟨Sum.inr PUnit.unit, rangeRecAccepts A,
      fun w => isSuccessorWordFrom_automatonSchemeFamily_iff.{u, u, u, u} A letter e w⟩

/--
**THE remaining theorem of the positive route**: the all-labelings
restart exchange for the concrete scheme family, on the regular hull,
at the concrete base.  Everything else is discharged.
-/
def AutomatonEntryRestartExchange (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop) : Prop :=
  EntryRestartExchange
    (RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P))
    (automatonSchemeFamily A letter)
    (concreteBase A letter S₀ entryMonitors) radius

/--
**The package**: the full reversal-closure certificate from the
concrete exchange alone.  Every generic field is discharged; the sole
hypothesis beyond the journal-atom interface data is
`AutomatonEntryRestartExchange`.
-/
noncomputable def entryRestartClosureCertificate_of_concreteExchange
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (radius : Nat) (P : Proc -> AutomatonEdgeType A.State -> Prop)
    (hlaw : PathSummaryLawful S₀)
    (hex : AutomatonEntryRestartExchange A letter S₀ entryMonitors radius P)
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
  entryRestartClosureCertificate
    (RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P))
    (automatonSchemeFamily A letter)
    (concreteBase A letter S₀ entryMonitors) radius
    (concreteBase_lawful A letter S₀ entryMonitors hlaw)
    (concreteBase_reachWindowDetermined A letter S₀ entryMonitors P)
    hex
    (fun _ _ closing => (closing.inputOne, closing.inputTwo))
    baseAtomOf continuationOf baseSound compatible hradius

/-! ### The finite failure certificate -/

/--
**The short-long counterexample certificate**: hull-reachable sources,
outputs with equal concrete base-window codes, and one continuation of
the first output that no same-boundary continuation of the second can
match code-for-code.  The intended run: depths one and two (a 3-edge
against a 9-edge output), tiny `A`, singleton inputs, Boolean outputs,
radius 2 -- first with trivial `entryMonitors`, then with the proposed
`M_A x Q_d` entry-state pair and acknowledgement monitor.

Interpretation of the three outcomes (recorded in GUIDE): collision
disappears -> the separating monitor component is the invariant for
the Range/Range proof; codes collide but profiles match -> direct
evidence of replace-not-accumulate; a reachable profile separation
remains -> genuine negative witness against that entry abstraction.
Do NOT eliminate collisions with a raw depth or length monitor: no
finite monitor distinguishes all `3^t` depths -- the necessary
component must make repeated expansion semantically idempotent.
-/
structure EntryRestartExchangeFailure (radius : Nat)
    (P : Proc -> AutomatonEdgeType A.State -> Prop) where
  side : Proc
  paramU : In₁ × In₂
  paramV : In₁ × In₂
  sourceU : TypedPath (AutomatonEdgeType A.State)
  sourceV : TypedPath (AutomatonEdgeType A.State)
  out : TypedPath (AutomatonEdgeType A.State)
  out' : TypedPath (AutomatonEdgeType A.State)
  reachU : RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P)
    side sourceU
  reachV : RangeHull (automatonSchemeFamily A letter) (singleEdgeInit A P)
    side sourceV
  memOut : out ∈
    (automatonSchemeFamily A letter side paramU).SuccessorWords sourceU
  memOut' : out' ∈
    (automatonSchemeFamily A letter side paramV).SuccessorWords sourceV
  codeEq :
    finiteSummaryWindowAbstraction
        (concreteBase A letter S₀ entryMonitors side.other) radius out =
      finiteSummaryWindowAbstraction
        (concreteBase A letter S₀ entryMonitors side.other) radius out'
  contParam : In₁ × In₂
  left : BoundaryLabel Out₁ Out₂
  right : BoundaryLabel Out₁ Out₂
  cont : TypedPath (AutomatonEdgeType A.State)
  contLocal :
    (automatonSchemeFamily A letter side.other contParam).LocalFrom
      left out cont right
  separated : ∀ w',
    (automatonSchemeFamily A letter side.other contParam).LocalFrom
        left out' w' right ->
      finiteSummaryWindowAbstraction
          (concreteBase A letter S₀ entryMonitors side.other.other) radius
          w' ≠
        finiteSummaryWindowAbstraction
          (concreteBase A letter S₀ entryMonitors side.other.other) radius
          cont

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- **Mechanical refutation**: a failure certificate refutes the
concrete exchange. -/
theorem not_automatonEntryRestartExchange_of_failure
    {radius : Nat} {P : Proc -> AutomatonEdgeType A.State -> Prop}
    (F : EntryRestartExchangeFailure A letter S₀ entryMonitors radius P) :
    ¬ AutomatonEntryRestartExchange A letter S₀ entryMonitors radius P := by
  intro hex
  obtain ⟨w', hw', hcode⟩ :=
    hex F.side F.paramU F.paramV F.sourceU F.sourceV F.out F.out'
      F.reachU F.reachV F.memOut F.memOut' F.codeEq F.contParam F.left
      F.right F.cont F.contLocal
  exact F.separated w' hw' hcode

end Concrete

end DistributedSynthesis
