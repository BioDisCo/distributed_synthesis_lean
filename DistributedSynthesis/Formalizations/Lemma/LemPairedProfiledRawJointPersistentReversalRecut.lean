/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadAlignment
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenAutomaticRecutEpochCoupling

/-!
# Automatic raw-joint cuts on a persistent strict-reversal tail

When simultaneous rounds disappear but both strict directions still recur,
the starts of maximal strict groups recur.  Hence the same automatic signed
recut used in the recurrent-synchronization case also gives a productive
sequence of physical cuts on this tail.

This matters for the raw-joint construction: the persistent-reversal case can
be checked by the same single fixed-policy alternating thread as recurrent
epochs.  It need not restart, or appeal to, an independent per-block checker.
All choices below are proof-side; no process receives a side, graph, cut, or
strict-leader signal.
-/

namespace DistributedSynthesis

universe u v w x y s

/-- If both strict directions occur arbitrarily late, then strict-group starts
also occur arbitrarily late.  Choose a late left round and then the first
later right round; minimality makes its predecessor different. -/
theorem strictGroupStartsRecurrent_of_bothStrictDirectionsRecurrent
    {graphs : Nat → Graph}
    (h : BothStrictDirectionsRecurrent graphs) :
    StrictGroupStartsRecurrent graphs := by
  classical
  intro start
  rcases h.1 (start + 1) with ⟨leftAt, hleftAt, hleft⟩
  have hexists : ∃ n : Nat, leftAt < n ∧ graphs n = .right := by
    rcases h.2 (leftAt + 1) with ⟨rightAt, hrightAt, hright⟩
    exact ⟨rightAt, by omega, hright⟩
  let firstRight := Nat.find hexists
  have hfirst := Nat.find_spec hexists
  have hprev : graphs (firstRight - 1) ≠ graphs firstRight := by
    intro heq
    have hprevRight : graphs (firstRight - 1) = .right := by
      rw [heq, hfirst.2]
    by_cases hpred : firstRight - 1 = leftAt
    · rw [hpred, hleft] at hprevRight
      contradiction
    · have hleftPred : leftAt < firstRight - 1 := by omega
      have hpredFirst : firstRight - 1 < firstRight := by omega
      exact Nat.find_min hexists hpredFirst ⟨hleftPred, hprevRight⟩
  refine ⟨firstRight, ?_, ?_, Or.inr hprev⟩
  · omega
  · rw [hfirst.2]
    exact Graph.noConfusion

/-- The productive strict-group suffix can be chosen after any prescribed
finite prefix.  This is the form used after the exceptional initial block. -/
theorem exists_drop_strictGroupStart_zero_and_recurrent_after
    {graphs : Nat → Graph}
    (hstarts : StrictGroupStartsRecurrent graphs) (lower : Nat) :
    ∃ shift : Nat,
      lower < shift ∧
        StrictGroupStart (fun n ↦ graphs (shift + n)) 0 ∧
        StrictGroupStartsRecurrent (fun n ↦ graphs (shift + n)) := by
  rcases hstarts lower with ⟨shift, hlower, hgroup⟩
  exact ⟨shift, hlower,
    strictGroupStart_drop_zero_of_strict graphs shift hgroup.1,
    strictGroupStartsRecurrent_drop hstarts shift⟩

/-- Strong extraction form: choose the recurrent physical cuts after an
arbitrary operational handoff time. -/
theorem exists_persistentStrictReversalEpochCutExtraction_after
    {In₁ : Type u} {In₂ : Type v}
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat) :
    ∃ extraction :
        DetParityAutomaton.RecurrentEnvironmentEpochCutExtraction env,
      lower < extraction.start := by
  have hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph) :=
    strictGroupStartsRecurrent_of_bothStrictDirectionsRecurrent h.2
  rcases exists_drop_strictGroupStart_zero_and_recurrent_after hstarts lower
      with ⟨start, hlower, hzero, hstartsTail⟩
  let tail : EnvironmentSequence In₁ In₂ := OmegaWord.drop env start
  have hzero' : StrictGroupStart (fun n ↦ (tail n).graph) 0 := by
    simpa [tail, OmegaWord.drop] using hzero
  have hstarts' : StrictGroupStartsRecurrent (fun n ↦ (tail n).graph) := by
    simpa [tail, OmegaWord.drop] using hstartsTail
  let decomposition :=
    DetParityAutomaton.recurrentProductiveStrictGapDecomposition tail hstarts'
      hzero'
  let extraction :
      DetParityAutomaton.RecurrentEnvironmentEpochCutExtraction env := {
    start := start
    cuts := decomposition.recuts.toFiniteRecutStream.physicalCuts
    cuts_strictMono :=
      decomposition.recuts.toFiniteRecutStream.physicalCuts_strictMono
    cuts_zero := rfl
    source := Or.inr ⟨decomposition, rfl,
      DetParityAutomaton.recurrentStrict_pairedBranchEnvironment_eq_original
        tail hstarts' hzero', rfl⟩ }
  exact ⟨extraction, hlower⟩

/-- A persistent strict-reversal tail admits the same finite-shift/productive
recut package used by the generic epoch-coupling layer. -/
theorem exists_persistentStrictReversalEpochCutExtraction
    {In₁ : Type u} {In₂ : Type v}
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    Nonempty (DetParityAutomaton.RecurrentEnvironmentEpochCutExtraction env) := by
  rcases exists_persistentStrictReversalEpochCutExtraction_after env h 0 with
    ⟨extraction, _⟩
  exact ⟨extraction⟩

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Recurrent synchronization cuts can likewise be shifted beyond any finite
operational prefix.  This rebases the already-proved extraction on a dropped
environment and transports its literal recut witness back to the original
clock. -/
theorem exists_recurrentEnvironmentEpochCutExtraction_after
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat) :
    ∃ extraction : RecurrentEnvironmentEpochCutExtraction env,
      lower < extraction.start := by
  let base := lower + 1
  let tail : EnvironmentSequence In₁ In₂ := OmegaWord.drop env base
  have htail : GraphBothRecurrent (fun n ↦ (tail n).graph) := by
    intro localStart
    rcases hboth (base + localStart) with ⟨n, hn, hgraph⟩
    have hbase : base ≤ n := Nat.le_trans (Nat.le_add_right base localStart) hn
    refine ⟨n - base, ?_, ?_⟩
    · omega
    · simpa [tail, OmegaWord.drop, Nat.add_sub_of_le hbase] using hgraph
  let chosen := recurrentEnvironmentEpochCutExtraction tail htail
  let start := base + chosen.start
  have hdrop : OmegaWord.drop tail chosen.start = OmegaWord.drop env start := by
    simp [tail, start, OmegaWord.drop_drop]
  let extraction : RecurrentEnvironmentEpochCutExtraction env := {
    start := start
    cuts := chosen.cuts
    cuts_strictMono := chosen.cuts_strictMono
    cuts_zero := chosen.cuts_zero
    source := by
      rcases chosen.source with hall | ⟨decomposition, henv, hbranch, hcuts⟩
      · exact Or.inl ⟨hall.1, fun side ↦ by
          simpa only [hdrop] using hall.2 side⟩
      · exact Or.inr ⟨decomposition, henv.trans hdrop,
          hbranch.trans hdrop, hcuts⟩ }
  refine ⟨extraction, ?_⟩
  simp only [extraction, start, base]
  omega

/-- Fixed proof-side recurrent cut choice after an operational prefix. -/
noncomputable def recurrentEnvironmentEpochCutExtractionAfter
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat) : RecurrentEnvironmentEpochCutExtraction env :=
  (exists_recurrentEnvironmentEpochCutExtraction_after env hboth lower).choose

/-- The chosen recurrent cuts really start after the requested prefix. -/
theorem recurrentEnvironmentEpochCutExtractionAfter_start
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower : Nat) :
    lower < (recurrentEnvironmentEpochCutExtractionAfter env hboth lower).start :=
  (exists_recurrentEnvironmentEpochCutExtraction_after env hboth lower).choose_spec

variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- Fix one proof-side automatic cut extraction for a persistent strict
reversal tail. -/
noncomputable def persistentStrictReversalEpochCutExtraction
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    RecurrentEnvironmentEpochCutExtraction env :=
  (exists_persistentStrictReversalEpochCutExtraction env h).some

/-- Fixed proof-side persistent-reversal cut choice after an operational
prefix. -/
noncomputable def persistentStrictReversalEpochCutExtractionAfter
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat) : RecurrentEnvironmentEpochCutExtraction env :=
  (exists_persistentStrictReversalEpochCutExtraction_after env h lower).choose

/-- The chosen persistent-reversal cuts really start after the requested
prefix. -/
theorem persistentStrictReversalEpochCutExtractionAfter_start
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower : Nat) :
    lower <
      (persistentStrictReversalEpochCutExtractionAfter env h lower).start :=
  (exists_persistentStrictReversalEpochCutExtraction_after env h lower).choose_spec

namespace ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Recurrent-synchronization acceptance in the literal actual-macro
presentation, with automatic cuts chosen after an arbitrary finite prefix. -/
theorem physicalTrace_accepts_of_recurrentThreadRootPriority_after
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (lower rootOffset : Nat)
    (blockMin_eq_threadRootPriority : ∀ k : Nat,
      let extraction :=
        recurrentEnvironmentEpochCutExtractionAfter env hboth lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        profiledRawJointThreadRootPriority A
          (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
            (thread.root (rootOffset + k + 1)))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let extraction := recurrentEnvironmentEpochCutExtractionAfter env hboth lower
  exact thread.physicalTrace_accepts_of_threadRootPriority A policy G outputOne
    outputTwo env rootOffset extraction.start extraction.cuts
      extraction.cuts_strictMono extraction.cuts_zero
      blockMin_eq_threadRootPriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Persistent strict-reversal acceptance in the same actual-macro
presentation, again with automatic cuts after a finite prefix. -/
theorem physicalTrace_accepts_of_persistentStrictReversalThreadRootPriority_after
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (lower rootOffset : Nat)
    (blockMin_eq_threadRootPriority : ∀ k : Nat,
      let extraction :=
        persistentStrictReversalEpochCutExtractionAfter env h lower
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k =
        profiledRawJointThreadRootPriority A
          (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
            (thread.root (rootOffset + k + 1)))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) := by
  let extraction :=
    persistentStrictReversalEpochCutExtractionAfter env h lower
  exact thread.physicalTrace_accepts_of_threadRootPriority A policy G outputOne
    outputTwo env rootOffset extraction.start extraction.cuts
      extraction.cuts_strictMono extraction.cuts_zero
      blockMin_eq_threadRootPriority

/-- Package an operational block-minimum identification at the automatically
chosen strict-group cuts as the standard raw-policy epoch coupling. -/
noncomputable def toPersistentStrictReversalPolicyEpochCoupling
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((persistentStrictReversalEpochCutExtraction env h).start + n)))
          (persistentStrictReversalEpochCutExtraction env h).cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (fun n ↦ (thread.states A policy (n + 1)).1)
            initialSide () (offset + k))) :
    ProfiledRawJointUnitPolicyEpochCoupling A strategy initialCode policy G
      outputOne outputTwo env :=
  thread.toPolicyEpochCoupling A policy G outputOne outputTwo env initialSide
    offset (persistentStrictReversalEpochCutExtraction env h).start
    (persistentStrictReversalEpochCutExtraction env h).cuts
    (persistentStrictReversalEpochCutExtraction env h).cuts_strictMono
    (persistentStrictReversalEpochCutExtraction env h).cuts_zero
    blockMin_eq_threadPriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed raw-joint policy closes the persistent strict-reversal branch as
soon as the operational carrier identifies its literal blocks at the
automatic cuts. -/
theorem physicalTrace_accepts_of_persistentStrictReversal
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
    {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode}
    (thread : ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (h : PersistentStrictReversalTail (fun n ↦ (env n).graph))
    (initialSide : IndexedLineageSide) (offset : Nat)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((persistentStrictReversalEpochCutExtraction env h).start + n)))
          (persistentStrictReversalEpochCutExtraction env h).cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (fun n ↦ (thread.states A policy (n + 1)).1)
            initialSide () (offset + k))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (thread.toPersistentStrictReversalPolicyEpochCoupling A G outputOne outputTwo
    env h initialSide offset blockMin_eq_threadPriority).physicalTrace_accepts A

end ProfiledRawJointUnitFixedPolicyRoot.AlternatingThread

end

end DetParityAutomaton

end DistributedSynthesis
