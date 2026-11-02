/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRecurrentEnvironmentRecut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedSemanticEpochParity
import DistributedSynthesis.Formalizations.Lemma.LemEpochReplayStep

/-!
# Automatic recurrent recuts as ordinary epoch couplings

This file is the deliberately thin semantic join between the automatic
physical recut and `FiniteGlobalMachineEpochCoupling`.

The graph combinatorics supplies a finite suffix shift and strictly increasing
relative cuts.  In the eventually-all-`.both` branch we use singleton cuts;
in the recurrent-strict branch we use the exact physical cuts of the
automatically extracted `ProductiveStrictGapDecomposition`.

After that extraction, the only model-specific semantic input is the
pointwise equality between concrete DPA block minima and a supplied min-even
epoch-priority sequence.  No monitor, active lineage, acceptance argument, or
strict-leader observation is assumed here.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- Proof-side origin of a recurrent cut extraction.  The two constructors are
kept as a proposition inside the structure so downstream parity code can use
only `start`, `cuts`, and their two laws. -/
structure RecurrentEnvironmentEpochCutExtraction
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂) where
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  source :
    ((cuts = fun n ↦ n) ∧
      ∀ initialSide : IndexedLineageSide,
        pairedBranchEnvironment
            (profiledOpenAllBothDirection (OmegaWord.drop env start)
              initialSide) =
          OmegaWord.drop env start) ∨
    (∃ decomposition :
        PairedSignedRecutStream.ProductiveStrictGapDecomposition In₁ In₂,
      decomposition.environment = OmegaWord.drop env start ∧
        pairedBranchEnvironment decomposition.recuts.toFiniteRecutStream.branch =
          OmegaWord.drop env start ∧
        cuts = decomposition.recuts.toFiniteRecutStream.physicalCuts)

/-- Recurrent `.both` graph behavior automatically supplies a finite shift and
a productive relative cut sequence. -/
theorem exists_recurrentEnvironmentEpochCutExtraction
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    Nonempty (RecurrentEnvironmentEpochCutExtraction env) := by
  rcases graphBothRecurrent_automatic_recut env hboth with
    ⟨start, hall | ⟨decomposition, henv, hbranch⟩⟩
  · exact ⟨{
      start := start
      cuts := fun n ↦ n
      cuts_strictMono := strictMono_id
      cuts_zero := rfl
      source := Or.inl ⟨rfl, hall⟩ }⟩
  · exact ⟨{
      start := start
      cuts := decomposition.recuts.toFiniteRecutStream.physicalCuts
      cuts_strictMono :=
        decomposition.recuts.toFiniteRecutStream.physicalCuts_strictMono
      cuts_zero := rfl
      source := Or.inr ⟨decomposition, henv, hbranch, rfl⟩ }⟩

/-- A fixed proof-side choice of the automatic recurrent cuts. -/
noncomputable def recurrentEnvironmentEpochCutExtraction
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    RecurrentEnvironmentEpochCutExtraction env :=
  (exists_recurrentEnvironmentEpochCutExtraction env hboth).some

namespace RecurrentEnvironmentEpochCutExtraction

/-- The automatic recut becomes the standard epoch-coupling object once the
abstract priority sequence is min-even and its values are identified with the
concrete physical block minima.  `blockMin_eq_epochPriority` is the single
model-specific equality field. -/
def toFiniteGlobalMachineEpochCoupling
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (extraction : RecurrentEnvironmentEpochCutExtraction env)
    (epochPriority : Nat → Nat)
    (epochParity : NatSeqMinEvenParity epochPriority)
    (blockMin_eq_epochPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (extraction.start + n)))
          extraction.cuts k = epochPriority k) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env where
  start := extraction.start
  cuts := extraction.cuts
  cuts_strictMono := extraction.cuts_strictMono
  cuts_zero := extraction.cuts_zero
  epochPriority := epochPriority
  epochParity := epochParity
  blockMin_eq_epochPriority := blockMin_eq_epochPriority

end RecurrentEnvironmentEpochCutExtraction

/-- Fully automatic recurrent-cut wrapper.  The caller sees exactly the
chosen shift/cuts in the type of the one remaining block-minimum law. -/
noncomputable def finiteGlobalMachineEpochCoupling_of_automaticRecut
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (epochPriority : Nat → Nat)
    (epochParity : NatSeqMinEvenParity epochPriority)
    (blockMin_eq_epochPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((recurrentEnvironmentEpochCutExtraction env hboth).start + n)))
          (recurrentEnvironmentEpochCutExtraction env hboth).cuts k =
        epochPriority k) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env :=
  RecurrentEnvironmentEpochCutExtraction.toFiniteGlobalMachineEpochCoupling
    A G outputOne outputTwo env
      (recurrentEnvironmentEpochCutExtraction env hboth)
      epochPriority epochParity blockMin_eq_epochPriority

/-- Acceptance handoff with no further recut-side obligations. -/
theorem finiteGlobalMachineTraceWord_accepts_of_automaticRecut
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (epochPriority : Nat → Nat)
    (epochParity : NatSeqMinEvenParity epochPriority)
    (blockMin_eq_epochPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((recurrentEnvironmentEpochCutExtraction env hboth).start + n)))
          (recurrentEnvironmentEpochCutExtraction env hboth).cuts k =
        epochPriority k) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne
    outputTwo env
      (finiteGlobalMachineEpochCoupling_of_automaticRecut A G outputOne
        outputTwo env hboth epochPriority epochParity
        blockMin_eq_epochPriority)

/-- A concrete block minimum is forced by literal entry-state and finite-slice
alignment.  Notice the `- 1`: `cutBlockMin` observes the state at the cut and
the states before the next cut, while the final physical letter closes the
segment and determines the next entry state. -/
theorem cutBlockMin_eq_priority_blockMinState_of_slice_alignment
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (start : Nat) (cuts : Nat → Nat) (k : Nat)
    (state : A.State)
    (block : List (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (hstate : A.run word (start + cuts k) = state)
    (hlength : block.length = cuts (k + 1) - cuts k - 1)
    (hslice : omegaPrefix (OmegaWord.drop word (start + cuts k)) block.length =
      block) :
    cutBlockMin
        (fun n ↦ A.priority (A.run word (start + n))) cuts k =
      A.priority (blockMinState A state block) := by
  let localWord := OmegaWord.drop word (start + cuts k)
  have hrun : ∀ j : Nat,
      A.priority (A.run word (start + (cuts k + j))) =
        A.priority (A.runFrom state localWord j) := by
    intro j
    rw [← hstate]
    have hdrop :
        A.runFrom (A.run word (start + cuts k)) localWord j =
          A.run word ((start + cuts k) + j) := by
      exact A.runFrom_drop A.initial word (start + cuts k) j
    rw [show start + (cuts k + j) = (start + cuts k) + j by omega]
    exact congrArg A.priority hdrop.symm
  calc
    cutBlockMin (fun n ↦ A.priority (A.run word (start + n))) cuts k =
        rangeMin (fun n ↦ A.priority (A.run word (start + n)))
          (cuts k) (cuts (k + 1) - cuts k - 1) := rfl
    _ = rangeMin
        (fun j ↦ A.priority (A.run word (start + (cuts k + j)))) 0
          (cuts (k + 1) - cuts k - 1) :=
      rangeMin_shift_origin
        (fun n ↦ A.priority (A.run word (start + n))) (cuts k) _
    _ = rangeMin (fun j ↦ A.priority (A.runFrom state localWord j)) 0
          block.length := by
      rw [← hlength]
      apply rangeMin_congr
      intro i _
      simpa using hrun i
    _ = A.priority
        (blockMinState A state (omegaPrefix localWord block.length)) :=
      (priority_blockMinState_omegaPrefix_eq_rangeMin A state localWord
        block.length).symm
    _ = A.priority (blockMinState A state block) := by rw [hslice]

/-! ## Concrete public semantic-priority adapter -/

section SemanticEpochPriorityAdapter

variable {I : Type*}
variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The semantic epoch chosen by the same two `Classical.choose` operations as
the public semantic-priority sequence.  Exposing the witness here lets the
remaining physical premise talk only about its literal entry state and block
word. -/
noncomputable def
    profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (n : Nat) :=
  let lineage := Classical.choose hsemantic
  let hlineage := Classical.choose (Classical.choose_spec hsemantic)
  profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package query
      halternates lineage hlineage n

/-- The public semantic-priority term is definitionally the original-DPA
minimum of the exposed semantic epoch's selected block. -/
theorem
    semanticEpochPriority_eq_profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (n : Nat) :
    let epoch :=
      profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates hsemantic n
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          query halternates hsemantic n =
      A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory epoch.sourceMemory
              epoch.direction))
          (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
            epoch.direction)) := by
  rfl

/-- The final trace-side obligation at one automatic epoch: the physical DPA
state at the cut is the selected semantic epoch's entry state, and the
physical prefix before the closing letter is literally its selected block
word. -/
def ProfiledOpenProvenancePolicyDistinguishedAutomaticRecutTraceAlignmentAt
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (k : Nat) : Prop :=
  let extraction := recurrentEnvironmentEpochCutExtraction env hboth
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let epoch :=
    profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hsemantic k
  let state := entryState (A := A)
    (PairedStrategyMemory.selectedHistory epoch.sourceMemory epoch.direction)
  let block :=
    PairedStrategyMemory.selectedBlockWord epoch.sourceMemory epoch.direction
  A.run word (extraction.start + extraction.cuts k) = state ∧
    block.length = extraction.cuts (k + 1) - extraction.cuts k - 1 ∧
      omegaPrefix
          (OmegaWord.drop word (extraction.start + extraction.cuts k))
          block.length = block

/-- Literal alignment at one epoch implies the
block-minimum equality. -/
theorem
    automaticRecut_cutBlockMin_eq_semanticEpochPriority_of_traceAlignmentAt
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (k : Nat)
    (halign :
      ProfiledOpenProvenancePolicyDistinguishedAutomaticRecutTraceAlignmentAt
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package query halternates hsemantic G outputOne outputTwo
            env hboth k) :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            ((recurrentEnvironmentEpochCutExtraction env hboth).start + n)))
        (recurrentEnvironmentEpochCutExtraction env hboth).cuts k =
      profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A strategy
        hwin basis initialCode codePolicy fixedPolicy point initialRoot package
          query halternates hsemantic k := by
  let extraction := recurrentEnvironmentEpochCutExtraction env hboth
  let word := G.globalMachineTraceWord outputOne outputTwo env
  let epoch :=
    profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hsemantic k
  let state := entryState (A := A)
    (PairedStrategyMemory.selectedHistory epoch.sourceMemory epoch.direction)
  let block :=
    PairedStrategyMemory.selectedBlockWord epoch.sourceMemory epoch.direction
  change A.run word (extraction.start + extraction.cuts k) = state ∧
      block.length = extraction.cuts (k + 1) - extraction.cuts k - 1 ∧
        omegaPrefix
            (OmegaWord.drop word (extraction.start + extraction.cuts k))
            block.length = block at halign
  rw [semanticEpochPriority_eq_profiledOpenProvenancePolicyDistinguishedAutomaticRecutSemanticEpochAt
    A strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package query halternates hsemantic k]
  exact cutBlockMin_eq_priority_blockMinState_of_slice_alignment A word
    extraction.start extraction.cuts k state block halign.1 halign.2.1
      halign.2.2

/-- Concrete one-arrow instantiation with the public distinguished semantic
epoch-priority sequence.  Its parity is discharged internally by
`profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority_parity`; the
only caller-supplied semantic statement is the pointwise equality with the
automatic physical cut-block minima. -/
noncomputable def
    finiteGlobalMachineEpochCoupling_of_automaticRecut_semanticEpochPriority
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (blockMin_eq_semanticEpochPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((recurrentEnvironmentEpochCutExtraction env hboth).start + n)))
          (recurrentEnvironmentEpochCutExtraction env hboth).cuts k =
        profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package query halternates hsemantic k) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env :=
  finiteGlobalMachineEpochCoupling_of_automaticRecut A G outputOne outputTwo
    env hboth
    (profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query halternates hsemantic)
    (profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority_parity A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates hsemantic)
    blockMin_eq_semanticEpochPriority

/-- Stronger concrete wrapper: the opaque minimum equality is discharged from
literal entry-state and pre-closing-slice alignment at every extracted epoch. -/
noncomputable def
    finiteGlobalMachineEpochCoupling_of_automaticRecut_semanticTraceAlignment
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (traceAlignment : ∀ k : Nat,
      ProfiledOpenProvenancePolicyDistinguishedAutomaticRecutTraceAlignmentAt
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package query halternates hsemantic G outputOne outputTwo
            env hboth k) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env :=
  finiteGlobalMachineEpochCoupling_of_automaticRecut_semanticEpochPriority A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package query halternates hsemantic G outputOne outputTwo env hboth
        (fun k ↦
          automaticRecut_cutBlockMin_eq_semanticEpochPriority_of_traceAlignmentAt
            A strategy hwin basis initialCode codePolicy fixedPolicy point
              initialRoot package query halternates hsemantic G outputOne
                outputTwo env hboth k (traceAlignment k))

/-- Acceptance corollary of the concrete public semantic-priority wrapper. -/
theorem
    finiteGlobalMachineTraceWord_accepts_of_automaticRecut_semanticEpochPriority
    (A : DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
      strategy hwin basis initialCode)
    {initialState : PairedProfiledTreeState A}
    (fixedPolicy :
      (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
      basis initialCode)
    (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
    (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot)
    (query : Nat → ProfiledOpenWitnessedTableQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph))
    (blockMin_eq_semanticEpochPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              ((recurrentEnvironmentEpochCutExtraction env hboth).start + n)))
          (recurrentEnvironmentEpochCutExtraction env hboth).cuts k =
        profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package query halternates hsemantic k) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne outputTwo
    env
      (finiteGlobalMachineEpochCoupling_of_automaticRecut_semanticEpochPriority
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package query halternates hsemantic G outputOne outputTwo
            env hboth blockMin_eq_semanticEpochPriority)

end SemanticEpochPriorityAdapter

end DetParityAutomaton

end DistributedSynthesis
