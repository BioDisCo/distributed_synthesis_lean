/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedEpochPriority

/-!
# Parity of the distinguished semantic epoch blocks

Active-lineage persistence selects one fixed target root at every completed
distinguished query.  The one-epoch semantic bridge realizes that exact slot
as a genuine strategy-memory step whose selected finite block has the same
minimum priority.  This file chooses those semantic witnesses pointwise and
transfers the already proved target-root parity to their exact block-minimum
sequence.

The clock equation is explicit: semantic epoch `n` equals the code-only
thread priority at positive time `n + 1`.  No claim is made here that these
pointwise semantic witnesses are the blocks cut from the physical recut
controller trace; that is the separate global trace-coupling obligation.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev SemanticEpochQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private noncomputable abbrev semanticEpochStateAt
    (query : Nat → SemanticEpochQuery A initialCode) (n : Nat) :=
  profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package query n

private noncomputable abbrev semanticEpochDescriptorAt
    (query : Nat → SemanticEpochQuery A initialCode) (n : Nat) :=
  profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package
      (semanticEpochStateAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query n)

private noncomputable abbrev semanticEpochCodeAt
    (query : Nat → SemanticEpochQuery A initialCode) (n : Nat) :=
  (semanticEpochDescriptorAt A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package query n).code

private abbrev semanticEpochSideAt
    (query : Nat → SemanticEpochQuery A initialCode) (n : Nat) :=
  (query n).1.1.1

private noncomputable abbrev semanticEpochCodeWord
    (query : Nat → SemanticEpochQuery A initialCode) :
    OmegaWord (ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  fun n ↦ semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
    fixedPolicy point initialRoot package query (n + 1)

private abbrev PersistentLineageActive
    (query : Nat → SemanticEpochQuery A initialCode) (lineage : I) :=
  ∀ n,
    profiledOpenIndexedBiBeliefCurrentSlots A
      (semanticEpochSideAt A initialCode query n)
      (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query n) lineage ≠ none

/-- The exact target root selected by the fixed persistent lineage. -/
private noncomputable abbrev semanticEpochTargetRootAt
    (query : Nat → SemanticEpochQuery A initialCode) (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) : ProfiledOpenClassifiedAnchor A :=
  profiledOpenProvenancePolicyDistinguishedTargetRootAt A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package query lineage
      hlineage n

/-- One pointwise strategy-level epoch realizing the fixed lineage's exact
target root. -/
structure ProfiledOpenProvenancePolicyDistinguishedSemanticEpochAt
    (query : Nat → SemanticEpochQuery A initialCode) (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) where
  sourceMemory : PairedStrategyMemory A strategy
  targetMemory : PairedStrategyMemory A strategy
  direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)
  compatible : PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
    direction
  target_eq : targetMemory = sourceMemory.step (A := A) direction
  target_priority_eq :
    pairedEntryPriority A targetMemory.toTreeState =
      profiledOpenIndexedRootPriority A
        (semanticEpochTargetRootAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query lineage hlineage n)
  block_min_eq :
    A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory sourceMemory direction))
          (PairedStrategyMemory.selectedBlockWord sourceMemory direction)) =
      profiledOpenIndexedRootPriority A
        (semanticEpochTargetRootAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query lineage hlineage n)

/-- The exact target slot produces one semantic epoch witness. -/
theorem
    nonempty_profiledOpenProvenancePolicyDistinguishedSemanticEpochAt
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) :
    Nonempty
      (ProfiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          lineage hlineage n) := by
  have htarget : ∀ k,
      profiledOpenIndexedBiBeliefCurrentSlots A (query k).1.1.1.other
        (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query (k + 1)) lineage ≠
        none := by
    intro k
    rw [profiledOpenProvenancePolicyDistinguishedTargetRootAt_targetSlot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage k]
    exact Option.some_ne_none _
  obtain ⟨root, hroot, sourceMemory, targetMemory, direction, hcompatible,
      htargetMemory, htargetPriority, hblockMin⟩ :=
    exists_profiledOpenProvenancePolicyDistinguishedEpochs_of_targetLineage A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query lineage htarget n
  have hchosen :=
    profiledOpenProvenancePolicyDistinguishedTargetRootAt_targetSlot A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        query halternates lineage hlineage n
  have hrootEq : root =
      semanticEpochTargetRootAt A strategy hwin basis initialCode codePolicy
        fixedPolicy point initialRoot package query lineage hlineage n := by
    apply Option.some.inj
    exact hroot.symm.trans hchosen
  subst root
  exact ⟨{
    sourceMemory := sourceMemory
    targetMemory := targetMemory
    direction := direction
    compatible := hcompatible
    target_eq := htargetMemory
    target_priority_eq := htargetPriority
    block_min_eq := hblockMin }⟩

/-- Canonically choose the finite semantic epoch witness.  This choice is
proof-side and does not alter either process's finite controller. -/
noncomputable def profiledOpenProvenancePolicyDistinguishedSemanticEpochAt
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) :
    ProfiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
        lineage hlineage n :=
  Classical.choice
    (nonempty_profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates lineage hlineage n)

/-- Exact block-minimum/root equation for the canonical semantic epoch. -/
theorem
    profiledOpenProvenancePolicyDistinguishedSemanticEpochAt_blockMin_eq
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) :
    let epoch :=
      profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          halternates lineage hlineage n
    A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory epoch.sourceMemory
              epoch.direction))
          (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
            epoch.direction)) =
      profiledOpenIndexedRootPriority A
        (semanticEpochTargetRootAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query lineage hlineage n) := by
  exact
    (profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
        halternates lineage hlineage n).block_min_eq

/-- Explicit clock equation: semantic epoch `n` has the code-only thread's
priority at positive time `n + 1`. -/
theorem
    profiledOpenProvenancePolicyDistinguishedSemanticEpochAt_blockMin_eq_codeRun_succ
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (lineage : I)
    (hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage)
    (n : Nat) :
    let epoch :=
      profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package query
          halternates lineage hlineage n
    A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory epoch.sourceMemory
              epoch.direction))
          (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
            epoch.direction)) =
      (codedAlternatingIndexedLineageCodeThreadSystem
        (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query 0)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun
          (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query 0)
          (profiledOpenIndexedBiBeliefCurrentSlots A)
          (semanticEpochCodeWord A strategy hwin basis initialCode codePolicy
            fixedPolicy point initialRoot package query)
          (semanticEpochSideAt A initialCode query 0) lineage (n + 1)) := by
  calc
    _ = profiledOpenIndexedRootPriority A
        (semanticEpochTargetRootAt A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query lineage hlineage n) :=
      profiledOpenProvenancePolicyDistinguishedSemanticEpochAt_blockMin_eq A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates lineage hlineage n
    _ = _ :=
      (profiledOpenProvenancePolicyDistinguished_codeRunPriority_eq_targetRoot A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates lineage hlineage n).symm

/-- Main strategy-level endpoint: one fixed lineage determines a canonical
semantic epoch at every completed query; its block minima are pointwise the
positive-time code priorities and form a min-even sequence. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ∃ lineage,
      ∃ hlineage : PersistentLineageActive A strategy hwin basis initialCode
        codePolicy fixedPolicy point initialRoot package query lineage,
        (∀ n,
          let epoch :=
            profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package query halternates lineage hlineage n
          A.priority
              (blockMinState A
                (entryState (A := A)
                  (PairedStrategyMemory.selectedHistory epoch.sourceMemory
                    epoch.direction))
                (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
                  epoch.direction)) =
            (codedAlternatingIndexedLineageCodeThreadSystem
              (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 0)
              (profiledOpenIndexedBiBeliefCurrentSlots A)
              (profiledOpenIndexedRootPriority A)).priority
              (codedAlternatingIndexedLineageCodeRun
                (semanticEpochCodeAt A strategy hwin basis initialCode
                  codePolicy fixedPolicy point initialRoot package query 0)
                (profiledOpenIndexedBiBeliefCurrentSlots A)
                (semanticEpochCodeWord A strategy hwin basis initialCode
                  codePolicy fixedPolicy point initialRoot package query)
                (semanticEpochSideAt A initialCode query 0) lineage (n + 1))) ∧
        NatSeqMinEvenParity (fun n ↦
          let epoch :=
            profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package query halternates lineage hlineage n
          A.priority
            (blockMinState A
              (entryState (A := A)
                (PairedStrategyMemory.selectedHistory epoch.sourceMemory
                  epoch.direction))
              (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
                epoch.direction))) := by
  obtain ⟨lineage, hlineage, hrootParity⟩ :=
    exists_profiledOpenProvenancePolicyDistinguished_targetRootParity A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package hroot query halternates hactive
  refine ⟨lineage, hlineage, ?_, ?_⟩
  · intro n
    exact
      profiledOpenProvenancePolicyDistinguishedSemanticEpochAt_blockMin_eq_codeRun_succ
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package query halternates lineage hlineage n
  · let blockMinPriority := fun n ↦
      let epoch :=
        profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            query halternates lineage hlineage n
      A.priority
        (blockMinState A
          (entryState (A := A)
            (PairedStrategyMemory.selectedHistory epoch.sourceMemory
              epoch.direction))
          (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
            epoch.direction))
    have heq : blockMinPriority = fun n ↦
        profiledOpenIndexedRootPriority A
          (semanticEpochTargetRootAt A strategy hwin basis initialCode
            codePolicy fixedPolicy point initialRoot package query lineage
              hlineage n) := by
      funext n
      exact
        profiledOpenProvenancePolicyDistinguishedSemanticEpochAt_blockMin_eq A
          strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package query halternates lineage hlineage n
    change NatSeqMinEvenParity blockMinPriority
    rw [heq]
    exact hrootParity

/-! ## Public packaged endpoint -/

/-- Public proposition packaging the fixed-lineage semantic-epoch endpoint.
The private clock abbreviations above remain implementation details, while
downstream physical-stream adapters can consume this proposition without
repeating the full dependent statement. -/
def ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query) : Prop :=
  ∃ lineage,
    ∃ hlineage : PersistentLineageActive A strategy hwin basis initialCode
      codePolicy fixedPolicy point initialRoot package query lineage,
      (∀ n,
        let epoch :=
          profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package query halternates lineage hlineage n
        A.priority
            (blockMinState A
              (entryState (A := A)
                (PairedStrategyMemory.selectedHistory epoch.sourceMemory
                  epoch.direction))
              (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
                epoch.direction)) =
          (codedAlternatingIndexedLineageCodeThreadSystem
            (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
              fixedPolicy point initialRoot package query 0)
            (profiledOpenIndexedBiBeliefCurrentSlots A)
            (profiledOpenIndexedRootPriority A)).priority
            (codedAlternatingIndexedLineageCodeRun
              (semanticEpochCodeAt A strategy hwin basis initialCode codePolicy
                fixedPolicy point initialRoot package query 0)
              (profiledOpenIndexedBiBeliefCurrentSlots A)
              (semanticEpochCodeWord A strategy hwin basis initialCode
                codePolicy fixedPolicy point initialRoot package query)
              (semanticEpochSideAt A initialCode query 0) lineage (n + 1))) ∧
      NatSeqMinEvenParity (fun n ↦
        let epoch :=
          profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy
            hwin basis initialCode codePolicy fixedPolicy point initialRoot
              package query halternates lineage hlineage n
        A.priority
          (blockMinState A
            (entryState (A := A)
              (PairedStrategyMemory.selectedHistory epoch.sourceMemory
                epoch.direction))
            (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
              epoch.direction)))

/-- The accepted distinguished query theorem, exposed through the public
packaged endpoint. -/
theorem
    profiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity_of_query
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        query) :
    ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package query halternates := by
  simpa only [
    ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity] using
    exists_profiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity
      A strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package hroot query halternates hactive

/-- Fixed lineage chosen from the packaged semantic-epoch endpoint. -/
private noncomputable def semanticEpochParityLineage
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates) : I :=
  Classical.choose hsemantic

/-- Activity proof for the fixed lineage selected above. -/
private noncomputable def semanticEpochParityLineageActive
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates) :
    PersistentLineageActive A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package query
        (semanticEpochParityLineage A strategy hwin basis initialCode codePolicy
          fixedPolicy point initialRoot package query halternates hsemantic) :=
  Classical.choose (Classical.choose_spec hsemantic)

/-- Public semantic priority sequence selected by the packaged endpoint.
Each term is literally the original DPA minimum of the corresponding chosen
semantic epoch block. -/
noncomputable def
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates) (n : Nat) : Nat :=
  let lineage := semanticEpochParityLineage A strategy hwin basis initialCode
    codePolicy fixedPolicy point initialRoot package query halternates hsemantic
  let hlineage := semanticEpochParityLineageActive A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package query
      halternates hsemantic
  let epoch :=
    profiledOpenProvenancePolicyDistinguishedSemanticEpochAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package query
        halternates lineage hlineage n
  A.priority
    (blockMinState A
      (entryState (A := A)
        (PairedStrategyMemory.selectedHistory epoch.sourceMemory
          epoch.direction))
      (PairedStrategyMemory.selectedBlockWord epoch.sourceMemory
        epoch.direction))

/-- The public selected semantic priority sequence is min-even. -/
theorem
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority_parity
    (query : Nat → SemanticEpochQuery A initialCode)
    (halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query)
    (hsemantic :
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates) :
    NatSeqMinEvenParity
      (profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates hsemantic) := by
  have hspec := Classical.choose_spec (Classical.choose_spec hsemantic)
  simpa only [
    profiledOpenProvenancePolicyDistinguishedSemanticEpochPriority,
    semanticEpochParityLineage, semanticEpochParityLineageActive] using hspec.2

end

end DetParityAutomaton

end DistributedSynthesis
