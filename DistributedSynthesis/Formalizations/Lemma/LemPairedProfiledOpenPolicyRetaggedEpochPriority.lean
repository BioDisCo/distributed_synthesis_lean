/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPolicyAlignedEpochPriority
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedCodePolicyAlignment

/-!
# Epoch priority through policy retagging

Policy retagging changes the installed semantic representative and its move,
but preserves the target `(code, control)` of the literal physical edge.  A
target-code lineage slot can therefore be pulled back to the physical target
and fed directly to the one-epoch block-minimum theorem.

This is the exact acceptance-relevant fact which survives retagging.  It does
not identify the retagged representative with the literal semantic child and
does not expose any proof-side orientation or lineage at runtime.
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

private abbrev RetaggedFamily :=
  ProfiledOpenWitnessedTableFamily A initialCode

private abbrev RetaggedDescriptor :=
  ProfiledOpenWitnessedTableBaseDescriptor A initialCode

private abbrev RetaggedBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev RetaggedQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

omit [Inhabited I] in
/-- The policy-installed edge inherits the literal physical block and its
exact hidden-root priority from the ordinary witnessed edge beneath the
retagging. -/
theorem exists_profiledOpenPolicyRetaggedEpochMemoryStep_of_targetSlot
    {sourceFamily : RetaggedFamily A initialCode}
    {source : RetaggedDescriptor A initialCode}
    {bank : RetaggedBank A initialCode}
    {query : RetaggedQuery A initialCode}
    {targetFamily : RetaggedFamily A initialCode}
    {target : RetaggedDescriptor A initialCode}
    (hedge : ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin
      basis initialCode codePolicy sourceFamily source bank query targetFamily
        target)
    (side : IndexedLineageSide) (lineage : I)
    (root : ProfiledOpenClassifiedAnchor A)
    (hside : side = query.1.1.1.other)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side target.code
      lineage = some root) :
    ∃ sourceMemory targetMemory : PairedStrategyMemory A strategy,
      ∃ direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂),
        PairedStrategyMemory.DirectionCompatible (A := A) sourceMemory
            direction ∧
          targetMemory = sourceMemory.step (A := A) direction ∧
          pairedEntryPriority A targetMemory.toTreeState =
              profiledOpenIndexedRootPriority A root ∧
          A.priority
              (blockMinState A
                (entryState (A := A)
                  (PairedStrategyMemory.selectedHistory sourceMemory
                    direction))
                (PairedStrategyMemory.selectedBlockWord sourceMemory
                  direction)) =
            profiledOpenIndexedRootPriority A root := by
  obtain ⟨physicalTarget, hphysical, hstate⟩ :=
    profiledOpenProvenancePolicyRetaggedExactEdge_state_eq_physical A strategy
      hwin basis initialCode codePolicy hedge
  have hcode : target.code = physicalTarget.2.code :=
    congrArg Prod.fst hstate
  have hphysicalSlot :
      profiledOpenIndexedBiBeliefCurrentSlots A side physicalTarget.2.code
        lineage = some root := by
    rw [← hcode]
    exact hslot
  exact exists_profiledOpenWitnessedEpochMemoryStep_of_targetSlot A strategy
    hwin basis initialCode hphysical side lineage root hside hphysicalSlot

end

end DetParityAutomaton

end DistributedSynthesis
