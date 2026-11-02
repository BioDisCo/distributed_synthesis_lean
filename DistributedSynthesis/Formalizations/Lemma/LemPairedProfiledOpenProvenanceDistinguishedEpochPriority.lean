/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedActiveLineage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenPolicyRetaggedEpochPriority

/-!
# Epoch priority on the distinguished provenance stream

The finite distinguished recurrence follows literal policy-retagged exact
edges.  If a fixed lineage occurs in the target code on the query-selected
opposite side, the existing one-epoch theorem therefore supplies an actual
strategy-memory step whose selected physical block has exactly the target
root priority.

This file deliberately stops at that exact semantic block.  Identifying the
block with the corresponding slice of the finite physical controller is the
next trace-coupling step; it is not hidden in the statement below.
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

private abbrev EpochState :=
  ProfiledOpenProvenancePolicyDistinguishedState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev EpochQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-- One target-code slot on a literal distinguished transition gives an
actual strategy-memory epoch with the same root and block-minimum priority. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguishedEpoch_of_targetSlot
    (current : EpochState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (query : EpochQuery A initialCode)
    (side : IndexedLineageSide) (lineage : I)
    (hside : side = query.1.1.1.other)
    (hslot : profiledOpenIndexedBiBeliefCurrentSlots A side
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package current
          query)).code lineage ≠ none) :
    ∃ root : ProfiledOpenClassifiedAnchor A,
      profiledOpenIndexedBiBeliefCurrentSlots A side
          (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            (profiledOpenProvenancePolicyDistinguishedStep A strategy hwin basis
              initialCode codePolicy fixedPolicy point initialRoot package
              current query)).code lineage = some root ∧
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
  obtain ⟨root, hroot⟩ := Option.ne_none_iff_exists'.mp hslot
  refine ⟨root, hroot, ?_⟩
  let next := profiledOpenProvenancePolicyDistinguishedStep A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package current
      query
  have hedge :=
    profiledOpenProvenancePolicyDistinguishedStep_exact A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package current query
  exact exists_profiledOpenPolicyRetaggedEpochMemoryStep_of_targetSlot A
    strategy hwin basis initialCode codePolicy hedge side lineage root hside
      hroot

/-- Stream form of the same bridge.  The premise is exactly the fixed target
slot supplied by active-lineage persistence; no fresh per-epoch lineage may
be selected. -/
theorem
    exists_profiledOpenProvenancePolicyDistinguishedEpochs_of_targetLineage
    (query : Nat → EpochQuery A initialCode)
    (lineage : I)
    (htarget : ∀ n,
      profiledOpenIndexedBiBeliefCurrentSlots A (query n).1.1.1.other
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package
            query (n + 1))).code lineage ≠ none) :
    ∀ n,
      ∃ root : ProfiledOpenClassifiedAnchor A,
        profiledOpenIndexedBiBeliefCurrentSlots A (query n).1.1.1.other
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
                basis initialCode codePolicy fixedPolicy point initialRoot
                package query (n + 1))).code lineage = some root ∧
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
  intro n
  rw [profiledOpenProvenancePolicyDistinguishedStateAt_succ]
  exact
    exists_profiledOpenProvenancePolicyDistinguishedEpoch_of_targetSlot A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package
        (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package query n)
        (query n) (query n).1.1.1.other lineage rfl (htarget n)

end

end DetParityAutomaton

end DistributedSynthesis
