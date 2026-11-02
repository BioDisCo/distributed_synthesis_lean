/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWinningMonitorPhysicalPriority
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization

/-!
# Pointed semantic children of the pinned receiver response

The classified response emitted by a semantically re-anchored physical
overlay is not merely an allowed root.  Its retained semantic table witness
constructs a pointed realization of the advertised child, and that child is
the literal next `PairedStrategyMemory` state.

This bridge deliberately does not use the independently rationalized public
coherent table of the source realization.  The output, child root, and memory
step all come from the one semantic past witnessing the pinned table response.
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

/-! ## Right-to-left pinned response -/

/-- A right installed overlay's literal pinned response supplies the pointed
semantic child that it advertises.  In particular, the classified root in the
physical record is the selected root of the child and the target state points
at that same root. -/
theorem exists_profiledOpenWitnessedRightPinnedResponseChildStep
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let output :=
      (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
        inputTwo).2.1
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ semanticPast :
            List ((({root // root ∈ lane.source.1} × In₂) × In₁)),
          ∃ child : ProfiledOpenLeftPointedRealization A strategy hwin basis
              (output.2 row).2,
            output =
                profiledOpenRightSemanticClassifiedFamilyReceiver A
                  lane.source strategy hwin lane.realization.entry basis
                  semanticPast ((decodedRoot, inputTwo), inputOne) ∧
              child.selected.1 = (output.2 row).1 ∧
              output.1.target row = .inr (.inr child.selected.1.1) ∧
              PairedStrategyMemory.step (A := A)
                  (.processOne (lane.realization.entry decodedRoot)
                    (lane.realization.minimum decodedRoot))
                  (.fromOne row
                    (semanticPast.map (fun old ↦ (old.1.2, old.2)))
                    (inputTwo, inputOne)) =
                .processTwo child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, semanticPast,
      hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorRightRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  let output :=
    (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
      inputTwo).2.1
  have hinverse :
      profiledOpenHiddenDescriptorRightRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorRightRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  have houtput : output =
      profiledOpenRightSemanticClassifiedFamilyReceiver A lane.source strategy
        hwin lane.realization.entry basis semanticPast
          ((decodedRoot, inputTwo), inputOne) := by
    change
      profiledOpenFixedRightQueryResponses A initialCode overlay.value
          overlay.query overlay.member
            ((overlay.root, inputTwo), inputOne) = _
    rw [← hinverse]
    exact congrFun hpast ((decodedRoot, inputTwo), inputOne)
  have houtput' :
      (profiledOpenWitnessedRightRoundRecord A initialCode overlay inputOne
          inputTwo).2.1 =
        profiledOpenRightSemanticClassifiedFamilyReceiver A lane.source
          strategy hwin lane.realization.entry basis semanticPast
            ((decodedRoot, inputTwo), inputOne) := by
    simpa only [output] using houtput
  let physicalPast := semanticPast.map (fun old ↦ (old.1.2, old.2))
  rw [houtput']
  let child := profiledOpenRightSemanticChildPointedRealization A lane.source
    strategy hwin basis lane.realization decodedRoot physicalPast
      (inputTwo, inputOne) row
  refine ⟨lane, decodedRoot, semanticPast, ?_, rfl, ?_, ?_, ?_⟩
  · simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenRightSemanticClassifiedReceiver,
      physicalPast] using child
  · exact profiledOpenRightSemanticChildPointedRealization_selected A
      lane.source strategy hwin basis lane.realization decodedRoot physicalPast
        (inputTwo, inputOne) row
  · have hselected : (id child).selected.1 =
        profiledOpenRightSemanticChildRoot A lane.source strategy hwin
          lane.realization.entry basis decodedRoot physicalPast
            (inputTwo, inputOne) row := by
      simpa only [child, id_eq] using
        (profiledOpenRightSemanticChildPointedRealization_selected A
          lane.source strategy hwin basis lane.realization decodedRoot
            physicalPast (inputTwo, inputOne) row)
    simpa only [hselected] using
      (profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A lane.source
        strategy hwin lane.realization.entry lane.realization.minimum basis
          semanticPast decodedRoot (inputTwo, inputOne) row).1
  · exact
      profiledOpenRightSemanticChildPointedRealization_memory_step A
        lane.source strategy hwin basis lane.realization decodedRoot physicalPast
          (inputTwo, inputOne) row

/-! ## Left-to-right pinned response -/

/-- Left mirror of the pinned-response pointed successor theorem. -/
theorem exists_profiledOpenWitnessedLeftPinnedResponseChildStep
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (row : PairedEntryRow) :
    let output :=
      (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
        inputTwo).2.1
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ semanticPast :
            List ((({root // root ∈ lane.source.1} × In₁) × In₂)),
          ∃ child : ProfiledOpenRightPointedRealization A strategy hwin basis
              (output.2 row).2,
            output =
                profiledOpenLeftSemanticClassifiedFamilyReceiver A lane.source
                  strategy hwin lane.realization.entry basis semanticPast
                  ((decodedRoot, inputOne), inputTwo) ∧
              child.selected.1 = (output.2 row).1 ∧
              output.1.target row = .inr (.inl child.selected.1.1) ∧
              PairedStrategyMemory.step (A := A)
                  (.processTwo (lane.realization.entry decodedRoot)
                    (lane.realization.minimum decodedRoot))
                  (.fromTwo row
                    (semanticPast.map (fun old ↦ (old.1.2, old.2)))
                    (inputOne, inputTwo)) =
                .processOne child.actualEntry child.actualMinimum := by
  classical
  dsimp only
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, semanticPast,
      hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorLeftRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  let output :=
    (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
      inputTwo).2.1
  have hinverse :
      profiledOpenHiddenDescriptorLeftRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  have houtput : output =
      profiledOpenLeftSemanticClassifiedFamilyReceiver A lane.source strategy
        hwin lane.realization.entry basis semanticPast
          ((decodedRoot, inputOne), inputTwo) := by
    change
      profiledOpenFixedLeftQueryResponses A initialCode overlay.value
          overlay.query overlay.member
            ((overlay.root, inputOne), inputTwo) = _
    rw [← hinverse]
    exact congrFun hpast ((decodedRoot, inputOne), inputTwo)
  have houtput' :
      (profiledOpenWitnessedLeftRoundRecord A initialCode overlay inputOne
          inputTwo).2.1 =
        profiledOpenLeftSemanticClassifiedFamilyReceiver A lane.source
          strategy hwin lane.realization.entry basis semanticPast
            ((decodedRoot, inputOne), inputTwo) := by
    simpa only [output] using houtput
  let physicalPast := semanticPast.map (fun old ↦ (old.1.2, old.2))
  rw [houtput']
  let child := profiledOpenLeftSemanticChildPointedRealization A lane.source
    strategy hwin basis lane.realization decodedRoot physicalPast
      (inputOne, inputTwo) row
  refine ⟨lane, decodedRoot, semanticPast, ?_, rfl, ?_, ?_, ?_⟩
  · simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenLeftSemanticClassifiedReceiver,
      physicalPast] using child
  · exact profiledOpenLeftSemanticChildPointedRealization_selected A
      lane.source strategy hwin basis lane.realization decodedRoot physicalPast
        (inputOne, inputTwo) row
  · have hselected : (id child).selected.1 =
        profiledOpenLeftSemanticChildRoot A lane.source strategy hwin
          lane.realization.entry basis decodedRoot physicalPast
            (inputOne, inputTwo) row := by
      simpa only [child, id_eq] using
        (profiledOpenLeftSemanticChildPointedRealization_selected A
          lane.source strategy hwin basis lane.realization decodedRoot
            physicalPast (inputOne, inputTwo) row)
    simpa only [hselected] using
      (profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A lane.source
        strategy hwin lane.realization.entry lane.realization.minimum basis
          semanticPast decodedRoot (inputOne, inputTwo) row).1
  · exact
      profiledOpenLeftSemanticChildPointedRealization_memory_step A lane.source
        strategy hwin basis lane.realization decodedRoot physicalPast
          (inputOne, inputTwo) row

end

end DetParityAutomaton

end DistributedSynthesis
