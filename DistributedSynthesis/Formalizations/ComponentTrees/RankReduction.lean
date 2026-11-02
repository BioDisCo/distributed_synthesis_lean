/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreeRanks

/-! Rank-minimal reduction of a full child component. The bound and table
are those of the component-tree proof, not the older game construction.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- B = (1+|Q|)^a a, where a = |Sigma|^D. This bounds the image. -/
def reductionBound : Nat :=
  (1 + Nat.card B.State) ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D) *
    Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D

theorem reductionBound_positive [Nonempty I₁] [Nonempty I₂] : 0 < reductionBound B := by
  letI : Nonempty (RoundRecord I₁ I₂ Graph Unit Unit) :=
    ⟨⟨Classical.arbitrary I₁, Classical.arbitrary I₂, .both, (), ()⟩⟩
  exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos Nat.card_pos)

variable {Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
variable (rank : EnvHistory I₁ I₂ → Rank)

/-- Progress of the next node's reduction, measured on the old reduced
source. The same suffix is retained, exactly as in the paper. -/
def ReductionProgress (N : CompressedNode B M bound)
    (P : Position I₁ I₂ B.State D) (r : Reduction P.past P.state) : Prop :=
  ∀ (h : P.Root) (a : N.extensionMove.source.Root) (u : BlockInput I₁ I₂ D),
    h.val = a.val ++ u.val → ∃ b : N.extensionMove.source.Root,
      (r.map.edge h).val = b.val ++ u.val ∧ rank b.val ≤ rank a.val

/-- No progress hypothesis is assumed: table representatives minimize the
actual rank, and the broadcaster/compression proof supplies their reduction. -/
theorem rank_minimal_reduction {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D)
    (N : CompressedNode B M bound) (P : Position I₁ I₂ B.State D) (next : N.Successor P) :
    ∃ r : Reduction P.past P.state,
      (r.imagePosition P).histories.card ≤ reductionBound B ∧ ReductionProgress B M rank N P r := by
  obtain ⟨C, component, phase, histories, labels⟩ := next
  let key := endpointTable N.extensionMove C (blockSuccessor B N.extensionMove.source.state N.rule)
  let ranking (h : participatingRoots N.extensionMove C) := rank h.val.val
  let rep := representative key ranking
  have preserves : ∀ h, key (rep h) = key h := representative_key key ranking
  have constant : ∀ h k, key h = key k → rep h = rep k :=
    fun _ _ eq => representative_eq key ranking eq
  obtain ⟨R, phaseR, historiesR, _, labelsR, r, action, small⟩ :=
    component_position_with_reduction M B N.extensionMove C
      (N.reduction.imagePosition_valid B M N.position N.valid)
      A recognizes positive consensus component rep preserves constant
  have eq : R = P := by
    apply position_ext R P (phaseR.trans phase.symm) (historiesR.trans histories.symm)
    intro h k hk
    have member : h.val ∈ C.image N.extensionMove.source.history := by rw [← historiesR]; exact h.property
    obtain ⟨e, he, eh⟩ := Finset.mem_image.mp member
    exact (labelsR h ⟨e, he⟩ eh.symm).trans (labels k ⟨e, he⟩ (hk.symm.trans eh.symm)).symm
  subst R
  refine ⟨r, (r.imagePosition_card P).trans_le small, ?_⟩
  intro h a u history
  have member : h.val ∈ C.image N.extensionMove.source.history := by rw [← histories]; exact h.property
  obtain ⟨e, he, eh⟩ := Finset.mem_image.mp member
  have scenario : e = wordScenario a u := N.extensionMove.source.history_injective
    (eh.trans (history.trans (wordScenario_history N.extensionMove.source.past a u).symm))
  have root : (rootOf N.extensionMove C ⟨e, he⟩).val = a := by
    change closingLayerRoot D e = a
    rw [scenario, wordScenario_root]
  have word : scenarioWord D e = u := by rw [scenario, scenarioWord_wordScenario]
  refine ⟨(rep (rootOf N.extensionMove C ⟨e, he⟩)).val, ?_, ?_⟩
  · rw [action h ⟨e, he⟩ eh.symm, word]
  · have le := representative_rank key ranking (rootOf N.extensionMove C ⟨e, he⟩)
    change rank (rep (rootOf N.extensionMove C ⟨e, he⟩)).val.val ≤ rank (rootOf N.extensionMove C ⟨e, he⟩).val.val at le
    rwa [root] at le

end
end Characterisation.ComponentTrees
