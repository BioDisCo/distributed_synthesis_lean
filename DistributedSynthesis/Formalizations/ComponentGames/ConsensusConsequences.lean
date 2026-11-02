/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusHoles
import DistributedSynthesis.Formalizations.ComponentGames.BoundedEquivalence

namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000

/-- Discharge the exact-hole premise of the existing representative and
bounded-strategy proofs, with any recognizer of the live prefix language. -/
theorem recognizer_exact_holes {V G : Type} [Nontrivial V]
    (A : Set (Nat → Graph)) (M : Recognizer Graph G)
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (D : Nat) (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A u) D) :
    ∀ h, ∃ z : List Graph, z.length = D ∧ M.eval (h++z) ∉ M.accept := by
  intro h
  obtain ⟨z,len,missing⟩ := repeated_consensus_exact_holes A D positive consensus h
  exact ⟨z,len,fun live => missing ((recognizes _).mpr live)⟩

end
end Characterisation.ComponentGames.Consensus

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- Lemma 7.9 with the manuscript's original consensus hypothesis. All
prefix, guard, finite-priority, and exact-width obligations are discharged. -/
theorem bounded_game_equivalence {V : Type} [Nontrivial V]
    (A : Set (Nat → Graph)) (adversary : DetParityAutomaton Graph)
    (recognizes : ∀ word, word ∈ A ↔ adversary.Accepts word)
    (i : WithInputs.Instance) {D : Nat} (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D) :
    let objective := WithInputs.guardedInstanceObjective adversary i
    let width := compressionBound (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1))
      (Fin (i.outputOneSizeMinusOne+1)) (Fin (i.outputTwoSizeMinusOne+1)) adversary.State objective.State D
    (∃ tree, Winning (D:=D) (prefixRecognizer adversary)
      (fun q e y => objective.step q (e,y)) (.bounded width) objective.initial objective.priority tree) ↔
    ∃ tree, Winning (D:=D) (prefixRecognizer adversary)
      (fun q e y => objective.step q (e,y)) .replacement objective.initial objective.priority tree := by
  dsimp only
  let objective := WithInputs.guardedInstanceObjective adversary i
  have prefixExact := prefixRecognizer_correct adversary A recognizes
  have closed : PrefixClosed (fun g => (prefixRecognizer adversary).eval g ∈ (prefixRecognizer adversary).accept) := by
    intro h w live
    exact (prefixExact h).mp (livePrefix_closed A h w ((prefixExact (h++w)).mpr live))
  have escape : ∀ (σ : WithInputs.Strategies i)
      (word : Nat → RoundRecord (Fin (i.inputOneSizeMinusOne+1)) (Fin (i.inputTwoSizeMinusOne+1)) Graph Unit Unit),
      (∃ n, (prefixRecognizer adversary).eval (History.graphSequence (branchNode word n)) ∉ (prefixRecognizer adversary).accept) →
      NatSeqMinEvenParity (fun n => objective.priority (strategyHistoryLabel σ
        (fun q e y => objective.step q (e,y)) objective.initial (branchNode word n))) := by
    intro σ word bad
    apply guarded_block_escape A adversary recognizes i objective (fun _ => Iff.rfl) σ word
    obtain ⟨n,missing⟩ := bad
    exact ⟨n,fun live => missing ((prefixExact _).mp live)⟩
  exact bounded_game_equivalence_of_holes (prefixRecognizer adversary)
    (fun q e y => objective.step q (e,y)) objective.initial objective.priority closed escape positive
    (Consensus.recognizer_exact_holes A (prefixRecognizer adversary) prefixExact D positive consensus)

end
end Characterisation.ComponentGames.HistoryGame

namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
variable {V I₁ I₂ O₁ O₂ G Q : Type} {D : Nat} [Nontrivial V]
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (m : Move I₁ I₂ O₁ O₂ Q D) (K : Finset m.source.End)
variable (rep : participatingRoots m K → participatingRoots m K)
variable (preserves : ∀ i, componentKey M m K (rep i) = componentKey M m K i)

/-- Lemma 7.6 with its consensus premise restored: arbitrary representatives
of the actual previous key, and an arbitrary distributed next output rule. -/
theorem bounded_representative_move_of_consensus [Fintype G] [Fintype Q] [Fintype O₁] [Fintype O₂]
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (A : Set (Nat → Graph)) (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (positive : 0 < D)
    (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
      Consensus.SolvesBy σ (Residual A u) D)
    (P : Position I₁ I₂ Q D) (component : IsComponent M m K)
    (histories : P.histories = K.image m.source.history)
    (labels : ∀ (h : P.Root) (e : m.source.End), e ∈ K → h.val = m.source.history e →
      P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl D) e)
    (out : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D) (distributed : ClosingPolicyCoherent P.shape out)
    (constant : ∀ i j, componentKey M m K i = componentKey M m K j → rep i = rep j) :
    let e := componentEquiv m K P histories
    let r := fun h => e (fold M m K rep preserves (e.symm h))
    ClosingPolicyCoherent P.shape (restrictClosingPolicy r out) ∧
      ReplacementChecks P.shape M (fun h => M.eval (History.graphSequence h.val))
        step P.state (restrictClosingPolicy r out) r ∧
      (Finset.univ.image r).card ≤
        (Nat.card G * Nat.card Q *
          Nat.card (O₁ × O₂) ^ (∑ t : Fin D, Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ (t.val+1)) *
          2 ^ (Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D)) *
        Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  exact bounded_representative_move M m K rep preserves step
    (Consensus.recognizer_exact_holes A M recognizes D positive consensus)
    P component histories labels out distributed constant
end
end Characterisation.ComponentGames.HistoryGame
