/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockExecution

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxSynthPendingDepth 16

def eventBlock {I₁ I₂ : Type} (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (D n : Nat) : BlockInput I₁ I₂ D :=
  ⟨List.ofFn (fun i : Fin D => word (n*D+i.val)), List.length_ofFn⟩

theorem prefix_append_segment {E : Type} (word : Nat → E) (a k : Nat) :
    branchNode word a ++ List.ofFn (fun i : Fin k => word (a+i.val)) = branchNode word (a+k) := by
  rw [branchNode_eq_ofFn,branchNode_eq_ofFn,List.ofFn_add]
  rfl

theorem eventBlock_take {I₁ I₂ : Type} (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (D n k : Nat) (within : k ≤ D) :
    (eventBlock word D n).val.take k = List.ofFn (fun i : Fin k => word (n*D+i.val)) := by
  apply List.ext_getElem
  · simp [eventBlock, Nat.min_eq_left within]
  · intro i hi hj
    simp [eventBlock]

theorem eventBlock_history {I₁ I₂ : Type} (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (D n : Nat) : blockHistory (branchNode (eventBlock word D) n) = branchNode word (n*D) := by
  induction n with
  | zero => simp [branchNode]
  | succ n ih =>
    change blockHistory (branchNode (eventBlock word D) n ++ [eventBlock word D n]) = _
    rw [blockHistory_append,ih,Nat.succ_mul]
    exact prefix_append_segment word (n*D) D

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq G] [DecidableEq Q]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
variable (χ : Q → Nat) (bounded : ∀ q, χ q ≤ K)
variable (tree : LabeledTree (BlockOutcome I₁ I₂ G Q B D) (BlockMove I₁ I₂ O₁ O₂ G Q B D))
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept)

def actualBlockBranch (input : Nat → BlockInput I₁ I₂ D) (n : Nat) : BlockOutcome I₁ I₂ G Q B D :=
  let state := blockMachine M step tree (branchNode input n)
  actualBlockOutcome M step (tree state.1) (wordScenario state.2 (input n))

omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
  [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem blockMachine_public_history (input : Nat → BlockInput I₁ I₂ D) (n : Nat) :
    (blockMachine M step tree (branchNode input n)).1 = branchNode (actualBlockBranch M step tree input) n := by
  induction n with
  | zero =>
    change (blockMachine M step tree []).1 = []
    rw [blockMachine_nil]
  | succ n ih =>
    change (blockMachine M step tree (branchNode input n++[input n])).1 = _
    rw [blockMachine_append]
    change _ ++ [actualBlockBranch M step tree input n] = _
    rw [ih]
    rfl

def actualBlockColor (input : Nat → BlockInput I₁ I₂ D) (n : Nat) : Fin (K+1) :=
  let state := blockMachine M step tree (branchNode input n)
  ⟨blockColor step (tree state.1) χ (wordScenario state.2 (input n)),
    Nat.lt_succ_of_le ((blockColor_le step (tree state.1) χ _).trans (bounded _))⟩

include closed recognizes in
theorem blockGame_blocks_accept
    (winning : (blockGame M step χ (initialBlockOutcome M q₀ B D) ((0,0) : HandoverCode B K)).WinningTree tree)
    (input : Nat → BlockInput I₁ I₂ D)
    (live : ∀ n, P (History.graphSequence (blockHistory (branchNode input n)))) :
    NatSeqMinEvenParity (fun n => (actualBlockColor M step χ bounded tree input n).val) := by
  classical
  letI : Inhabited (BlockOutcome I₁ I₂ G Q B D) := ⟨initialBlockOutcome M q₀ B D⟩
  obtain ⟨legal,progress⟩ := (blockGame_winning_iff M step χ _ _ tree).mp winning
  let state n := blockMachine M step tree (branchNode input n)
  let branch := actualBlockBranch M step tree input
  let code : Nat → HandoverCode B K
    | 0 => (0,0)
    | n+1 => ((state (n+1)).2, actualBlockColor M step χ bounded tree input n)
  have slot : ∀ n, (code n).1 = (state n).2 := by
    intro n
    cases n with
    | zero => simp [code,state,branchNode]
    | succ n => rfl
  let thread : HiddenCodeContinuityThread ((0,0) : HandoverCode B K) (BlockEdge M step χ)
      (observableThreadWord tree branch) := {
    code := code
    initial := rfl
    edge := by
      intro n
      have liveEnd := blockMachine_endpoint_live M step tree q₀ legal P closed recognizes
        (branchNode input n) (input n) (live (n+1))
      change BlockEdge M step χ (code n) (tree (branchNode branch n)) (branch n) (code (n+1))
      rw [← blockMachine_public_history M step tree input n]
      refine ⟨actualBlockOutcome_offered M step (tree (state n).1) _ liveEnd, ?_⟩
      refine ⟨wordScenario (state n).2 (input n), (blockComponent_self M _ _).trans liveEnd, ?_, ?_, rfl⟩
      · exact (wordScenario_root _ _).trans (slot n).symm
      · change _ = (blockMachine M step tree (branchNode input n++[input n])).2
        rw [blockMachine_append]
        rfl
  }
  exact progress branch thread

include closed recognizes bounded in
/-- Soundness of the finite game on every execution whose graph prefixes
remain live. The guarded objective handles executions that leave them. -/
theorem blockGame_sound [Nonempty O₁] [Nonempty O₂] (positive : 0 < D)
    (winning : (blockGame M step χ (initialBlockOutcome M q₀ B D) ((0,0) : HandoverCode B K)).WinningTree tree) :
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
        (∀ n, P (History.graphSequence (branchNode word n))) →
        NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n))) := by
  classical
  letI : Inhabited (BlockOutcome I₁ I₂ G Q B D) := ⟨initialBlockOutcome M q₀ B D⟩
  have legal := ((blockGame_winning_iff M step χ _ _ tree).mp winning).1
  obtain ⟨σ,implements⟩ := blockController_strategy M step q₀ tree legal P closed recognizes
  refine ⟨σ,fun word live => ?_⟩
  let input := eventBlock word D
  have liveBlocks : ∀ n, P (History.graphSequence (blockHistory (branchNode input n))) := by
    intro n
    rw [eventBlock_history]
    exact live _
  have parity := blockGame_blocks_accept M step q₀ χ bounded tree P closed recognizes winning input liveBlocks
  let score n := χ (strategyHistoryLabel σ step q₀ (branchNode word n))
  have minima : ∀ n, (actualBlockColor M step χ bounded tree input n).val = cutBlockMin score (fun k => k*D) n := by
    intro n
    change blockColor step _ χ _ = _
    rw [blockMachine_color M step q₀ tree legal P closed recognizes σ implements
      (branchNode input n) (input n) (liveBlocks (n+1)) χ]
    unfold blockMinimum cutBlockMin
    rw [(input n).property]
    have span : (n+1)*D - n*D - 1 = D-1 := by simp [Nat.add_mul]
    rw [span]
    apply rangeMin_congr
    intro k within
    dsimp only [score]
    congr 2
    simp only [Nat.zero_add]
    dsimp only [input]
    rw [eventBlock_history, eventBlock_take word D n k (by omega)]
    exact prefix_append_segment word (n*D) k
  rw [funext minima] at parity
  exact (natSeqMinEvenParity_cutBlockMin score (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) (by simp)).mp parity

end
end Characterisation.PeriodicBlocks
