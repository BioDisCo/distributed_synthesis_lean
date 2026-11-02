/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockSoundness
import DistributedSynthesis.Formalizations.ComponentGames.ComponentReadback

/- Component-game proof: replay the prescribed distributed algorithm on
actual histories, including intermediate states and the half-open block minima. -/
namespace Characterisation.ComponentGames.HistoryGame
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ G Q : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

/-- The state recursion at an arbitrary next-position history and its unique
previous-block decomposition, rather than a freely chosen state witness. -/
theorem next_state_of_extension (m : Move I₁ I₂ O₁ O₂ Q D)
    (P : Position I₁ I₂ Q D) (next : Next M step m P) (h : P.Root)
    (a : m.source.Root) (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (eq : h.val = a.val ++ w.val) :
    P.state h = closingLayerLabels step m.source.state m.rule D (Nat.le_refl _) (wordScenario a w) := by
  obtain ⟨_,K,_,histories,labels⟩ := next
  have mem : h.val ∈ K.image m.source.history := by rw [← histories]; exact h.property
  obtain ⟨e,he,history⟩ := Finset.mem_image.mp mem
  have equal : e = wordScenario a w := m.source.history_injective (by
    rw [history,eq]
    exact (wordScenario_history m.source.past a w).symm)
  exact (labels h e he history.symm).trans (congrArg (closingLayerLabels step m.source.state m.rule D (Nat.le_refl _)) equal)

variable (q₀ : Q) (σ : StrategyPair I₁ I₂ O₁ O₂)

def algorithmRule (P : Position I₁ I₂ Q D) : ClosingPolicy P.Root I₁ I₂ O₁ O₂ D :=
  fun n e => (σ.one (currentView .one (closingLayerHistory P.past (n.val+1) e)),
              σ.two (currentView .two (closingLayerHistory P.past (n.val+1) e)))

def algorithmMove (P : Position I₁ I₂ Q D) : Move I₁ I₂ O₁ O₂ Q D := ⟨P,algorithmRule σ P,id⟩

def algorithmTree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D) :=
  fun node => algorithmMove σ (observableAt (Position.initial q₀) node)

theorem algorithmMove_legal (P : Position I₁ I₂ Q D) :
    Legal M step .component P (algorithmMove σ P) := by
  refine ⟨rfl,?_,rfl⟩
  intro n
  have exactShape := closingLayerShape_exact P.past P.shape (extractInputShape_exact P.past) (n.val+1)
  constructor
  · intro e f same
    exact congrArg σ.one ((exactShape .one e f).mp same)
  · intro e f same
    exact congrArg σ.two ((exactShape .two e f).mp same)

theorem algorithmTree_legal : SupportedMovesValid (offers M step) (Position.initial q₀)
    (Legal M step .component) (algorithmTree q₀ σ (D:=D)) :=
  fun _ _ => algorithmMove_legal M step σ _

theorem algorithmTree_states (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) (algorithmTree q₀ σ) node = true)
    (h : (algorithmTree q₀ σ node).source.Root) :
    (algorithmTree q₀ σ node).source.state h = strategyHistoryLabel σ step q₀ h.val := by
  induction node using List.reverseRecOn with
  | nil =>
    have empty : h.val = [] := Finset.mem_singleton.mp h.property
    change q₀ = _
    rw [empty]; rfl
  | append_singleton node P ih =>
    have both : publicSupport (offers M step) (algorithmTree q₀ σ) node = true ∧
        offers M step (algorithmTree q₀ σ node) P = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    have next : Next M step (algorithmTree q₀ σ node) P := of_decide_eq_true both.2
    have current : algorithmTree q₀ σ (node ++ [P]) = algorithmMove σ P := by simp [algorithmTree,observableAt]
    revert h
    rw [current]
    intro h
    obtain ⟨_,K,_,histories,labels⟩ := next
    have mem : h.val ∈ K.image (algorithmTree q₀ σ node).source.history := by rw [← histories]; exact h.property
    obtain ⟨e,he,history⟩ := Finset.mem_image.mp mem
    have replay := closingLayerLabels_strategyHistory σ (algorithmTree q₀ σ node).source.past step q₀
      (algorithmTree q₀ σ node).source.state (ih both.1)
      (algorithmTree q₀ σ node).rule (fun _ _ => rfl) D (Nat.le_refl _) e
    exact (labels h e he history.symm).trans (replay.trans (congrArg (strategyHistoryLabel σ step q₀) history))

/-- A compatible Component run consists of growing prefixes of one infinite
input word. This is false for arbitrary replacement runs, so identity is used. -/
theorem component_run_word (positive : 0 < D)
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (legal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree)
    (branch : Nat → Position I₁ I₂ Q D)
    (supported : ∀ n, publicSupport (offers M step) tree (branchNode branch n) = true)
    (run : CompatibleRun tree branch) :
    ∃ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit, ∀ n,
      branchNode word (n*D) = (run.history n).val := by
  have lengths (n : Nat) : List.length (run.history n).val = n*D := by
    have len := (tree (branchNode branch n)).source.lengths _ (run.history n).property
    rw [source_phase M step tree q₀ legal _ (supported n),TreeNonemptiness.branch_length] at len
    exact len
  have next (n : Nat) : (run.history n).val.IsPrefix (run.history (n+1)).val := by
    refine ⟨(run.word n).val,?_⟩
    have eq := run.next n
    rw [(legal _ (supported n)).2.2] at eq
    exact eq.symm
  obtain ⟨word,exactHistory⟩ := exists_word_of_prefix_chain (fun n => (run.history n).val)
    (fun a b lt => by
      change List.length (run.history a).val < List.length (run.history b).val
      rw [lengths,lengths]
      exact Nat.mul_lt_mul_of_pos_right lt positive) next
  refine ⟨word,fun n => ?_⟩
  rw [branchNode_eq_ofFn,← lengths n]
  exact exactHistory n

/-- The run's chosen block is exactly the corresponding segment of its word. -/
theorem component_run_blocks
    (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
    (legal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree)
    (branch : Nat → Position I₁ I₂ Q D)
    (supported : ∀ n, publicSupport (offers M step) tree (branchNode branch n) = true)
    (run : CompatibleRun tree branch) (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
    (histories : ∀ n, branchNode word (n*D) = (run.history n).val) (n : Nat) :
    run.word n = eventBlock word D n := by
  apply Subtype.ext
  apply List.append_cancel_left (as := (run.history n).val)
  have eq := run.next n
  rw [(legal _ (supported n)).2.2] at eq
  simp only [id_eq] at eq
  rw [← eq,← histories (n+1),← histories n]
  simpa only [Nat.add_mul,Nat.one_mul,eventBlock] using (prefix_append_segment word (n*D) D).symm

theorem algorithmTree_stateAt (node : List (Position I₁ I₂ Q D))
    (supported : publicSupport (offers M step) (algorithmTree q₀ σ) node = true)
    (h : (algorithmTree q₀ σ node).source.Root)
    (w : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) (t : Nat) :
    stateAt step (algorithmTree q₀ σ node) h w t =
      strategyHistoryLabel σ step q₀ (h.val ++ w.val.take t) := by
  unfold stateAt
  rw [closingLayerLabels_strategyHistory σ (algorithmTree q₀ σ node).source.past step q₀
    (algorithmTree q₀ σ node).source.state
    (algorithmTree_states M step q₀ σ node supported)
    (algorithmTree q₀ σ node).rule (fun _ _ => rfl)]
  rw [wordScenario_history]
  rfl

/-- Converse of the Component-game equivalence, following the paper:
restrict a realizing algorithm to each component and replay every run. -/
theorem algorithm_winning_component (positive : 0 < D) (χ : Q → Nat)
    (realizes : ∀ word : Nat → RoundRecord I₁ I₂ Graph Unit Unit,
      NatSeqMinEvenParity (fun n => χ (strategyHistoryLabel σ step q₀ (branchNode word n)))) :
    Winning M step .component q₀ χ (algorithmTree q₀ σ (D:=D)) := by
  have legal := algorithmTree_legal M step q₀ σ (D:=D)
  refine ⟨legal,fun branch supported run => ?_⟩
  obtain ⟨word,histories⟩ := component_run_word M step q₀ positive _ legal branch supported run
  have words := component_run_blocks M step q₀ _ legal branch supported run word histories
  let score n := χ (strategyHistoryLabel σ step q₀ (branchNode word n))
  have minima : ∀ n, rangeMin
      (fun t => χ (stateAt step (algorithmTree q₀ σ (branchNode branch n)) (run.history n) (run.word n) t))
      0 (D-1) = cutBlockMin score (fun k => k*D) n := by
    intro n
    unfold cutBlockMin
    have span : (n+1)*D - n*D - 1 = D-1 := by simp [Nat.add_mul]
    rw [span]
    apply rangeMin_congr
    intro t within
    simp only [Nat.zero_add]
    rw [algorithmTree_stateAt M step q₀ σ _ (supported n),words n,← histories n,
      eventBlock_take word D n t (by omega),prefix_append_segment]
  rw [funext minima]
  exact (natSeqMinEvenParity_cutBlockMin score
    (fun _ _ h => Nat.mul_lt_mul_of_pos_right h positive) (by simp)).mpr (realizes word)

end
end Characterisation.ComponentGames.HistoryGame

