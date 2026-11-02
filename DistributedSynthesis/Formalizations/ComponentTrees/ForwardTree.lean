/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ForwardLocal
import DistributedSynthesis.Formalizations.ComponentTrees.RankReduction

/-! Recursive forward bounded representation, following the manuscript's
association of each compressed node with a node of the original tree.
-/
namespace Characterisation.ComponentTrees.ForwardConstruction
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G V : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Nonempty I₁] [Nonempty I₂] [Nontrivial V]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (A : Set (Nat → Graph))
variable (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
variable (positive : 0 < D)
variable (consensus : ∀ u, LivePrefix A u → ∃ σ : StrategyPair V V (Option V) (Option V),
  Consensus.SolvesBy σ (Residual A u) D)
variable (original : UncompressedTree B M) (accepting : original.Accepting)

structure State where
  position : Position I₁ I₂ B.State D
  valid : PositionValid B M position
  reduction : Reduction position.past position.state
  small : (reduction.imagePosition position).histories.card ≤ reductionBound B
  node : List (Position I₁ I₂ B.State D)
  supported : publicSupport UncompressedNode.offers original node = true
  inc : PositionInclusion B position (original node).position

def action (st : State B M original) : CompressedNode B M (reductionBound B) :=
  restrictNode B M (original st.node) st.position st.valid st.reduction st.small st.inc

def initialState : State B M original := by
  let P := (original []).position
  let r := Reduction.identity P.past P.state
  have initial : P = Position.initial B.initial := accepting.1 [] (publicSupport_nil _ _)
  have small : (r.imagePosition P).histories.card ≤ reductionBound B := by
    apply le_trans (Finset.card_le_card (r.imageHistories_subset P))
    rw [initial]
    simpa only [Position.initial, Finset.card_singleton] using reductionBound_positive B
  exact ⟨P, (original []).valid, r, small, [], publicSupport_nil _ _, PositionInclusion.identity P⟩

structure AdvanceData (st : State B M original) (P : Position I₁ I₂ B.State D) where
  target : Position I₁ I₂ B.State D
  next : (original st.node).Successor target
  inc : PositionInclusion B P target
  reduction : Reduction P.past P.state
  small : (reduction.imagePosition P).histories.card ≤ reductionBound B
  progress : ReductionProgress B M (original.rank accepting A recognizes) (action B M original st) P reduction

def advanceData (st : State B M original) (P : Position I₁ I₂ B.State D)
    (next : (action B M original st).Successor P) : AdvanceData B M A recognizes original accepting st P := by
  let inclusion := inclusion_next B M (original st.node) st.position
    st.valid st.reduction st.small st.inc P next
  let reduction := rank_minimal_reduction B M
    (original.rank accepting A recognizes) A recognizes positive consensus (action B M original st) P next
  exact ⟨inclusion.choose, inclusion.choose_spec.1, Classical.choice inclusion.choose_spec.2,
    reduction.choose, reduction.choose_spec.1, reduction.choose_spec.2⟩

def advanceState (st : State B M original) (P : Position I₁ I₂ B.State D)
    (next : (action B M original st).Successor P) : State B M original := by
  let data := advanceData B M A recognizes positive consensus original accepting st P next
  have support : publicSupport UncompressedNode.offers original (st.node ++ [data.target]) = true := by
    rw [publicSupport_append, st.supported, Bool.true_and]
    exact decide_eq_true data.next
  have source : (original (st.node ++ [data.target])).position = data.target := by
    simpa [observableAt] using accepting.1 _ support
  exact ⟨P, ComponentSuccessor.valid B M next
    (st.reduction.imagePosition_valid B M st.position st.valid),
    data.reduction, data.small, st.node ++ [data.target], support, data.inc.castTarget source.symm⟩

def stepState (st : State B M original) (P : Position I₁ I₂ B.State D) : State B M original :=
  if next : (action B M original st).Successor P then
    advanceState B M A recognizes positive consensus original accepting st P next else st

def atState (node : List (Position I₁ I₂ B.State D)) : State B M original :=
  node.foldl (stepState B M A recognizes positive consensus original accepting)
    (initialState B M original accepting)

def tree : CompressedTree B M (reductionBound B) := fun node =>
  action B M original (atState B M A recognizes positive consensus original accepting node)

@[simp] theorem atState_append (node : List (Position I₁ I₂ B.State D)) (P : Position I₁ I₂ B.State D) :
    atState B M A recognizes positive consensus original accepting (node ++ [P]) =
      stepState B M A recognizes positive consensus original accepting
        (atState B M A recognizes positive consensus original accepting node) P := by
  simp only [atState, List.foldl_append, List.foldl_cons, List.foldl_nil]

@[simp] theorem stepState_of_next (st : State B M original) (P : Position I₁ I₂ B.State D)
    (next : (action B M original st).Successor P) :
    stepState B M A recognizes positive consensus original accepting st P =
      advanceState B M A recognizes positive consensus original accepting st P next := dif_pos next

theorem tree_valid : (tree B M A recognizes positive consensus original accepting).Valid := by
  intro node supported
  cases node using List.reverseRecOn with
  | nil => exact accepting.1 [] (publicSupport_nil _ _)
  | append_singleton node P =>
    have both : publicSupport CompressedNode.offers
        (tree B M A recognizes positive consensus original accepting) node = true ∧
        CompressedNode.offers (tree B M A recognizes positive consensus original accepting node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (action B M original (atState B M A recognizes positive consensus original accepting node)).Successor P :=
      of_decide_eq_true both.2
    change (action B M original (atState B M A recognizes positive consensus original accepting (node ++ [P]))).position = _
    rw [atState_append, stepState_of_next B M A recognizes positive consensus original accepting _ P next]
    change P = observableAt (Position.initial B.initial) (node ++ [P])
    simp only [observableAt, List.getLast?_concat, Option.getD_some]

/-- One original node at the same depth for each supported compressed node. -/
theorem atState_depth (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport CompressedNode.offers
      (tree B M A recognizes positive consensus original accepting) node = true) :
    (atState B M A recognizes positive consensus original accepting node).node.length = node.length := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node P ih =>
    have both : publicSupport CompressedNode.offers
        (tree B M A recognizes positive consensus original accepting) node = true ∧
        CompressedNode.offers (tree B M A recognizes positive consensus original accepting node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (action B M original (atState B M A recognizes positive consensus original accepting node)).Successor P :=
      of_decide_eq_true both.2
    rw [atState_append, stepState_of_next B M A recognizes positive consensus original accepting _ P next]
    change (_ ++ [_]).length = _
    simp only [List.length_append, List.length_singleton, ih both.1]

/-- Actual history labels are unchanged at every supported compressed node. -/
theorem original_labels (node : List (Position I₁ I₂ B.State D))
    (h : (tree B M A recognizes positive consensus original accepting node).position.Root) :
    original.stateOf (historyBlocks D h.val) =
      (tree B M A recognizes positive consensus original accepting node).position.state h := by
  let st := atState B M A recognizes positive consensus original accepting node
  have eq := original.stateOf_history accepting.1 positive st.node st.supported (st.inc.edge h)
  exact eq.trans (st.inc.states h).symm

/-- All compatible runs accept. Their reduced edges make ordinal progress
although their unreduced histories need not be prefixes of a single word. -/
theorem tree_accepting : (tree B M A recognizes positive consensus original accepting).Accepting := by
  refine ⟨tree_valid B M A recognizes positive consensus original accepting, ?_⟩
  intro branch supported run
  let st n := atState B M A recognizes positive consensus original accepting (branchNode branch n)
  let N n := action B M original (st n)
  have next n : (N n).Successor (branch n) := by
    have support := supported (n+1)
    change publicSupport CompressedNode.offers _ (branchNode branch n ++ [branch n]) = true at support
    rw [publicSupport_append, Bool.and_eq_true] at support
    exact of_decide_eq_true support.2
  have advance n : st (n+1) = advanceState B M A recognizes positive consensus original accepting
      (st n) (branch n) (next n) := by
    change atState B M A recognizes positive consensus original accepting (branchNode branch n ++ [branch n]) = _
    rw [atState_append, stepState_of_next]
  have progress n : ReductionProgress B M (original.rank accepting A recognizes)
      (N n) (st (n+1)).position (st (n+1)).reduction := by
    rw [advance]
    exact (advanceData B M A recognizes positive consensus original accepting (st n) (branch n) (next n)).progress
  let edge n : (st n).position.Root := run.history n
  let reduced n : (N n).extensionMove.source.Root := (st n).reduction.imageProjection (st n).position (edge n)
  have witnesses n : ∃ b : (N n).extensionMove.source.Root,
      ((st (n+1)).reduction.map.edge (edge (n+1))).val = b.val ++ (run.word n).val ∧
      original.rank accepting A recognizes b.val ≤ original.rank accepting A recognizes (reduced n).val :=
    progress n (edge (n+1)) (reduced n) (run.word n) (run.next n)
  let chosen n := (witnesses n).choose
  apply original.reduced_paths_accept accepting A recognizes positive
    (fun n => ((st n).reduction.map.edge (edge n)).val) (fun n => (chosen n).val) run.word
    (fun n => (st n).position.state (edge n))
  · intro n
    have len := (N n).extensionMove.source.lengths _ (chosen n).property
    change List.length (chosen n).val = (st n).position.phase * D at len
    rw [(st n).inc.phase, original.position_phase accepting.1 (st n).node (st n).supported,
      atState_depth B M A recognizes positive consensus original accepting _ (supported n), TreeNonemptiness.branch_length] at len
    exact len
  · intro n
    exact (witnesses n).choose_spec.2
  · intro n
    exact (witnesses n).choose_spec.1
  · intro n
    exact (st (n+1)).valid.1 ((st (n+1)).reduction.map.edge (edge (n+1)))
  · intro n
    exact (original_labels B M A recognizes positive consensus original accepting _
      ((st (n+1)).reduction.map.edge (edge (n+1)))).trans
      ((st (n+1)).reduction.states (edge (n+1)))

end
end Characterisation.ComponentTrees.ForwardConstruction
