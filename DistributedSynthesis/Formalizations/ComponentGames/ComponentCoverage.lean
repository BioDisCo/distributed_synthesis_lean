/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ComponentExecutions

/- The Component-game proof's coverage step: follow an arbitrary live word
by selecting the component containing its next block. -/
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

theorem next_contains (m : Move I₁ I₂ O₁ O₂ Q D) (e : m.source.End)
    (alive : extensionLive M m e = true) :
    ∃ P, Next M step m P ∧ m.source.history e ∈ P.histories := by
  let K := Finset.univ.filter (fun f =>
    closingComponentMask (closingLayerShape m.source.shape D) (extensionLive M m) e f = true)
  have component : IsComponent M m K := ⟨e,alive,by intro f; simp only [K,Finset.mem_filter,Finset.mem_univ,true_and]⟩
  have inside : e ∈ K := by
    simp only [K,Finset.mem_filter,Finset.mem_univ,true_and,
      closingComponentMask,alive,Bool.true_and,decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl e
  obtain ⟨P,phase,histories,labels⟩ := next_component_data M step m K component
  refine ⟨P,⟨phase,K,component,histories,labels⟩,?_⟩
  rw [histories]
  exact Finset.mem_image.mpr ⟨e,inside,rfl⟩

variable (tree : LabeledTree (Position I₁ I₂ Q D) (Move I₁ I₂ O₁ O₂ Q D))
variable (q₀ : Q)
variable (legal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree)
variable (word : Nat → RoundRecord I₁ I₂ Graph Unit Unit)
variable (live : ∀ n, M.eval (History.graphSequence (branchNode word n)) ∈ M.accept)

structure FollowState (n : Nat) where
  node : List (Position I₁ I₂ Q D)
  supported : publicSupport (offers M step) tree node = true
  root : (tree node).source.Root
  history : root.val = branchNode word (n*D)

def firstFollow (initialLegal : SupportedMovesValid (offers M step) (Position.initial q₀) (Legal M step .component) tree) : FollowState M step tree word 0 where
  node := []
  supported := publicSupport_nil _ _
  root := ⟨[],by rw [(initialLegal [] (publicSupport_nil _ _)).1]; exact Finset.mem_singleton_self []⟩
  history := by simp [branchNode]

def followEndpoint {n : Nat} (st : FollowState M step tree word n) : (tree st.node).source.End :=
  wordScenario st.root (eventBlock word D n)

theorem followEndpoint_history {n : Nat} (st : FollowState M step tree word n) :
    (tree st.node).source.history (followEndpoint M step tree word st) = branchNode word ((n+1)*D) := by
  rw [Position.history,followEndpoint,wordScenario_history]
  change st.root.val ++ _ = _
  rw [st.history,Nat.add_mul,Nat.one_mul]
  exact prefix_append_segment word (n*D) D

def followChoice {n : Nat} (st : FollowState M step tree word n) :
    { P : Position I₁ I₂ Q D // Next M step (tree st.node) P ∧
      (tree st.node).source.history (followEndpoint M step tree word st) ∈ P.histories } := by
  have alive : extensionLive M (tree st.node) (followEndpoint M step tree word st) = true := by
    simp only [extensionLive,decide_eq_true_eq]
    constructor
    · simp [retained,(legal _ st.supported).2.2]
    · rw [followEndpoint_history M step tree word st]
      exact live _
  exact ⟨(next_contains M step _ _ alive).choose,(next_contains M step _ _ alive).choose_spec⟩

def nextFollow {n : Nat} (st : FollowState M step tree word n) : FollowState M step tree word (n+1) := by
  let chosen := followChoice M step tree q₀ legal word live st
  have supported : publicSupport (offers M step) tree (st.node ++ [chosen.val]) = true := by
    simp only [publicSupport_append,st.supported,Bool.true_and,offers,decide_eq_true_eq]
    exact chosen.property.1
  have source : (tree (st.node ++ [chosen.val])).source = chosen.val := by
    simpa only [observableAt,List.getLast?_append,List.getLast?_singleton,Option.or_some,Option.getD_some] using
      (legal _ supported).1
  exact {
    node := st.node ++ [chosen.val]
    supported := supported
    root := ⟨(tree st.node).source.history (followEndpoint M step tree word st),by
      rw [source]; exact chosen.property.2⟩
    history := followEndpoint_history M step tree word st }

def follow : (n : Nat) → FollowState M step tree word n
  | 0 => firstFollow M step tree q₀ word legal
  | n+1 => nextFollow M step tree q₀ legal word live (follow n)

def followBranch (n : Nat) : Position I₁ I₂ Q D :=
  (followChoice M step tree q₀ legal word live (follow M step tree q₀ legal word live n)).val

theorem follow_node (n : Nat) :
    (follow M step tree q₀ legal word live n).node = branchNode (followBranch M step tree q₀ legal word live) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (follow M step tree q₀ legal word live n).node ++ [_] = _
    exact congrArg (fun xs => xs ++ [followBranch M step tree q₀ legal word live n]) ih

include legal live in
/-- Every infinite word with live prefixes occurs in a supported play and
in one compatible run of that play, with exactly its own block segments. -/
theorem component_word_run :
    ∃ branch : Nat → Position I₁ I₂ Q D,
      (∀ n, publicSupport (offers M step) tree (branchNode branch n) = true) ∧
      ∃ run : CompatibleRun tree branch,
        (∀ n, (run.history n).val = branchNode word (n*D)) ∧
        (∀ n, run.word n = eventBlock word D n) := by
  let branch := followBranch M step tree q₀ legal word live
  have nodes := follow_node M step tree q₀ legal word live
  have supported (n : Nat) : publicSupport (offers M step) tree (branchNode branch n) = true := by
    rw [← nodes n]; exact (follow M step tree q₀ legal word live n).supported
  let h (n : Nat) : (tree (branchNode branch n)).source.Root :=
    ⟨(follow M step tree q₀ legal word live n).root.val,by
      rw [← nodes n]; exact (follow M step tree q₀ legal word live n).root.property⟩
  have histories (n : Nat) : (h n).val = branchNode word (n*D) :=
    (follow M step tree q₀ legal word live n).history
  let run : CompatibleRun tree branch := {
    history := h
    word := eventBlock word D
    initial := by simpa [branchNode] using histories 0
    next := by
      intro n
      rw [(legal _ (supported n)).2.2]
      change (h (n+1)).val = (h n).val ++ _
      rw [histories,histories,Nat.add_mul,Nat.one_mul]
      exact (prefix_append_segment word (n*D) D).symm }
  exact ⟨branch,supported,run,histories,fun _ => rfl⟩
end
end Characterisation.ComponentGames.HistoryGame
