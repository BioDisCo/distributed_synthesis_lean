/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ExecutableReverse
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReadback

/-! Unique occurrence of live histories in an uncompressed component tree.
This is the first paragraph of the forward bounded-representation proof.
The geometric and public-support machinery is reused from the games; state
labels are the actual block-automaton successors throughout.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- Every child edge has an actual source edge and a full length-D suffix. -/
theorem ComponentSuccessor.previous {m : Move I₁ I₂ O₁ O₂ B.State D}
    {P : Position I₁ I₂ B.State D} (next : ComponentSuccessor B M m P) (h : P.Root) :
    ∃ a : m.source.Root, ∃ u : BlockInput I₁ I₂ D, h.val = a.val ++ u.val := by
  obtain ⟨C, _, _, histories, _⟩ := next
  have mem : h.val ∈ C.image m.source.history := by rw [← histories]; exact h.property
  obtain ⟨e, _, eh⟩ := Finset.mem_image.mp mem
  exact ⟨closingLayerRoot D e, scenarioWord D e, eh.symm.trans (scenarioWord_history m.source.past D e)⟩

/-- Full children sharing even one vertex are identical, with their labels. -/
theorem ComponentSuccessor.unique_of_view (m : Move I₁ I₂ O₁ O₂ B.State D)
    (P R : Position I₁ I₂ B.State D)
    (first : ComponentSuccessor B M m P) (second : ComponentSuccessor B M m R)
    (h : P.Root) (k : R.Root) (p : Proc)
    (same : currentView p h.val = currentView p k.val) : P = R := by
  obtain ⟨C, cc, pc, hc, sc⟩ := first
  obtain ⟨L, cl, pl, hl, sl⟩ := second
  have hm : h.val ∈ C.image m.source.history := by rw [← hc]; exact h.property
  have km : k.val ∈ L.image m.source.history := by rw [← hl]; exact k.property
  obtain ⟨e, he, eh⟩ := Finset.mem_image.mp hm
  obtain ⟨f, hf, fk⟩ := Finset.mem_image.mp km
  obtain ⟨a, alive, mask⟩ := cl
  have reach := (mask f).mp hf
  simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq] at reach
  let graph := closingObservationGraph (closingLayerShape m.source.shape D) (extensionLive M m)
  have ef : graph.Reachable f e := by
    by_cases eq : f = e
    · rw [eq]
    apply SimpleGraph.Adj.reachable
    refine ⟨eq, reach.1, component_member_live M m C cc e he, p, Or.inl ?_⟩
    apply (closingLayerShape_exact m.source.past _ (extractInputShape_exact m.source.past) D p f e).mpr
    change currentView p (m.source.history f) = currentView p (m.source.history e)
    rw [eh, fk]
    exact same.symm
  have inL : e ∈ L := (mask e).mpr (by
    simp only [closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨component_member_live M m C cc e he, reach.2.trans ef⟩)
  have eq : C = L := ExecutableHistories.components_eq_of_common M m C L cc ⟨a, alive, mask⟩ e he inL
  apply position_ext P R (pc.trans pl.symm) (by rw [hc, hl, eq])
  intro x y xy
  have inside : x.val ∈ C.image m.source.history := by rw [← hc]; exact x.property
  obtain ⟨t, ht, th⟩ := Finset.mem_image.mp inside
  exact (sc x ⟨t, ht⟩ th.symm).trans (sl y ⟨t, eq ▸ ht⟩ (xy.symm.trans th.symm)).symm

/-- Every allowed extension belongs to one of the full child components. -/
theorem UncompressedNode.child_contains (N : UncompressedNode B M)
    (a : N.position.Root) (u : BlockInput I₁ I₂ D)
    (live : M.eval (History.graphSequence (a.val ++ u.val)) ∈ M.accept) :
    ∃ P, N.Successor P ∧ a.val ++ u.val ∈ P.histories := by
  let e := wordScenario a u
  have alive : extensionLive M N.move e = true := by
    change extensionLive M ⟨N.position, N.rule, id⟩ e = true
    rw [extensionLive_identity]
    exact decide_eq_true (by simpa only [e, Position.history, wordScenario_history, Position.past] using live)
  let C := Finset.univ.filter (fun x => closingComponentMask
    (closingLayerShape N.position.shape D) (extensionLive M N.move) e x = true)
  have component : IsComponent M N.move C :=
    ⟨e, alive, fun x => by
      change x ∈ C ↔ _
      simp only [C, UncompressedNode.move, Finset.mem_filter, Finset.mem_univ, true_and]
      rfl⟩
  have member : e ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_univ, true_and, closingComponentMask,
      alive, Bool.true_and, decide_eq_true_eq]
    exact SimpleGraph.Reachable.refl _
  obtain ⟨P, phase, histories, _, states⟩ := component_position M B N.move C N.valid component
  refine ⟨P, ⟨C, component, phase, histories, states⟩, ?_⟩
  rw [histories]
  exact Finset.mem_image.mpr ⟨e, member, wordScenario_history N.position.past a u⟩

namespace UncompressedTree
variable {B M} (tree : UncompressedTree B M) (valid : tree.Valid)

include valid in
theorem position_phase (node : List (Position I₁ I₂ B.State D))
    (supported : publicSupport UncompressedNode.offers tree node = true) :
    (tree node).position.phase = node.length := by
  induction node using List.reverseRecOn with
  | nil => rw [valid [] supported]; rfl
  | append_singleton node P ih =>
    have both : publicSupport UncompressedNode.offers tree node = true ∧
        UncompressedNode.offers (tree node) P = true := by
      simpa only [publicSupport_append, Bool.and_eq_true] using supported
    have next : (tree node).Successor P := of_decide_eq_true both.2
    have source : (tree (node ++ [P])).position = P := by simpa [observableAt] using valid _ supported
    rw [source, next.choose_spec.2.1]
    change (tree node).position.phase + 1 = _
    rw [ih both.1, List.length_append, List.length_singleton]

include valid in
theorem nodes_equal_of_view (node other : List (Position I₁ I₂ B.State D))
    (lengths : node.length = other.length)
    (supported : publicSupport UncompressedNode.offers tree node = true)
    (otherSupported : publicSupport UncompressedNode.offers tree other = true)
    (h : (tree node).position.Root) (k : (tree other).position.Root) (p : Proc)
    (same : currentView p h.val = currentView p k.val) : node = other := by
  induction node using List.reverseRecOn generalizing other with
  | nil =>
    have empty : other = [] := by simpa using lengths.symm
    exact empty.symm
  | append_singleton node P ih =>
    cases other using List.reverseRecOn with
    | nil => simp at lengths
    | append_singleton other R =>
      have first : publicSupport UncompressedNode.offers tree node = true ∧
          UncompressedNode.offers (tree node) P = true := by
        simpa only [publicSupport_append, Bool.and_eq_true] using supported
      have second : publicSupport UncompressedNode.offers tree other = true ∧
          UncompressedNode.offers (tree other) R = true := by
        simpa only [publicSupport_append, Bool.and_eq_true] using otherSupported
      have nextP : (tree node).Successor P := of_decide_eq_true first.2
      have nextR : (tree other).Successor R := of_decide_eq_true second.2
      have sourceP : (tree (node ++ [P])).position = P := by simpa [observableAt] using valid _ supported
      have sourceR : (tree (other ++ [R])).position = R := by simpa [observableAt] using valid _ otherSupported
      let hp : P.Root := ⟨h.val, by simpa only [Position.Root, sourceP] using h.property⟩
      let kr : R.Root := ⟨k.val, by simpa only [Position.Root, sourceR] using k.property⟩
      obtain ⟨a, u, hu⟩ := ComponentSuccessor.previous B M nextP hp
      obtain ⟨b, v, kv⟩ := ComponentSuccessor.previous B M nextR kr
      have oldSame : currentView p a.val = currentView p b.val := by
        have views : currentView p (a.val ++ u.val) = currentView p (b.val ++ v.val) := by
          rw [← hu, ← kv]; exact same
        have lu := lagView_suffix p a.val u.val
        have lv := lagView_suffix p b.val v.val
        rw [u.property] at lu
        rw [v.property] at lv
        exact lu.symm.trans ((congrArg (lagView D) views).trans lv)
      have oldEq := ih other (by simpa using lengths) first.1 second.1 a b oldSame
      subst other
      have positions := ComponentSuccessor.unique_of_view B M (tree node).move P R nextP nextR hp kr p same
      rw [positions]

/-- The address and edge containing a complete-block history. -/
structure Occurrence (words : List (BlockInput I₁ I₂ D)) where
  node : List (Position I₁ I₂ B.State D)
  supported : publicSupport UncompressedNode.offers tree node = true
  depth : node.length = words.length
  member : blockHistory words ∈ (tree node).position.histories

include valid in
theorem occurrence_unique {words : List (BlockInput I₁ I₂ D)}
    (x y : tree.Occurrence words) : x.node = y.node :=
  nodes_equal_of_view tree valid x.node y.node (x.depth.trans y.depth.symm)
    x.supported y.supported ⟨_, x.member⟩ ⟨_, y.member⟩ .one rfl

include valid in
theorem occurrence_nil : Nonempty (tree.Occurrence []) := by
  refine ⟨⟨[], publicSupport_nil _ _, rfl, ?_⟩⟩
  rw [valid [] (publicSupport_nil _ _)]
  exact Finset.mem_singleton_self _

include valid in
theorem occurrence_extend {words : List (BlockInput I₁ I₂ D)}
    (x : tree.Occurrence words) (u : BlockInput I₁ I₂ D)
    (live : M.eval (History.graphSequence (blockHistory (words ++ [u]))) ∈ M.accept) :
    ∃ y : tree.Occurrence (words ++ [u]), ∃ P, y.node = x.node ++ [P] := by
  obtain ⟨P, next, member⟩ := UncompressedNode.child_contains B M (tree x.node) ⟨_, x.member⟩ u
    (by simpa only [blockHistory_append] using live)
  have support : publicSupport UncompressedNode.offers tree (x.node ++ [P]) = true := by
    rw [publicSupport_append, x.supported, Bool.true_and]
    exact decide_eq_true next
  have source : (tree (x.node ++ [P])).position = P := by simpa [observableAt] using valid _ support
  exact ⟨⟨x.node ++ [P], support, by simp only [List.length_append, List.length_singleton, x.depth],
    by rw [source, blockHistory_append]; exact member⟩, P, rfl⟩

include valid in
/-- No extra coverage hypothesis: recognizer correctness and prefix closure
of LivePrefix provide every allowed block-boundary history. -/
theorem occurrence_of_live (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (words : List (BlockInput I₁ I₂ D))
    (live : M.eval (History.graphSequence (blockHistory words)) ∈ M.accept) :
    Nonempty (tree.Occurrence words) := by
  induction words using List.reverseRecOn with
  | nil => exact occurrence_nil tree valid
  | append_singleton words u ih =>
    have parent : M.eval (History.graphSequence (blockHistory words)) ∈ M.accept := by
      apply (recognizes _).mp
      have alive := (recognizes _).mpr live
      rw [blockHistory_append, History.graphSequence, List.map_append] at alive
      exact livePrefix_closed A _ _ alive
    obtain ⟨x⟩ := ih parent
    obtain ⟨y, _⟩ := occurrence_extend tree valid x u live
    exact ⟨y⟩

theorem state_at_equal_nodes {node other : List (Position I₁ I₂ B.State D)}
    (eq : node = other) (h : (tree node).position.Root) (k : (tree other).position.Root)
    (history : h.val = k.val) : (tree node).position.state h = (tree other).position.state k := by
  subst other
  exact congrArg (tree node).position.state (Subtype.ext history)

/-- The original tree's state q_U on a complete-block history. The fallback
is used only outside the live domain and cannot affect the rank proof. -/
def stateOf (words : List (BlockInput I₁ I₂ D)) : B.State :=
  if ex : Nonempty (tree.Occurrence words) then
    let x := Classical.choice ex
    (tree x.node).position.state ⟨_, x.member⟩
  else B.initial

include valid in
theorem stateOf_eq {words : List (BlockInput I₁ I₂ D)} (x : tree.Occurrence words) :
    tree.stateOf words = (tree x.node).position.state ⟨_, x.member⟩ := by
  unfold stateOf
  split
  · rename_i ex
    dsimp only
    have eq := occurrence_unique tree valid (Classical.choice ex) x
    exact state_at_equal_nodes tree eq _ _ rfl
  · rename_i ex
    exact False.elim (ex ⟨x⟩)

include valid in
/-- Every infinite live sequence of complete blocks induces one supported
branch and one run with exactly those histories and state labels. -/
theorem live_word_run (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (word : Nat → BlockInput I₁ I₂ D)
    (live : ∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) :
    ∃ branch : Nat → Position I₁ I₂ B.State D,
      (∀ n, publicSupport UncompressedNode.offers tree (branchNode branch n) = true) ∧
      ∃ run : tree.Run branch,
        (∀ n, (run.history n).val = blockHistory (branchNode word n)) ∧
        (∀ n, (tree (branchNode branch n)).position.state (run.history n) = tree.stateOf (branchNode word n)) := by
  let x n := Classical.choice (occurrence_of_live tree valid A recognizes (branchNode word n) (live n))
  have advances n : ∃ P, (x (n+1)).node = (x n).node ++ [P] := by
    obtain ⟨y, P, eq⟩ := occurrence_extend tree valid (x n) (word n) (live (n+1))
    exact ⟨P, (occurrence_unique tree valid (x (n+1)) y).trans eq⟩
  let branch n := (advances n).choose
  have nodes n : branchNode branch n = (x n).node := by
    induction n with
    | zero =>
      have depth := (x 0).depth
      have empty : (x 0).node = [] := by simpa only [TreeNonemptiness.branch_length, List.length_eq_zero_iff] using depth
      exact empty.symm
    | succ n ih =>
      change branchNode branch n ++ [branch n] = _
      rw [ih]
      exact (advances n).choose_spec.symm
  have support n : publicSupport UncompressedNode.offers tree (branchNode branch n) = true := by
    rw [nodes]; exact (x n).supported
  let histories n : (tree (branchNode branch n)).position.Root :=
    ⟨blockHistory (branchNode word n), by rw [nodes]; exact (x n).member⟩
  let run : tree.Run branch :=
    { history := histories
      word := word
      initial := rfl
      next := fun n => blockHistory_append (branchNode word n) (word n) }
  refine ⟨branch, support, run, fun _ => rfl, ?_⟩
  intro n
  have eq := stateOf_eq tree valid (x n)
  rw [eq]
  change (tree (branchNode branch n)).position.state (histories n) = _
  exact state_at_equal_nodes tree (nodes n) _ _ rfl

include valid in
theorem stateOf_accepts (accepting : tree.Accepting) (A : Set (Nat → Graph))
    (recognizes : ∀ h, LivePrefix A h ↔ M.eval h ∈ M.accept)
    (word : Nat → BlockInput I₁ I₂ D)
    (live : ∀ n, M.eval (History.graphSequence (blockHistory (branchNode word n))) ∈ M.accept) :
    NatSeqMinEvenParity (fun n => B.priority (tree.stateOf (branchNode word n))) := by
  obtain ⟨branch, support, run, _, labels⟩ := live_word_run tree valid A recognizes word live
  simpa only [labels] using accepting.2 branch support run

end UncompressedTree
end
end Characterisation.ComponentTrees
