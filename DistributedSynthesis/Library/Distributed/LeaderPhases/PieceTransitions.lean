/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RecentPieceInterfaces
import DistributedSynthesis.Formalizations.Lemma.LemJointviewsdeterminehistory

/-! Recent pieces never merge in one round. Across distinct pieces of one
component, only a nonreceiving continuation of the old coordinator can retain
a shared view. These are statements about actual histories and views. -/
namespace Characterisation
open DistributedSynthesis

theorem joint_env_history {I₁ I₂ : Type*} (h k : EnvHistory I₁ I₂)
    (one : currentView .one h = currentView .one k)
    (two : currentView .two h = currentView .two k) : h = k := by
  obtain ⟨graphs,inputsOne,inputsTwo⟩ := jointViews_determine_inputGraphHistory h k one two
  have len : h.length = k.length := by
    have eq := congrArg List.length graphs
    simpa [History.graphSequence] using eq
  apply List.ext_getElem len
  intro i hi hk
  have eg := congrArg (fun w => w[i]?) graphs
  have eo := congrArg (fun w => w[i]?) inputsOne
  have et := congrArg (fun w => w[i]?) inputsTwo
  simp [History.graphSequence,hi,hk] at eg eo et
  have records : ∀ a b : RoundRecord I₁ I₂ Graph Unit Unit,
      a.graph = b.graph → a.inputOne = b.inputOne → a.inputTwo = b.inputTwo → a = b := by
    intro a b g x y
    cases a; cases b
    simp_all
  exact records _ _ eg eo et

/-- A recent child link has both parents in one recent piece. A receiving
child determines the whole parent history; a nonreceiving child retains a
recent parent view. No holes hypothesis is needed. -/
theorem recent_extension_parent {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (r s : RoundRecord I₁ I₂ Graph Unit Unit)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (adj : RecentAdjacent d (h++[r]) (k++[s])) : RecentConnected P d h k := by
  obtain ⟨q,eq,young⟩ := adj
  change currentView q (History.append h r) = currentView q (History.append k s) at eq
  change silentAge (currentView q (History.append h r)) < d at young
  cases q
  · rw [currentView_one_append,currentView_one_append] at eq
    rw [currentView_one_append] at young
    cases rg : r.graph <;> cases sg : s.graph <;>
      simp only [rg,sg,Proc.other,View.recv.injEq,View.noRecv.injEq,
        reduceCtorEq,silentAge] at eq young
    all_goals first
      | contradiction
      | have same := joint_env_history h k eq.1 eq.2.2.1
        subst k
        exact .refl
      | exact Relation.ReflTransGen.single ⟨liveH,liveK,.one,eq.1,by omega⟩
  · rw [currentView_two_append,currentView_two_append] at eq
    rw [currentView_two_append] at young
    cases rg : r.graph <;> cases sg : s.graph <;>
      simp only [rg,sg,Proc.other,View.recv.injEq,View.noRecv.injEq,
        reduceCtorEq,silentAge] at eq young
    all_goals first
      | contradiction
      | have same := joint_env_history h k eq.2.2.1 eq.1
        subst k
        exact .refl
      | exact Relation.ReflTransGen.single ⟨liveH,liveK,.two,eq.1,by omega⟩

theorem recentAdjacent_parent {I₁ I₂ : Type*} (P : List Graph → Prop)
    (closed : PrefixClosed P) (d : Nat) (h k : EnvHistory I₁ I₂)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (adj : RecentAdjacent d h k) : RecentConnected P d h.dropLast k.dropLast := by
  have inputAdj : InputAdjacent h k := by
    obtain ⟨q,eq,_⟩ := adj
    cases q <;> [exact Or.inl eq; exact Or.inr eq]
  have len : h.length = k.length := by
    have eq := adjacent_same_depth (inputAdjacent_projects inputAdj)
    simpa [History.graphSequence] using eq
  change List.length h = List.length k at len
  cases h using List.reverseRecOn with
  | nil =>
    have empty : k = [] := List.length_eq_zero_iff.mp (by simpa using len.symm)
    subst k
    exact .refl
  | append_singleton h r =>
    cases k using List.reverseRecOn with
    | nil => simp at len
    | append_singleton k s =>
      simp only [List.dropLast_concat]
      have parentH := live_parent P closed liveH
      have parentK := live_parent P closed liveK
      simp only [← graphSequence_dropLast, List.dropLast_concat] at parentH parentK
      exact recent_extension_parent P d h k r s parentH parentK adj

/-- A recent child piece has a unique parent recent piece. -/
theorem recentConnected_parent {I₁ I₂ : Type*} (P : List Graph → Prop)
    (closed : PrefixClosed P) (d : Nat) {h k : EnvHistory I₁ I₂}
    (conn : RecentConnected P d h k) : RecentConnected P d h.dropLast k.dropLast := by
  induction conn with
  | refl => exact .refl
  | @tail a b conn step ih =>
    exact ih.trans (recentAdjacent_parent P closed d a b step.1 step.2.1 step.2.2)

/-- The other process's view separates distinct recent pieces. -/
theorem other_view_separates_pieces {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (p : Proc)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (recent : RecentOther P d (History.graphSequence h) p)
    (separate : ¬ RecentConnected P d h k) : currentView p.other h ≠ currentView p.other k := by
  intro eq
  have owner := (shared_view_between_pieces_is_old P d h k p p.other
    liveH liveK recent separate eq).1
  cases p <;> simp [Proc.other] at owner

/-- With process one selected, cross-piece equality persists exactly on
rightward rounds with equal process-one inputs and equal old leader views.
The new view of process two always distinguishes the pieces. -/
theorem cross_piece_right_transition {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (r s : RoundRecord I₁ I₂ Graph Unit Unit)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (recent : RecentOther P d (History.graphSequence h) .one)
    (separate : ¬ RecentConnected P d h k) :
    (currentView .one (h++[r]) = currentView .one (k++[s]) ↔
      r.graph = .right ∧ s.graph = .right ∧
      currentView .one h = currentView .one k ∧ r.inputOne = s.inputOne) ∧
    currentView .two (h++[r]) ≠ currentView .two (k++[s]) := by
  have different := other_view_separates_pieces P d h k .one liveH liveK recent separate
  change currentView .two h ≠ currentView .two k at different
  change (_ ↔ _) ∧ currentView .two (History.append h r) ≠ currentView .two (History.append k s)
  change (currentView .one (History.append h r) = currentView .one (History.append k s) ↔ _) ∧ _
  rw [currentView_one_append,currentView_one_append,currentView_two_append,currentView_two_append]
  cases rg : r.graph <;> cases sg : s.graph <;>
    simp [Proc.other,different]

theorem cross_piece_left_transition {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (r s : RoundRecord I₁ I₂ Graph Unit Unit)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (recent : RecentOther P d (History.graphSequence h) .two)
    (separate : ¬ RecentConnected P d h k) :
    (currentView .two (h++[r]) = currentView .two (k++[s]) ↔
      r.graph = .left ∧ s.graph = .left ∧
      currentView .two h = currentView .two k ∧ r.inputTwo = s.inputTwo) ∧
    currentView .one (h++[r]) ≠ currentView .one (k++[s]) := by
  have different := other_view_separates_pieces P d h k .two liveH liveK recent separate
  change currentView .one h ≠ currentView .one k at different
  change (_ ↔ _) ∧ currentView .one (History.append h r) ≠ currentView .one (History.append k s)
  change (currentView .two (History.append h r) = currentView .two (History.append k s) ↔ _) ∧ _
  rw [currentView_two_append,currentView_two_append,currentView_one_append,currentView_one_append]
  cases rg : r.graph <;> cases sg : s.graph <;>
    simp [Proc.other,different]

end Characterisation
