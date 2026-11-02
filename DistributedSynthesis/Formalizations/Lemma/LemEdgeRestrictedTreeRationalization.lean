/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton

/-!
# Rational trees with a parent-to-child consistency law

This file adds the depth-one safety condition needed by the guarded-entry
construction.  A node commits finite data in its label; after the environment
chooses a branch, the child label must realize the corresponding commitment.

The restriction is deliberately symmetric.  It stores the actual parent
label and branch, not a bit saying which process is the strict leader.  Thus
it can check a local overlap law without making that information available to
either distributed process.
-/

namespace DistributedSynthesis

universe u v w

namespace DeterministicBlockMonitor

variable {Branch : Type u} {Alphabet : Type v}

/-- Finite memory used to check an edge law one level after the edge is taken. -/
abbrev EdgeRestrictionState
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet) :=
  M.State × Option (Alphabet × Branch) × Bool

private def edgeCheck
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (pending : Option (Alphabet × Branch)) (label : Alphabet) : Bool :=
  match pending with
  | none => true
  | some parent => decide (Allowed (parent.1, parent.2, label))

/--
Add a sticky parent-to-child law to a deterministic monitor.  The law is
checked when the child label is read.  A violation is therefore visible one
transition later, which is harmless on infinite branches.
-/
noncomputable def restrictEdges
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed] :
    DeterministicBlockMonitor.{u, v, max u v w} Branch Alphabet := by
  classical
  letI := M.branchFinite
  letI := M.alphabetFinite
  letI := M.stateFinite
  exact {
    branchFinite := M.branchFinite
    alphabetFinite := M.alphabetFinite
    State := EdgeRestrictionState M
    stateFinite := inferInstance
    initial := (M.initial, none, true)
    step := fun state label branch =>
      (M.step state.1 label branch,
        some (label, branch),
        state.2.2 && edgeCheck Allowed state.2.1 label)
    priority := fun state => if state.2.2 then M.priority state.1 + 2 else 1
  }

/-- Pointwise formulation of the local edge law on a labeled tree. -/
def TreeEdgesAllowed
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    (tree : LabeledTree Branch Alphabet) : Prop :=
  ∀ node branch, Allowed (tree node, branch, tree (node ++ [branch]))

theorem restrictEdges_control_base
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet) (node : TreeNode Branch) :
    ((M.restrictEdges Allowed).control tree node).1 = M.control tree node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [(M.restrictEdges Allowed).control_append, M.control_append]
      exact congrArg (fun state => M.step state (tree node) branch) ih

theorem restrictEdges_control_pending_append
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet) (node : TreeNode Branch) (branch : Branch) :
    ((M.restrictEdges Allowed).control tree (node ++ [branch])).2.1 =
      some (tree node, branch) := by
  rw [(M.restrictEdges Allowed).control_append]
  rfl

theorem restrictEdges_control_safe_of_all
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (hall : TreeEdgesAllowed Allowed tree) :
    ∀ node, ((M.restrictEdges Allowed).control tree node).2.2 = true := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node branch ih =>
      rw [(M.restrictEdges Allowed).control_append]
      change Bool.and _ (edgeCheck Allowed _ _) = true
      rw [ih]
      cases node using List.reverseRecOn with
      | nil =>
          change edgeCheck Allowed none (tree []) = true
          rfl
      | append_singleton parent incoming =>
          rw [M.restrictEdges_control_pending_append Allowed]
          simp only [edgeCheck, Bool.true_and, decide_eq_true_eq]
          exact hall parent incoming

theorem restrictEdges_control_safe_false_persists
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (node : TreeNode Branch)
    (hfalse : ((M.restrictEdges Allowed).control tree node).2.2 = false) :
    ∀ suffix,
      ((M.restrictEdges Allowed).control tree (node ++ suffix)).2.2 = false := by
  intro suffix
  induction suffix using List.reverseRecOn with
  | nil => simpa using hfalse
  | append_singleton suffix branch ih =>
      rw [← List.append_assoc, (M.restrictEdges Allowed).control_append]
      change Bool.and _ (edgeCheck Allowed _ _) = false
      rw [ih]
      rfl

theorem restrictEdges_winningTree_of
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (hwin : M.WinningTree tree)
    (hall : TreeEdgesAllowed Allowed tree) :
    (M.restrictEdges Allowed).WinningTree tree := by
  intro branch
  have hsafe := M.restrictEdges_control_safe_of_all Allowed tree hall
  have hbase := hwin branch
  have heq :
      (fun n => (M.restrictEdges Allowed).priority
        ((M.restrictEdges Allowed).control tree (branchNode branch n))) =
      fun n => M.priority (M.control tree (branchNode branch n)) + 2 := by
    funext n
    change (if _ then _ else 1) = _
    rw [hsafe, if_pos rfl, M.restrictEdges_control_base Allowed]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hbase

private def edgeBranchExtending [Inhabited Branch]
    (node : TreeNode Branch) : Nat -> Branch :=
  fun n => node.getD n default

private theorem edgeBranchNode_getD_basic [Inhabited Branch]
    (node : TreeNode Branch) : ∀ n, n ≤ node.length ->
    branchNode (edgeBranchExtending node) n = node.take n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [show branchNode (edgeBranchExtending node) (n + 1) =
          branchNode (edgeBranchExtending node) n ++ [node.getD n default] from rfl,
        ih (by omega), List.getD_eq_getElem node default (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl

private theorem edgeBranchNode_length [Inhabited Branch]
    (node : TreeNode Branch) :
    branchNode (edgeBranchExtending node) node.length = node := by
  rw [edgeBranchNode_getD_basic node node.length (Nat.le_refl _), List.take_length]

/-- Winning the edge restriction is exactly base winning plus the edge law. -/
theorem restrictEdges_winningTree_iff
    [Inhabited Branch]
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet) :
    (M.restrictEdges Allowed).WinningTree tree ↔
      M.WinningTree tree ∧ TreeEdgesAllowed Allowed tree := by
  constructor
  · intro hrestricted
    have hall : TreeEdgesAllowed Allowed tree := by
      intro node branch
      by_contra hnot
      let child := node ++ [branch]
      let witness := child ++ [(default : Branch)]
      have hfalse :
          ((M.restrictEdges Allowed).control tree witness).2.2 = false := by
        rw [(M.restrictEdges Allowed).control_append]
        change Bool.and _ (edgeCheck Allowed _ _) = false
        rw [M.restrictEdges_control_pending_append Allowed]
        simp only [edgeCheck]
        rw [decide_eq_false (by simpa [child] using hnot)]
        simp
      let infiniteBranch := edgeBranchExtending witness
      have hprefix : branchNode infiniteBranch witness.length = witness :=
        edgeBranchNode_length witness
      have hpersist : ∀ k,
          ((M.restrictEdges Allowed).control tree
            (branchNode infiniteBranch (witness.length + k))).2.2 = false := by
        intro k
        induction k with
        | zero => simpa [hprefix] using hfalse
        | succ k ih =>
            rw [Nat.add_succ]
            change
              ((M.restrictEdges Allowed).control tree
                (branchNode infiniteBranch (witness.length + k) ++
                [infiniteBranch (witness.length + k)])).2.2 = false
            rw [(M.restrictEdges Allowed).control_append]
            change Bool.and _ (edgeCheck Allowed _ _) = false
            rw [ih]
            rfl
      have heventual : ∀ n, witness.length ≤ n ->
          (M.restrictEdges Allowed).priority
            ((M.restrictEdges Allowed).control tree
              (branchNode infiniteBranch n)) = 1 := by
        intro n hn
        obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
        change (if _ then _ else 1) = 1
        rw [hpersist k]
        rfl
      exact not_natSeqMinEvenParity_of_eventually_one _ witness.length heventual
        (hrestricted infiniteBranch)
    refine ⟨?_, hall⟩
    intro branch
    have hr := hrestricted branch
    have hsafe := M.restrictEdges_control_safe_of_all Allowed tree hall
    have heq :
        (fun n => (M.restrictEdges Allowed).priority
          ((M.restrictEdges Allowed).control tree (branchNode branch n))) =
        fun n => M.priority (M.control tree (branchNode branch n)) + 2 := by
      funext n
      change (if _ then _ else 1) = _
      rw [hsafe, if_pos rfl, M.restrictEdges_control_base Allowed]
    rw [heq] at hr
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hr
  · rintro ⟨hwin, hall⟩
    exact M.restrictEdges_winningTree_of Allowed tree hwin hall

/--
Rabin rationalization preserves any decidable depth-one edge law.  This is
the reusable finite-state extraction theorem needed by guarded handoffs.
-/
theorem exists_transitionRational_of_winning_of_edgesAllowed
    [Inhabited Branch]
    (M : DeterministicBlockMonitor.{u, v, w} Branch Alphabet)
    (Allowed : Alphabet × Branch × Alphabet -> Prop)
    [DecidablePred Allowed]
    (tree : LabeledTree Branch Alphabet)
    (hwin : M.WinningTree tree)
    (hall : TreeEdgesAllowed Allowed tree) :
    ∃ controller : TransitionRationalTree.{u, v, max u v w} Branch Alphabet,
      M.WinningTree controller.labeledTree ∧
        TreeEdgesAllowed Allowed controller.labeledTree := by
  classical
  letI := M.branchFinite
  letI := M.alphabetFinite
  letI := M.stateFinite
  let restricted := M.restrictEdges Allowed
  have hrestricted : restricted.WinningTree tree :=
    M.restrictEdges_winningTree_of Allowed tree hwin hall
  rcases restricted.toRunAutomaton.exists_transitionRational_accepted
      ⟨tree, (restricted.acceptsTree_iff_winningTree tree).mpr hrestricted⟩ with
    ⟨controller, haccepts⟩
  have hrestricted' : restricted.WinningTree controller.labeledTree :=
    (restricted.acceptsTree_iff_winningTree controller.labeledTree).mp haccepts
  have hsplit :=
    (M.restrictEdges_winningTree_iff Allowed controller.labeledTree).mp hrestricted'
  exact ⟨controller, hsplit⟩

end DeterministicBlockMonitor

end DistributedSynthesis
