/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness

/-! # Executable nonemptiness for finite run-based parity tree automata

A node label contains the original label and the complete successor assignment.
An invalid assignment sets a permanent rejecting flag. The resulting deterministic
monitor is decided by the library's existing finite-policy and finite-orbit search.
The semantic automaton and its regular-run theorem remain `RunParityTreeAutomaton`.
-/

namespace DistributedSynthesis.RunParityTreeAutomaton

variable {Branch Label : Type*} [Fintype Branch] [DecidableEq Branch] [Fintype Label]
  (A : RunParityTreeAutomaton Branch Label)
  [DecidableEq A.State] [∀ q l f, Decidable (A.delta q l f)]

/-- Announce a whole transition before the environment chooses its direction. -/
def transitionMonitor : DeterministicBlockMonitor Branch (Label × (Branch → A.State)) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := A.State × Bool
  stateFinite := inferInstance
  initial := (A.initial, true)
  step s l b := (l.2 b, s.2 && decide (A.delta s.1 l.1 l.2))
  priority s := if s.2 then A.priority s.1 else 1

private def extendBranch [Inhabited Branch] (node : List Branch) : Nat → Branch :=
  fun n => node.getD n default

omit [Fintype Branch] [DecidableEq Branch] in
private theorem branchNode_extend [Inhabited Branch] (node : List Branch) :
    branchNode (extendBranch node) node.length = node := by
  have h : ∀ n, n ≤ node.length → branchNode (extendBranch node) n = node.take n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [show branchNode (extendBranch node) (n + 1) =
          branchNode (extendBranch node) n ++ [node.getD n default] from rfl,
        ih (by omega), List.getD_eq_getElem node default (by omega),
        List.take_add_one, List.getElem?_eq_getElem (by omega)]
      rfl
  simpa using h node.length le_rfl

omit [DecidableEq A.State] in
private theorem safe_of_winning [Inhabited Branch]
    (tree : LabeledTree Branch (Label × (Branch → A.State)))
    (hwin : A.transitionMonitor.WinningTree tree) (node : List Branch) :
    (A.transitionMonitor.control tree node).2 = true := by
  by_contra h
  have hfalse : (A.transitionMonitor.control tree node).2 = false := by simpa using h
  let branch := extendBranch node
  have hpersist : ∀ k,
      (A.transitionMonitor.control tree (branchNode branch (node.length + k))).2 = false := by
    intro k
    induction k with
    | zero => simpa only [Nat.add_zero, branch, branchNode_extend] using hfalse
    | succ k ih =>
      rw [Nat.add_succ, branchNode, A.transitionMonitor.control_append]
      change Bool.and _ _ = false
      rw [ih]
      rfl
  apply not_natSeqMinEvenParity_of_eventually_one _ node.length ?_ (hwin branch)
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  change (if _ then _ else 1) = 1
  rw [hpersist k]
  rfl

omit [DecidableEq A.State] in
/-- Successor annotations preserve the entire tree language, not just nonemptiness. -/
theorem transitionMonitor_accepts_iff [Inhabited Branch] (inputTree : LabeledTree Branch Label) :
    (∃ successors : TreeNode Branch → (Branch → A.State),
      A.transitionMonitor.toRunAutomaton.acceptsTree (fun node => (inputTree node, successors node))) ↔
      A.acceptsTree inputTree := by
  constructor
  · rintro ⟨successors, ht⟩
    let tree := fun node => (inputTree node, successors node)
    have hwin := (A.transitionMonitor.acceptsTree_iff_winningTree tree).mp ht
    have hsafe := safe_of_winning A tree hwin
    let run := fun node => (A.transitionMonitor.control tree node).1
    refine ⟨run, ⟨rfl, ?_⟩, ?_⟩
    · intro node
      have hc := hsafe (node ++ [default])
      rw [A.transitionMonitor.control_append] at hc
      change (_ && decide (A.delta (run node) (tree node).1 (tree node).2)) = true at hc
      simp only [Bool.and_eq_true] at hc
      have hd := of_decide_eq_true hc.2
      have hchildren : (fun b => run (node ++ [b])) = (tree node).2 := by
        funext b
        exact congrArg Prod.fst (A.transitionMonitor.control_append tree node b)
      rw [hchildren]
      exact hd
    · intro branch
      have h := hwin branch
      have heq : (fun n => A.transitionMonitor.priority
          (A.transitionMonitor.control tree (branchNode branch n))) =
          fun n => A.priority (run (branchNode branch n)) := by
        funext n
        change (if _ then _ else 1) = _
        rw [hsafe]
        rfl
      rwa [heq] at h
  · rintro ⟨run, ⟨hinit, hstep⟩, hparity⟩
    let tree := inputTree
    refine ⟨fun node b => run (node ++ [b]), fun node => (run node, true), ⟨?_, ?_⟩, ?_⟩
    · exact congrArg (fun q => (q, true)) hinit
    · intro node b
      change (run (node ++ [b]), true) =
        (run (node ++ [b]), true && decide (A.delta (run node) (tree node)
          (fun b => run (node ++ [b]))))
      rw [decide_eq_true (hstep node)]
      rfl
    · exact hparity

omit [DecidableEq A.State] in
/-- Packing nondeterministic successor choices into labels preserves nonemptiness. -/
theorem transitionMonitor_nonempty_iff [Inhabited Branch] :
    (∃ tree, A.transitionMonitor.toRunAutomaton.acceptsTree tree) ↔
      ∃ tree, A.acceptsTree tree := by
  constructor
  · rintro ⟨tree, accepts⟩
    refine ⟨fun node => (tree node).1, (A.transitionMonitor_accepts_iff _).mp ?_⟩
    exact ⟨fun node => (tree node).2, accepts⟩
  · rintro ⟨tree, accepts⟩
    obtain ⟨successors, accepts⟩ := (A.transitionMonitor_accepts_iff tree).mpr accepts
    exact ⟨fun node => (tree node, successors node), accepts⟩

/-- Finite transition data use the same decision backend as deterministic monitors. -/
def nonemptyDecidable [Inhabited Branch] : Decidable (∃ tree, A.acceptsTree tree) :=
  letI : DecidableEq A.transitionMonitor.State := inferInstanceAs (DecidableEq (A.State × Bool))
  letI := TreeNonemptiness.nonemptyDecidable A.transitionMonitor
  decidable_of_iff _ A.transitionMonitor_nonempty_iff

end DistributedSynthesis.RunParityTreeAutomaton
