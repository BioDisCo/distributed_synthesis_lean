/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness

/-! # Exactly one marked tree node

A searching state follows one child until it reaches the marker. All other
subtrees forbid markers. Odd priority on the searching state rules out an
infinite unsuccessful search. -/

namespace DistributedSynthesis.TreeSingleton
variable {Branch Alphabet : Type*} [DecidableEq Branch]
variable (marked : Alphabet → Bool)

def automaton : RunParityTreeAutomaton Branch Alphabet where
  State := Bool
  stateFinite := inferInstance
  initial := true
  delta q a next := if q then
    if marked a then ∀ b, next b = false
    else ∃ d, ∀ b, next b = decide (b = d)
    else marked a = false ∧ ∀ b, next b = false
  priority q := if q then 1 else 0

section Run
variable {marked} {tree : LabeledTree Branch Alphabet} {run : TreeNode Branch → Bool}
variable (legal : (automaton marked).IsRun tree run)
include legal

private theorem inactive (node : TreeNode Branch) (h : run node = false) :
    marked (tree node) = false ∧ ∀ b, run (node ++ [b]) = false := by
  simpa only [automaton, h, Bool.false_eq_true, ↓reduceIte] using legal.2 node

private theorem inactive_descendants (node rest : TreeNode Branch) (h : run node = false) :
    marked (tree (node ++ rest)) = false := by
  induction rest generalizing node with
  | nil => simpa using (inactive legal node h).1
  | cons b rest ih =>
    simpa only [List.append_assoc, List.singleton_append] using
      ih (node ++ [b]) ((inactive legal node h).2 b)

private theorem active_of_descendant (node rest : TreeNode Branch)
    (h : marked (tree (node ++ rest)) = true) : run node = true := by
  cases hq : run node
  · have := inactive_descendants legal node rest hq
    rw [h] at this
    contradiction
  · rfl

private theorem marked_children (node : TreeNode Branch) (h : marked (tree node) = true) :
    ∀ b, run (node ++ [b]) = false := by
  have active := active_of_descendant legal node [] (by simpa using h)
  simpa only [automaton, active, h, ↓reduceIte] using legal.2 node

private theorem child_unique (node : TreeNode Branch) (b c : Branch)
    (hb : run (node ++ [b]) = true) (hc : run (node ++ [c]) = true) : b = c := by
  have active : run node = true := by
    cases hq : run node
    · have := (inactive legal node hq).2 b
      rw [hb] at this
      contradiction
    · rfl
  have unmarked : marked (tree node) = false := by
    cases hm : marked (tree node)
    · rfl
    · have := marked_children legal node hm b
      rw [hb] at this
      contradiction
  have transition := legal.2 node
  simp only [automaton, active, unmarked, ↓reduceIte] at transition
  obtain ⟨d, hd⟩ := transition
  have b_eq : b = d := of_decide_eq_true ((hd b).symm.trans hb)
  have c_eq : c = d := of_decide_eq_true ((hd c).symm.trans hc)
  exact b_eq.trans c_eq.symm

private theorem unique_from (base x y : TreeNode Branch)
    (hx : marked (tree (base ++ x)) = true) (hy : marked (tree (base ++ y)) = true) : x = y := by
  induction x generalizing base y with
  | nil =>
    cases y with
    | nil => rfl
    | cons b rest =>
      have inactive := marked_children legal base (by simpa using hx) b
      have hm := inactive_descendants legal (base ++ [b]) rest inactive
      simp only [List.append_assoc, List.singleton_append] at hm
      rw [hy] at hm
      contradiction
  | cons b rest ih =>
    cases y with
    | nil =>
      have inactive := marked_children legal base (by simpa using hy) b
      have hm := inactive_descendants legal (base ++ [b]) rest inactive
      simp only [List.append_assoc, List.singleton_append] at hm
      rw [hx] at hm
      contradiction
    | cons c rest' =>
      have activeB := active_of_descendant legal (base ++ [b]) rest
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
      have activeC := active_of_descendant legal (base ++ [c]) rest'
        (by simpa only [List.append_assoc, List.singleton_append] using hy)
      have same := child_unique legal base b c activeB activeC
      subst c
      exact congrArg (List.cons b) (ih (base ++ [b]) rest'
        (by simpa only [List.append_assoc, List.singleton_append] using hx)
        (by simpa only [List.append_assoc, List.singleton_append] using hy))

end Run

variable {marked} {tree : LabeledTree Branch Alphabet}
variable [Nonempty Branch]

private theorem exists_marked (accepts : (automaton marked).acceptsTree tree) :
    ∃ node, marked (tree node) = true := by
  classical
  obtain ⟨run, legal, parity⟩ := accepts
  by_contra absent
  have unmarked (node : TreeNode Branch) : marked (tree node) = false := by
    cases hm : marked (tree node)
    · rfl
    · exact False.elim (absent ⟨node,hm⟩)
  have next (node : TreeNode Branch) (active : run node = true) :
      ∃ b, run (node ++ [b]) = true := by
    have h := legal.2 node
    simp only [automaton, active, unmarked, ↓reduceIte] at h
    obtain ⟨b, hb⟩ := h
    exact ⟨b, by simpa using hb b⟩
  let select := fun node => if h : run node = true then (next node h).choose
    else Classical.arbitrary Branch
  have active (n : Nat) : run (selectorNode select n) = true := by
    induction n with
    | zero => exact legal.1
    | succ n ih =>
      change run (selectorNode select n ++ [select (selectorNode select n)]) = true
      simpa only [select, dif_pos ih] using (next (selectorNode select n) ih).choose_spec
  have even := parity (fun n => select (selectorNode select n))
  have priorities (n : Nat) : (automaton (Branch := Branch) marked).priority
      (run (branchNode (fun n => select (selectorNode select n)) n)) = 1 := by
    rw [← selectorNode_eq_branchNode, active]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ 0 (fun n _ => priorities n) even

/-- Acceptance implies exactly one marked node, including existence. -/
theorem accepts_implies_singleton (accepts : (automaton marked).acceptsTree tree) :
    ∃ witness, ∀ node, marked (tree node) = true ↔ node = witness := by
  obtain ⟨witness, hw⟩ := exists_marked accepts
  obtain ⟨run, legal, _⟩ := accepts
  refine ⟨witness, fun node => ⟨?_, fun h => h ▸ hw⟩⟩
  intro markedNode
  exact unique_from legal [] node witness markedNode hw

omit [Nonempty Branch] in
/-- A singleton marking has the run that searches along its unique root path. -/
theorem accepts_of_singleton (witness : TreeNode Branch)
    (labels : ∀ node, marked (tree node) = true ↔ node = witness) :
    (automaton marked).acceptsTree tree := by
  classical
  let run := fun node : TreeNode Branch => decide (node <+: witness)
  refine ⟨run, ⟨?_, ?_⟩, ?_⟩
  · simp [run, automaton]
  · intro node
    by_cases path : node <+: witness
    · by_cases atTarget : node = witness
      · have hm := (labels node).mpr atTarget
        simp only [automaton, run, decide_eq_true_eq, path, hm, ↓reduceIte]
        intro b
        apply decide_eq_false_iff_not.mpr
        intro impossible
        have lengths := impossible.length_le
        simp only [List.length_append, List.length_singleton, atTarget] at lengths
        omega
      · have hm : marked (tree node) = false := by
          cases h : marked (tree node)
          · rfl
          · exact False.elim (atTarget ((labels node).mp h))
        simp only [automaton, run, decide_eq_true_eq, path, hm, ↓reduceIte]
        obtain ⟨rest, equation⟩ := path
        cases rest with
        | nil => simp only [List.append_nil] at equation; exact False.elim (atTarget equation)
        | cons d rest =>
          refine ⟨d, fun b => ?_⟩
          rw [← equation]
          simp
    · have hm : marked (tree node) = false := by
        cases h : marked (tree node)
        · rfl
        · have := (labels node).mp h
          exact False.elim (path (this ▸ List.prefix_refl witness))
      simp only [automaton, run, decide_eq_true_eq, path, hm, ↓reduceIte, true_and]
      intro b
      apply decide_eq_false_iff_not.mpr
      intro impossible
      exact path ((List.prefix_append node [b]).trans impossible)
  · intro branch
    have zero (n : Nat) (hn : witness.length + 1 ≤ n) :
        (automaton (Branch := Branch) marked).priority (run (branchNode branch n)) = 0 := by
      have outside : ¬ branchNode branch n <+: witness := by
        intro inside
        have lengths := inside.length_le
        rw [TreeNonemptiness.branch_length] at lengths
        omega
      simp [automaton, run, outside]
    refine ⟨0, ⟨0, rfl⟩, ?_, fun _ _ => Nat.zero_le _⟩
    intro n
    exact ⟨max n (witness.length+1), le_max_left _ _, zero _ (le_max_right _ _)⟩

/-- Exactly singleton support, with no extra finiteness restriction on the tree. -/
theorem accepts_iff : (automaton marked).acceptsTree tree ↔
    ∃ witness, ∀ node, marked (tree node) = true ↔ node = witness :=
  ⟨accepts_implies_singleton, fun ⟨witness, labels⟩ => accepts_of_singleton witness labels⟩

end DistributedSynthesis.TreeSingleton
