/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedRunTree
import DistributedSynthesis.Library.Automata.RunTreeNonemptiness
import DistributedSynthesis.Library.Automata.TreeStateEncoding
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Correctness of the finite transition-table compiler -/
namespace DistributedSynthesis.EncodedRunTree

variable (x : Input)

abbrev Direction := Fin (branches x)
abbrev Label := Fin (alphabet x)
abbrev State := Fin (states x)
abbrev Successors := Direction x → State x

def source : RunParityTreeAutomaton (Direction x) (Label x) where
  State := State x
  stateFinite := inferInstance
  initial := ⟨initial x % states x, Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := (priorities x).getD q.val 0
  delta q a v := valid x q.val a.val (FiniteFunctionCoding.encode v)

instance sourceDecidableEq : DecidableEq (source x).State := inferInstanceAs (DecidableEq (State x))
instance sourceDeltaDecidable (q : (source x).State) (a : Label x) (v : Direction x → (source x).State) :
    Decidable ((source x).delta q a v) := inferInstanceAs (Decidable (valid x q.val a.val (FiniteFunctionCoding.encode v)))

noncomputable def choiceEquiv : (Label x × Successors x) ≃ Fin (choices x) :=
  (Equiv.prodCongr (Equiv.refl _) (FiniteFunctionCoding.equiv _ _)).trans finProdFinEquiv

theorem stateSize : EncodedParityTables.size (wordData x) = 2 * states x := by
  exact Nat.sub_add_cancel (by have : 0 < states x := Nat.succ_pos _; omega)

noncomputable def stateEquiv : (source x).transitionMonitor.State ≃
    Fin (EncodedParityTables.size (wordData x)) :=
  ((Equiv.prodCongr (Equiv.refl (State x)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (by rw [stateSize]; omega))

theorem stateEquiv_val (q : State x) (flag : Bool) :
    (stateEquiv x (q, flag)).val = 2 * q.val + if flag then 1 else 0 := by
  cases flag
  · change 0 + 2 * q.val = 2 * q.val + 0
    omega
  · change 1 + 2 * q.val = 2 * q.val + 1
    omega

theorem choice_div (a : Label x) (v : Successors x) :
    (choiceEquiv x (a, v)).val / (vectors x).length = a.val := by
  have hi : (FiniteFunctionCoding.equiv (branches x) (states x) v).val < (vectors x).length :=
    (FiniteFunctionCoding.equiv (branches x) (states x) v).isLt
  change ((FiniteFunctionCoding.equiv _ _ v).val + (vectors x).length * a.val) / (vectors x).length = _
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt hi), Nat.div_eq_of_lt hi, Nat.zero_add]

theorem choice_vector (a : Label x) (v : Successors x) :
    (vectors x).getD ((choiceEquiv x (a, v)).val % (vectors x).length) [] =
      FiniteFunctionCoding.encode v := by
  change (vectors x).getD
    (((FiniteFunctionCoding.equiv _ _ v).val + (vectors x).length * a.val) % (vectors x).length) [] = _
  have hi : (FiniteFunctionCoding.equiv (branches x) (states x) v).val < (vectors x).length :=
    (FiniteFunctionCoding.equiv (branches x) (states x) v).isLt
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hi]
  exact FiniteFunctionCoding.get_equiv v

theorem rawStep_encode (q : State x) (flag : Bool) (a : Label x) (v : Successors x) (b : Direction x) :
    rawStep x (stateEquiv x (q, flag)).val (choiceEquiv x (a, v)).val b.val =
      (stateEquiv x ((source x).transitionMonitor.step (q, flag) (a, v) b)).val := by
  rw [rawStep, choice_vector, choice_div, FiniteFunctionCoding.lookup_encode, stateEquiv_val]
  change 2 * (v b).val + (if _ then 1 else 0) =
    (stateEquiv x (v b, flag && decide ((source x).delta q a v))).val
  rw [stateEquiv_val]
  cases flag <;> simp [source, Nat.mul_add_div, Nat.mul_add_mod, Bool.and_eq_true]

theorem rawPriority_encode (q : State x) (flag : Bool) :
    rawPriority x (stateEquiv x (q, flag)).val = (source x).transitionMonitor.priority (q, flag) := by
  rw [rawPriority, stateEquiv_val]
  cases flag <;> simp [RunParityTreeAutomaton.transitionMonitor, source, Nat.mul_add_div, Nat.mul_add_mod]

noncomputable def typedMonitor : DeterministicBlockMonitor (Direction x) (Fin (choices x)) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := (source x).transitionMonitor.State
  stateFinite := inferInstance
  initial := (source x).transitionMonitor.initial
  priority := (source x).transitionMonitor.priority
  step q a b := (source x).transitionMonitor.step q ((choiceEquiv x).symm a) b

abbrev numericMonitor := EncodedTreeNonemptiness.monitor (EncodedProjectedTree.monitorData (compile x))

theorem initial_encode : (numericMonitor x).initial = stateEquiv x (typedMonitor x).initial := by
  apply Fin.ext
  change (2 * (initial x % states x) + 1) % EncodedParityTables.size (wordData x) = _
  rw [show (stateEquiv x (typedMonitor x).initial).val = 2 * (initial x % states x) + 1 from
    stateEquiv_val x _ true]
  exact Nat.mod_eq_of_lt (by
    rw [stateSize]
    have := Nat.mod_lt (initial x) (Nat.succ_pos (x.2.2.1))
    change initial x % states x < states x at this
    omega)

theorem priority_encode (q : (typedMonitor x).State) :
    (numericMonitor x).priority (stateEquiv x q) = (typedMonitor x).priority q := by
  change ((List.range (2 * states x)).map (rawPriority x)).getD (stateEquiv x q).val 0 = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range, ← stateSize x]
    using (stateEquiv x q).isLt)]
  simp only [List.getElem_map, List.getElem_range]
  exact rawPriority_encode x q.1 q.2

theorem step_encode (q : (typedMonitor x).State) (a : Fin (choices x)) (b : Direction x) :
    (numericMonitor x).step (stateEquiv x q) a b = stateEquiv x ((typedMonitor x).step q a b) := by
  change (EncodedTreeNonemptiness.monitor (EncodedWordTree.compile _)).step _ _ _ = _
  rw [EncodedWordTree.step_eq]
  apply Fin.ext
  change (((List.range (choices x * branches x)).map (fun l =>
      (List.range (2 * states x)).map (fun s => rawStep x s (l / branches x) (l % branches x)))).getD
        (a.val * branches x + b.val) []).getD (stateEquiv x q).val 0 %
          EncodedParityTables.size (wordData x) = _
  have hb : a.val * branches x + b.val < choices x * branches x := by
    calc
      a.val * branches x + b.val < a.val * branches x + branches x := Nat.add_lt_add_left b.isLt _
      _ = (a.val + 1) * branches x := by ring
      _ ≤ choices x * branches x := Nat.mul_le_mul_right _ a.isLt
  have row : ((List.range (choices x * branches x)).map (fun l =>
      (List.range (2 * states x)).map (fun s => rawStep x s (l / branches x) (l % branches x)))).getD
        (a.val * branches x + b.val) [] =
      (List.range (2 * states x)).map (fun s => rawStep x s a.val b.val) := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range] using hb)]
    simp only [List.getElem_map, List.getElem_range]
    rw [Nat.mul_comm a.val (branches x), Nat.mul_add_div (Nat.zero_lt_of_lt b.isLt),
      Nat.div_eq_of_lt b.isLt, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  rw [row, List.getD_eq_getElem _ _ (by
    simpa only [List.length_map, List.length_range, ← stateSize x] using (stateEquiv x q).isLt)]
  simp only [List.getElem_map, List.getElem_range]
  obtain ⟨⟨label, v⟩, rfl⟩ := (choiceEquiv x).surjective a
  rcases q with ⟨q, flag⟩
  rw [rawStep_encode]
  change (stateEquiv x ((source x).transitionMonitor.step (q, flag) (label, v) b)).val % _ = _
  rw [Nat.mod_eq_of_lt (stateEquiv x ((source x).transitionMonitor.step (q, flag) (label, v) b)).isLt]
  simp only [typedMonitor, Equiv.symm_apply_apply]
  rfl

theorem monitor_accepts_iff (tree : LabeledTree (Direction x) (Fin (choices x))) :
    (numericMonitor x).toRunAutomaton.acceptsTree tree ↔
      (source x).transitionMonitor.toRunAutomaton.acceptsTree ((choiceEquiv x).symm ∘ tree) := by
  have h := RunParityTreeAutomaton.acceptsTree_iff_of_equiv
    (typedMonitor x).toRunAutomaton (numericMonitor x).toRunAutomaton (stateEquiv x)
    (initial_encode x).symm (priority_encode x) (fun q a next => ?_) tree
  · exact h
  · change (∀ b, stateEquiv x (next b) = (numericMonitor x).step (stateEquiv x q) a b) ↔
      ∀ b, next b = (typedMonitor x).step q a b
    constructor
    · intro h b
      exact (stateEquiv x).injective ((h b).trans (step_encode x q a b))
    · intro h b
      exact (congrArg (stateEquiv x) (h b)).trans (step_encode x q a b).symm

theorem projection_label (a : Label x) (v : Successors x) :
    EncodedProjectedTree.letter (compile x) (choiceEquiv x (a, v)) = a := by
  apply Fin.ext
  change ((List.range (choices x)).map (fun l => l / (vectors x).length)).getD
    (choiceEquiv x (a, v)).val 0 % alphabet x = _
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_range]
    using (choiceEquiv x (a, v)).isLt)]
  simp only [List.getElem_map, List.getElem_range]
  rw [choice_div, Nat.mod_eq_of_lt a.isLt]

variable [Inhabited (Direction x)]

/-- Full language preservation for arbitrary finite transition tables. -/
theorem compile_correct (tree : LabeledTree (Direction x) (Label x)) :
    (EncodedProjectedTree.automaton (compile x)).acceptsTree tree ↔ (source x).acceptsTree tree := by
  classical
  rw [EncodedProjectedTree.accepts_iff, ← (source x).transitionMonitor_accepts_iff tree]
  constructor
  · rintro ⟨annotated, projected, accepts⟩
    let decoded := (choiceEquiv x).symm ∘ annotated
    have first (node) : (decoded node).1 = tree node := by
      have h := projection_label x (decoded node).1 (decoded node).2
      have hchoice : choiceEquiv x (decoded node) = annotated node := (choiceEquiv x).apply_symm_apply _
      exact h.symm.trans ((congrArg (EncodedProjectedTree.letter (compile x)) hchoice).trans
        (congrFun projected node))
    refine ⟨fun node => (decoded node).2, ?_⟩
    have heq : (fun node => (tree node, (decoded node).2)) = decoded := by
      funext node
      exact Prod.ext (first node).symm rfl
    exact heq.symm ▸ (monitor_accepts_iff x annotated).mp accepts
  · rintro ⟨successors, accepts⟩
    let annotated := fun node => choiceEquiv x (tree node, successors node)
    refine ⟨annotated, ?_, (monitor_accepts_iff x annotated).mpr ?_⟩
    · funext node
      exact projection_label x (tree node) (successors node)
    · have heq : (choiceEquiv x).symm ∘ annotated = fun node => (tree node, successors node) := by
        funext node
        exact (choiceEquiv x).symm_apply_apply _
      exact heq.symm ▸ accepts

end DistributedSynthesis.EncodedRunTree
