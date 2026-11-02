/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedWordTree

/-! # Reading a numeric tree monitor along a branch -/
namespace DistributedSynthesis.EncodedTreeWord
open EncodedTreeNonemptiness

/-- Paired letters are numbered `label * branchCount + direction`. -/
def compile (d : Data) : EncodedParityTables.Data :=
  (d.1, initial d, priorities d,
    (List.range (labels d * branches d)).map (fun a =>
      (List.range (bound d)).map (fun q => rawNext d q (a / branches d) (a % branches d))))

attribute [local fun_prop] initial_primrec priorities_primrec labels_primrec branches_primrec bound_primrec

private theorem next_primrec :
    Primrec (fun x : Data × Nat × Nat × Nat => rawNext x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  rawNext_primrec Primrec.fst (Primrec.fst.comp Primrec.snd)
    (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
attribute [local fun_prop] next_primrec

theorem compile_primrec : Primrec compile := by
  unfold compile
  fun_prop

theorem alphabet_length (d : Data) :
    (EncodedParityTables.rows (compile d)).length = labels d * branches d := by
  simp only [compile, EncodedParityTables.rows, List.length_map, List.length_range]

def letter (d : Data) (a : Fin (labels d) × Fin (branches d)) :
    Fin (EncodedParityTables.rows (compile d)).length :=
  ⟨a.1.val * branches d + a.2.val, by
    rw [alphabet_length]
    calc
      a.1.val * branches d + a.2.val < a.1.val * branches d + branches d :=
        Nat.add_lt_add_left a.2.isLt _
      _ = (a.1.val + 1) * branches d := by ring
      _ ≤ labels d * branches d := Nat.mul_le_mul_right _ a.1.isLt⟩

theorem step_encode (d : Data) (q : Fin (bound d))
    (l : Fin (labels d)) (b : Fin (branches d)) :
    (EncodedParityTables.automaton (compile d)).step q (letter d (l, b)) =
      (monitor d).step q l b := by
  apply Fin.ext
  change (((List.range (labels d * branches d)).map (fun a =>
    (List.range (bound d)).map (fun q => rawNext d q (a / branches d) (a % branches d)))).getD
      (letter d (l, b)).val []).getD q.val 0 % bound d = _
  rw [List.getD_eq_getElem
    ((List.range (labels d * branches d)).map (fun a =>
      (List.range (bound d)).map (fun q => rawNext d q (a / branches d) (a % branches d)))) []
    (by simpa only [List.length_map, List.length_range, ← alphabet_length d] using (letter d (l,b)).isLt)]
  simp only [List.getElem_map, List.getElem_range, letter]
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp only [List.getElem_map, List.getElem_range]
  rw [Nat.mul_comm l.val (branches d), Nat.mul_add_div (Nat.zero_lt_of_lt b.isLt), Nat.div_eq_of_lt b.isLt, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  rfl

theorem control_run (d : Data) (tree : LabeledTree (Fin (branches d)) (Fin (labels d)))
    (branch : Nat → Fin (branches d)) (n : Nat) :
    (EncodedParityTables.automaton (compile d)).run
        (OmegaWord.map (letter d) (WordTreeMonitor.word tree branch)) n =
      (monitor d).control tree (branchNode branch n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [DetParityAutomaton.run_succ, ih]
    change (EncodedParityTables.automaton (compile d)).step _ (letter d (_, _)) = _
    rw [step_encode, branchNode, DeterministicBlockMonitor.control_append]

theorem accepts_iff (d : Data) (tree : LabeledTree (Fin (branches d)) (Fin (labels d))) :
    (monitor d).toRunAutomaton.acceptsTree tree ↔
      ∀ branch, (EncodedParityTables.automaton (compile d)).Accepts
        (OmegaWord.map (letter d) (WordTreeMonitor.word tree branch)) := by
  rw [DeterministicBlockMonitor.acceptsTree_iff_winningTree]
  change (∀ branch, NatSeqMinEvenParity (fun n =>
      (monitor d).priority ((monitor d).control tree (branchNode branch n)))) ↔
    ∀ branch, NatSeqMinEvenParity (fun n => (EncodedParityTables.automaton (compile d)).priority
      ((EncodedParityTables.automaton (compile d)).run
        (OmegaWord.map (letter d) (WordTreeMonitor.word tree branch)) n))
  simp only [control_run]
  rfl

end DistributedSynthesis.EncodedTreeWord
