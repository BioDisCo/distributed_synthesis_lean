/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityTables
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators

/-! # Primitive-recursive complementation of numeric parity tables -/
namespace DistributedSynthesis.EncodedParityOperations
open EncodedParityTables

theorem lookup_range {n : Nat} (f : Nat → Nat) (q : Fin n) :
    ((List.range n).map f).getD q.val 0 = f q.val := by
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp only [List.getElem_map,List.getElem_range]

/-- Fill all priorities before shifting: even an omitted input priority becomes one. -/
def complement (d : Data) : Data :=
  (d.1,initial d,(List.range (size d)).map (fun q => priority d q + 1),rows d)

theorem complement_primrec : Primrec complement :=
  Primrec.fst.pair (initial_primrec.pair
    ((Primrec.list_map (Primrec.list_range.comp size_primrec)
      (Primrec.succ.comp priority_primrec).to₂).pair rows_primrec))

theorem automaton_complement (d : Data) :
    automaton (complement d) = (automaton d).shiftPriority 1 := by
  unfold automaton complement DetParityAutomaton.shiftPriority
  congr 1
  funext q
  exact lookup_range _ q

theorem complement_accepts_iff (d : Data) (w : OmegaWord (Fin (rows d).length)) :
    (automaton (complement d)).Accepts w ↔ ¬ (automaton d).Accepts w := by
  rw [automaton_complement]
  exact DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts (automaton d) w
end DistributedSynthesis.EncodedParityOperations
