/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanAutomaton
import DistributedSynthesis.Library.Automata.EncodedParityTables

/-! # Primitive-recursive finite Büchi-to-parity table compilation

Input: Büchi state count, initial index, accepting indices, and one edge list
per letter. Output: the complete numeric deterministic parity tables. The
semantic theorem takes a numbered Büchi automaton and proves language equality;
there is no well-formed-tree classifier or compiler hypothesis in that theorem.
-/

namespace DistributedSynthesis.EncodedPitermanCompiler
open EncodedPitermanAutomaton
abbrev Input := Nat × Nat × List Nat × List EncodedPitermanTransition.Edges

def row (x : Context) : List Nat := (List.range (size x.1)).map (next x)
def compile (x : Input) : EncodedParityTables.Data :=
  ((EncodedPitermanStates.allCodes x.1).length,
    locate x.1 (some (initialCode x.1 x.2.1)),
    (List.range (size x.1)).map (priority x.1),
    x.2.2.2.map (fun edges => row (x.1, edges, x.2.2.1)))

theorem row_primrec : Primrec row :=
  Primrec.list_map (Primrec.list_range.comp (size_primrec.comp Primrec.fst)) next_primrec
theorem compile_primrec : Primrec compile := by
  have hn : Primrec (fun x : Input => x.1) := Primrec.fst
  have hi : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : Input => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun x : Input => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_length.comp (EncodedPitermanStates.allCodes_primrec.comp hn)).pair
    ((locate_primrec.comp hn (Primrec.option_some.comp (initialCode_primrec.comp hn hi))).pair
      ((Primrec.list_map (Primrec.list_range.comp (size_primrec.comp hn))
        (priority_primrec.comp (hn.comp Primrec.fst) Primrec.snd).to₂).pair
        (Primrec.list_map he (row_primrec.comp
          ((hn.comp Primrec.fst).pair (Primrec.snd.pair (ha.comp Primrec.fst)))).to₂)))

theorem alphabet_size (x : Input) : (EncodedParityTables.rows (compile x)).length = x.2.2.2.length := by
  simp [EncodedParityTables.rows, compile]

/-- The table automaton, with its alphabet identified with the input row indices. -/
def automaton (x : Input) : DetParityAutomaton (Fin x.2.2.2.length) :=
  (EncodedParityTables.automaton (compile x)).comap (Fin.cast (alphabet_size x).symm)

private theorem lookup_range {n : Nat} (f : Nat → Nat) (q : Fin n) :
    ((List.range n).map f).getD q.val 0 = f q.val := by
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp

theorem automaton_eq (x : Input) : automaton x =
    EncodedPitermanAutomaton.automaton x.2.1 (fun a : Fin x.2.2.2.length => x.2.2.2[a]) x.2.2.1 x.1 := by
  unfold automaton DetParityAutomaton.comap EncodedParityTables.automaton
    EncodedPitermanAutomaton.automaton
  congr 1
  · apply Fin.ext
    exact Nat.mod_eq_of_lt (locate_lt _ _)
  · funext q a
    apply Fin.ext
    change (((x.2.2.2.map (fun edges => row (x.1, edges, x.2.2.1))).getD a.val []).getD q.val 0) % size x.1 = _
    have hr : (x.2.2.2.map (fun edges => row (x.1, edges, x.2.2.1))).getD a.val [] =
        row (x.1, x.2.2.2[a], x.2.2.1) := by
      rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
      simp
    rw [hr]
    change ((List.range (size x.1)).map (next (x.1, x.2.2.2[a], x.2.2.1))).getD q.val 0 % size x.1 = _
    rw [lookup_range (n := size x.1) _ q]
    exact Nat.mod_eq_of_lt (locate_lt _ _)
  · funext q
    exact lookup_range _ q

open NondetBuchiAutomaton.Piterman
variable {k : Nat} (A : NondetBuchiAutomaton (Fin k)) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State))
  (decStep : ∀ q a r, Decidable (A.step q a r)) (decAccept : DecidablePred A.accepting)
  (edges : List EncodedPitermanTransition.Edges) (hlen : edges.length = k) (acc : List Nat)
  (he : ∀ q (a : Fin k) r, ((number q).val, (number r).val) ∈ edges[a.val]?.getD [] ↔ A.step q a r)
  (ha : ∀ q, (number q).val ∈ acc ↔ A.accepting q)

include he ha decStep decAccept in
theorem accepts_iff (word : OmegaWord (Fin k)) :
    ((automaton (Fintype.card A.State, (number A.initial).val, acc, edges)).comap
      (Fin.cast hlen.symm)).Accepts word ↔ A.Accepts word := by
  rw [automaton_eq]
  have he' (q : A.State) (a : Fin k) (r : A.State) :
      ((number q).val, (number r).val) ∈ edges[Fin.cast hlen.symm a] ↔ A.step q a r := by
    simpa only [List.getElem?_eq_getElem (by omega : a.val < edges.length), Option.getD_some] using he q a r
  exact EncodedPitermanAutomaton.accepts_iff A number decStep decAccept
    (fun a => edges[Fin.cast hlen.symm a]) acc he' ha word

end DistributedSynthesis.EncodedPitermanCompiler
