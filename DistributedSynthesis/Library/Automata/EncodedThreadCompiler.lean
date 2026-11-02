/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadNumbering
import DistributedSynthesis.Library.Automata.EncodedParityOperations

/-! # Numeric determinization and complementation of bad-thread tables -/
namespace DistributedSynthesis.EncodedThreadCompiler
open EncodedThreadBuchi

def badTables (x : Input) := EncodedPitermanCompiler.compile (EncodedThreadNumbering.compile x)
def compile (x : Input) := EncodedParityOperations.complement (badTables x)
theorem badTables_primrec : Primrec badTables :=
  EncodedPitermanCompiler.compile_primrec.comp EncodedThreadNumbering.compile_primrec
theorem compile_primrec : Primrec compile := EncodedParityOperations.complement_primrec.comp badTables_primrec

def badAutomaton (x : Input) : DetParityAutomaton (Fin x.2.2.2.length) :=
  (EncodedPitermanCompiler.automaton (EncodedThreadNumbering.compile x)).comap
    (Fin.cast (EncodedThreadNumbering.alphabet_size x).symm)
@[irreducible] def automaton (x : Input) : DetParityAutomaton (Fin x.2.2.2.length) :=
  (badAutomaton x).shiftPriority 1

theorem config_accepts_congr {n m i j : Nat} (ps : List Nat) (es : List Edges)
    (hn : n = m) (hi : i = j) (word : OmegaWord (Fin es.length)) :
    (automaton (n,i,ps,es)).Accepts word ↔ (automaton (m,j,ps,es)).Accepts word := by
  cases hn
  cases hi
  rfl

theorem alphabet_size (x : Input) : (EncodedParityTables.rows (compile x)).length = x.2.2.2.length := by
  exact (EncodedPitermanCompiler.alphabet_size (EncodedThreadNumbering.compile x)).trans
    (EncodedThreadNumbering.alphabet_size x)

private theorem shift_comap {L K : Type*} (D : DetParityAutomaton L) (f : K → L) :
    (D.comap f).shiftPriority 1 = (D.shiftPriority 1).comap f := rfl

private theorem cast_comap {n m k : Nat} (D : DetParityAutomaton (Fin n))
    (h : n = m) (h' : m = k) :
    (D.comap (Fin.cast h.symm)).comap (Fin.cast h'.symm) =
      D.comap (Fin.cast (h.trans h').symm) := by
  cases h; cases h'; rfl

theorem automaton_eq (x : Input) : automaton x =
    (EncodedParityTables.automaton (compile x)).comap (Fin.cast (alphabet_size x).symm) := by
  unfold automaton badAutomaton EncodedPitermanCompiler.automaton
  rw [cast_comap _ (EncodedPitermanCompiler.alphabet_size (EncodedThreadNumbering.compile x))
    (EncodedThreadNumbering.alphabet_size x), shift_comap,
    ← EncodedParityOperations.automaton_complement]
  rfl

end DistributedSynthesis.EncodedThreadCompiler
