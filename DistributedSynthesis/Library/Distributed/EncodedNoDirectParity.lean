/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirect
import DistributedSynthesis.Library.Automata.EncodedLTLParity

/-! # Numeric parity frontend for the encoded synthesis instances

The complete round-record enumeration fixes the alphabet order. The table
compiler is primitive recursive and recognizes the original LTL objective on
every execution word. Journal compilation remains a separate next stage.
-/

namespace DistributedSynthesis.EncodedNoDirectParity
open EncodedNoDirect
set_option synthInstance.maxSize 1024

def valuations (d : Instance) : List (List Nat) :=
  (letters d).map (EncodedLTLTransitions.trueAtoms d.truthTable)
theorem valuations_primrec : Primrec valuations :=
  Primrec.list_map letters_primrec
    (EncodedLTLTransitions.trueAtoms_primrec.comp (truthTable_primrec.comp Primrec.fst) Primrec.snd).to₂

def compile (d : Instance) : EncodedParityTables.Data := EncodedLTLParity.compile (d.formula, valuations d)
theorem compile_primrec : Primrec compile :=
  EncodedLTLParity.compile_primrec.comp (formula_primrec.pair valuations_primrec)

def letterIndex (d : Instance) (a : Letter d) : Fin (valuations d).length :=
  ⟨(letters d).idxOf (letterCode a), by
    have hm := (mem_letters_iff d (letterCode a)).mpr ⟨a, rfl⟩
    simpa [valuations] using List.idxOf_lt_length_of_mem hm⟩

theorem valuation_letterIndex (d : Instance) (a : Letter d) :
    (valuations d)[letterIndex d a] = EncodedLTLTransitions.trueAtoms d.truthTable (letterCode a) := by
  have hb : (letters d).idxOf (letterCode a) < (letters d).length :=
    List.idxOf_lt_length_of_mem ((mem_letters_iff d _).mpr ⟨a, rfl⟩)
  have hb' : (letters d).idxOf (letterCode a) <
      ((letters d).map (EncodedLTLTransitions.trueAtoms d.truthTable)).length := by simpa using hb
  change ((letters d).map (EncodedLTLTransitions.trueAtoms d.truthTable))[(letters d).idxOf (letterCode a)] = _
  rw [List.getElem_map, List.getElem_idxOf]

def automaton (d : Instance) : DetParityAutomaton (Letter d) :=
  (EncodedLTLParity.automaton (d.formula, valuations d)).comap (letterIndex d)

theorem accepts_iff (d : Instance) (word : OmegaWord (Letter d)) :
    (automaton d).Accepts word ↔ LTL.Satisfies (interp d) word (EncodedFiniteLTL.decode d.formula) := by
  rw [automaton, DetParityAutomaton.comap_accepts_iff, EncodedLTLParity.accepts_iff]
  have hw : (fun t => (valuations d)[(OmegaWord.map (letterIndex d) word) t]) =
      OmegaWord.map (fun a : Letter d => EncodedLTLTransitions.trueAtoms d.truthTable (letterCode a)) word := by
    funext t
    exact valuation_letterIndex d (word t)
  rw [hw, LTL.satisfies_word_map]
  have hi : (fun ap (a : Letter d) => EncodedLTLAutomaton.interp ap
      (EncodedLTLTransitions.trueAtoms d.truthTable (letterCode a))) = interp d := by
    funext ap a
    exact propext (EncodedLTLTransitions.mem_trueAtoms d.truthTable (letterCode a) ap)
  rw [hi]

theorem realizable_iff (d : Instance) : EncodedNoDirect.Realizable d ↔ NoDirectJournal.Realizable (automaton d) := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun env henv => (accepts_iff d _).mpr (hσ env henv)⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, fun env henv => (accepts_iff d _).mp (hσ env henv)⟩

end DistributedSynthesis.EncodedNoDirectParity
