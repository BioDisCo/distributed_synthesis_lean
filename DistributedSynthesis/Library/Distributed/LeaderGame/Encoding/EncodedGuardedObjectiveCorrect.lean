/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGuardedObjective
import DistributedSynthesis.Library.Automata.EncodedParityProductCorrect

/-! The numeric guard is equivalent to the original physical guarded
objective on every word, including inadmissible and nonclosed-adversary
words. The adversary table is fixed before the synthesis instance. -/
namespace Characterisation.EncodedGuardedObjective
open DistributedSynthesis

variable (d : Data)

theorem translations_length (i : EncodedNoDirect.Instance) : (translations i).length = (EncodedNoDirect.letters i).length := by
  simp [translations]
theorem objective_alphabet (i : EncodedNoDirect.Instance) :
    (EncodedParityTables.rows (EncodedNoDirectParity.compile i)).length = (EncodedNoDirect.letters i).length := by
  rw [EncodedNoDirectParity.compile,EncodedLTLParity.alphabet_size]
  simp [EncodedNoDirectParity.valuations]
theorem product_alphabet : (EncodedParityTables.rows (EncodedParityProduct.transition (product d))).length =
    (EncodedNoDirect.letters d.2).length := by
  rw [EncodedParityProduct.alphabet_transition]
  exact translations_length _
theorem compile_alphabet : (EncodedParityTables.rows (compile d)).length = (EncodedNoDirect.letters d.2).length := by
  rw [compile,EncodedParityProduct.guard,EncodedParityFamilies.compile,EncodedMuller.alphabet_compile]
  exact product_alphabet d

def graphAutomaton (adversary : EncodedParityTables.Data)
    (alphabet : (EncodedParityTables.rows adversary).length = 3) : DetParityAutomaton Graph :=
  (EncodedParityTables.automaton adversary).comap
    (fun g => Fin.cast alphabet.symm (EncodedNoDirect.graphCode g))

def recordIndex (a : EncodedNoDirect.Letter d.2) : EncodedParityProduct.Alphabet (product d) :=
  ⟨(EncodedNoDirect.letters d.2).idxOf (EncodedNoDirect.letterCode a),by
    rw [product_alphabet]
    exact List.idxOf_lt_length_of_mem ((EncodedNoDirect.mem_letters_iff _ _).mpr ⟨a,rfl⟩)⟩

def automaton : DetParityAutomaton (WithInputs.TupleLetter d.2) :=
  (EncodedParityFamilies.automaton (EncodedParityProduct.guardData (product d))).comap
    (fun a => recordIndex d (continuationRecord a))

theorem translation_get (a : Fin (EncodedNoDirect.letters d.2).length) :
    EncodedParityProduct.letter (product d) a.val =
      (((EncodedNoDirect.letters d.2)[a.val]).2.2.1.val,a.val) := by
  unfold EncodedParityProduct.letter product EncodedParityProduct.letters translations
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp only [List.getElem_map,List.getElem_range]
  rw [List.getD_eq_getElem _ _ a.isLt]

theorem graph_lt (a : Fin (EncodedNoDirect.letters d.2).length) :
    ((EncodedNoDirect.letters d.2)[a.val]).2.2.1.val < 3 := by
  obtain ⟨r,h⟩ := (EncodedNoDirect.mem_letters_iff d.2 _).mp (List.getElem_mem a.isLt)
  rw [← h]
  exact (EncodedNoDirect.graphCode r.graph).isLt

variable (alphabet : (EncodedParityTables.rows d.1).length = 3)

def leftLetter (a : EncodedParityProduct.Alphabet (product d)) :
    Fin (EncodedParityTables.rows (EncodedParityProduct.left (product d))).length :=
  ⟨(EncodedParityProduct.letter (product d) a.val).1,by
    change _ < (EncodedParityTables.rows d.1).length
    rw [alphabet,translation_get d ⟨a.val,by simpa only [product_alphabet] using a.isLt⟩]
    exact graph_lt d _⟩
def rightLetter (a : EncodedParityProduct.Alphabet (product d)) :
    Fin (EncodedParityTables.rows (EncodedParityProduct.right (product d))).length :=
  ⟨a.val,by
    change _ < (EncodedParityTables.rows (EncodedNoDirectParity.compile d.2)).length
    rw [objective_alphabet]
    simpa only [product_alphabet] using a.isLt⟩

theorem translation_right (a : EncodedParityProduct.Alphabet (product d)) :
    (EncodedParityProduct.letter (product d) a.val).2 = (rightLetter d a).val := by
  rw [translation_get d ⟨a.val,by simpa only [product_alphabet] using a.isLt⟩]
  rfl

theorem left_record (a : EncodedNoDirect.Letter d.2) :
    leftLetter d alphabet (recordIndex d a) = Fin.cast alphabet.symm (EncodedNoDirect.graphCode a.graph) := by
  apply Fin.ext
  change (EncodedParityProduct.letter (product d) (recordIndex d a).val).1 = _
  rw [translation_get d ⟨(recordIndex d a).val,by rw [← product_alphabet]; exact (recordIndex d a).isLt⟩]
  have hbound : (EncodedNoDirect.letters d.2).idxOf (EncodedNoDirect.letterCode a) < (EncodedNoDirect.letters d.2).length :=
    List.idxOf_lt_length_of_mem ((EncodedNoDirect.mem_letters_iff _ _).mpr ⟨a,rfl⟩)
  change ((EncodedNoDirect.letters d.2)[(EncodedNoDirect.letters d.2).idxOf (EncodedNoDirect.letterCode a)]).2.2.1.val = _
  rw [List.getElem_idxOf]
  rfl

theorem right_record (a : EncodedNoDirect.Letter d.2) :
    rightLetter d (recordIndex d a) =
      Fin.cast (EncodedLTLParity.alphabet_size (d.2.formula,EncodedNoDirectParity.valuations d.2)).symm
        (EncodedNoDirectParity.letterIndex d.2 a) := rfl

/-- Exact physical guarded language, with the original LTL frontend on the
right of the implication. This statement does not restrict graph words. -/
theorem accepts_iff (word : OmegaWord (WithInputs.TupleLetter d.2)) :
    (automaton d).Accepts word ↔
      ((graphAutomaton d.1 alphabet).Accepts (fun n => (word n).1.2.2) →
        (EncodedLeaderObjective.automaton (EncodedRoundObjectives.fromInstance d.2)).Accepts word) := by
  rw [automaton,DetParityAutomaton.comap_accepts_iff]
  apply (EncodedParityProduct.accepts_guard_iff (product d) (leftLetter d alphabet) (rightLetter d)
    (fun _ => rfl) (translation_right d) _).trans
  apply imp_congr
  · have lword : (fun n => leftLetter d alphabet
        ((OmegaWord.map (fun a => recordIndex d (continuationRecord a)) word) n)) =
        OmegaWord.map (fun g => Fin.cast alphabet.symm (EncodedNoDirect.graphCode g)) (fun n => (word n).1.2.2) := by
      funext n
      exact left_record d alphabet _
    change (EncodedParityTables.automaton d.1).Accepts _ ↔ _
    exact (iff_of_eq (congrArg (EncodedParityTables.automaton d.1).Accepts lword)).trans
      (DetParityAutomaton.comap_accepts_iff _ _ _).symm
  · symm
    rw [EncodedLeaderObjective.automaton_fromInstance]
    change ((EncodedNoDirectParity.automaton d.2).comap continuationRecord).Accepts word ↔ _
    rw [DetParityAutomaton.comap_accepts_iff]
    rw [EncodedNoDirectParity.automaton,DetParityAutomaton.comap_accepts_iff]
    rw [EncodedLTLParity.automaton,DetParityAutomaton.comap_accepts_iff]
    rfl

/-- The new guard may have different internal states from the classical
Muller construction; its accepted physical words are exactly the same. -/
theorem accepts_semantic_guard_iff (word : OmegaWord (WithInputs.TupleLetter d.2)) :
    (automaton d).Accepts word ↔
      (WithInputs.guardedInstanceObjective (graphAutomaton d.1 alphabet) d.2).Accepts word := by
  rw [accepts_iff d alphabet,WithInputs.guardedInstanceObjective,guardedPhysicalObjective_accepts_iff,
    EncodedLeaderObjective.automaton_fromInstance]
  rfl

end Characterisation.EncodedGuardedObjective
