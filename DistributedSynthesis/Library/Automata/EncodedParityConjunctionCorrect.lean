/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityConjunction
import DistributedSynthesis.Library.Automata.EncodedParityProductCorrect

/-! Finite conjunction correctness on a shared physical alphabet. -/
namespace Characterisation.EncodedParityConjunction
open DistributedSynthesis

/-- Numeric table semantics on an explicit alphabet. All later uses prove
that this alphabet is exactly the generated row set. -/
def read (d : EncodedParityTables.Data) (alphabet : Nat) : DetParityAutomaton (Fin alphabet) where
  State := Fin (EncodedParityTables.size d)
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial d % EncodedParityTables.size d,Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨EncodedParityTables.next d q.val a.val,Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := EncodedParityTables.priority d q.val

theorem read_eq_comap (d : EncodedParityTables.Data) {E : Nat}
    (h : (EncodedParityTables.rows d).length = E) :
    read d E = (EncodedParityTables.automaton d).comap (Fin.cast h.symm) := rfl

theorem product_alphabet (E : Nat) (left right : EncodedParityTables.Data) :
    (EncodedParityTables.rows (EncodedParityProduct.transition (product E left right))).length = E := by
  rw [EncodedParityProduct.alphabet_transition]
  simp [product,EncodedParityProduct.letters,identityLetters]
theorem pair_alphabet (E : Nat) (left right : EncodedParityTables.Data) :
    (EncodedParityTables.rows (pair E left right)).length = E := by
  rw [pair,EncodedParityProduct.conjunction,EncodedParityFamilies.compile,EncodedMuller.alphabet_compile]
  exact product_alphabet E left right
theorem top_alphabet (E : Nat) : (EncodedParityTables.rows (top E)).length = E := by
  simp [top,EncodedParityTables.rows]
theorem compile_alphabet (d : Data) : (EncodedParityTables.rows (compile d)).length = d.1 := by
  rcases d with ⟨E,ds⟩
  cases ds with
  | nil => exact top_alphabet E
  | cons a ds => exact pair_alphabet E a _

theorem identity_letter (E : Nat) (left right : EncodedParityTables.Data) (a : Fin E) :
    EncodedParityProduct.letter (product E left right) a.val = (a.val,a.val) := by
  change ((List.range E).map (fun a => (a,a))).getD a.val (0,0) = _
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp only [List.getElem_map,List.getElem_range]

theorem pair_accepts_iff (E : Nat) (left right : EncodedParityTables.Data)
    (hl : (EncodedParityTables.rows left).length = E)
    (hr : (EncodedParityTables.rows right).length = E) (word : OmegaWord (Fin E)) :
    (read (pair E left right) E).Accepts word ↔
      (read left E).Accepts word ∧ (read right E).Accepts word := by
  let index : Fin E → EncodedParityProduct.Alphabet (product E left right) :=
    Fin.cast (product_alphabet E left right).symm
  let l : EncodedParityProduct.Alphabet (product E left right) → Fin (EncodedParityTables.rows left).length :=
    fun a => Fin.cast hl.symm (Fin.cast (product_alphabet E left right) a)
  let r : EncodedParityProduct.Alphabet (product E left right) → Fin (EncodedParityTables.rows right).length :=
    fun a => Fin.cast hr.symm (Fin.cast (product_alphabet E left right) a)
  have he (a : EncodedParityProduct.Alphabet (product E left right)) :
      EncodedParityProduct.letter (product E left right) a.val = ((l a).val,(r a).val) :=
    identity_letter E left right (Fin.cast (product_alphabet E left right) a)
  have adapter : read (pair E left right) E =
      (EncodedParityFamilies.automaton (EncodedParityProduct.conjunctionData (product E left right))).comap index := rfl
  rw [adapter,DetParityAutomaton.comap_accepts_iff]
  apply (EncodedParityProduct.accepts_conjunction_iff (product E left right) l r
    (fun a => congrArg Prod.fst (he a)) (fun a => congrArg Prod.snd (he a)) _).trans
  apply and_congr
  · exact (DetParityAutomaton.comap_accepts_iff (EncodedParityTables.automaton left) (Fin.cast hl.symm) word).symm
  · exact (DetParityAutomaton.comap_accepts_iff (EncodedParityTables.automaton right) (Fin.cast hr.symm) word).symm

theorem top_accepts (E : Nat) (word : OmegaWord (Fin E)) : (read (top E) E).Accepts word := by
  change NatSeqMinEvenParity (fun t => (read (top E) E).priority ((read (top E) E).run word t))
  have priorities (t : Nat) : (read (top E) E).priority ((read (top E) E).run word t) = 0 := by
    have h := ((read (top E) E).run word t).isLt
    have zero : ((read (top E) E).run word t).val = 0 := by change _ < 1 at h; omega
    change ([0] : List Nat).getD _ 0 = 0
    rw [zero]
    rfl
  simp only [priorities]
  exact ⟨0,⟨0,rfl⟩,(fun n => ⟨n,le_rfl,rfl⟩),fun _ _ => Nat.zero_le _⟩

theorem accepts_iff (d : Data)
    (alphabet : ∀ a ∈ d.2, (EncodedParityTables.rows a).length = d.1)
    (word : OmegaWord (Fin d.1)) :
    (read (compile d) d.1).Accepts word ↔ ∀ a ∈ d.2, (read a d.1).Accepts word := by
  rcases d with ⟨E,ds⟩
  induction ds with
  | nil => simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true,iff_true]; exact top_accepts E word
  | cons a ds ih =>
    change (read (pair E a (compile (E,ds))) E).Accepts word ↔ _
    rw [pair_accepts_iff E a _ (alphabet a (by simp)) (compile_alphabet (E,ds))]
    rw [ih (fun b hb => alphabet b (by simp [hb]))]
    simp only [List.mem_cons,forall_eq_or_imp]

end Characterisation.EncodedParityConjunction
