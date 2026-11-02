/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.BlockTranslation
import Mathlib.Data.Fintype.EquivFin

/-! # Finite binary codes and literal block tests

Codes are injective Boolean words. The concrete `finCode` is executable and
one-hot, not length-optimal. Formula constructors use explicit finite lists;
they do not introduce semantic oracle atoms.
-/
namespace DistributedSynthesis.BinaryWords
open LTL.BlockTranslation

structure Code (O : Type*) (K : Nat) where
  bits : O → Fin K → Bool
  injective : Function.Injective bits

def ofEmbedding {O : Type*} {K : Nat} (e : O ↪ Fin K) : Code O K where
  bits a j := decide (e a = j)
  injective := by
    intro a b hab
    have h := congrFun hab (e a)
    simp only [decide_true] at h
    exact e.injective (of_decide_eq_true h.symm).symm

def finCode (m K : Nat) (hm : m ≤ K) : Code (Fin m) K :=
  ofEmbedding ⟨fun a ↦ ⟨a.val, Nat.lt_of_lt_of_le a.isLt hm⟩,
    fun a b h ↦ Fin.ext (congrArg (fun x : Fin K ↦ x.val) h)⟩

noncomputable def finiteCode (O : Type*) [Fintype O] (K : Nat)
    (hK : Fintype.card O ≤ K) : Code O K :=
  ofEmbedding ⟨fun a ↦ ⟨(Fintype.equivFin O a).val,
      Nat.lt_of_lt_of_le (Fintype.equivFin O a).isLt hK⟩,
    fun a b h ↦ (Fintype.equivFin O).injective (Fin.ext (congrArg (fun x : Fin K ↦ x.val) h))⟩

def bitTest {AP : Type*} (p : AP) (b : Bool) : LTL AP := if b then .atom p else .neg (.atom p)

def wordTest {AP : Type*} {K : Nat} (p : AP) (bits : Fin K → Bool) : LTL AP :=
  (List.ofFn fun j : Fin K ↦ nextN (2*j.val+3) (bitTest p (bits j))).foldr LTL.conj .verum

def valid {AP O : Type*} {K : Nat} (p : AP) (code : Code O K) (alphabet : List O) : LTL AP :=
  (alphabet.map fun a ↦ wordTest p (code.bits a)).foldr LTL.disj .falsum

private theorem all_iff {AP A : Type*} (I : AP → A → Prop) (w : OmegaWord A)
    (xs : List (LTL AP)) :
    LTL.Satisfies I w (xs.foldr LTL.conj .verum) ↔ ∀ φ ∈ xs, LTL.Satisfies I w φ := by
  induction xs with
  | nil => simp [LTL.Satisfies]
  | cons φ xs ih => simp [LTL.Satisfies, ih]

private theorem any_iff {AP A : Type*} (I : AP → A → Prop) (w : OmegaWord A)
    (xs : List (LTL AP)) :
    LTL.Satisfies I w (xs.foldr LTL.disj .falsum) ↔ ∃ φ ∈ xs, LTL.Satisfies I w φ := by
  induction xs with
  | nil => simp [LTL.Satisfies]
  | cons φ xs ih => simp [LTL.Satisfies, ih]

theorem bitTest_iff {AP A : Type*} (I : AP → A → Prop) (w : OmegaWord A)
    (p : AP) (b : Bool) :
    LTL.Satisfies I w (bitTest p b) ↔ (I p (w 0) ↔ b = true) := by
  cases b <;> simp [bitTest, LTL.Satisfies]

theorem wordTest_iff {AP A : Type*} {K : Nat} (I : AP → A → Prop) (w : OmegaWord A)
    (p : AP) (bits : Fin K → Bool) (t : Nat) :
    LTL.Satisfies I (w.drop t) (wordTest p bits) ↔
      ∀ j : Fin K, (I p (w (t+(2*j.val+3))) ↔ bits j = true) := by
  simp [wordTest, all_iff, List.mem_ofFn, satisfies_nextN, bitTest_iff, OmegaWord.drop]

theorem valid_iff {AP A O : Type*} {K : Nat} (I : AP → A → Prop) (w : OmegaWord A)
    (p : AP) (code : Code O K) (alphabet : List O) (t : Nat) :
    LTL.Satisfies I (w.drop t) (valid p code alphabet) ↔
      ∃ a ∈ alphabet, ∀ j : Fin K, (I p (w (t+(2*j.val+3))) ↔ code.bits a j = true) := by
  simp [valid, any_iff, wordTest_iff]

/-- Non-optimal common-width codes exist for any two finite alphabets. The
finite-index specialization `finCode` avoids the arbitrary-type enumeration. -/
theorem exists_common_codes (O₁ O₂ : Type*) [Fintype O₁] [Fintype O₂] :
    ∃ K, 0 < K ∧ Nonempty (Code O₁ K) ∧ Nonempty (Code O₂ K) := by
  refine ⟨Fintype.card O₁+Fintype.card O₂+1, by omega, ?_, ?_⟩
  · exact ⟨finiteCode O₁ _ (by omega)⟩
  · exact ⟨finiteCode O₂ _ (by omega)⟩

/-- A block cannot pass the tests for two different letters of one code. -/
theorem wordTest_unique {AP A O : Type*} {K : Nat} (I : AP → A → Prop) (w : OmegaWord A)
    (p : AP) (code : Code O K) (t : Nat) {a b : O}
    (ha : LTL.Satisfies I (w.drop t) (wordTest p (code.bits a)))
    (hb : LTL.Satisfies I (w.drop t) (wordTest p (code.bits b))) : a = b := by
  apply code.injective
  funext j
  have h₁ := (wordTest_iff I w p (code.bits a) t).mp ha j
  have h₂ := (wordTest_iff I w p (code.bits b) t).mp hb j
  cases ea : code.bits a j <;> cases eb : code.bits b j <;> simp_all

end DistributedSynthesis.BinaryWords
