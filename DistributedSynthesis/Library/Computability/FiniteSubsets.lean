/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort

/-! # Canonical numeric codes for subsets of a finite interval

Codes are increasing lists of elements below the bound. Normalization removes
duplicates and out-of-range entries. All subset codes, and all pairs of such
codes, are enumerated uniformly; no input-dependent finite-type encoding is
assumed computable.
-/

namespace DistributedSynthesis.FiniteSubsets

def normalize (n : Nat) (xs : List Nat) : List Nat :=
  (List.range n).filter (fun q => decide (q ∈ xs))

def decode (n : Nat) (xs : List Nat) : Finset (Fin n) :=
  Finset.univ.filter (fun q => q.val ∈ xs)

@[simp] theorem mem_decode (n : Nat) (xs : List Nat) (q : Fin n) :
    q ∈ decode n xs ↔ q.val ∈ xs := by simp [decode]

@[simp] theorem mem_normalize (n q : Nat) (xs : List Nat) :
    q ∈ normalize n xs ↔ q < n ∧ q ∈ xs := by simp [normalize]

theorem normalize_nodup (n : Nat) (xs : List Nat) : (normalize n xs).Nodup :=
  List.nodup_range.filter _

theorem decode_normalize (n : Nat) (xs : List Nat) : decode n (normalize n xs) = decode n xs := by
  ext q
  simp [q.isLt]

theorem normalize_eq_iff (n : Nat) (xs ys : List Nat) :
    normalize n xs = normalize n ys ↔ decode n xs = decode n ys := by
  constructor
  · intro h
    simpa only [decode_normalize] using congrArg (decode n) h
  · intro h
    apply List.filter_congr
    intro q hq
    have he := Finset.ext_iff.mp h ⟨q, List.mem_range.mp hq⟩
    simp only [mem_decode] at he
    simp only [he]

theorem normalize_idem (n : Nat) (xs : List Nat) :
    normalize n (normalize n xs) = normalize n xs :=
  (normalize_eq_iff _ _ _).mpr (decode_normalize _ _)

theorem normalize_empty (n : Nat) : normalize n [] = [] := by simp [normalize]

theorem normalize_eq_nil_iff (n : Nat) (xs : List Nat) :
    normalize n xs = [] ↔ decode n xs = ∅ := by
  have he : decode n [] = ∅ := by ext q; simp
  simpa only [normalize_empty, he] using normalize_eq_iff n xs []

def encode {n : Nat} (s : Finset (Fin n)) : List Nat :=
  (List.range n).filter (fun q => decide (∃ h : q < n, (⟨q, h⟩ : Fin n) ∈ s))

theorem filter_range_eq_encode {n : Nat} (p : Nat → Bool) (s : Finset (Fin n))
    (hp : ∀ q : Fin n, p q.val = true ↔ q ∈ s) :
    (List.range n).filter p = encode s := by
  apply List.filter_congr
  intro q hq
  have h := hp ⟨q, List.mem_range.mp hq⟩
  apply Bool.eq_iff_iff.mpr
  simpa [List.mem_range.mp hq] using h

theorem decode_encode {n : Nat} (s : Finset (Fin n)) : decode n (encode s) = s := by
  ext q
  simp [encode, q.isLt]

theorem normalize_encode {n : Nat} (s : Finset (Fin n)) : normalize n (encode s) = encode s := by
  simp only [normalize, encode, List.filter_filter]
  apply List.filter_congr
  intro q hq
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  simp [List.mem_range.mp hq]

def codes (n : Nat) : List (List Nat) := (List.range n).sublists'

theorem encode_mem_codes {n : Nat} (s : Finset (Fin n)) : encode s ∈ codes n :=
  List.mem_sublists'.mpr List.filter_sublist

theorem normalize_mem_codes (n : Nat) (xs : List Nat) : normalize n xs ∈ codes n :=
  List.mem_sublists'.mpr List.filter_sublist

theorem codes_complete {n : Nat} (s : Finset (Fin n)) :
    ∃ xs ∈ codes n, decode n xs = s := ⟨encode s, encode_mem_codes s, decode_encode s⟩

abbrev Pair := List Nat × List Nat
def pairs (n : Nat) : List Pair := (codes n).product (codes n)
def normalizePair (n : Nat) (s : Pair) : Pair := (normalize n s.1, normalize n s.2)
def decodePair (n : Nat) (s : Pair) := (decode n s.1, decode n s.2)

theorem normalizePair_eq_iff (n : Nat) (s t : Pair) :
    normalizePair n s = normalizePair n t ↔ decodePair n s = decodePair n t := by
  simp only [normalizePair, decodePair, Prod.mk.injEq, normalize_eq_iff]

theorem pairs_complete {n : Nat} (s : Finset (Fin n) × Finset (Fin n)) :
    ∃ xs ∈ pairs n, decodePair n xs = s := by
  refine ⟨(encode s.1, encode s.2), ?_, ?_⟩
  · exact List.mem_product.mpr ⟨encode_mem_codes _, encode_mem_codes _⟩
  · simp [decodePair, decode_encode]

theorem normalize_primrec : Primrec₂ normalize := by
  have hm : PrimrecRel (fun q (xs : List Nat) => q ∈ xs) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap
  exact hm.listFilter.comp (Primrec.list_range.comp Primrec.fst) Primrec.snd

theorem codes_primrec : Primrec codes := FiniteSearch.sublists_primrec.comp Primrec.list_range
theorem pairs_primrec : Primrec pairs := FiniteSearch.product_primrec.comp codes_primrec codes_primrec
theorem normalizePair_primrec : Primrec₂ normalizePair :=
  (normalize_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair
    (normalize_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

/-- Normalization uses exactly the increasing order used by finite-set allocation. -/
theorem sort_decode (n : Nat) (xs : List Nat) :
    ((decode n xs).sort (· ≤ ·)).map Fin.val = normalize n xs := by
  have hm : (decode n xs).map Fin.valEmbedding = (normalize n xs).toFinset := by
    ext r
    simp only [Finset.mem_map, List.mem_toFinset, mem_normalize, mem_decode]
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨q.isLt, hq⟩
    · rintro ⟨hr, hm⟩
      exact ⟨⟨r, hr⟩, hm, rfl⟩
  trans ((decode n xs).map Fin.valEmbedding).sort (· ≤ ·)
  · exact Finset.map_sort Fin.valEmbedding (decode n xs) (· ≤ ·) (· ≤ ·)
      (fun _ _ _ _ => Iff.rfl)
  rw [hm]
  exact (List.toFinset_sort (· ≤ ·) (normalize_nodup n xs)).mpr
    (List.pairwise_le_range.filter _)

theorem normalize_encode_eq_sort {n : Nat} (s : Finset (Fin n)) :
    normalize n (encode s) = (s.sort (· ≤ ·)).map Fin.val := by
  rw [← sort_decode, decode_encode]

theorem encode_length {n : Nat} (s : Finset (Fin n)) : (encode s).length = s.card := by
  rw [← normalize_encode, normalize_encode_eq_sort, List.length_map, Finset.length_sort]

theorem idxOf_map_val {n : Nat} (xs : List (Fin n)) (q : Fin n) :
    (xs.map Fin.val).idxOf q.val = xs.idxOf q := by
  induction xs with
  | nil => simp
  | cons r xs ih =>
    by_cases h : r = q
    · subst r; simp
    · have hv : r.val ≠ q.val := fun he => h (Fin.ext he)
      simp [List.idxOf_cons, h, hv, Ne.symm h, Ne.symm hv, ih]

end DistributedSynthesis.FiniteSubsets
