/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PitermanComputable
import DistributedSynthesis.Library.Computability.FiniteSubsets

/-! # Uniform numeric codes for Piterman's raw compact trees

A code contains six fields: active bits, temporary names, parent indices,
labels, and the two recorded names. For an NBW with `n` states there are `2*n`
node positions. Every raw compact tree has a code in the explicit finite
enumeration. The semantic correspondence takes an explicit state numbering;
no computability of a choice of finite-type equivalence is assumed.
-/

namespace DistributedSynthesis.EncodedPitermanStates

abbrev Code := List Nat × List Nat × List Nat × List (List Nat) × Nat × Nat

def allCodes (n : Nat) : List Code :=
  (FiniteSearch.tables 2 (2 * n)).product
    ((FiniteSearch.tables (2 * n) (2 * n)).product
      ((FiniteSearch.tables (2 * n) (2 * n)).product
        ((FiniteSearch.words (FiniteSubsets.codes n) (2 * n)).product
          ((List.range (n + 1)).product (List.range (n + 1))))))

theorem allCodes_primrec : Primrec allCodes := by
  have hnodes : Primrec (fun n : Nat => 2 * n) := Primrec.nat_mul.comp (Primrec.const 2) Primrec.id
  have hb := FiniteSearch.tables_primrec.comp (Primrec.const 2) hnodes
  have ht := FiniteSearch.tables_primrec.comp hnodes hnodes
  have hl := FiniteSearch.words_primrec.comp FiniteSubsets.codes_primrec hnodes
  have hn := Primrec.list_range.comp Primrec.succ
  exact FiniteSearch.product_primrec.comp hb (FiniteSearch.product_primrec.comp ht
    (FiniteSearch.product_primrec.comp ht (FiniteSearch.product_primrec.comp hl
      (FiniteSearch.product_primrec.comp hn hn))))

def read (xs : List Nat) (q : Nat) : Nat := xs[q]?.getD 0
def readLabel (c : Code) (q : Nat) : List Nat := c.2.2.2.1[q]?.getD []

theorem read_primrec : Primrec₂ read :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const 0)

theorem readLabel_primrec : Primrec₂ readLabel :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      Primrec.snd) (Primrec.const [])

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
variable (number : A.State ≃ Fin (Fintype.card A.State))

def decodeLabel (xs : List Nat) : Finset A.State :=
  (FiniteSubsets.decode (Fintype.card A.State) xs).image number.symm

def encodeLabel (s : Finset A.State) : List Nat := FiniteSubsets.encode (s.image number)

omit [DecidableEq A.State] in
theorem filter_range_eq_encodeLabel (p : Nat → Bool) (s : Finset A.State)
    (hp : ∀ q, p (number q).val = true ↔ q ∈ s) :
    (List.range (Fintype.card A.State)).filter p = encodeLabel A number s := by
  apply FiniteSubsets.filter_range_eq_encode
  intro q
  refine (show p q.val = true ↔ number.symm q ∈ s by simpa using hp (number.symm q)).trans ?_
  constructor
  · intro h
    exact Finset.mem_image.mpr ⟨number.symm q, h, number.apply_symm_apply q⟩
  · intro h
    obtain ⟨r, hr, he⟩ := Finset.mem_image.mp h
    simpa only [← he, Equiv.symm_apply_apply] using hr

theorem decode_encodeLabel (s : Finset A.State) :
    decodeLabel A number (encodeLabel A number s) = s := by
  simp [decodeLabel, encodeLabel, FiniteSubsets.decode_encode, Finset.image_image]

theorem encodeLabel_injective : Function.Injective (encodeLabel A number) := by
  intro s t h
  simpa only [decode_encodeLabel] using congrArg (decodeLabel A number) h

theorem encodeLabel_eq_nil (s : Finset A.State) : encodeLabel A number s = [] ↔ s = ∅ := by
  have he : encodeLabel A number ∅ = [] := by simp [encodeLabel, FiniteSubsets.encode]
  rw [← he]
  exact (encodeLabel_injective A number).eq_iff

theorem mem_decodeLabel (xs : List Nat) (q : A.State) :
    q ∈ decodeLabel A number xs ↔ (number q).val ∈ xs := by
  simp [decodeLabel, Equiv.symm_apply_eq]

def decode (c : Code) : CompactTreeData A where
  active q := decide (read c.1 q.val = 1)
  name q := ⟨read c.2.1 q.val % (2 * Fintype.card A.State), Nat.mod_lt _ (by
    have := Fintype.card_pos_iff.mpr ⟨A.initial⟩; omega)⟩
  parent q := ⟨read c.2.2.1 q.val % (2 * Fintype.card A.State), Nat.mod_lt _ (by
    have := Fintype.card_pos_iff.mpr ⟨A.initial⟩; omega)⟩
  label q := decodeLabel A number (readLabel c q.val)
  e := ⟨c.2.2.2.2.1 % (Fintype.card A.State + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩
  f := ⟨c.2.2.2.2.2 % (Fintype.card A.State + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

def encode (tree : CompactTreeData A) : Code :=
  (List.ofFn (fun q => (tree.active q).toNat),
    List.ofFn (fun q => (tree.name q).val),
    List.ofFn (fun q => (tree.parent q).val),
    List.ofFn (fun q => encodeLabel A number (tree.label q)), tree.e.val, tree.f.val)

omit [DecidableEq A.State] in
theorem readLabel_encode (tree : CompactTreeData A) (q : Node A) :
    readLabel (encode A number tree) q.val = encodeLabel A number (tree.label q) := by
  simp [readLabel, encode, q.isLt]

theorem decode_encode (tree : CompactTreeData A) : decode A number (encode A number tree) = tree := by
  cases tree with
  | mk active name parent label e f =>
    simp only [encode, decode]
    congr 1
    · funext q
      simp [read]
    · funext q
      apply Fin.ext
      simp [read, Nat.mod_eq_of_lt (name q).isLt]
    · funext q
      apply Fin.ext
      simp [read, Nat.mod_eq_of_lt (parent q).isLt]
    · funext q
      simp [readLabel, decode_encodeLabel]
    · exact Fin.ext (Nat.mod_eq_of_lt e.isLt)
    · exact Fin.ext (Nat.mod_eq_of_lt f.isLt)

omit [DecidableEq A.State] in
theorem encode_mem_allCodes (tree : CompactTreeData A) :
    encode A number tree ∈ allCodes (Fintype.card A.State) := by
  have ha : List.ofFn (fun q => (tree.active q).toNat) ∈
      FiniteSearch.tables 2 (2 * Fintype.card A.State) := by
    apply (FiniteSearch.mem_tables_iff _ _ _).mpr
    refine ⟨by simp, ?_⟩
    intro x hx
    obtain ⟨q, rfl⟩ := List.mem_ofFn.mp hx
    cases tree.active q <;> decide
  have hn := FiniteSearch.ofFn_mem_tables tree.name
  have hp := FiniteSearch.ofFn_mem_tables tree.parent
  have hl := FiniteSearch.ofFn_mem_words (FiniteSubsets.codes (Fintype.card A.State))
    (fun q => encodeLabel A number (tree.label q))
    (fun q => FiniteSubsets.encode_mem_codes _)
  exact List.mem_product.mpr ⟨ha, List.mem_product.mpr ⟨hn, List.mem_product.mpr
    ⟨hp, List.mem_product.mpr ⟨hl, List.mem_product.mpr
      ⟨List.mem_range.mpr tree.e.isLt, List.mem_range.mpr tree.f.isLt⟩⟩⟩⟩⟩

/-- Every semantic raw tree is represented, including all live well-formed trees. -/
theorem allCodes_complete (tree : CompactTreeData A) :
    ∃ c ∈ allCodes (Fintype.card A.State), decode A number c = tree :=
  ⟨encode A number tree, encode_mem_allCodes A number tree, decode_encode A number tree⟩

end DistributedSynthesis.EncodedPitermanStates
