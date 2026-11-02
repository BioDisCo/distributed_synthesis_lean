/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanStates

/-! # Numeric Piterman transition operations

The first stage updates every label by the NBW successor relation. The numeric
implementation normalizes source sets before searching the finite edge list;
its semantics therefore agrees even on noncanonical or malformed raw codes.
-/

namespace DistributedSynthesis.EncodedPitermanTransition
open EncodedPitermanStates

abbrev Edges := List (Nat × Nat)

def stepImage (n : Nat) (edges : Edges) (xs : List Nat) : List Nat :=
  (List.range n).filter (fun r => decide (∃ q ∈ FiniteSubsets.normalize n xs, (q, r) ∈ edges))

theorem mem_stepImage (n : Nat) (edges : Edges) (xs : List Nat) (r : Nat) :
    r ∈ stepImage n edges xs ↔ r < n ∧ ∃ q, q < n ∧ q ∈ xs ∧ (q, r) ∈ edges := by
  simp only [stepImage, List.mem_filter, List.mem_range, decide_eq_true_eq,
    FiniteSubsets.mem_normalize]
  aesop

theorem stepImage_primrec :
    Primrec (fun x : Nat × Edges × List Nat => stepImage x.1 x.2.1 x.2.2) := by
  have hm : PrimrecRel (fun (edges : Edges) (edge : Nat × Nat) => edge ∈ edges) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  have hp : PrimrecRel (fun (x : Nat × Edges × List Nat) r =>
      ∃ q ∈ FiniteSubsets.normalize x.1 x.2.2, (q, r) ∈ x.2.1) :=
    FiniteSearch.exists_mem
      (FiniteSubsets.normalize_primrec.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      (hm.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))
  exact hp.swap.listFilter.comp (Primrec.list_range.comp Primrec.fst) Primrec.id

def stage1 (n : Nat) (edges : Edges) (c : Code) : Code :=
  (c.1, c.2.1, c.2.2.1,
    (List.range (2 * n)).map (fun q => stepImage n edges (readLabel c q)), n, n)

theorem stage1_primrec :
    Primrec (fun x : Nat × Edges × Code => stage1 x.1 x.2.1 x.2.2) := by
  have hn : Primrec (fun x : Nat × Edges × Code => x.1) := Primrec.fst
  have he : Primrec (fun x : Nat × Edges × Code => x.2.1) := Primrec.fst.comp Primrec.snd
  have hc : Primrec (fun x : Nat × Edges × Code => x.2.2) := Primrec.snd.comp Primrec.snd
  exact (Primrec.fst.comp hc).pair ((Primrec.fst.comp (Primrec.snd.comp hc)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))).pair
      ((Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) hn))
        (stepImage_primrec.comp ((hn.comp Primrec.fst).pair
          ((he.comp Primrec.fst).pair
            (readLabel_primrec.comp (hc.comp Primrec.fst) Primrec.snd)))).to₂).pair (hn.pair hn))))

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
variable (number : A.State ≃ Fin (Fintype.card A.State))

theorem stepImage_correct (edges : Edges) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (xs : List Nat) :
    decodeLabel A number (stepImage (Fintype.card A.State) edges xs) =
      CompactTreeData.stepImage A letter (decodeLabel A number xs) := by
  ext r
  rw [mem_decodeLabel, mem_stepImage, CompactTreeData.mem_stepImage]
  constructor
  · rintro ⟨_, q, hq, hm, hqr⟩
    refine ⟨number.symm ⟨q, hq⟩, ?_, ?_⟩
    · simpa only [mem_decodeLabel, Equiv.apply_symm_apply] using hm
    · apply (he _ r).mp
      simpa only [Equiv.apply_symm_apply] using hqr
  · rintro ⟨q, hq, hqr⟩
    exact ⟨(number r).isLt, (number q).val, (number q).isLt,
      (mem_decodeLabel A number xs q).mp hq, (he q r).mpr hqr⟩

theorem stage1_correct (edges : Edges) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (c : Code) :
    decode A number (stage1 (Fintype.card A.State) edges c) =
      (decode A number c).stage1 A letter := by
  unfold stage1 decode CompactTreeData.stage1
  congr 1
  · funext q
    simp only [readLabel, List.getElem?_map, List.getElem?_range q.isLt,
      Option.map_some, Option.getD_some]
    exact stepImage_correct A number edges letter he _
  · exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_succ_self _))
  · exact Fin.ext (Nat.mod_eq_of_lt (Nat.lt_succ_self _))

theorem stage1_eq_executable (edges : Edges) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (decStep : ∀ q a r, Decidable (A.step q a r)) (c : Code) :
    decode A number (stage1 (Fintype.card A.State) edges c) =
      Computable.stage1 A decStep (decode A number c) letter :=
  (stage1_correct A number edges letter he c).trans (Computable.stage1_eq A decStep _ letter).symm

/-- The first stage also preserves the canonical code representation exactly. -/
theorem stage1_encode (edges : Edges) (letter : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ edges ↔ A.step q letter r)
    (decStep : ∀ q a r, Decidable (A.step q a r)) (tree : CompactTreeData A) :
    stage1 (Fintype.card A.State) edges (encode A number tree) =
      encode A number (Computable.stage1 A decStep tree letter) := by
  rw [Computable.stage1_eq]
  unfold stage1 encode
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))))
  apply FiniteSearch.tabulate_eq_ofFn (n := 2 * Fintype.card A.State)
  intro q
  change stepImage _ edges (readLabel (encode A number tree) q.val) =
    encodeLabel A number (CompactTreeData.stepImage A letter (tree.label q))
  rw [readLabel_encode]
  apply filter_range_eq_encodeLabel
  intro r
  have hm := (mem_decodeLabel A number
    (stepImage (Fintype.card A.State) edges (encodeLabel A number (tree.label q))) r).symm
  rw [stepImage_correct A number edges letter he, decode_encodeLabel] at hm
  simpa only [stepImage, List.mem_filter, List.mem_range, (number r).isLt, true_and,
    decide_eq_true_eq] using hm

end DistributedSynthesis.EncodedPitermanTransition
