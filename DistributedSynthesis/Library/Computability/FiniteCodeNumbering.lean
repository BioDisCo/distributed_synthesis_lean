/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Data.List.NodupEquivFin

/-! # Explicit numbering from a possibly repeated list of finite codes

The executable numbering removes repetitions and uses list positions. A
semantic finite-type equivalence certifies this same search; it does not
choose a different numbering.
-/
namespace DistributedSynthesis.FiniteCodeNumbering
variable {C : Type*} [DecidableEq C]
local instance : BEq C := instBEqOfDecidableEq

def unique (xs : List C) : List C :=
  xs.foldr (fun x ys => if x ∈ ys then ys else x :: ys) []
def name (xs : List C) (c : C) : Nat := (unique xs).idxOf c

theorem mem_unique (xs : List C) (c : C) : c ∈ unique xs ↔ c ∈ xs := by
  induction xs generalizing c with
  | nil => simp [unique]
  | cons x xs ih =>
    change c ∈ (if x ∈ unique xs then unique xs else x :: unique xs) ↔ c ∈ x :: xs
    split_ifs with h
    · have hx := (ih x).mp h
      simp only [ih, List.mem_cons]
      exact ⟨Or.inr, fun hc => hc.elim (fun he => he ▸ hx) id⟩
    · simp only [List.mem_cons, ih]

theorem unique_nodup (xs : List C) : (unique xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    change (if x ∈ unique xs then unique xs else x :: unique xs).Nodup
    split_ifs with h
    · exact ih
    · exact List.nodup_cons.mpr ⟨h,ih⟩

theorem unique_primrec [Primcodable C] : Primrec (unique (C := C)) := by
  have hm : PrimrecRel (fun (xs : List C) x => x ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.ite (hm.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))).to₂

theorem name_primrec [Primcodable C] : Primrec₂ (name (C := C)) :=
  Primrec.list_idxOf.comp Primrec.snd (unique_primrec.comp Primrec.fst)

theorem name_injective (xs : List C) {s t : C} (hs : s ∈ xs) (ht : t ∈ xs)
    (h : name xs s = name xs t) : s = t := by
  let e := (List.Nodup.getEquiv (unique xs) (unique_nodup xs)).symm
  exact congrArg Subtype.val (e.injective
    (show e ⟨s,(mem_unique xs s).mpr hs⟩ = e ⟨t,(mem_unique xs t).mpr ht⟩ from Fin.ext h))

section Semantic
variable {S : Type*} [Fintype S] (xs : List C) (encode : S → C)
  (hinj : Function.Injective encode) (hmem : ∀ s, encode s ∈ xs)
  (hcomplete : ∀ c ∈ xs, ∃ s, encode s = c)

noncomputable def codeEquiv : S ≃ {c : C // c ∈ unique xs} :=
  Equiv.ofBijective (fun s => ⟨encode s,(mem_unique xs _).mpr (hmem s)⟩)
    ⟨fun _ _ h => hinj (congrArg Subtype.val h), by
      intro c
      obtain ⟨s,hs⟩ := hcomplete c.val ((mem_unique xs c.val).mp c.property)
      exact ⟨s,Subtype.ext hs⟩⟩

noncomputable def equiv : S ≃ Fin (unique xs).length :=
  (codeEquiv xs encode hinj hmem hcomplete).trans
    (List.Nodup.getEquiv (unique xs) (unique_nodup xs)).symm

include encode hinj hmem hcomplete in
theorem card_eq : Fintype.card S = (unique xs).length := by
  simpa using Fintype.card_congr (equiv xs encode hinj hmem hcomplete)

noncomputable def number : S ≃ Fin (Fintype.card S) :=
  (equiv xs encode hinj hmem hcomplete).trans (finCongr (card_eq xs encode hinj hmem hcomplete).symm)

theorem number_val (s : S) :
    (number xs encode hinj hmem hcomplete s).val = name xs (encode s) := rfl

include hmem in
omit [Fintype S] in
theorem get_name (s : S) : (unique xs)[name xs (encode s)]? = some (encode s) :=
  List.getElem?_idxOf ((mem_unique xs _).mpr (hmem s))
end Semantic
end DistributedSynthesis.FiniteCodeNumbering
