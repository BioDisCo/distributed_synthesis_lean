/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayers
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservationsCorrect

/-! Exact enumeration of the old iterated closing scenarios. It keeps every
private-input and graph continuation without collapsing physical depths. -/
namespace Characterisation.EncodedClosingLayers
open DistributedSynthesis

variable {H I₁ I₂ : Type} {R E n : Nat}
  (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)

def encode (s : ClosingLayer H I₁ I₂ n) : Slot :=
  ((root (closingLayerRoot n s)).val,List.ofFn (fun i => (env (closingLayerWord n s i)).val))

theorem encode_fromWord (h : H) (word : Fin n → I₁ × I₂ × Graph) :
    encode root env (closingLayerFromWord h n word) = ((root h).val,List.ofFn (fun i => (env (word i)).val)) := by
  simp only [encode,closingLayerRoot_fromWord,closingLayerWord_fromWord]

theorem encode_injective : Function.Injective (encode (n:=n) root env) := by
  intro s t same
  have roots : closingLayerRoot n s = closingLayerRoot n t := root.injective (Fin.ext (congrArg Prod.fst same))
  have words : closingLayerWord n s = closingLayerWord n t := by
    funext i
    apply env.injective
    apply Fin.ext
    have entries := congrArg (fun code : Slot => code.2[i.val]?) same
    simpa only [encode,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.some.injEq] using entries
  rw [← EncodedClosingObservations.layerFromWord_word n s,
    ← EncodedClosingObservations.layerFromWord_word n t,roots,words]

theorem encode_mem (s : ClosingLayer H I₁ I₂ n) : encode root env s ∈ raw (R,E,n) :=
  List.mem_product.mpr ⟨List.mem_range.mpr (root (closingLayerRoot n s)).isLt,FiniteSearch.ofFn_mem_tables _⟩

theorem encode_sound (code : Slot) (member : code ∈ raw (R,E,n)) :
    ∃ s : ClosingLayer H I₁ I₂ n, encode root env s = code := by
  obtain ⟨hr,hw⟩ := List.mem_product.mp member
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy code.2).mp hw
  refine ⟨closingLayerFromWord (root.symm ⟨code.1,List.mem_range.mp hr⟩) n (fun i => env.symm (policy i)),?_⟩
  rw [encode_fromWord]
  apply Prod.ext
  · simp
  · simpa only [Equiv.apply_symm_apply] using equal

variable [Fintype H] [Fintype I₁] [Fintype I₂]

noncomputable def number : ClosingLayer H I₁ I₂ n ≃ Fin (count (R,E,n)) :=
  (FiniteCodeNumbering.equiv (raw (R,E,n)) (encode root env) (encode_injective root env)
    (encode_mem root env) (encode_sound root env)).trans (finCongr (by rw [count,slots]))

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem number_val (s : ClosingLayer H I₁ I₂ n) :
    (number root env s).val = name (R,E,n) (encode root env s) := rfl

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem slots_eq_ofFn : slots (R,E,n) =
    List.ofFn (fun i : Fin (count (R,E,n)) => encode root env ((number (n:=n) root env).symm i)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,count]
  · intro i hi hj
    let index : Fin (count (R,E,n)) := ⟨i,hi⟩
    have h := FiniteCodeNumbering.get_name (raw (R,E,n)) (encode root env)
      (encode_mem root env) ((number root env).symm index)
    have index_eq : name (R,E,n) (encode root env ((number root env).symm index)) = i := by
      rw [← number_val,Equiv.apply_symm_apply]
    rw [← slots] at h
    change (slots (R,E,n))[name (R,E,n) (encode root env ((number root env).symm index))]? = _ at h
    rw [index_eq,List.getElem?_eq_getElem hi] at h
    simpa only [List.getElem_ofFn] using Option.some.inj h

include root env in
theorem count_eq_card : count (R,E,n) = Fintype.card (ClosingLayer H I₁ I₂ n) := by
  have h : Fintype.card (ClosingLayer H I₁ I₂ n) = count (R,E,n) :=
    by simpa using Fintype.card_congr (number (n:=n) root env)
  exact h.symm

end Characterisation.EncodedClosingLayers
