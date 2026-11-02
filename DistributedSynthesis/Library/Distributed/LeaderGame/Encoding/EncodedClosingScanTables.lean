/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScans
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayersCorrect

/-! Exact coding of all bounded scan tables. The domain includes every
source and every hypothetical input/graph prefix, including depth zero. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis

abbrev Scenario (H I₁ I₂ : Type) (D : Nat) := Σ n : Fin (D+1), ClosingLayer H I₁ I₂ n.val

variable {H I₁ I₂ Q : Type} {R E M D : Nat}
  (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)

def scenarioEncode (s : Scenario H I₁ I₂ D) : EncodedClosingLayers.Slot := EncodedClosingLayers.encode root env s.2

theorem scenarioEncode_injective : Function.Injective (scenarioEncode (D:=D) root env) := by
  rintro ⟨n,s⟩ ⟨m,t⟩ equal
  have length := congrArg (fun x : EncodedClosingLayers.Slot => x.2.length) equal
  simp only [scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn] at length
  have time : n=m := Fin.ext length
  subst m
  have same := EncodedClosingLayers.encode_injective root env equal
  exact congrArg (Sigma.mk n) same

theorem scenarioEncode_mem (s : Scenario H I₁ I₂ D) : scenarioEncode root env s ∈ raw (R,E,D) := by
  apply List.mem_flatMap.mpr
  refine ⟨s.1.val,List.mem_range.mpr s.1.isLt,?_⟩
  rw [EncodedClosingLayers.slots,FiniteCodeNumbering.mem_unique]
  exact EncodedClosingLayers.encode_mem root env s.2

theorem scenarioEncode_sound (code : EncodedClosingLayers.Slot) (member : code ∈ raw (R,E,D)) :
    ∃ s : Scenario H I₁ I₂ D, scenarioEncode root env s = code := by
  obtain ⟨n,hn,hs⟩ := List.mem_flatMap.mp member
  rw [EncodedClosingLayers.slots,FiniteCodeNumbering.mem_unique] at hs
  obtain ⟨s,encoded⟩ := EncodedClosingLayers.encode_sound (n:=n) root env code hs
  exact ⟨⟨⟨n,List.mem_range.mp hn⟩,s⟩,encoded⟩

variable [Fintype H] [Fintype I₁] [Fintype I₂]

noncomputable def scenarioNumber : Scenario H I₁ I₂ D ≃ Fin (domain (R,E,D)).length := by
  letI : Fintype (Scenario H I₁ I₂ D) := inferInstanceAs (Fintype (Σ n : Fin (D+1), ClosingLayer H I₁ I₂ n.val))
  exact (FiniteCodeNumbering.equiv (raw (R,E,D)) (scenarioEncode root env)
    (scenarioEncode_injective root env) (scenarioEncode_mem root env) (scenarioEncode_sound root env)).trans
    (finCongr (by rw [domain]))

variable (states : Q ≃ Fin M)

noncomputable def tableEncode (table : (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Q) : List Nat :=
  FiniteFunctionCodes.encode (scenarioNumber root env) (fun s => states (table s.1 s.2))

omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem domain_eq_ofFn : domain (R,E,D) =
    List.ofFn (fun i : Fin (domain (R,E,D)).length =>
      scenarioEncode root env ((scenarioNumber (D:=D) root env).symm i)) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn]
  · intro i hi hj
    let index : Fin (domain (R,E,D)).length := ⟨i,hi⟩
    have h := FiniteCodeNumbering.get_name (raw (R,E,D)) (scenarioEncode root env)
      (scenarioEncode_mem root env) ((scenarioNumber root env).symm index)
    have index_eq : name (R,E,D) (scenarioEncode root env ((scenarioNumber root env).symm index)) = i := by
      change (scenarioNumber root env ((scenarioNumber root env).symm index)).val = i
      rw [Equiv.apply_symm_apply]
    rw [← domain] at h
    change (domain (R,E,D))[name (R,E,D) (scenarioEncode root env ((scenarioNumber root env).symm index))]? = _ at h
    rw [index_eq,List.getElem?_eq_getElem hi] at h
    simpa only [List.getElem_ofFn] using Option.some.inj h

section
omit [Fintype H] [Fintype I₁] [Fintype I₂]

theorem entry_encode (table : (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Q)
    (n : Fin (D+1)) (s : ClosingLayer H I₁ I₂ n.val) :
    entry (R,E,D) (tableEncode root env states table) (scenarioEncode root env ⟨n,s⟩) = (states (table n s)).val :=
  FiniteFunctionCodes.eval_encode (scenarioNumber root env) (fun s => states (table s.1 s.2)) ⟨n,s⟩

theorem tableEncode_mem (table : (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Q) :
    tableEncode root env states table ∈ FiniteSearch.tables M (domain (R,E,D)).length :=
  FiniteFunctionCodes.encode_mem _ _

theorem tableEncode_sound (code : List Nat) (member : code ∈ FiniteSearch.tables M (domain (R,E,D)).length) :
    ∃ table : (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Q, tableEncode root env states table = code := by
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy code).mp member
  refine ⟨fun n s => states.symm (policy (scenarioNumber root env ⟨n,s⟩)),?_⟩
  simpa only [tableEncode,FiniteFunctionCodes.encode,Sigma.eta,Equiv.apply_symm_apply] using equal

theorem tableEncode_injective : Function.Injective (tableEncode (D:=D) root env states) := by
  intro left right equal
  funext n s
  apply states.injective
  apply Fin.ext
  have h := congrArg (fun code => entry (R,E,D) code (scenarioEncode root env ⟨n,s⟩)) equal
  simpa only [entry_encode] using h

theorem scenarioEncode_parent {n : Nat} (bound : n+1 ≤ D) (s : ClosingLayer H I₁ I₂ (n+1)) :
    parent (scenarioEncode (D:=D) root env ⟨⟨n+1,by omega⟩,s⟩) =
      scenarioEncode (D:=D) root env ⟨⟨n,by omega⟩,s.1⟩ := by
  apply Prod.ext
  · rfl
  · simp only [parent,scenarioEncode,EncodedClosingLayers.encode,List.length_ofFn]
    rw [Nat.add_sub_cancel,List.ofFn_succ',List.concat_eq_append]
    simp only [closingLayerWord,Fin.lastCases_castSucc,Fin.lastCases_last,List.take_append,
      List.length_ofFn,Nat.sub_self,List.take_zero,List.append_nil]
    exact List.take_of_length_le (by simp)

end

end Characterisation.EncodedClosingScans
