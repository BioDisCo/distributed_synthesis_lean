/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedGraphMemoryCorrect

/-! Complete enumeration of the concrete graph memory. Every enumerated
state decodes to a semantic memory, and every semantic memory is present.
The only size assumption identifies the supplied annotation table's carrier. -/
namespace Characterisation.EncodedGraphMemory
open DistributedSynthesis
local instance numberingStateBEq : BEq State := instBEqOfDecidableEq

variable {H G GQ Q I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K : Nat}
variable [Fintype H] [Fintype GQ] [Fintype Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq H] [DecidableEq GQ] [DecidableEq Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (graphs : GraphRootState GQ d K ≃ Fin S)
variable (advance : GraphRootState GQ d K → GraphRootState GQ d K)
variable (source : H → GraphRootState GQ d K) (start : H → Q)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ d) (transitions : EncodedParityTables.Data)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))


local notation "input" => dataEncode root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum
local notation "encode" => stateEncode root env output number graphs
local notation "Memory" => GraphLeaderMemory H GQ Q I₁ I₂ O₁ O₂ d K

omit [Fintype H] [Fintype GQ] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq GQ] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] in
theorem stateEncode_injective : Function.Injective (encode) := by
  intro q t equal
  have fields := equal
  simp only [stateEncode,Prod.mk.injEq] at fields
  obtain ⟨⟨hg,ha,hl⟩,hb,hf⟩ := fields
  apply Prod.ext
  · apply Prod.ext
    · funext h
      apply graphs.injective
      apply Fin.ext
      have entry :=  congrArg (fun xs : List Nat => xs.getD (root h).val 0) hg
      simpa only [FiniteFunctionCodes.eval_encode,Function.comp_apply] using entry
    · apply Prod.ext
      · funext h
        have entry :=  congrArg (fun xs : List Bool => xs.getD (root h).val false) ha
        simpa only [EncodedClosingBanks.table_eval] using entry
      · funext h
        apply number.injective
        apply Fin.ext
        have entry :=  congrArg (fun xs : List Nat => xs.getD (root h).val 0) hl
        simpa only [FiniteFunctionCodes.eval_encode,Function.comp_apply] using entry
  · exact Prod.ext (EncodedClosingBanks.bankEncode_injective root env output hb) hf

variable (size : EncodedParityTables.size transitions = J)

include size in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem stateEncode_mem (q : Memory) : encode q ∈ rawStates input := by
  change _ ∈ ((FiniteSearch.tables S R).product ((FiniteSearch.words [false,true] R).product
    (FiniteSearch.tables (EncodedParityTables.size transitions) R))).product
    ((EncodedClosingBanks.banks (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (d+1)) V).product [false,true])
  rw [size]
  refine List.mem_product.mpr ⟨List.mem_product.mpr ⟨FiniteFunctionCodes.encode_mem _ _,
    List.mem_product.mpr ⟨?_,FiniteFunctionCodes.encode_mem _ _⟩⟩,
    List.mem_product.mpr ⟨EncodedClosingBanks.bankEncode_mem root env one two output outOne outTwo shape _,?_⟩⟩
  · exact FiniteSearch.ofFn_mem_words [false,true] _ (fun i => by cases q.1.2.1 (root.symm i) <;> simp)
  · cases q.2.2 <;> simp

include size in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] in
theorem stateEncode_sound (code : State) (member : code ∈ rawStates input) : ∃ q : Memory, encode q = code := by
  change code ∈ ((FiniteSearch.tables S R).product ((FiniteSearch.words [false,true] R).product
    (FiniteSearch.tables (EncodedParityTables.size transitions) R))).product
    ((EncodedClosingBanks.banks (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (d+1)) V).product [false,true]) at member
  rw [size] at member
  obtain ⟨hm,hb⟩ := List.mem_product.mp member
  obtain ⟨hg,hr⟩ := List.mem_product.mp hm
  obtain ⟨ha,hl⟩ := List.mem_product.mp hr
  obtain ⟨hb,_⟩ := List.mem_product.mp hb
  obtain ⟨g,hg⟩ := (FiniteSearch.mem_tables_iff_policy code.1.1).mp hg
  obtain ⟨l,hl⟩ := (FiniteSearch.mem_tables_iff_policy code.1.2.2).mp hl
  obtain ⟨b,hb⟩ := EncodedClosingBanks.bankEncode_sound root env one two output outOne outTwo shape code.2.1 hb
  have length : code.1.2.1.length = R := by
    have h := (List.forall₂_iff_get.mp (List.mem_sections.mp ha)).1
    simpa only [List.length_map,List.length_range] using h
  refine ⟨((fun h => graphs.symm (g (root h)),fun h => code.1.2.1.getD (root h).val false,
    fun h => number.symm (l (root h))),b,code.2.2),?_⟩
  apply Prod.ext
  · apply Prod.ext
    · simpa only [stateEncode,FiniteFunctionCodes.encode,Function.comp_apply,Equiv.apply_symm_apply] using hg
    · apply Prod.ext
      · change List.ofFn (fun i : Fin R => code.1.2.1.getD (root (root.symm i)).val false) = code.1.2.1
        simp only [Equiv.apply_symm_apply]
        apply List.ext_getElem
        · simp only [List.length_ofFn,length]
        · intro i hi hj
          simp only [List.getElem_ofFn]
          exact List.getD_eq_getElem _ _ hj
      · simpa only [stateEncode,FiniteFunctionCodes.encode,Function.comp_apply,Equiv.apply_symm_apply] using hl
  · exact Prod.ext hb rfl

noncomputable def stateNumber : Memory ≃ Fin (states input).length :=
  FiniteCodeNumbering.equiv (rawStates input) encode
    (stateEncode_injective root env output number graphs)
    (stateEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size)
    (stateEncode_sound root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size)

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem stateNumber_val (q : Memory) :
    (stateNumber root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q).val =
      name input (encode q) := rfl

include size in
omit [DecidableEq Q] [DecidableEq O₁] [DecidableEq O₂] in
omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] in
theorem get_name (q : Memory) : (states input).getD (name input (encode q)) (([],[],[]),[],false) = encode q := by
  have mem := stateEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size q
  have get := FiniteCodeNumbering.get_name (rawStates input) encode
    (stateEncode_mem root env one two output outOne outTwo number shape recognizer graphs advance source start bank transitions slot minimum size) q
  change ((FiniteCodeNumbering.unique (rawStates input))[FiniteCodeNumbering.name (rawStates input) (encode q)]?).getD _ = _
  rw [get]
  rfl

omit [Fintype H] [Fintype Q] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq H] [DecidableEq Q] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] in
theorem initial_encode : initial input = encode ((source,(fun _ => true),start),bank,true) := by
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · exact FiniteSearch.tabulate_eq_ofFn _ _ (fun _ => rfl)
      · rfl
  · rfl

end Characterisation.EncodedGraphMemory
