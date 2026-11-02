/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanks
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingPlansCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservationsCorrect

/-! Exactness of the numeric whole-bank consistency test. All numbered
root/scenario pairs are represented, including empty root alphabets. -/
namespace Characterisation.EncodedClosingBanks
open DistributedSynthesis
open EncodedClosingPlans EncodedClosingObservations

theorem table_eval {X Y : Type} {n : Nat} (e : X ≃ Fin n) (f : X → Y)
    (fallback : Y) (x : X) :
    (List.ofFn (fun i => f (e.symm i))).getD (e x).val fallback = f x := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

variable {H I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ D : Nat}
  (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
  (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
  (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)

def dataEncode (shape : InputShape H) (horizon : Nat) : Data :=
  (R,(E,horizon),List.ofFn (fun i => roundEncode one two (env.symm i)),
    List.ofFn (fun i => ((outOne (output.symm i).1).val,(outTwo (output.symm i).2).val)),
    List.ofFn (fun i => let hk := (FiniteFunctionCodes.prod root root).symm i
      (shape .one hk.1 hk.2,shape .two hk.1 hk.2)))

noncomputable def bankEncode (bank : H → LeaderClosingPlan I₁ I₂ O₁ O₂ D) : Bank :=
  List.ofFn (fun i => planEncode env output (bank (root.symm i)))

def slotEncode (h : H) (s : ClosingScenario I₁ I₂ D) : Slot :=
  ((root h).val,scenarioEncode env s)

theorem bankEncode_mem (shape : InputShape H) (bank : H → LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    bankEncode root env output bank ∈ banks (dataEncode root env one two output outOne outTwo shape D) V :=
  FiniteSearch.ofFn_mem_words _ _ (fun _ => planEncode_mem env output _)

theorem bankEncode_injective : Function.Injective (bankEncode (D:=D) root env output) := by
  intro left right equal
  funext h
  apply planEncode_injective env output
  have entries := congrArg (fun bank : Bank => bank.getD (root h).val []) equal
  unfold bankEncode at entries
  dsimp only at entries
  rw [table_eval root (fun h => planEncode env output (left h)) [] h,
    table_eval root (fun h => planEncode env output (right h)) [] h] at entries
  exact entries

theorem bankEncode_sound (shape : InputShape H) (code : Bank)
    (member : code ∈ banks (dataEncode root env one two output outOne outTwo shape D) V) :
    ∃ bank : H → LeaderClosingPlan I₁ I₂ O₁ O₂ D, bankEncode root env output bank = code := by
  classical
  have hrows := List.forall₂_iff_get.mp (List.mem_sections.mp member)
  have length : code.length = R := by simpa using hrows.1
  have rowMem (h : H) : code.getD (root h).val [] ∈ plans (E,D) V := by
    have hc : (root h).val < code.length := by simpa only [length] using (root h).isLt
    have h := hrows.2 (root h).val hc (by simpa only [List.length_map,List.length_range,roots,dataEncode] using (root h).isLt)
    simpa only [List.getD_eq_getElem _ _ hc,List.get_eq_getElem,List.getElem_map,
      List.getElem_range,context,dataEncode] using h
  choose bank entries using fun h => planEncode_sound env output _ (rowMem h)
  refine ⟨bank,?_⟩
  apply List.ext_getElem
  · simpa only [bankEncode,List.length_ofFn] using length.symm
  · intro i hi hj
    have hi' : i < R := by simpa only [bankEncode,List.length_ofFn] using hi
    have h := entries (root.symm ⟨i,hi'⟩)
    simpa only [bankEncode,List.getElem_ofFn,Equiv.apply_symm_apply,List.getD_eq_getElem _ _ hj] using h

theorem slotEncode_mem (shape : InputShape H) (h : H) (s : ClosingScenario I₁ I₂ D) :
    slotEncode root env h s ∈ slots (dataEncode root env one two output outOne outTwo shape D) := by
  apply List.mem_product.mpr
  refine ⟨List.mem_range.mpr (root h).isLt,?_⟩
  rw [scenarios,FiniteCodeNumbering.mem_unique]
  exact scenarioEncode_mem env s

theorem slotEncode_sound (shape : InputShape H) (code : Slot)
    (member : code ∈ slots (dataEncode root env one two output outOne outTwo shape D)) :
    ∃ (h : H) (s : ClosingScenario I₁ I₂ D), slotEncode root env h s = code := by
  obtain ⟨hr,hw⟩ := List.mem_product.mp member
  rw [scenarios,FiniteCodeNumbering.mem_unique] at hw
  obtain ⟨s,hs⟩ := scenarioEncode_sound (D:=D) env code.2 hw
  refine ⟨root.symm ⟨code.1,List.mem_range.mp hr⟩,s,?_⟩
  apply Prod.ext
  · change (root (root.symm _)).val = code.1
    simp
  · exact hs

theorem word_encode (shape : InputShape H) (s : ClosingScenario I₁ I₂ D) :
    word (dataEncode root env one two output outOne outTwo shape D) (scenarioEncode env s) =
      List.ofFn (fun i => roundEncode one two (s.2.2 i)) := by
  unfold word scenarioEncode
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact table_eval env (roundEncode one two) (0,0,0) (s.2.2 i)

theorem response_encode (shape : InputShape H) (bank : H → LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (h : H) (s : ClosingScenario I₁ I₂ D) :
    response (dataEncode root env one two output outOne outTwo shape D)
      (bankEncode root env output bank) (slotEncode root env h s) =
      ((outOne (bank h s).1).val,(outTwo (bank h s).2).val) := by
  rw [response]
  change (List.ofFn (fun i => ((outOne (output.symm i).1).val,(outTwo (output.symm i).2).val))).getD
    (entry (E,D) ((List.ofFn (fun i => planEncode env output (bank (root.symm i)))).getD (root h).val [])
      (scenarioEncode env s)) (0,0) = _
  rw [table_eval root (fun h => planEncode env output (bank h)) [] h,entry_encode]
  exact table_eval output (fun out => ((outOne out.1).val,(outTwo out.2).val)) (0,0) (bank h s)

variable [DecidableEq I₁] [DecidableEq I₂]

theorem observed_encode (shape : InputShape H) (h k : H) (t : Fin D)
    (left right : Fin (t.val+1) → I₁ × I₂ × Graph) :
    observed (dataEncode root env one two output outOne outTwo shape D)
      (slotEncode root env h ((),⟨t,left⟩)) (slotEncode root env k ((),⟨t,right⟩)) =
      (closingLayerShape shape (t.val+1) .one (closingLayerFromWord h _ left) (closingLayerFromWord k _ right),
       closingLayerShape shape (t.val+1) .two (closingLayerFromWord h _ left) (closingLayerFromWord k _ right)) := by
  rw [observed]
  simp only [slotEncode]
  rw [word_encode,word_encode]
  have matrixEntry : (matrix (dataEncode root env one two output outOne outTwo shape D)).getD
      ((root k).val+R*(root h).val) (false,false) = (shape .one h k,shape .two h k) :=
    table_eval (FiniteFunctionCodes.prod root root) (fun hk => (shape .one hk.1 hk.2,shape .two hk.1 hk.2))
      (false,false) (h,k)
  change compareWords ((matrix _).getD ((root k).val+R*(root h).val) (false,false)) _ _ = _
  rw [matrixEntry,compareWords,paired_ofFn,compare_fromWord]

/-- A numeric bank passes exactly when the original bounded closing policy
is implementable by local responses on its entire represented family. -/
theorem coherent_encode (shape : InputShape H) (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) :
    coherent (dataEncode root env one two output outOne outTwo shape (D+1))
      (bankEncode root env output bank) = true ↔ ClosingBankCoherent shape bank := by
  rw [coherent,decide_eq_true_eq]
  constructor
  · intro test t
    have pair (s r : ClosingLayer H I₁ I₂ (t.val+1)) :=
      test (slotEncode root env (closingLayerRoot _ s) ((),⟨t,closingLayerWord _ s⟩))
        (slotEncode_mem root env one two output outOne outTwo shape _ _)
        (slotEncode root env (closingLayerRoot _ r) ((),⟨t,closingLayerWord _ r⟩))
        (slotEncode_mem root env one two output outOne outTwo shape _ _)
    have exactPair (s r : ClosingLayer H I₁ I₂ (t.val+1)) :
        (closingLayerShape shape (t.val+1) .one s r = true →
          (closingPolicyOfBank bank t s).1 = (closingPolicyOfBank bank t r).1) ∧
        (closingLayerShape shape (t.val+1) .two s r = true →
          (closingPolicyOfBank bank t s).2 = (closingPolicyOfBank bank t r).2) := by
      have checked := pair s r (by simp [slotEncode,scenarioEncode])
      rw [observed_encode,layerFromWord_word,layerFromWord_word,response_encode,response_encode] at checked
      exact ⟨fun h => outOne.injective (Fin.ext (checked.1 h)),
        fun h => outTwo.injective (Fin.ext (checked.2 h))⟩
    exact ⟨fun s r => (exactPair s r).1,fun s r => (exactPair s r).2⟩
  · intro coherentBank left hl right hr time
    obtain ⟨h,s,rfl⟩ := slotEncode_sound root env one two output outOne outTwo shape left hl
    obtain ⟨k,r,rfl⟩ := slotEncode_sound root env one two output outOne outTwo shape right hr
    rcases s with ⟨⟨⟩,t,word⟩
    rcases r with ⟨⟨⟩,u,word'⟩
    have equalTime : t=u := Fin.ext (by simpa [slotEncode,scenarioEncode] using time)
    subst u
    rw [observed_encode,response_encode,response_encode]
    have checked := coherentBank t
    have outputs (h : H) (word : Fin (t.val+1) → I₁ × I₂ × Graph) :
        closingPolicyOfBank bank t (closingLayerFromWord h _ word) = bank h ((),⟨t,word⟩) := by
      simp only [closingPolicyOfBank,closingLayerRoot_fromWord,closingLayerWord_fromWord]
    constructor
    · intro eq
      have h := checked.1 (closingLayerFromWord h _ word) (closingLayerFromWord k _ word') eq
      rw [outputs,outputs] at h
      exact congrArg (fun value => (outOne value).val) h
    · intro eq
      have h := checked.2 (closingLayerFromWord h _ word) (closingLayerFromWord k _ word') eq
      rw [outputs,outputs] at h
      exact congrArg (fun value => (outTwo value).val) h

end Characterisation.EncodedClosingBanks
