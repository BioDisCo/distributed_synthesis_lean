/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockPriorityCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderProgressCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048
attribute [local instance] Classical.propDecidable

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D E V S N N₁ N₂ P₁ P₂ K : Nat}
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (graph : G ≃ Fin S) (objective : Q ≃ Fin N)
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (physical : EncodedParityTables.Data)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (χ : Q → Nat)
variable (transition : ∀ q e y, EncodedParityTables.next physical (objective q).val
  ((env e).val*V+(output y).val) = (objective (step q e y)).val)
variable (ranks : ∀ q, EncodedParityTables.priority physical (objective q).val = χ q)
variable (positive : 0 < D)
variable (first : BlockOutcome I₁ I₂ G Q B D) (code : HandoverCode B K)

local notation "Move" => BlockMove I₁ I₂ O₁ O₂ G Q B D
local notation "Outcome" => BlockOutcome I₁ I₂ G Q B D
local notation "ctx" => blockContext (B:=B) (D:=D) (S:=S) (N:=N) env output one two outOne outTwo
local notation "data" => blockData (B:=B) (D:=D) (N:=N) env output one two outOne outTwo graph M physical
local notation "movP" => movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective
local notation "obsP" => outcomePresentation (B:=B) (D:=D) env graph objective
local notation "encM" => FinitePresentation.encode movP
local notation "encO" => FinitePresentation.encode obsP
local notation "system" => hiddenCodeContinuitySystem (handoverPriorityDPA B K) code (BlockEdge (B:=B) (D:=D) (K:=K) M step χ)

def blockInput : EncodedBlock.Input := (data,K,encO first,(code.1.val,code.2.val))
local notation "input" => blockInput env output one two outOne outTwo graph objective M physical first code

def moveNumber : Move ≃ Fin (EncodedBlock.moves ctx).length := (movP).number

def outcomeNumber : Outcome ≃ Fin (EncodedBlock.outcomes ctx).length := (obsP).number

local notation "numM" => moveNumber env output one two outOne outTwo graph objective
local notation "numO" => outcomeNumber (B:=B) (D:=D) env output one two outOne outTwo graph objective

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem moveNumber_get (m : Move) : (EncodedBlock.moves ctx)[(numM m).val] = encM m := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (numM m).isLt).symm.trans
  exact FiniteCodeNumbering.get_name (movP).codes (movP).encode (movP).member m

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem outcomeNumber_get (b : Outcome) : (EncodedBlock.outcomes ctx)[(numO b).val] = encO b := by
  apply Option.some.inj
  apply (List.getElem?_eq_getElem (numO b).isLt).symm.trans
  exact FiniteCodeNumbering.get_name (obsP).codes (obsP).encode (obsP).member b

local notation "stateNum" => EncodedLeaderProgress.stateNumber B 0 K
local notation "stateEnc" => @EncodedLeaderProgress.encode B K

include transition ranks positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] [DecidableEq O₁] [DecidableEq O₂] in
theorem encoded_threadStep (q : EncodedLeaderProgress.SemanticState B K) (a : Move × Outcome)
    (r : HandoverCode B K) :
    EncodedBlock.threadStep data (stateEnc q) (encM a.1,encO a.2) (r.1.val,r.2.val) =
      stateEnc ((system).step q a r) := by
  cases q with
  | dead => rfl
  | live old control =>
    have checked := encoded_edge env output one two outOne outTwo graph objective M physical step χ
      transition ranks positive old r a.1 a.2
    by_cases h : BlockEdge M step χ old a.1 a.2 r
    · rw [hiddenCodeContinuitySystem_step_live_of _ _ _ _ _ _ _ h]
      change (if EncodedBlock.Edge data (old.1.val,old.2.val) (encM a.1) (encO a.2) (r.1.val,r.2.val)
        then some (r.1.val,r.2.val,r.2.val) else none) = _
      exact if_pos (checked.mpr h)
    · rw [hiddenCodeContinuitySystem_step_live_dead_of _ _ _ _ _ _ _ h]
      change (if EncodedBlock.Edge data (old.1.val,old.2.val) (encM a.1) (encO a.2) (r.1.val,r.2.val)
        then some (r.1.val,r.2.val,r.2.val) else none) = none
      exact if_neg (fun h' => h (checked.mp h'))

include transition ranks positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] [DecidableEq O₁] [DecidableEq O₂] in
theorem block_edgeRow_correct (q r : EncodedLeaderProgress.SemanticState B K) (a : Move × Outcome) :
    ((stateNum q).val,(stateNum r).val) ∈ EncodedBlock.edgeRow input (encM a.1,encO a.2) ↔
      ∃ resolution : HandoverCode B K, r = (system).step q a resolution := by
  simp only [EncodedLeaderProgress.stateNumber_val,EncodedBlock.edgeRow]
  constructor
  · rintro member
    obtain ⟨old,hold,h⟩ := List.mem_flatMap.mp member
    obtain ⟨res,hres,equal⟩ := List.mem_map.mp h
    have oldRaw : old ∈ EncodedLeaderProgress.rawStates (B,0,K) := by
      change old ∈ EncodedLeaderProgress.states (B,0,K) at hold
      rwa [EncodedLeaderProgress.states,FiniteCodeNumbering.mem_unique] at hold
    obtain ⟨s,rfl⟩ := EncodedLeaderProgress.codes_sound B 0 K old oldRaw
    have hs : s=q := EncodedLeaderProgress.encode_injective
      (FiniteCodeNumbering.name_injective _ (EncodedLeaderProgress.encode_mem B 0 K s)
        (EncodedLeaderProgress.encode_mem B 0 K q) (congrArg Prod.fst equal))
    subst s
    obtain ⟨hi,hj⟩ := List.mem_product.mp hres
    let resolution : HandoverCode B K := (⟨res.1,List.mem_range.mp hi⟩,⟨res.2,List.mem_range.mp hj⟩)
    have he := congrArg Prod.snd equal
    change EncodedLeaderProgress.name (B,0,K)
      (EncodedBlock.threadStep data (stateEnc q) (encM a.1,encO a.2) (resolution.1.val,resolution.2.val)) =
      EncodedLeaderProgress.name (B,0,K) (stateEnc r) at he
    rw [encoded_threadStep env output one two outOne outTwo graph objective M physical step χ
      transition ranks positive code] at he
    have target := EncodedLeaderProgress.encode_injective
      (FiniteCodeNumbering.name_injective _ (EncodedLeaderProgress.encode_mem B 0 K ((system).step q a resolution))
        (EncodedLeaderProgress.encode_mem B 0 K r) he)
    exact ⟨resolution,target.symm⟩
  · rintro ⟨resolution,rfl⟩
    apply List.mem_flatMap.mpr
    refine ⟨stateEnc q,?_,List.mem_map.mpr ⟨(resolution.1.val,resolution.2.val),?_,?_⟩⟩
    · change stateEnc q ∈ EncodedLeaderProgress.states (B,0,K)
      rw [EncodedLeaderProgress.states,FiniteCodeNumbering.mem_unique]
      exact EncodedLeaderProgress.encode_mem B 0 K q
    · exact List.mem_product.mpr ⟨List.mem_range.mpr resolution.1.isLt,List.mem_range.mpr resolution.2.isLt⟩
    · exact Prod.ext rfl (congrArg (EncodedLeaderProgress.name (B,0,K))
        (encoded_threadStep env output one two outOne outTwo graph objective M physical step χ
          transition ranks positive code q a resolution))

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem block_edgeRows_length : (EncodedBlock.edgeRows input).length =
    (EncodedBlock.moves ctx).length * (EncodedBlock.outcomes ctx).length := by
  simp only [EncodedBlock.edgeRows,List.length_map]
  exact List.length_product _ _

def rowNumber : (Move × Outcome) ≃ Fin (EncodedBlock.edgeRows input).length :=
  (FiniteFunctionCodes.prod numM numO).trans
    (finCongr (block_edgeRows_length env output one two outOne outTwo graph objective M physical first code).symm)

local notation "numRow" => rowNumber env output one two outOne outTwo graph objective M physical first code

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem rowNumber_val (a : Move × Outcome) :
    (numRow a).val = (numM a.1).val * (EncodedBlock.outcomes ctx).length + (numO a.2).val := by
  change (numO a.2).val + (EncodedBlock.outcomes ctx).length * (numM a.1).val = _
  ac_rfl

omit [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q] in
theorem block_edgeRows_get (a : Move × Outcome) :
    (EncodedBlock.edgeRows input).getD (numRow a).val [] =
      EncodedBlock.edgeRow input (encM a.1,encO a.2) := by
  rw [rowNumber_val]
  have h := FinitePresentation.lookup2 (EncodedBlock.moves ctx) (EncodedBlock.outcomes ctx)
    (fun m b => EncodedBlock.edgeRow input (m,b)) (numM a.1) (numO a.2) []
  rw [moveNumber_get,outcomeNumber_get] at h
  simpa only [EncodedBlock.edgeRows,List.product,List.map_flatMap,List.map_map,Function.comp_def] using h

include transition ranks positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] [DecidableEq O₁] [DecidableEq O₂] in
theorem block_edgeRows_correct (q r : EncodedLeaderProgress.SemanticState B K)
    (a : Fin (EncodedBlock.edgeRows input).length) :
    ((stateNum q).val,(stateNum r).val) ∈ (EncodedBlock.edgeRows input)[a.val]?.getD [] ↔
      ∃ resolution : HandoverCode B K, r = (system).step q ((numRow).symm a) resolution := by
  rw [← List.getD_eq_getElem?_getD]
  have h := block_edgeRows_get env output one two outOne outTwo graph objective M physical first code ((numRow).symm a)
  simp only [Equiv.apply_symm_apply] at h
  rw [h]
  exact block_edgeRow_correct env output one two outOne outTwo graph objective M physical step χ
    transition ranks positive first code q r _

def blockProgress : DetParityAutomaton (Move × Outcome) :=
  (EncodedThreadCompiler.automaton (EncodedBlock.threadData input)).comap numRow

include transition ranks positive in
omit [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q] [DecidableEq O₁] [DecidableEq O₂] in
theorem blockProgress_accepts (word : OmegaWord (Move × Outcome)) :
    (blockProgress env output one two outOne outTwo graph objective M physical first code).Accepts word ↔
      (system).universalRunDPA.Accepts word := by
  letI : Fintype (system).Resolution := inferInstanceAs (Fintype (HandoverCode B K))
  letI : DecidableEq (system).State := Classical.typeDecidableEq _
  let ps := (EncodedBlock.threadStates input).map EncodedLeaderProgress.priority
  let es := EncodedBlock.edgeRows input
  have priority : ∀ q, ps.getD (stateNum q).val 0 = (system).priority q :=
    EncodedLeaderProgress.priority_lookup (Q:=Unit) code
  have range : ∀ p, p ∈ ps ↔ p ∈ (system).priorityRange :=
    EncodedLeaderProgress.priority_range (Q:=Unit) code
  let numericWord := OmegaWord.map numRow word
  have correct := EncodedFiniteThreads.accepts_iff (system) stateNum ps priority range es (numRow).symm
    (fun q a r => block_edgeRows_correct env output one two outOne outTwo graph objective M physical
      step χ transition ranks positive first code q r a) numericWord
  have initialName : EncodedBlock.stateName input
      (EncodedLeaderProgress.initial (EncodedBlock.progressContext input,input.2.2.2)) =
      (stateNum (system).initial).val := by
    change EncodedLeaderProgress.name (B,0,K) (EncodedLeaderProgress.initial ((B,0,K),(code.1.val,code.2.val))) = _
    rw [EncodedLeaderProgress.initial_encode (Q:=Unit) (N:=0) code,EncodedLeaderProgress.stateNumber_val]
    rfl
  have same := EncodedThreadCompiler.config_accepts_congr ps es
    (EncodedLeaderProgress.card_eq B 0 K).symm initialName numericWord
  have decoded : OmegaWord.map (numRow).symm numericWord = word := by
    funext n
    exact (numRow).symm_apply_apply (word n)
  rw [decoded] at correct
  rw [blockProgress,DetParityAutomaton.comap_accepts_iff]
  exact same.trans correct

end
end
end Characterisation.PeriodicBlocks
