/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockPresentation
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplayCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingComponentsCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D E V S N N₁ N₂ P₁ P₂ : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (graph : G ≃ Fin S) (objective : Q ≃ Fin N)
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (physical : EncodedParityTables.Data)

local notation "ctx" => blockContext (B:=B) (D:=D) (S:=S) (N:=N) env output one two outOne outTwo
local notation "encB" => FinitePresentation.encode (boundaryPresentation (B:=B) graph objective)
local notation "encM" => FinitePresentation.encode (movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective)
local notation "numE" => endNumber (B:=B) (D:=D) env
local notation "encE" => EncodedClosingLayers.encode (n:=D) (Equiv.refl (BlockSlots B)) env
local notation "encMask" => FinitePresentation.encode (maskPresentation (B:=B) (D:=D) env)

def blockData : EncodedBlock.Data :=
  (ctx,List.ofFn (fun e => List.ofFn (fun g =>
    (graph (M.step (graph.symm g) (env.symm e).2.2)).val)),
    List.ofFn (fun g => decide (graph.symm g ∈ M.accept)),physical)

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_bankData (b : BlockBoundary G Q B) : EncodedBlock.bankData ctx (encB b) =
    EncodedClosingBanks.dataEncode (Equiv.refl _) env one two output outOne outTwo b.shape D := rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_endpoint (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.endpoint ctx (numE e).val = encE e := by
  change (EncodedClosingLayers.slots (B+1,E,D)).getD (numE e).val (0,[]) = _
  rw [EncodedClosingLayers.slots_eq_ofFn (Equiv.refl _) env]
  exact EncodedClosingBanks.table_eval numE encE (0,[]) e

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_mask_get (mask : ComponentMask I₁ I₂ B D) (e : BlockEnd I₁ I₂ B D) :
    (encMask mask).getD (numE e).val false = mask e :=
  FinitePresentation.table_get numE FinitePresentation.bool mask false e

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_response (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (mask : ComponentMask I₁ I₂ B D) :
    EncodedBlock.response ctx (encM m) (encMask mask) =
      (responsePresentation env).encode (m.response mask) := by
  change ((FinitePresentation.table (maskNumber env) (responsePresentation env)).encode m.response).getD
    (@List.idxOf (List Bool) instBEqOfDecidableEq (encMask mask) (EncodedBlock.masks ctx)) ([],[]) = _
  have index : @List.idxOf (List Bool) instBEqOfDecidableEq (encMask mask) (EncodedBlock.masks ctx) =
      (maskNumber env mask).val := rfl
  rw [index]
  exact FinitePresentation.table_get (maskNumber env) (responsePresentation env) m.response ([],[]) mask

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_keep (r : BlockResponse I₁ I₂ B D) (i : BlockSlots B) :
    ((responsePresentation env).encode r).1.getD i.val 0 = (numE (r.keep i)).val :=
  FinitePresentation.table_get (Equiv.refl _) ((FinitePresentation.fin _).transport numE) r.keep 0 i

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_fold (r : BlockResponse I₁ I₂ B D) (e : BlockEnd I₁ I₂ B D) :
    ((responsePresentation env).encode r).2.getD (numE e).val 0 = (r.fold e).val :=
  FinitePresentation.table_get numE (FinitePresentation.fin _) r.fold 0 e

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_folded (r : BlockResponse I₁ I₂ B D) (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.folded ((responsePresentation env).encode r) (numE e).val =
      (numE (r.keep (r.fold e))).val := by
  rw [EncodedBlock.folded,encoded_fold,encoded_keep]

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_round_word (b : BlockBoundary G Q B) {n : Nat} (w : Fin n → I₁ × I₂ × Graph) :
    EncodedClosingBanks.word (EncodedBlock.bankData ctx (encB b)) (List.ofFn (fun i => (env (w i)).val)) =
      List.ofFn (fun i => EncodedClosingObservations.roundEncode one two (w i)) := by
  unfold EncodedClosingBanks.word
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact EncodedClosingBanks.table_eval env (EncodedClosingObservations.roundEncode one two) (0,0,0) (w i)

omit [Fintype I₁] [Fintype I₂] in
theorem encoded_observed (b : BlockBoundary G Q B) (e f : BlockEnd I₁ I₂ B D) :
    EncodedBlock.observed ctx (encB b) (numE e).val (numE f).val =
      (closingLayerShape b.shape D .one e f,closingLayerShape b.shape D .two e f) := by
  rw [EncodedBlock.observed,encoded_endpoint,encoded_endpoint,EncodedClosingBanks.observed]
  change EncodedClosingObservations.compareWords
    ((encB b).1.getD ((closingLayerRoot D f).val+(B+1)*(closingLayerRoot D e).val) (false,false))
    (EncodedClosingBanks.word (EncodedBlock.bankData ctx (encB b))
      (List.ofFn (fun i => (env (closingLayerWord D e i)).val)))
    (EncodedClosingBanks.word (EncodedBlock.bankData ctx (encB b))
      (List.ofFn (fun i => (env (closingLayerWord D f i)).val))) = _
  rw [encoded_round_word,encoded_round_word]
  have matrix := FinitePresentation.table_get
    (FiniteFunctionCodes.prod (Equiv.refl (BlockSlots B)) (Equiv.refl (BlockSlots B)))
    FinitePresentation.views (shapeEquiv b.shape) (false,false) (closingLayerRoot D e,closingLayerRoot D f)
  change (encB b).1.getD _ (false,false) = _ at matrix
  simp only [FiniteFunctionCodes.prod,Equiv.trans_apply,Equiv.prodCongr_apply,
    Equiv.refl_apply,finProdFinEquiv_apply_val,Prod.map_apply] at matrix
  rw [matrix]
  exact EncodedClosingObservations.compareWords_layer one two b.shape D e f

local notation "data" => blockData (B:=B) (D:=D) (N:=N) env output one two outOne outTwo graph M physical

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_graph_step (q : G) (e : I₁ × I₂ × Graph) :
    (data.2.1.getD (env e).val []).getD (graph q).val 0 = (graph (M.step q e.2.2)).val := by
  have row := EncodedClosingBanks.table_eval env
    (fun e => List.ofFn (fun g => (graph (M.step (graph.symm g) e.2.2)).val)) [] e
  change (List.ofFn (fun e => List.ofFn (fun g =>
    (graph (M.step (graph.symm g) (env.symm e).2.2)).val))).getD (env e).val [] = _ at row
  change ((List.ofFn _).getD (env e).val []).getD (graph q).val 0 = _
  rw [row]
  exact EncodedClosingBanks.table_eval graph (fun q => (graph (M.step q e.2.2)).val) 0 q

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_graph_layer (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (n : Nat) (hn : n ≤ D) (e : ClosingLayer (BlockSlots B) I₁ I₂ n) :
    EncodedBlock.graphAt data (encB m.source) (EncodedClosingLayers.encode (Equiv.refl _) env e) =
      (graph (closingLayerLabels (fun q e _ => M.step q e.2.2) m.source.graph m.policy n hn e)).val := by
  induction n with
  | zero =>
    change ((encB m.source).2.1).getD e.val 0 = _
    exact FinitePresentation.table_get (Equiv.refl _) ((FinitePresentation.fin S).transport graph)
      m.source.graph 0 e
  | succ n ih =>
    rcases e with ⟨old,last⟩
    have word : List.ofFn (fun i => (env (closingLayerWord (n+1) (old,last) i)).val) =
        List.ofFn (fun i => (env (closingLayerWord n old i)).val) ++ [(env last).val] := by
      rw [List.ofFn_succ',List.concat_eq_append]
      simp only [closingLayerWord,Fin.lastCases_castSucc,Fin.lastCases_last]
    unfold EncodedBlock.graphAt EncodedClosingLayers.encode
    rw [word,List.foldl_append]
    change (data.2.1.getD (env last).val []).getD
      (EncodedBlock.graphAt data (encB m.source) (EncodedClosingLayers.encode (Equiv.refl _) env old)) 0 = _
    rw [ih (by omega),encoded_graph_step]
    rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_graphEnd (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.graphEnd data (encM m) (numE e).val = (graph (blockEndGraph M m e)).val := by
  change EncodedBlock.graphAt data (encB m.source) (EncodedBlock.endpoint ctx (numE e).val) = _
  rw [encoded_endpoint]
  exact encoded_graph_layer env output one two outOne outTwo graph objective M physical m D (Nat.le_refl _) e

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_live (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.live data (encM m) (numE e).val = blockEndLive M m e := by
  rw [EncodedBlock.live,encoded_graphEnd]
  exact EncodedClosingBanks.table_eval graph (fun g => decide (g ∈ M.accept)) false (blockEndGraph M m e)

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q e y, EncodedParityTables.next physical (objective q).val
  ((env e).val*V+(output y).val) = (objective (step q e y)).val)

include transition in
omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_objective_layer {d : Nat} (m : BlockMove I₁ I₂ O₁ O₂ G Q B (d+1))
    (n : Nat) (hn : n ≤ d+1) (e : ClosingLayer (BlockSlots B) I₁ I₂ n) :
    EncodedBlock.objectiveAt
      (blockData (B:=B) (D:=d+1) (N:=N) env output one two outOne outTwo graph M physical)
      ((movePresentation env output one two outOne outTwo graph objective).encode m)
      (EncodedClosingLayers.encode (Equiv.refl _) env e) =
      (objective (closingLayerLabels step m.source.objective m.policy n hn e)).val := by
  let bank := policyBankEquiv m.policy
  have policy : closingPolicyOfBank bank = m.policy := policyBankEquiv.symm_apply_apply m.policy
  have replay := EncodedClosingReplay.replay_layer env output physical objective step transition
    bank m.source.objective n hn e
  rw [policy] at replay
  unfold EncodedBlock.objectiveAt
  change EncodedClosingReplay.replay physical
    (((boundaryPresentation graph objective).encode m.source).2.2.getD (closingLayerRoot n e).val 0)
    ((E,d+1),V,
      (EncodedClosingBanks.bankEncode (Equiv.refl _) env output bank).getD (closingLayerRoot n e).val [],
      List.ofFn (fun i => (env (closingLayerWord n e i)).val)) = _
  rw [show ((boundaryPresentation graph objective).encode m.source).2.2.getD
      (closingLayerRoot n e).val 0 = (objective (m.source.objective (closingLayerRoot n e))).val from
    FinitePresentation.table_get (Equiv.refl _) ((FinitePresentation.fin N).transport objective)
      m.source.objective 0 (closingLayerRoot n e)]
  rw [EncodedClosingBanks.bankEncode]
  have entry := EncodedClosingBanks.table_eval (Equiv.refl (BlockSlots B))
    (fun i => EncodedClosingPlans.planEncode env output (bank i)) [] (closingLayerRoot n e)
  simp only [Equiv.refl_apply] at entry
  rw [entry]
  exact replay

include transition in
omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_objectiveEnd {d : Nat} (m : BlockMove I₁ I₂ O₁ O₂ G Q B (d+1))
    (e : BlockEnd I₁ I₂ B (d+1)) :
    EncodedBlock.objectiveEnd
      (blockData (B:=B) (D:=d+1) (N:=N) env output one two outOne outTwo graph M physical)
      ((movePresentation env output one two outOne outTwo graph objective).encode m)
      (endNumber env e).val = (objective (blockEndObjective step m e)).val := by
  change EncodedBlock.objectiveAt _ _
    (EncodedBlock.endpoint (blockContext (B:=B) (D:=d+1) (S:=S) (N:=N)
      env output one two outOne outTwo) (endNumber env e).val) = _
  rw [encoded_endpoint]
  exact encoded_objective_layer env output one two outOne outTwo graph objective M physical step transition
    m (d+1) (Nat.le_refl _) e

include transition in
omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_objectiveEnd_positive (positive : 0 < D)
    (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.objectiveEnd data (encM m) (numE e).val =
      (objective (blockEndObjective step m e)).val := by
  cases D with
  | zero => omega
  | succ d =>
    exact encoded_objectiveEnd env output one two outOne outTwo graph objective M physical
      step transition m e

omit [Fintype I₁] [Fintype I₂] in
theorem encoded_coherent (positive : 0 < D) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    EncodedClosingBanks.coherent (EncodedBlock.bankData ctx (encB m.source)) (encM m).2.1 = true ↔
      ClosingPolicyCoherent m.source.shape m.policy := by
  cases D with
  | zero => omega
  | succ d =>
    let bank := policyBankEquiv m.policy
    have policy : closingPolicyOfBank bank = m.policy := policyBankEquiv.symm_apply_apply m.policy
    have h := EncodedClosingBanks.coherent_encode (Equiv.refl _) env one two output outOne outTwo m.source.shape bank
    rw [ClosingBankCoherent,policy] at h
    exact h

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_wordScenario {n : Nat} (i : BlockSlots B)
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) n) :
    EncodedClosingLayers.encode (Equiv.refl _) env (wordScenario i u) =
      (i.val,u.val.map (fun r => (env ((envRecordEquiv I₁ I₂).symm r)).val)) := by
  apply Prod.ext
  · simp only [EncodedClosingLayers.encode,wordScenario_root,Equiv.refl_apply]
  · simp only [EncodedClosingLayers.encode,wordScenario,closingLayerWord_fromWord]
    apply List.ext_getElem
    · simp only [List.length_ofFn,List.length_map,u.property]
    · intro j hj hj'
      simp only [List.getElem_ofFn,List.getElem_map,List.get_eq_getElem]
      rfl

include transition in
omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_stateAt (positive : 0 < D) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (e : BlockEnd I₁ I₂ B D) (k : Nat) :
    EncodedBlock.objectiveAt data (encM m) ((encE e).1,(encE e).2.take k) =
      (objective (blockStateAt step m e k)).val := by
  let u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) (min k D) :=
    ⟨(scenarioWord D e).val.take k,by simp [(scenarioWord D e).property]⟩
  have code : EncodedClosingLayers.encode (Equiv.refl _) env (wordScenario (closingLayerRoot D e) u) =
      ((encE e).1,(encE e).2.take k) := by
    rw [encoded_wordScenario]
    apply Prod.ext
    · rfl
    · change ((scenarioWord D e).val.take k).map _ = _
      rw [List.map_take]
      simp only [scenarioWord,List.map_ofFn,Function.comp_def,Equiv.symm_apply_apply]
      rfl
  rw [← code]
  cases D with
  | zero => omega
  | succ d =>
    exact encoded_objective_layer env output one two outOne outTwo graph objective M physical step transition
      m (min k (d+1)) (Nat.min_le_right _ _) (wordScenario (closingLayerRoot (d+1) e) u)

end
end
end Characterisation.PeriodicBlocks
