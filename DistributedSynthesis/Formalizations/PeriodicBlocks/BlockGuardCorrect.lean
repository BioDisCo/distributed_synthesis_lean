/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockTableCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 2400000
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
local notation "data" => blockData (B:=B) (D:=D) (N:=N) env output one two outOne outTwo graph M physical
local notation "encB" => FinitePresentation.encode (boundaryPresentation (B:=B) graph objective)
local notation "encM" => FinitePresentation.encode (movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective)
local notation "encO" => FinitePresentation.encode (outcomePresentation (B:=B) (D:=D) env graph objective)
local notation "numE" => endNumber (B:=B) (D:=D) env
local notation "encMask" => FinitePresentation.encode (maskPresentation (B:=B) (D:=D) env)

omit [Fintype I₁] [Fintype I₂] in
theorem encoded_components (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    EncodedBlock.components data (encM m) =
      EncodedClosingComponents.encode numE (blockEndShape m) (blockEndLive M m) := by
  have n : EncodedBlock.endCount ctx = EncodedClosingLayers.count (B+1,E,D) := rfl
  have rows : (List.range (EncodedBlock.endCount ctx)).map (fun i =>
      (List.range (EncodedBlock.endCount ctx)).map (fun j => EncodedBlock.observed ctx (encB m.source) i j)) =
      List.ofFn (fun i : Fin (EncodedClosingLayers.count (B+1,E,D)) =>
        List.ofFn (fun j : Fin (EncodedClosingLayers.count (B+1,E,D)) =>
          (blockEndShape m .one ((numE).symm i) ((numE).symm j),
           blockEndShape m .two ((numE).symm i) ((numE).symm j)))) := by
    apply FiniteSearch.tabulate_eq_ofFn
    intro i
    apply FiniteSearch.tabulate_eq_ofFn
    intro j
    have h := encoded_observed env output one two outOne outTwo graph objective m.source ((numE).symm i) ((numE).symm j)
    simpa only [Equiv.apply_symm_apply] using h
  have matrix := congrArg List.flatten rows
  rw [← List.flatMap_def,FinitePresentation.flatten_ofFn] at matrix
  have alive : (List.range (EncodedBlock.endCount ctx)).map (fun i => EncodedBlock.live data (encM m) i) =
      List.ofFn (fun i => blockEndLive M m ((numE).symm i)) := by
    apply FiniteSearch.tabulate_eq_ofFn
    intro i
    have h := encoded_live env output one two outOne outTwo graph objective M physical m ((numE).symm i)
    simpa only [Equiv.apply_symm_apply] using h
  exact Prod.ext rfl (Prod.ext matrix alive)

theorem encoded_component (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.component data (encM m) (numE e).val = encMask (blockComponent M m e) := by
  unfold EncodedBlock.component
  rw [encoded_components]
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  have h := EncodedClosingComponents.mask_encode numE (blockEndShape m) (blockEndLive M m) e ((numE).symm i)
  simpa only [Equiv.apply_symm_apply] using h

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q e y, EncodedParityTables.next physical (objective q).val
  ((env e).val*V+(output y).val) = (objective (step q e y)).val)

include transition in
omit [Fintype I₁] [Fintype I₂] in
theorem encoded_target (positive : 0 < D) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (mask : ComponentMask I₁ I₂ B D) :
    EncodedBlock.target data (encM m) (encMask mask) = encB (blockTarget M step m mask) := by
  unfold EncodedBlock.target
  change (let keep := (EncodedBlock.response ctx (encM m) (encMask mask)).1
    (keep.flatMap (fun i => keep.map (EncodedBlock.observed ctx (encB m.source) i)),
      keep.map (EncodedBlock.graphEnd data (encM m)),
      keep.map (EncodedBlock.objectiveEnd data (encM m)))) = _
  rw [encoded_response]
  change ((List.ofFn (fun i : BlockSlots B => (numE ((m.response mask).keep i)).val)).flatMap
      (fun i => (List.ofFn (fun j : BlockSlots B => (numE ((m.response mask).keep j)).val)).map
        (EncodedBlock.observed ctx (encB m.source) i)),
    (List.ofFn (fun i : BlockSlots B => (numE ((m.response mask).keep i)).val)).map
      (EncodedBlock.graphEnd data (encM m)),
    (List.ofFn (fun i : BlockSlots B => (numE ((m.response mask).keep i)).val)).map
      (EncodedBlock.objectiveEnd data (encM m))) = _
  rw [List.flatMap_def]
  simp only [List.map_ofFn,Function.comp_def]
  rw [FinitePresentation.flatten_ofFn]
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact encoded_observed env output one two outOne outTwo graph objective m.source
      ((m.response mask).keep (finProdFinEquiv.symm i).1)
      ((m.response mask).keep (finProdFinEquiv.symm i).2)
  · apply Prod.ext
    · apply congrArg List.ofFn
      funext i
      exact encoded_graphEnd env output one two outOne outTwo graph objective M physical m _
    · apply congrArg List.ofFn
      funext i
      exact encoded_objectiveEnd_positive env output one two outOne outTwo graph objective M physical
        step transition positive m _

include transition in
omit [Fintype I₁] [Fintype I₂] in
theorem encoded_responseValid (positive : 0 < D) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (mask : ComponentMask I₁ I₂ B D) :
    EncodedBlock.ResponseValid data (encM m) (encMask mask) ↔ ResponseValid M step m mask := by
  have reindex (p : Nat → Prop) : (∀ i < EncodedBlock.endCount ctx, p i) ↔
      ∀ e, p (numE e).val := FinitePresentation.forall_lt_number numE p
  have keep (p : Nat → Prop) : (∀ i ∈ ((responsePresentation env).encode (m.response mask)).1,p i) ↔
      ∀ j, p (numE ((m.response mask).keep j)).val := by
    change (∀ i ∈ List.ofFn (fun j : BlockSlots B => (numE ((m.response mask).keep j)).val),p i) ↔ _
    constructor
    · intro h j; exact h _ (List.mem_ofFn.mpr ⟨j,rfl⟩)
    · intro h i hi
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hi
      exact h j
  unfold EncodedBlock.ResponseValid
  dsimp only
  have rEq : EncodedBlock.response data.1 (encM m) (encMask mask) =
      (responsePresentation env).encode (m.response mask) :=
    encoded_response env output one two outOne outTwo graph objective m mask
  rw [rEq]
  simp only [show data.1=ctx from rfl,show (encM m).1=encB m.source from rfl]
  rw [keep]
  simp only [reindex,encoded_mask_get,encoded_folded,
    encoded_observed,encoded_graphEnd,
    encoded_objectiveEnd_positive env output one two outOne outTwo graph objective M physical step transition positive]
  simp only [Fin.val_injective.eq_iff,graph.injective.eq_iff,objective.injective.eq_iff]
  unfold ResponseValid ResponseChecks
  constructor
  · rintro ⟨hk,hv,hl⟩
    refine ⟨hk,?_,hl⟩
    intro p e f he hf same
    cases p
    · exact (hv e f he hf).1 same
    · exact (hv e f he hf).2 same
  · rintro ⟨hk,hv,hl⟩
    exact ⟨hk,fun e f he hf => ⟨hv .one e f he hf,hv .two e f he hf⟩,hl⟩

include transition in
theorem encoded_legal (positive : 0 < D) (b : BlockBoundary G Q B)
    (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    EncodedBlock.legal data (encB b) (encM m) = true ↔ BlockMoveValid M step b m := by
  rw [EncodedBlock.legal,decide_eq_true_eq,EncodedBlock.Legal]
  change (encB m.source=encB b ∧
    EncodedClosingBanks.coherent (EncodedBlock.bankData ctx (encB m.source)) (encM m).2.1=true ∧
    ∀ i < EncodedBlock.endCount ctx, EncodedBlock.live data (encM m) i=true →
      EncodedBlock.ResponseValid data (encM m) (EncodedBlock.component data (encM m) i)) ↔ _
  rw [(boundaryPresentation graph objective).injective.eq_iff,encoded_coherent]
  unfold BlockMoveValid
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [show EncodedBlock.endCount ctx=EncodedClosingLayers.count (B+1,E,D) from rfl,
    FinitePresentation.forall_lt_number numE]
  apply forall_congr'
  intro e
  rw [encoded_live,encoded_component]
  apply imp_congr_right
  intro _
  exact encoded_responseValid env output one two outOne outTwo graph objective M physical step transition positive m _
  exact positive

include transition in
theorem encoded_offered [DecidableEq G] [DecidableEq Q] (positive : 0 < D)
    (m : BlockMove I₁ I₂ O₁ O₂ G Q B D) (b : BlockOutcome I₁ I₂ G Q B D) :
    EncodedBlock.offered data (encM m) (encO b) = blockOffers M step m b := by
  apply Bool.eq_iff_iff.mpr
  rw [EncodedBlock.offered,blockOffers,decide_eq_true_eq,decide_eq_true_eq]
  change (encB b.target=EncodedBlock.target data (encM m) (encMask b.component) ∧
    ∃ i < EncodedBlock.endCount ctx, EncodedBlock.live data (encM m) i=true ∧
      encMask b.component=EncodedBlock.component data (encM m) i) ↔ _
  rw [encoded_target env output one two outOne outTwo graph objective M physical step transition positive,
    (boundaryPresentation graph objective).injective.eq_iff]
  apply and_congr_right
  intro _
  rw [show EncodedBlock.endCount ctx=EncodedClosingLayers.count (B+1,E,D) from rfl,
    FinitePresentation.exists_lt_number numE]
  apply exists_congr
  intro e
  rw [encoded_live,encoded_component,(maskPresentation env).injective.eq_iff]

end
end
end Characterisation.PeriodicBlocks
