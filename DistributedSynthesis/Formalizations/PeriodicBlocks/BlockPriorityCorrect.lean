/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockGuardCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

theorem minWith_range (f : Nat → Nat) (D : Nat) (positive : 0 < D) :
    FiniteSearch.minWith (f 0) ((List.range D).map f) = rangeMin f 0 (D-1) := by
  apply Nat.le_antisymm
  · obtain ⟨k,hk,eq⟩ := rangeMin_attained f 0 (D-1)
    rw [eq]
    apply FiniteSearch.minWith_le_mem
    exact List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),by simp⟩
  · apply (FiniteSearch.le_minWith _ _ _).mpr
    refine ⟨rangeMin_le f 0 (D-1) 0 (by omega),?_⟩
    intro r hr
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hr
    have h := rangeMin_le f 0 (D-1) k (by have := List.mem_range.mp hk; omega)
    simpa only [Nat.zero_add] using h

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D E V S N N₁ N₂ P₁ P₂ K : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
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

local notation "ctx" => blockContext (B:=B) (D:=D) (S:=S) (N:=N) env output one two outOne outTwo
local notation "data" => blockData (B:=B) (D:=D) (N:=N) env output one two outOne outTwo graph M physical
local notation "encB" => FinitePresentation.encode (boundaryPresentation (B:=B) graph objective)
local notation "encM" => FinitePresentation.encode (movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective)
local notation "encO" => FinitePresentation.encode (outcomePresentation (B:=B) (D:=D) env graph objective)
local notation "numE" => endNumber (B:=B) (D:=D) env
local notation "encE" => EncodedClosingLayers.encode (n:=D) (Equiv.refl (BlockSlots B)) env
local notation "encMask" => FinitePresentation.encode (maskPresentation (B:=B) (D:=D) env)

include transition ranks in
omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem encoded_color (positive : 0 < D) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (e : BlockEnd I₁ I₂ B D) :
    EncodedBlock.color data (encM m) (numE e).val = blockColor step m χ e := by
  unfold EncodedBlock.color
  simp only [show data.1=ctx from rfl]
  rw [encoded_endpoint]
  change FiniteSearch.minWith
    (EncodedParityTables.priority physical ((encB m.source).2.2.getD (closingLayerRoot D e).val 0))
    ((List.range D).map (fun k => EncodedParityTables.priority physical
      (EncodedBlock.objectiveAt data (encM m) ((encE e).1,(encE e).2.take k)))) = _
  rw [show (encB m.source).2.2.getD (closingLayerRoot D e).val 0 =
    (objective (m.source.objective (closingLayerRoot D e))).val from
    FinitePresentation.table_get (Equiv.refl _) ((FinitePresentation.fin N).transport objective)
      m.source.objective 0 (closingLayerRoot D e)]
  simp only [encoded_stateAt env output one two outOne outTwo graph objective M physical step transition positive,ranks]
  have initial : blockStateAt step m e 0 = m.source.objective (closingLayerRoot D e) := rfl
  rw [← initial]
  exact minWith_range (fun k => χ (blockStateAt step m e k)) D positive

include transition ranks in
theorem encoded_edge [DecidableEq G] [DecidableEq Q] (positive : 0 < D)
    (old next : HandoverCode B K) (m : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (b : BlockOutcome I₁ I₂ G Q B D) :
    EncodedBlock.Edge data (old.1.val,old.2.val) (encM m) (encO b) (next.1.val,next.2.val) ↔
      BlockEdge M step χ old m b next := by
  unfold EncodedBlock.Edge BlockEdge
  rw [encoded_offered env output one two outOne outTwo graph objective M physical step transition positive]
  apply and_congr_right
  intro _
  change (∃ i < EncodedClosingLayers.count (B+1,E,D),
    (encMask b.component).getD i false=true ∧ (EncodedBlock.endpoint ctx i).1=old.1.val ∧
    (EncodedBlock.response ctx (encM m) (encMask b.component)).2.getD i 0=next.1.val ∧
    EncodedBlock.color data (encM m) i=next.2.val) ↔ _
  rw [FinitePresentation.exists_lt_number numE]
  apply exists_congr
  intro e
  rw [encoded_mask_get,encoded_endpoint,encoded_response,encoded_fold,
    encoded_color env output one two outOne outTwo graph objective M physical step χ transition ranks positive]
  change (b.component e=true ∧ (closingLayerRoot D e).val=old.1.val ∧
    ((m.response b.component).fold e).val=next.1.val ∧ blockColor step m χ e=next.2.val) ↔ _
  simp only [Fin.val_injective.eq_iff]

end
end
end Characterisation.PeriodicBlocks
