/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedScheduledCollector
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.ScheduledOfferCompilation
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScheduleCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplayCorrect

/-! The generated layer data equal the original scheduled collector's data.
Every promised physical output is replayed, and all target numberings are
retained. The transition table hypothesis identifies explicit input data;
it does not assert computability of an unconstructed local test. -/
namespace Characterisation.EncodedScheduledCollector
open DistributedSynthesis

variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {R E V N₁ N₂ P₁ P₂ J S B C d K D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q] [Fintype GQ]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [DecidableEq GQ]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) (start : H → Q)
variable (transitions : EncodedParityTables.Data)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)

noncomputable def replayDataEncode : ReplayData :=
  (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (D+1),
    EncodedClosingBanks.bankEncode root env output bank,V,transitions,
    FiniteFunctionCodes.encode root (number ∘ start))

include transition in
omit [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
    [DecidableEq Q] in
theorem label_encode (n : Nat) (bound : n ≤ D+1) (s : ClosingLayer H I₁ I₂ n) :
    label (replayDataEncode root env one two output outOne outTwo number shape bank start transitions)
      (EncodedClosingLayers.encode root env s) =
      (number (closingLayerLabels step start (closingPolicyOfBank bank) n bound s)).val := by
  unfold label
  change EncodedClosingReplay.replay transitions
    ((FiniteFunctionCodes.encode root (number ∘ start)).getD (root (closingLayerRoot n s)).val 0)
    ((E,D+1),V,(EncodedClosingBanks.bankEncode root env output bank).getD (root (closingLayerRoot n s)).val [],
      List.ofFn (fun i => (env (closingLayerWord n s i)).val)) = _
  rw [FiniteFunctionCodes.eval_encode]
  unfold EncodedClosingBanks.bankEncode
  rw [EncodedClosingBanks.table_eval root (fun h => EncodedClosingPlans.planEncode env output (bank h)) []]
  exact EncodedClosingReplay.replay_layer env output transitions number step transition bank start n bound s

variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (source : H → GraphRootState GQ d K)
variable (table : ClosingGraphTable H I₁ I₂ GQ d K (D+1))
variable (firstWindow : Bool) (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

noncomputable def dataEncode : Data :=
  (replayDataEncode root env one two output outOne outTwo number shape bank start transitions,
    FiniteFunctionCodes.encode root slot,FiniteFunctionCodes.encode number minimum,
    EncodedClosingScans.dataEncode root env recognizer states source (D+1),
    EncodedClosingScans.tableEncode root env states table,firstWindow,B)

local notation "input" => dataEncode root env one two output outOne outTwo number shape bank start transitions
  recognizer states source table firstWindow slot minimum

omit [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem slots_encode (n : Nat) : slots input n =
    List.ofFn (fun i => EncodedClosingLayers.encode root env ((EncodedClosingLayers.number (n:=n) root env).symm i)) :=
  EncodedClosingLayers.slots_eq_ofFn root env

omit [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] in
theorem observed_encode (t : Fin (D+1)) (s r : ClosingLayer H I₁ I₂ (t.val+1)) :
    EncodedClosingBanks.observed (bankData input.1)
      (EncodedClosingLayers.encode root env s) (EncodedClosingLayers.encode root env r) =
      (closingLayerShape shape (t.val+1) .one s r,closingLayerShape shape (t.val+1) .two s r) := by
  have h := EncodedClosingBanks.observed_encode root env one two output outOne outTwo shape
    (closingLayerRoot _ s) (closingLayerRoot _ r) t (closingLayerWord _ s) (closingLayerWord _ r)
  rw [EncodedClosingObservations.layerFromWord_word,EncodedClosingObservations.layerFromWord_word] at h
  exact h

omit [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq O₁] [DecidableEq O₂]
    [DecidableEq Q] [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem views_encode (t : Fin (D+1)) : views input (t.val+1) =
    List.ofFn (fun i => let sr := (FiniteFunctionCodes.prod
      (EncodedClosingLayers.number (n:=t.val+1) root env) (EncodedClosingLayers.number root env)).symm i
      (closingLayerShape shape (t.val+1) .one sr.1 sr.2,closingLayerShape shape (t.val+1) .two sr.1 sr.2)) := by
  unfold views
  rw [slots_encode]
  simp only [List.length_ofFn]
  apply FiniteSearch.tabulate_eq_ofFn
  intro index
  let N := EncodedClosingLayers.count (R,E,t.val+1)
  let pair : Fin N × Fin N := finProdFinEquiv.symm index
  have left := EncodedClosingBanks.table_eval (Equiv.refl (Fin N))
    (fun i => EncodedClosingLayers.encode root env ((EncodedClosingLayers.number (n:=t.val+1) root env).symm i)) (0,[]) pair.1
  have right := EncodedClosingBanks.table_eval (Equiv.refl (Fin N))
    (fun i => EncodedClosingLayers.encode root env ((EncodedClosingLayers.number (n:=t.val+1) root env).symm i)) (0,[]) pair.2
  change (List.ofFn _).getD (index.val/N) (0,[]) = _ at left
  change (List.ofFn _).getD (index.val%N) (0,[]) = _ at right
  simp only [Equiv.refl_symm,Equiv.refl_apply,N] at left right
  rw [left,right,observed_encode]
  rfl

include transition in
omit [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq O₁] [DecidableEq O₂]
    [DecidableEq Q] in
omit [Fintype H] [Fintype I₁] [Fintype I₂] in
theorem layer_encode (t : Fin (D+1)) : layer input (t.val+1) =
    scheduledLayerCode (fun t : Fin (D+1) => EncodedClosingLayers.count (R,E,t.val+1))
      (fun _ => EncodedClosingLayers.number root env) number shape firstWindow
      (closingGraphBoundaryTable recognizer table) (closingGraphLiveTable table)
      step start (closingPolicyOfBank bank) slot minimum t := by
  unfold layer scheduledLayerCode EncodedClosingLayerOffers.encode EncodedClosingComponents.encode
  rw [slots_encode,views_encode]
  simp only [List.length_ofFn,List.map_ofFn]
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · apply congrArg List.ofFn
        funext i
        exact (EncodedClosingScans.live_encode root env recognizer states source table ⟨t.val+1,by omega⟩ _).trans
          (by simp only [closingFlagAt,dif_pos (show t.val+1 < D+1+1 by omega)])
  · apply Prod.ext
    · rfl
    · apply Prod.ext
      · apply congrArg List.ofFn
        funext i
        exact EncodedClosingScans.eligible_encode root env recognizer states source table firstWindow ⟨t.val+1,by omega⟩ _
      · apply Prod.ext
        · apply congrArg List.ofFn
          funext i
          exact label_encode root env one two output outOne outTwo number shape bank start transitions step transition _ (by omega) _
        · apply Prod.ext
          · apply congrArg List.ofFn
            funext i
            exact FiniteFunctionCodes.eval_encode root slot _
          · apply congrArg List.ofFn
            funext i
            change (FiniteFunctionCodes.encode number minimum).getD
              (label (replayDataEncode root env one two output outOne outTwo number shape bank start transitions) _) 0 = _
            rw [label_encode root env one two output outOne outTwo number shape bank start transitions step transition _ (by omega)]
            exact FiniteFunctionCodes.eval_encode number minimum _

include transition in
omit [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq Q] in
theorem layerData_encode : layerData input =
    numberedScheduledCollectorCode root env number shape firstWindow
      (closingGraphBoundaryTable recognizer table) (closingGraphLiveTable table)
      step start (closingPolicyOfBank bank) slot minimum := by
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    change EncodedClosingBanks.coherent
      (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (D+1))
      (EncodedClosingBanks.bankEncode root env output bank) = true ↔
      decide (ClosingPolicyCoherent shape (closingPolicyOfBank bank)) = true
    rw [decide_eq_true_eq]
    exact EncodedClosingBanks.coherent_encode root env one two output outOne outTwo shape bank
  · change (List.range (D+1)).map _ = List.ofFn _
    apply FiniteSearch.tabulate_eq_ofFn
    intro t
    exact layer_encode root env one two output outOne outTwo number shape bank start transitions step transition
      recognizer states source table firstWindow slot minimum t

include transition in
/-- The primitive recursive generator returns exactly the original scheduled
offers for this source bank and graph scan. -/
theorem collect_encode (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number outcome ∈ collect input ↔
      outcome ∈ scheduledClosingOffers shape firstWindow
        (closingGraphBoundaryTable recognizer table) (closingGraphLiveTable table)
        step start (closingPolicyOfBank bank) slot minimum := by
  rw [collect,layerData_encode root env one two output outOne outTwo number shape bank start transitions step transition]
  exact numberedScheduledCollectorCode_correct root env number shape firstWindow _ _ step start _ slot minimum outcome

end Characterisation.EncodedScheduledCollector
