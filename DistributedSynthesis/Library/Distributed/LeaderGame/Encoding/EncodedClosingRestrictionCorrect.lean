/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingRestriction
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedScheduledCollectorCorrect

/-! Source restriction commutes with all collector data, including the
entire graph scan. No hypothesis of injectivity is needed for these data
identities; the active-root application uses the subtype inclusion. -/
namespace Characterisation.EncodedClosingRestriction
open DistributedSynthesis

section Basic
variable {H H' Z : Type} {R R' : Nat} (root : H ≃ Fin R) (selected : H' ≃ Fin R') (f : H' → H)

theorem gather_encode (fallback : Z) (values : H → Z) :
    gather fallback (List.ofFn (fun i => values (root.symm i)))
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      List.ofFn (fun i => values (f (selected.symm i))) := by
  unfold gather FiniteFunctionCodes.encode
  rw [List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  exact EncodedClosingBanks.table_eval root values fallback (f (selected.symm i))

theorem gather_functionEncode {N : Nat} (values : H → Fin N) :
    gather 0 (FiniteFunctionCodes.encode root values) (FiniteFunctionCodes.encode selected (root ∘ f)) =
      FiniteFunctionCodes.encode selected (values ∘ f) :=
  gather_encode root selected f 0 (fun h => (values h).val)

theorem keep_length : (FiniteFunctionCodes.encode selected (root ∘ f)).length = R' := List.length_ofFn

variable {I₁ I₂ : Type} {E n : Nat} (env : (I₁ × I₂ × Graph) ≃ Fin E)

theorem word_map (s : ClosingLayer H' I₁ I₂ n) :
    closingLayerWord n (mapClosingLayer f n s) = closingLayerWord n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [closingLayerWord,mapClosingLayer,ih]

theorem mapSlot_encode (s : ClosingLayer H' I₁ I₂ n) :
    mapSlot (FiniteFunctionCodes.encode selected (root ∘ f)) (EncodedClosingLayers.encode selected env s) =
      EncodedClosingLayers.encode root env (mapClosingLayer f n s) := by
  apply Prod.ext
  · change (FiniteFunctionCodes.encode selected (root ∘ f)).getD (selected (closingLayerRoot n s)).val 0 =
      (root (closingLayerRoot n (mapClosingLayer f n s))).val
    rw [closingLayerRoot_map]
    exact FiniteFunctionCodes.eval_encode selected (root ∘ f) (closingLayerRoot n s)
  · simp only [mapSlot,EncodedClosingLayers.encode,word_map]

theorem policy_map {O₁ O₂ : Type} {D : Nat} (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) :
    closingPolicyOfBank (bank ∘ f) = restrictClosingPolicy f (closingPolicyOfBank bank) := by
  funext t s
  simp only [closingPolicyOfBank,restrictClosingPolicy,closingLayerRoot_map,word_map,Function.comp_apply]

end Basic

section Banks
variable {H H' I₁ I₂ O₁ O₂ : Type} {R R' E V N₁ N₂ P₁ P₂ D : Nat}
variable (root : H ≃ Fin R) (selected : H' ≃ Fin R') (f : H' → H)
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (shape : InputShape H)

theorem matrix_encode :
    matrix (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape D)
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedClosingBanks.matrix (EncodedClosingBanks.dataEncode selected env one two output outOne outTwo
        (restrictInputShape shape f) D) := by
  unfold matrix
  rw [keep_length]
  apply FiniteSearch.tabulate_eq_ofFn
  intro index
  let pair : Fin R' × Fin R' := finProdFinEquiv.symm index
  have left := FiniteFunctionCodes.eval_encode selected (root ∘ f) (selected.symm pair.1)
  have right := FiniteFunctionCodes.eval_encode selected (root ∘ f) (selected.symm pair.2)
  simp only [Equiv.apply_symm_apply] at left right
  have hp : pair.1.val = index.val/R' := rfl
  have hq : pair.2.val = index.val%R' := rfl
  rw [hp] at left
  rw [hq] at right
  rw [left,right]
  exact EncodedClosingBanks.table_eval (FiniteFunctionCodes.prod root root)
    (fun hk => (shape .one hk.1 hk.2,shape .two hk.1 hk.2)) (false,false)
    (f (selected.symm pair.1),f (selected.symm pair.2))

theorem bankData_encode :
    bankData (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape D)
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedClosingBanks.dataEncode selected env one two output outOne outTwo (restrictInputShape shape f) D := by
  unfold bankData
  rw [keep_length,matrix_encode]
  rfl

end Banks

section Scans
variable {H H' I₁ I₂ Q : Type} {R R' E S D : Nat}
variable [Fintype H] [Fintype H'] [Fintype I₁] [Fintype I₂]
variable (root : H ≃ Fin R) (selected : H' ≃ Fin R') (f : H' → H)
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (states : Q ≃ Fin S)
variable (table : (n : Fin (D+1)) → ClosingLayer H I₁ I₂ n.val → Q)

omit [Fintype H] [Fintype H'] [Fintype I₁] [Fintype I₂] in
theorem scan_encode :
    scan (R,E,D) (EncodedClosingScans.tableEncode root env states table)
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedClosingScans.tableEncode selected env states (fun n s => table n (mapClosingLayer f n.val s)) := by
  unfold scan context
  rw [keep_length,EncodedClosingScans.domain_eq_ofFn selected env,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply,EncodedClosingScans.scenarioEncode]
  rw [mapSlot_encode]
  exact EncodedClosingScans.entry_encode root env states table _ _

end Scans

section Graphs
variable {H H' I₁ I₂ GQ : Type} {R R' E S d K D : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (root : H ≃ Fin R) (selected : H' ≃ Fin R') (f : H' → H)
variable (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (source : H → GraphRootState GQ d K)

theorem graphData_encode :
    graphData (EncodedClosingScans.dataEncode root env recognizer states source D)
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedClosingScans.dataEncode selected env recognizer states (source ∘ f) D := by
  unfold graphData
  change ((_,E,D),_,_,gather 0 (FiniteFunctionCodes.encode root (states ∘ source)) _) = _
  rw [keep_length,gather_functionEncode]
  rfl

omit [Fintype GQ] [DecidableEq GQ] in
theorem boundary_map (table : ClosingGraphTable H I₁ I₂ GQ d K D) :
    closingGraphBoundaryTable recognizer (fun n s => table n (mapClosingLayer f n.val s)) =
      restrictClosingFlags f (closingGraphBoundaryTable recognizer table) := by
  funext n s
  rcases n with ⟨n,hn⟩
  cases n with
  | zero => rfl
  | succ n =>
    simp only [closingGraphBoundaryTable,closingGraphBoundary,restrictClosingFlags,mapClosingLayer,
      closingGraphAt,dif_pos (show n < D+1 by omega)]

end Graphs

section Collector
variable {H H' I₁ I₂ O₁ O₂ Q GQ : Type} {R R' E V N₁ N₂ P₁ P₂ J S B C d K D : Nat}
variable [Fintype H] [Fintype H'] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q] [Fintype GQ]
variable [DecidableEq H] [DecidableEq H'] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [DecidableEq GQ]
variable (root : H ≃ Fin R) (selected : H' ≃ Fin R') (f : H' → H)
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (number : Q ≃ Fin J) (shape : InputShape H)
variable (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) (start : H → Q) (transitions : EncodedParityTables.Data)
variable (recognizer : Recognizer Graph GQ) [DecidablePred (· ∈ recognizer.accept)]
variable (states : GraphRootState GQ d K ≃ Fin S) (source : H → GraphRootState GQ d K)
variable (table : ClosingGraphTable H I₁ I₂ GQ d K (D+1))
variable (firstWindow : Bool) (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

omit [Fintype H] [Fintype H'] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq H'] [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁]
    [DecidableEq O₂] [DecidableEq Q] in
theorem replayData_encode :
    replayData (EncodedScheduledCollector.replayDataEncode root env one two output outOne outTwo number shape bank start transitions)
      (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedScheduledCollector.replayDataEncode selected env one two output outOne outTwo number
        (restrictInputShape shape f) (bank ∘ f) (start ∘ f) transitions := by
  unfold replayData
  change (bankData (EncodedClosingBanks.dataEncode root env one two output outOne outTwo shape (D+1)) _,
    gather [] (EncodedClosingBanks.bankEncode root env output bank) _,V,transitions,
    gather 0 (FiniteFunctionCodes.encode root (number ∘ start)) _) = _
  rw [bankData_encode,gather_functionEncode]
  unfold EncodedClosingBanks.bankEncode
  rw [gather_encode root selected f [] (fun h => EncodedClosingPlans.planEncode env output (bank h))]
  rfl

omit [Fintype H] [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq H']
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
    [Fintype H'] [Fintype I₁] [Fintype I₂] in
theorem apply_encode :
    apply (EncodedScheduledCollector.dataEncode root env one two output outOne outTwo number shape bank start transitions
      recognizer states source table firstWindow slot minimum) (FiniteFunctionCodes.encode selected (root ∘ f)) =
      EncodedScheduledCollector.dataEncode selected env one two output outOne outTwo number
        (restrictInputShape shape f) (bank ∘ f) (start ∘ f) transitions recognizer states (source ∘ f)
        (fun n s => table n (mapClosingLayer f n.val s)) firstWindow (slot ∘ f) minimum := by
  unfold apply
  change (replayData (EncodedScheduledCollector.replayDataEncode root env one two output outOne outTwo number shape bank start transitions) _,
    gather 0 (FiniteFunctionCodes.encode root slot) _,FiniteFunctionCodes.encode number minimum,
    graphData (EncodedClosingScans.dataEncode root env recognizer states source (D+1)) _,
    scan (R,E,D+1) (EncodedClosingScans.tableEncode root env states table) _,firstWindow,B) = _
  rw [replayData_encode,gather_functionEncode,graphData_encode,scan_encode]
  rfl

variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (transition : ∀ q r o, EncodedParityTables.next transitions (number q).val
  ((env r).val*V+(output o).val) = (number (step q r o)).val)

include transition in
omit [Fintype H] [DecidableEq H] in
/-- The generated restricted collector agrees with the original collector
on precisely the selected source family. -/
theorem collect_encode (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode number outcome ∈
      EncodedScheduledCollector.collect
        (apply (EncodedScheduledCollector.dataEncode root env one two output outOne outTwo number shape bank start transitions
          recognizer states source table firstWindow slot minimum) (FiniteFunctionCodes.encode selected (root ∘ f))) ↔
      outcome ∈ scheduledClosingOffers (restrictInputShape shape f) firstWindow
        (restrictClosingFlags f (closingGraphBoundaryTable recognizer table))
        (restrictClosingFlags f (closingGraphLiveTable table)) step (start ∘ f)
        (restrictClosingPolicy f (closingPolicyOfBank bank)) (slot ∘ f) minimum := by
  rw [apply_encode,EncodedScheduledCollector.collect_encode selected env one two output outOne outTwo number
    (restrictInputShape shape f) (bank ∘ f) (start ∘ f) transitions step transition]
  rw [boundary_map,policy_map]
  rfl

end Collector
end Characterisation.EncodedClosingRestriction
