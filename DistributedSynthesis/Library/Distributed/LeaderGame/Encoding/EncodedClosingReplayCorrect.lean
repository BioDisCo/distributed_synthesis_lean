/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReplay
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingPlansCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBankCoherence
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservationsCorrect

/-! Numeric replay computes the original closing monitor on all physical
outputs, for any explicitly numbered transition table. -/
namespace Characterisation.EncodedClosingReplay
open DistributedSynthesis
open EncodedClosingPlans

variable {I₁ I₂ O₁ O₂ Q : Type} {E V N D n : Nat}
  (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)

theorem prefix_encode (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) (i : Fin n) :
    (List.ofFn (fun j => (env (future j)).val)).take (i.val+1) =
      scenarioEncode env (closingPrefix bound future i) := by
  apply List.ext_getElem
  · simp only [List.length_take,List.length_ofFn,scenarioEncode,closingPrefix]
    have hi := i.isLt
    omega
  · intro j hj hk
    simp only [scenarioEncode,closingPrefix,List.getElem_take,List.getElem_ofFn]

theorem letters_encode (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) :
    letters ((E,D),V,planEncode env output plan,List.ofFn (fun i => (env (future i)).val)) =
      List.ofFn (fun i => (env (future i)).val * V + (output (closingOutputs plan bound future i)).val) := by
  unfold letters
  simp only [List.length_ofFn]
  apply FiniteSearch.tabulate_eq_ofFn
  intro i
  rw [List.getD_eq_getElem _ _ (by simp),prefix_encode env bound future i,entry_encode]
  simp only [List.getElem_ofFn,closingOutputs]

variable (data : EncodedParityTables.Data) (number : Q ≃ Fin N)
  (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
  (transition : ∀ q r o, EncodedParityTables.next data (number q).val
    ((env r).val*V+(output o).val) = (number (step q r o)).val)

include transition in
theorem fold_encode (physical : List ((I₁ × I₂ × Graph) × (O₁ × O₂))) (start : Q) :
    (physical.map (fun letter => (env letter.1).val*V+(output letter.2).val)).foldl
      (EncodedParityTables.next data) (number start).val =
      (number (physical.foldl (fun q letter => step q letter.1 letter.2) start)).val := by
  induction physical generalizing start with
  | nil => rfl
  | cons letter tail ih =>
    simp only [List.map_cons,List.foldl_cons]
    rw [transition,ih]

include transition in
/-- The table computes the entire original closing monitor, so any graph
state or priority minimum carried in that monitor is preserved as well. -/
theorem replay_encode (start : Q) (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D)
    (bound : n ≤ D) (future : Fin n → I₁ × I₂ × Graph) :
    replay data (number start).val
      ((E,D),V,planEncode env output plan,List.ofFn (fun i => (env (future i)).val)) =
      (number (closingMonitor step start plan bound future)).val := by
  rw [replay,letters_encode env output plan bound future]
  have h := fold_encode env output data number step transition
    (List.ofFn (fun i => (future i,closingOutputs plan bound future i))) start
  simpa only [List.map_ofFn,closingMonitor] using h

section Banks
variable {H : Type}

theorem bank_trace_fromWord (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (h : H) (n : Nat) (bound : n ≤ D+1) (future : Fin n → I₁ × I₂ × Graph) :
    closingLayerTrace (closingPolicyOfBank bank) n bound (closingLayerFromWord h n future) =
      List.ofFn (fun i => (future i,closingOutputs (bank h) bound future i)) := by
  induction n with
  | zero => simp [closingLayerTrace]
  | succ n ih =>
    change closingLayerTrace (closingPolicyOfBank bank) n (by omega)
      (closingLayerFromWord h n (fun i => future i.castSucc)) ++
      [(future (Fin.last n),closingPolicyOfBank bank ⟨n,by omega⟩ (closingLayerFromWord h (n+1) future))] = _
    rw [ih,List.ofFn_succ',List.concat_eq_append]
    apply congrArg₂ List.append
    · apply congrArg List.ofFn
      funext i
      rfl
    · simp only [closingPolicyOfBank,closingLayerRoot_fromWord,closingLayerWord_fromWord]
      rfl

include transition in
/-- This is the label recomputation used by closing certificates, for an
arbitrary root and hypothetical closing layer. -/
theorem replay_layer (bank : ClosingPlanBank H I₁ I₂ O₁ O₂ D) (initial : H → Q)
    (n : Nat) (bound : n ≤ D+1) (s : ClosingLayer H I₁ I₂ n) :
    replay data (number (initial (closingLayerRoot n s))).val
      ((E,D+1),V,planEncode env output (bank (closingLayerRoot n s)),
        List.ofFn (fun i => (env (closingLayerWord n s i)).val)) =
      (number (closingLayerLabels step initial (closingPolicyOfBank bank) n bound s)).val := by
  have trace := bank_trace_fromWord bank (closingLayerRoot n s) n bound (closingLayerWord n s)
  rw [EncodedClosingObservations.layerFromWord_word] at trace
  rw [closingLayerLabels_replay,trace]
  exact replay_encode env output data number step transition _ _ bound (closingLayerWord n s)

end Banks

end Characterisation.EncodedClosingReplay
