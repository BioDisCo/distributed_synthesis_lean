/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderMemory
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect
import DistributedSynthesis.Library.Distributed.LeaderPhases.JointLeaderMonitor

/-! The generated leader-memory predicate is the existing semantic check,
with no supplied legality oracle. -/
namespace Characterisation.EncodedLeaderMemory
open DistributedSynthesis
open EncodedClosingBanks EncodedClosingPlans

variable {H I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ D : Nat}
  (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
  (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
  (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)

noncomputable def transitionEncode (old new : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (r : I₁ × I₂ × Graph) (actual : H → O₁ × O₂) : Transition :=
  (bankEncode root env output old,bankEncode root env output new,(env r).val,
    List.ofFn (fun i => ((outOne (actual (root.symm i)).1).val,(outTwo (actual (root.symm i)).2).val)))

theorem rootChecked_encode (shape : InputShape H) (old new : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (r : I₁ × I₂ × Graph) (actual : H → O₁ × O₂) (h : H) :
    RootChecked (dataEncode root env one two output outOne outTwo shape (D+1))
      (transitionEncode root env output outOne outTwo old new r actual) (root h).val ↔
      RollingClosingOverlap (old h) (new h) r ∧
        closingPlanEntry (old h) (fun _ => r) ⟨0,by omega⟩ = actual h := by
  unfold RootChecked
  change overlap ((E,D+1-1),
    (List.ofFn (fun i => planEncode env output (old (root.symm i)))).getD (root h).val [],
    (List.ofFn (fun i => planEncode env output (new (root.symm i)))).getD (root h).val [],(env r).val) = true ∧
    response (dataEncode root env one two output outOne outTwo shape (D+1)) (bankEncode root env output old)
      ((root h).val,[(env r).val]) =
      (List.ofFn (fun i => ((outOne (actual (root.symm i)).1).val,(outTwo (actual (root.symm i)).2).val))).getD
        (root h).val (0,0) ↔ _
  rw [Nat.add_sub_cancel,table_eval root (fun h => planEncode env output (old h)) [] h,
    table_eval root (fun h => planEncode env output (new h)) [] h,overlap_encode]
  have first : ((root h).val,[(env r).val]) =
      slotEncode root env h ((),⟨(⟨0,by omega⟩ : Fin (D+1)),fun _ => r⟩) := by
    simp [slotEncode,scenarioEncode,List.ofFn_succ]
  rw [first,response_encode,table_eval root
    (fun h => ((outOne (actual h).1).val,(outTwo (actual h).2).val)) (0,0) h]
  apply and_congr_right
  intro _
  constructor
  · intro same
    exact Prod.ext (outOne.injective (Fin.ext (congrArg Prod.fst same)))
      (outTwo.injective (Fin.ext (congrArg Prod.snd same)))
  · intro same
    exact congrArg (fun value => ((outOne value.1).val,(outTwo value.2).val)) same

variable [DecidableEq I₁] [DecidableEq I₂]

theorem check_encode (oldShape newShape : InputShape H)
    (old new : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (r : I₁ × I₂ × Graph) (actual : H → O₁ × O₂) :
    check (dataEncode root env one two output outOne outTwo oldShape (D+1),
      dataEncode root env one two output outOne outTwo newShape (D+1))
      (transitionEncode root env output outOne outTwo old new r actual) = true ↔
      ClosingBankCoherent oldShape old ∧ ClosingBankCoherent newShape new ∧
      ∀ h, RollingClosingOverlap (old h) (new h) r ∧
        closingPlanEntry (old h) (fun _ => r) ⟨0,by omega⟩ = actual h := by
  rw [check,Bool.and_eq_true,Bool.and_eq_true]
  change (coherent _ (bankEncode root env output old) = true ∧
    coherent _ (bankEncode root env output new) = true) ∧ rollingCheck _ _ = true ↔ _
  rw [coherent_encode,coherent_encode,and_assoc,rollingCheck,decide_eq_true_eq]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  constructor
  · intro tested h
    exact (rootChecked_encode root env one two output outOne outTwo oldShape old new r actual h).mp
      (tested (root h).val (root h).isLt)
  · intro checked i hi
    have proof := (rootChecked_encode root env one two output outOne outTwo oldShape old new r actual
      (root.symm ⟨i,hi⟩)).mpr (checked _)
    simpa only [Equiv.apply_symm_apply] using proof

section Joint
variable {G : Type} [Fintype H] [DecidableEq H] [Fintype G] [DecidableEq G]
  [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]

omit [DecidableEq H] [Fintype G] [DecidableEq G] [Fintype O₁] [Fintype O₂] in
/-- Instantiation with the original leader's output vector and receiver's
root-indexed responses gives exactly `jointLeaderCheck`. -/
theorem jointLeaderCheck_encode (group : H → G) (shape : InputShape H)
    (state : ClosingPlanBank H I₁ I₂ O₁ O₂ D × Bool)
    (letter : RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) (G → O₁)) :
    check (dataEncode root env one two output outOne outTwo (jointLeaderShape shape state.2) (D+1),
      dataEncode root env one two output outOne outTwo (rightRefinedShape shape) (D+1))
      (transitionEncode root env output outOne outTwo state.1 letter.2.1.2
        (letter.1.2,letter.1.1,.right) (fun h => (letter.2.2 (group h),letter.2.1.1 h))) =
      jointLeaderCheck group shape state letter := by
  apply Bool.eq_iff_iff.mpr
  rw [check_encode,jointLeaderCheck,decide_eq_true_eq]

end Joint
end Characterisation.EncodedLeaderMemory
