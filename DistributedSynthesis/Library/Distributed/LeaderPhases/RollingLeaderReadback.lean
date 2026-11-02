/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingWindowSources

/-! Agreement of the leader's outgoing promises across all receiver-input
threads and all window starts. The own-input word retains its full length,
so this does not identify actions in different rounds. -/
namespace Characterisation
open DistributedSynthesis

/-- Equal leader views give equal complete own-input extensions of the
common initial leader view. In particular, their lengths agree. -/
theorem rollingSourceHistory_one_inputs {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (node word : List (I₂ × I₁)) (h k : H)
    (same : currentView .one (rollingSourceHistory past node h) =
      currentView .one (rollingSourceHistory past word k)) :
    senderWord node = senderWord word := by
  have own := congrArg ownInputs same
  rw [ownInputs_current,ownInputs_current] at own
  have base := congrArg ownInputs (leaders h k)
  rw [ownInputs_current,ownInputs_current] at base
  simp only [rollingSourceHistory,inputWord,List.map_append] at own
  change inputWord .one (past h) ++ inputWord .one (rightInputHistory node) =
    inputWord .one (past k) ++ inputWord .one (rightInputHistory word) at own
  rw [base] at own
  have tail := List.append_cancel_left own
  have tagged : (senderWord node).map (PSum.inl : I₁ → PSum I₁ I₂) =
      (senderWord word).map PSum.inl := by
    simpa only [senderWord,inputWord,rightInputHistory,List.map_map,Function.comp_def,
      RoundRecord.input] using tail
  exact (Function.Injective.list_map (fun _ _ eq => PSum.inl.inj eq)) tagged

/-- An outgoing closing prefix occupies precisely its original rounds. -/
theorem closingEntryHistory_right {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (node : List (I₂ × I₁)) (h : H)
    (env : Nat → I₂ × I₁) (t : Nat) :
    closingEntryHistory (rollingSourceHistory past node h)
      (fun n => ((env n).2,(env n).1,.right)) t =
      rollingSourceHistory past (node ++ branchNode env (t+1)) h := by
  have wordEq : rightInputHistory (node ++ branchNode env (t+1)) =
      rightInputHistory node ++ rightInputHistory (branchNode env (t+1)) := by
    simp only [rightInputHistory,List.map_append]
  simp only [closingEntryHistory,rollingSourceHistory,wordEq,rightInputHistory_branchNode,
    List.append_assoc]

/-- Every outgoing promise equals the shared leader strategy's output at
the full own-input history of that round. Receiver inputs and window starts
may differ; the complete own-input history is retained. -/
theorem rollingBanks_leader_promises {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (leader : SenderBlockStrategy I₁ O₁)
    (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
      (banks (node ++ [r]) h) (r.2,r.1,.right))
    (first : ∀ node (r : I₂ × I₁) h,
      (closingPlanEntry (banks node h) (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩).1 =
        leader (senderWord node) r.2)
    (node : List (I₂ × I₁)) (h : H) (env : Nat → I₂ × I₁)
    (t : Nat) (within : t < D+1) :
    (closingPlanEntry (banks node h) (fun n => ((env n).2,(env n).1,.right)) ⟨t,within⟩).1 =
      leader (senderWord (node ++ branchNode env t)) (env t).2 := by
  have transport := rollingBanks_transport banks overlap node h env
    (fun n => ((env n).2,(env n).1,.right)) t 0 (by omega) (fun _ _ => rfl)
  simp only [Nat.add_zero] at transport
  rw [transport,closingPlanEntry_zero]
  exact first _ _ _

/-- Cross-window, cross-thread agreement for a leader that has not received
since its window started. Equality of the actual views, not equality of the
relative offsets, is the hypothesis. -/
theorem rollingBanks_outgoing_leader_agree {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (past : H → EnvHistory I₁ I₂)
    (leaders : ∀ h k, currentView .one (past h) = currentView .one (past k))
    (banks : List (I₂ × I₁) → ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (leader : SenderBlockStrategy I₁ O₁)
    (overlap : ∀ node r h, RollingClosingOverlap (banks node h)
      (banks (node ++ [r]) h) (r.2,r.1,.right))
    (first : ∀ node (r : I₂ × I₁) h,
      (closingPlanEntry (banks node h) (fun _ => (r.2,r.1,.right)) ⟨0,by omega⟩).1 =
        leader (senderWord node) r.2)
    (node word : List (I₂ × I₁)) (h k : H)
    (env other : Nat → I₂ × I₁) (t u : Nat) (withinT : t < D+1) (withinU : u < D+1)
    (same : currentView .one (closingEntryHistory (rollingSourceHistory past node h)
        (fun n => ((env n).2,(env n).1,.right)) t) =
      currentView .one (closingEntryHistory (rollingSourceHistory past word k)
        (fun n => ((other n).2,(other n).1,.right)) u)) :
    (closingPlanEntry (banks node h) (fun n => ((env n).2,(env n).1,.right)) ⟨t,withinT⟩).1 =
      (closingPlanEntry (banks word k) (fun n => ((other n).2,(other n).1,.right)) ⟨u,withinU⟩).1 := by
  rw [closingEntryHistory_right,closingEntryHistory_right] at same
  have words := rollingSourceHistory_one_inputs past leaders _ _ h k same
  have full : senderWord (node ++ branchNode env t) ++ [(env t).2] =
      senderWord (word ++ branchNode other u) ++ [(other u).2] := by
    simpa only [branchNode,List.append_assoc,senderWord,List.map_append,List.map_singleton] using words
  have old := congrArg List.dropLast full
  simp only [List.dropLast_concat] at old
  have fresh := congrArg List.getLast? full
  simp only [List.getLast?_concat,Option.some.injEq] at fresh
  rw [rollingBanks_leader_promises banks leader overlap first,
    rollingBanks_leader_promises banks leader overlap first,old,fresh]

/-- Direct consequence for a winning compressed phase table: at every
physical starting time, all still-promised arbitrary closing suffixes agree
with the bank after the intervening rightward rounds. -/
theorem rollingLeaderMonitor_closing_transport {H I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
    (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
    (initial : ClosingPlanBank H I₁ I₂ O₁ O₂ D)
    (play : Nat → RealizedBlockRound I₂ I₁ (RollingReceiverOutput H I₁ I₂ O₁ O₂ D) O₁)
    (wins : (rollingLeaderMonitor M initial).WinsPlay play)
    (h : H) (a k t : Nat) (within : k+t < D+1)
    (future : Nat → I₁ × I₂ × Graph)
    (follows : ∀ n, n < k → future n = ((play (a+n)).1.2,(play (a+n)).1.1,.right)) :
    closingPlanEntry (phaseMemoryRun initial rollingLeaderNext play a h) future ⟨k+t,within⟩ =
      closingPlanEntry (phaseMemoryRun initial rollingLeaderNext play (a+k) h)
        (fun n => future (k+n)) ⟨t,by omega⟩ := by
  have checks := ((rollingLeaderMonitor_correct M initial play).mp wins).2
  have overlap : ∀ n, RollingClosingOverlap
      (phaseMemoryRun initial rollingLeaderNext play (a+n) h)
      (phaseMemoryRun initial rollingLeaderNext play (a+(n+1)) h)
      ((play (a+n)).1.2,(play (a+n)).1.1,.right) := by
    intro n
    simpa only [Nat.add_assoc] using (checks (a+n) h).1
  simpa only [Nat.add_zero] using rollingClosingPlans_transport
    (fun n => phaseMemoryRun initial rollingLeaderNext play (a+n) h)
    (fun n => ((play (a+n)).1.2,(play (a+n)).1.1,.right)) overlap future k t within follows

end Characterisation
