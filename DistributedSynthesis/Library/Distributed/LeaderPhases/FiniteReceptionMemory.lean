/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CarriedScheduledBundles

/-! Finite reception memory computes delayed checkpoints at their physical
rounds. Its update reads a scenario graph, not a new observation supplied
to a process. The existing locality theorems govern implementation. -/
namespace Characterisation
open DistributedSynthesis

abbrev ReceptionMemory (d : Nat) := Proc → Fin (d+1) → Bool

def graphReceives : Proc → Graph → Bool
  | .one, .right => false
  | .two, .left => false
  | _, _ => true

def receptionMemoryStep {d : Nat} (memory : ReceptionMemory d) (g : Graph) : ReceptionMemory d :=
  fun p i => if zero : i.val = 0 then graphReceives p g
    else memory p ⟨i.val-1,by omega⟩

def receptionMemoryRun (d : Nat) : List Graph → ReceptionMemory d :=
  List.foldl receptionMemoryStep (fun _ _ => true)

theorem receptionMemoryRun_append (d : Nat) (g : List Graph) (r : Graph) :
    receptionMemoryRun d (g++[r]) = receptionMemoryStep (receptionMemoryRun d g) r := by
  simp only [receptionMemoryRun,List.foldl_append,List.foldl_cons,List.foldl_nil]

/-- Slot i records whether the view i physical rounds ago has silent age
zero. Before the initial round it refers to the empty view, whose age is zero. -/
theorem receptionMemoryRun_exact {I₁ I₂ : Type} (d : Nat) (h : EnvHistory I₁ I₂)
    (p : Proc) (i : Fin (d+1)) :
    receptionMemoryRun d (History.graphSequence h) p i =
      decide (silentAge (lagView i.val (currentView p h)) = 0) := by
  induction h using List.reverseRecOn generalizing i with
  | nil => cases p <;> simp [History.graphSequence,receptionMemoryRun,lagView_empty,silentAge,currentView,viewPair]
  | append_singleton h r ih =>
    rw [show History.graphSequence (h++[r]) = History.graphSequence h ++ [r.graph] by simp [History.graphSequence],receptionMemoryRun_append]
    by_cases zero : i.val = 0
    · simp only [receptionMemoryStep,zero,lagView]
      cases p
      · erw [currentView_one_append]
        cases r.graph <;> simp [graphReceives,silentAge]
      · erw [currentView_two_append]
        cases r.graph <;> simp [graphReceives,silentAge]
    · rw [receptionMemoryStep,dif_neg zero,ih]
      have index : i.val = (i.val-1)+1 := by omega
      conv_rhs => rw [index,lagView_append]

/-- Select the delayed checkpoint bit using the currently agreed leader. -/
def receptionCheckpoint {d : Nat} (memory : ReceptionMemory d) (leader : Proc) : Bool :=
  memory leader ⟨d,by omega⟩

theorem receptionCheckpoint_exact {I₁ I₂ : Type} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) :
    receptionCheckpoint (receptionMemoryRun d (History.graphSequence h))
      (componentLeader P d (History.graphSequence h)) = leaderCheckpoint P d h := by
  exact receptionMemoryRun_exact d h _ ⟨d,by omega⟩

abbrev CappedReceptionAge (d : Nat) := Proc → Fin (d+1)

def cappedReceptionStep {d : Nat} (age : CappedReceptionAge d) (g : Graph) : CappedReceptionAge d :=
  fun p => if graphReceives p g then ⟨0,by omega⟩ else ⟨min d ((age p).val+1),by omega⟩

def cappedReceptionRun (d : Nat) : List Graph → CappedReceptionAge d :=
  List.foldl cappedReceptionStep (fun _ => ⟨0,by omega⟩)

theorem cappedReceptionRun_append (d : Nat) (g : List Graph) (r : Graph) :
    cappedReceptionRun d (g++[r]) = cappedReceptionStep (cappedReceptionRun d g) r := by
  simp only [cappedReceptionRun,List.foldl_append,List.foldl_cons,List.foldl_nil]

theorem cappedReceptionRun_exact {I₁ I₂ : Type} (d : Nat) (h : EnvHistory I₁ I₂) (p : Proc) :
    (cappedReceptionRun d (History.graphSequence h) p).val = min d (silentAge (currentView p h)) := by
  induction h using List.reverseRecOn with
  | nil => cases p <;> simp [History.graphSequence,cappedReceptionRun,currentView,viewPair,silentAge]
  | append_singleton h r ih =>
    rw [show History.graphSequence (h++[r]) = History.graphSequence h ++ [r.graph] by simp [History.graphSequence],cappedReceptionRun_append]
    cases p
    · erw [currentView_one_append]
      cases r.graph <;> simp only [cappedReceptionStep,graphReceives,Bool.false_eq_true,
        ite_false,ite_true,silentAge]
      all_goals first | simp | rw [ih]; omega
    · erw [currentView_two_append]
      cases r.graph <;> simp only [cappedReceptionStep,graphReceives,Bool.false_eq_true,
        ite_false,ite_true,silentAge]
      all_goals first | simp | rw [ih]; omega

instance receptionMemory_fintype (d : Nat) : Fintype (ReceptionMemory d) := inferInstance
instance cappedReceptionAge_fintype (d : Nat) : Fintype (CappedReceptionAge d) := inferInstance

end Characterisation
