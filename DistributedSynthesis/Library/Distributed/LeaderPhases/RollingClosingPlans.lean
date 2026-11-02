/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryInputFibers

/-! Replenish a bounded closing plan without changing any promised output.
The overlap law is finite, applies before a closing time is known, and is
witnessed by the plans of every actual strategy. -/
namespace Characterisation
open DistributedSynthesis

def restrictClosingScenario {I₁ I₂ : Type*} {D E : Nat} (bound : D ≤ E)
    (s : ClosingScenario I₁ I₂ D) : ClosingScenario I₁ I₂ E :=
  ((),⟨⟨s.2.1.val,by have := s.2.1.isLt; omega⟩,s.2.2⟩)

def restrictClosingPlan {I₁ I₂ O₁ O₂ : Type*} {D E : Nat} (bound : D ≤ E)
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ E) : LeaderClosingPlan I₁ I₂ O₁ O₂ D :=
  fun s => plan (restrictClosingScenario bound s)

theorem restrictClosingPlan_ofStrategy {I₁ I₂ O₁ O₂ : Type*} {D E : Nat}
    (bound : D ≤ E) (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) :
    restrictClosingPlan bound (closingPlanOfStrategy σ h E) = closingPlanOfStrategy σ h D := by
  funext s
  rfl

def RollingClosingOverlap {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (old new : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (round : I₁ × I₂ × Graph) : Prop :=
  advanceClosingPlan old round = restrictClosingPlan (Nat.le_succ D) new

instance rollingClosingOverlap_decidable {I₁ I₂ O₁ O₂ : Type*}
    [Fintype I₁] [Fintype I₂] [DecidableEq O₁] [DecidableEq O₂] {D : Nat}
    (old new : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1)) (round : I₁ × I₂ × Graph) :
    Decidable (RollingClosingOverlap old new round) := by
  letI : Fintype (ClosingScenario I₁ I₂ D) := by
    unfold ClosingScenario WindowScenario
    infer_instance
  unfold RollingClosingOverlap
  infer_instance

theorem rollingClosingOverlap_ofStrategy {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂)
    (round : I₁ × I₂ × Graph) :
    RollingClosingOverlap (closingPlanOfStrategy σ h (D+1))
      (closingPlanOfStrategy σ (h ++ [⟨round.1,round.2.1,round.2.2,(),()⟩]) (D+1)) round := by
  unfold RollingClosingOverlap
  rw [advanceClosingPlan_ofStrategy,restrictClosingPlan_ofStrategy]

def closingPlanEntry {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) (rounds : Nat → I₁ × I₂ × Graph)
    (t : Fin D) : O₁ × O₂ := plan ((),⟨t,fun j => rounds j.val⟩)

theorem closingPlanEntry_zero {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (rounds : Nat → I₁ × I₂ × Graph) :
    closingPlanEntry plan rounds ⟨0,by omega⟩ =
      closingPlanEntry plan (fun _ => rounds 0) ⟨0,by omega⟩ := by
  unfold closingPlanEntry
  apply congrArg plan
  apply Prod.ext
  · rfl
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext j
  have zero : j.val = 0 := by have bound : j.val < 1 := j.isLt; omega
  change rounds j.val = rounds 0
  rw [zero]

theorem closingPlanEntry_restrict {I₁ I₂ O₁ O₂ : Type*} {D E : Nat}
    (bound : D ≤ E) (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ E)
    (rounds : Nat → I₁ × I₂ × Graph) (t : Fin D) :
    closingPlanEntry (restrictClosingPlan bound plan) rounds t =
      closingPlanEntry plan rounds ⟨t.val,by have := t.isLt; omega⟩ := rfl

theorem closingPlanEntry_succ {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (rounds : Nat → I₁ × I₂ × Graph) (t : Fin D) :
    closingPlanEntry plan rounds ⟨t.val+1,by have := t.isLt; omega⟩ =
      closingPlanEntry (advanceClosingPlan plan (rounds 0)) (fun n => rounds (n+1)) t := by
  unfold closingPlanEntry advanceClosingPlan prependClosingScenario
  apply congrArg plan
  apply Prod.ext
  · rfl
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext j
  refine Fin.cases ?_ (fun i => ?_) j <;> rfl

/-- Repeated replenishment preserves every output promised by an earlier
plan during its original horizon. This concerns all future rounds, not just
the final value or a decreasing menu of possible plans. -/
theorem rollingClosingPlans_preserve_promises {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (plans : Nat → LeaderClosingPlan I₁ I₂ O₁ O₂ (D+1))
    (rounds : Nat → I₁ × I₂ × Graph)
    (overlap : ∀ a, RollingClosingOverlap (plans a) (plans (a+1)) (rounds a))
    (a t : Nat) (within : t < D+1) :
    closingPlanEntry (plans a) (fun n => rounds (a+n)) ⟨t,within⟩ =
      closingPlanEntry (plans (a+t)) (fun n => rounds (a+t+n)) ⟨0,by omega⟩ := by
  induction t generalizing a with
  | zero => simp
  | succ t ih =>
    rw [closingPlanEntry_succ (plans a) (fun n => rounds (a+n)) ⟨t,by omega⟩]
    change closingPlanEntry (advanceClosingPlan (plans a) (rounds a))
      (fun n => rounds (a+(n+1))) ⟨t,by omega⟩ = _
    rw [overlap a,closingPlanEntry_restrict]
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using ih (a+1) (by omega)

end Characterisation
