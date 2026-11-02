/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderClosingPlans
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderInstructionReadback
import DistributedSynthesis.Library.Distributed.LeaderPhases.InstructionDelivery

/-! Finite contingent instructions observable to a leader, and their readback
at a receiver. All constructions are relative to a fixed strategy. They do
not assert that these perfect-recall maps have effective finite updates. -/
namespace Characterisation
open DistributedSynthesis

abbrev ClosingMenu (I₁ I₂ O₁ O₂ : Type*) (D : Nat) :=
  Set (LeaderClosingPlan I₁ I₂ O₁ O₂ D)

instance closingMenu_finite {I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂] (D : Nat) :
    Finite (ClosingMenu I₁ I₂ O₁ O₂ D) := by
  unfold ClosingMenu
  infer_instance

/-- The leader can specify the set of plans consistent with its own view.
It does not select a hidden history within that view. -/
def leaderClosingMenu {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) (p : Proc)
    (v : View I₁ I₂ p) : ClosingMenu I₁ I₂ O₁ O₂ D :=
  {plan | ∃ h : EnvHistory I₁ I₂,
    currentView p h = v ∧ closingPlanOfStrategy σ h D = plan}

theorem actual_plan_mem_leaderClosingMenu {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) (p : Proc)
    (h : EnvHistory I₁ I₂) :
    closingPlanOfStrategy σ h D ∈ leaderClosingMenu σ D p (currentView p h) :=
  ⟨h,rfl,rfl⟩

/-- Upon delivery, the receiver can recover the previous-history plan using
its own view together with the delivered leader view. The two delivering
graphs give the same readback; neither is supplied as an extra observation. -/
theorem closing_plan_readback_from_one {I₁ I₂ O₁ O₂ : Type*}
    [Nonempty O₁] [Nonempty O₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) :
    ∃ select : View I₁ I₂ .two → LeaderClosingPlan I₁ I₂ O₁ O₂ D,
      ∀ (h : EnvHistory I₁ I₂) x y g, g = .right ∨ g = .both →
        select (currentView .two (h++[⟨x,y,g,(),()⟩])) = closingPlanOfStrategy σ h D ∧
        select (currentView .two (h++[⟨x,y,g,(),()⟩])) ∈
          leaderClosingMenu σ D .one (currentView .one h) ∧
        receivedInstruction (fun v _ => leaderClosingMenu σ D .one v)
          (currentView .two (h++[⟨x,y,g,(),()⟩])) =
          some (leaderClosingMenu σ D .one (currentView .one h)) := by
  obtain ⟨select, correct⟩ := receiving_two_table_is_local
    (fun h (_ : I₁) (_ : I₂) => closingPlanOfStrategy σ h D)
  refine ⟨select, fun h x y g delivered => ?_⟩
  rw [correct h x y g delivered]
  exact ⟨rfl, actual_plan_mem_leaderClosingMenu σ D .one h,
    instruction_from_one (fun v _ => leaderClosingMenu σ D .one v) h _ delivered⟩

theorem closing_plan_readback_from_two {I₁ I₂ O₁ O₂ : Type*}
    [Nonempty O₁] [Nonempty O₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) :
    ∃ select : View I₁ I₂ .one → LeaderClosingPlan I₁ I₂ O₁ O₂ D,
      ∀ (h : EnvHistory I₁ I₂) x y g, g = .left ∨ g = .both →
        select (currentView .one (h++[⟨x,y,g,(),()⟩])) = closingPlanOfStrategy σ h D ∧
        select (currentView .one (h++[⟨x,y,g,(),()⟩])) ∈
          leaderClosingMenu σ D .two (currentView .two h) ∧
        receivedInstruction (fun v _ => leaderClosingMenu σ D .two v)
          (currentView .one (h++[⟨x,y,g,(),()⟩])) =
          some (leaderClosingMenu σ D .two (currentView .two h)) := by
  obtain ⟨select, correct⟩ := receiving_one_table_is_local
    (fun h (_ : I₁) (_ : I₂) => closingPlanOfStrategy σ h D)
  refine ⟨select, fun h x y g delivered => ?_⟩
  rw [correct h x y g delivered]
  exact ⟨rfl, actual_plan_mem_leaderClosingMenu σ D .two h,
    instruction_from_two (fun v _ => leaderClosingMenu σ D .two v) h _ delivered⟩

/-- The receiver knows the previous history and both fresh inputs, but
retains both possibilities for the current delivering graph. -/
def receivedClosingSuccessors {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) (sender : Proc)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) : ClosingMenu I₁ I₂ O₁ O₂ D :=
  {plan | plan = advanceClosingPlan (closingPlanOfStrategy σ h (D+1))
      (x,y,leaderOutgoingGraph sender) ∨
    plan = advanceClosingPlan (closingPlanOfStrategy σ h (D+1)) (x,y,.both)}

/-- Exact two-candidate update, not a choice of the unobservable graph. -/
theorem receivedClosingSuccessors_exact {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) (sender : Proc)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂)
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    plan ∈ receivedClosingSuccessors σ D sender h x y ↔
      ∃ g, (g = leaderOutgoingGraph sender ∨ g = .both) ∧
        closingPlanOfStrategy σ (h++[⟨x,y,g,(),()⟩]) D = plan := by
  simp only [receivedClosingSuccessors, Set.mem_setOf_eq, advanceClosingPlan_ofStrategy]
  constructor
  · rintro (eq | eq)
    · exact ⟨leaderOutgoingGraph sender,Or.inl rfl,eq.symm⟩
    · exact ⟨.both,Or.inr rfl,eq.symm⟩
  · rintro ⟨g, (rfl | rfl), eq⟩
    · exact Or.inl eq.symm
    · exact Or.inr eq.symm

theorem closing_successors_local_from_one {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) :
    ∃ update : View I₁ I₂ .two → ClosingMenu I₁ I₂ O₁ O₂ D,
      ∀ (h : EnvHistory I₁ I₂) x y g, g = .right ∨ g = .both →
        update (currentView .two (h++[⟨x,y,g,(),()⟩])) =
          receivedClosingSuccessors σ D .one h x y :=
  receiving_two_table_is_local (receivedClosingSuccessors σ D .one)

theorem closing_successors_local_from_two {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat) :
    ∃ update : View I₁ I₂ .one → ClosingMenu I₁ I₂ O₁ O₂ D,
      ∀ (h : EnvHistory I₁ I₂) x y g, g = .left ∨ g = .both →
        update (currentView .one (h++[⟨x,y,g,(),()⟩])) =
          receivedClosingSuccessors σ D .two h x y :=
  receiving_one_table_is_local (receivedClosingSuccessors σ D .two)

theorem receiving_two_history_fiber {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    currentView .two k = currentView .two (h++[⟨x,y,.right,(),()⟩]) ↔
      ∃ g, (g = .right ∨ g = .both) ∧ k = h++[⟨x,y,g,(),()⟩] := by
  constructor
  · intro same
    rcases List.eq_nil_or_concat' k with rfl | ⟨past,r,rfl⟩
    · change View.empty .two = currentView .two (History.append h _) at same
      rw [currentView_two_append] at same
      cases same
    · rcases r with ⟨a,b,g,⟨⟩,⟨⟩⟩
      cases g with
      | left =>
        change currentView .two (History.append past _) = currentView .two (History.append h _) at same
        rw [currentView_two_append,currentView_two_append] at same
        cases same
      | right =>
        have facts := receiving_two_identifies_past past h
          ⟨a,b,.right,(),()⟩ ⟨x,y,.right,(),()⟩ (Or.inl rfl) (Or.inl rfl) same
        rcases facts with ⟨rfl,ha,hb⟩
        dsimp only at ha hb
        subst a; subst b
        exact ⟨.right,Or.inl rfl,rfl⟩
      | both =>
        have facts := receiving_two_identifies_past past h
          ⟨a,b,.both,(),()⟩ ⟨x,y,.right,(),()⟩ (Or.inr rfl) (Or.inl rfl) same
        rcases facts with ⟨rfl,ha,hb⟩
        dsimp only at ha hb
        subst a; subst b
        exact ⟨.both,Or.inr rfl,rfl⟩
  · rintro ⟨g, (rfl | rfl), rfl⟩
    · rfl
    · change currentView .two (History.append h _) = currentView .two (History.append h _)
      rw [currentView_two_append,currentView_two_append]

theorem receiving_one_history_fiber {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    currentView .one k = currentView .one (h++[⟨x,y,.left,(),()⟩]) ↔
      ∃ g, (g = .left ∨ g = .both) ∧ k = h++[⟨x,y,g,(),()⟩] := by
  constructor
  · intro same
    rcases List.eq_nil_or_concat' k with rfl | ⟨past,r,rfl⟩
    · change View.empty .one = currentView .one (History.append h _) at same
      rw [currentView_one_append] at same
      cases same
    · rcases r with ⟨a,b,g,⟨⟩,⟨⟩⟩
      cases g with
      | right =>
        change currentView .one (History.append past _) = currentView .one (History.append h _) at same
        rw [currentView_one_append,currentView_one_append] at same
        cases same
      | left =>
        have facts := receiving_one_identifies_past past h
          ⟨a,b,.left,(),()⟩ ⟨x,y,.left,(),()⟩ (Or.inl rfl) (Or.inl rfl) same
        rcases facts with ⟨rfl,ha,hb⟩
        dsimp only at ha hb
        subst a; subst b
        exact ⟨.left,Or.inl rfl,rfl⟩
      | both =>
        have facts := receiving_one_identifies_past past h
          ⟨a,b,.both,(),()⟩ ⟨x,y,.left,(),()⟩ (Or.inr rfl) (Or.inl rfl) same
        rcases facts with ⟨rfl,ha,hb⟩
        dsimp only at ha hb
        subst a; subst b
        exact ⟨.both,Or.inr rfl,rfl⟩
  · rintro ⟨g, (rfl | rfl), rfl⟩
    · rfl
    · change currentView .one (History.append h _) = currentView .one (History.append h _)
      rw [currentView_one_append,currentView_one_append]

/-- The two successor plans are exactly all plans compatible with the
receiver's current observation, with no additional hidden histories. -/
theorem closing_menu_after_delivery_from_one {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) (g : Graph)
    (delivered : g = .right ∨ g = .both) :
    leaderClosingMenu σ D .two (currentView .two (h++[⟨x,y,g,(),()⟩])) =
      receivedClosingSuccessors σ D .one h x y := by
  have obs : currentView .two (h++[⟨x,y,g,(),()⟩]) =
      currentView .two (h++[⟨x,y,.right,(),()⟩]) := by
    change currentView .two (History.append h _) = currentView .two (History.append h _)
    rw [currentView_two_append,currentView_two_append]
    rcases delivered with rfl | rfl <;> rfl
  rw [obs]
  ext plan
  constructor
  · rintro ⟨k,same,eq⟩
    obtain ⟨graph, hg, rfl⟩ := (receiving_two_history_fiber h k x y).mp same
    exact (receivedClosingSuccessors_exact σ D .one h x y plan).mpr ⟨graph,hg,eq⟩
  · intro mem
    obtain ⟨graph,hg,eq⟩ := (receivedClosingSuccessors_exact σ D .one h x y plan).mp mem
    exact ⟨_,(receiving_two_history_fiber h _ x y).mpr ⟨graph,hg,rfl⟩,eq⟩

/-- The two successor plans are exactly all plans compatible with the
receiver's current observation, with no additional hidden histories. -/
theorem closing_menu_after_delivery_from_two {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) (g : Graph)
    (delivered : g = .left ∨ g = .both) :
    leaderClosingMenu σ D .one (currentView .one (h++[⟨x,y,g,(),()⟩])) =
      receivedClosingSuccessors σ D .two h x y := by
  have obs : currentView .one (h++[⟨x,y,g,(),()⟩]) =
      currentView .one (h++[⟨x,y,.left,(),()⟩]) := by
    change currentView .one (History.append h _) = currentView .one (History.append h _)
    rw [currentView_one_append,currentView_one_append]
    rcases delivered with rfl | rfl <;> rfl
  rw [obs]
  ext plan
  constructor
  · rintro ⟨k,same,eq⟩
    obtain ⟨graph, hg, rfl⟩ := (receiving_one_history_fiber h k x y).mp same
    exact (receivedClosingSuccessors_exact σ D .two h x y plan).mpr ⟨graph,hg,eq⟩
  · intro mem
    obtain ⟨graph,hg,eq⟩ := (receivedClosingSuccessors_exact σ D .two h x y plan).mp mem
    exact ⟨_,(receiving_one_history_fiber h _ x y).mpr ⟨graph,hg,rfl⟩,eq⟩

/-- Even on an always-right prefix, the receiver may remember its first
private bit. Reproducing this strategy's entire closing plan cannot be a
function of the leader view alone. This is not a synthesis counterexample. -/
theorem single_closing_plan_not_leader_observable :
    ∃ σ : StrategyPair Unit Bool Unit Bool,
      ¬ ∃ select : View Unit Bool .one → LeaderClosingPlan Unit Bool Unit Bool 1,
        ∀ b : Bool, select (currentView .one [⟨(),b,.right,(),()⟩]) =
          closingPlanOfStrategy σ [⟨(),b,.right,(),()⟩] 1 := by
  let σ : StrategyPair Unit Bool Unit Bool :=
    ⟨fun _ => (), fun v => match ownInputs v with
      | .inr b :: _ => b
      | _ => false⟩
  refine ⟨σ, ?_⟩
  rintro ⟨select, correct⟩
  have same : currentView .one ([⟨(),false,.right,(),()⟩] : EnvHistory Unit Bool) =
      currentView .one ([⟨(),true,.right,(),()⟩] : EnvHistory Unit Bool) := rfl
  have plans := (correct false).symm.trans ((congrArg select same).trans (correct true))
  let s : ClosingScenario Unit Bool 1 := ((),⟨⟨0,by omega⟩,fun _ => ((),false,.right)⟩)
  have bit := congrArg (fun plan => (plan s).2) plans
  change false = true at bit
  cases bit

end Characterisation
