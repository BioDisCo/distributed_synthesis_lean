/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderClosingSelection
/-! Exact finite-set updates during a round without reception. These consume
one round of the available horizon; they do not replenish rolling plans. -/
namespace Characterisation
open DistributedSynthesis

theorem nonreceiving_one_history_fiber {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    currentView .one k = currentView .one (h++[⟨x,y,.right,(),()⟩]) ↔
      ∃ past z, currentView .one past = currentView .one h ∧
        k = past++[⟨x,z,.right,(),()⟩] := by
  constructor
  · intro same
    rcases List.eq_nil_or_concat' k with rfl | ⟨past,r,rfl⟩
    · change View.empty .one = currentView .one (History.append h _) at same
      rw [currentView_one_append] at same
      cases same
    · rcases r with ⟨a,b,g,⟨⟩,⟨⟩⟩
      change currentView .one (History.append past _) = currentView .one (History.append h _) at same
      rw [currentView_one_append,currentView_one_append] at same
      cases g with
      | left => cases same
      | both => cases same
      | right =>
        simp only [View.noRecv.injEq, PSum.inl.injEq] at same
        obtain ⟨obs,rfl⟩ := same
        exact ⟨past,b,obs,rfl⟩
  · rintro ⟨past,z,obs,rfl⟩
    change currentView .one (History.append past _) = currentView .one (History.append h _)
    rw [currentView_one_append,currentView_one_append]
    exact congrArg (fun v => View.noRecv v (.inl x)) obs

def blindClosingUpdateOne {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (menu : ClosingMenu I₁ I₂ O₁ O₂ (D+1)) (x : I₁) : ClosingMenu I₁ I₂ O₁ O₂ D :=
  {plan | ∃ old ∈ menu, ∃ y, advanceClosingPlan old (x,y,.right) = plan}

theorem closing_menu_no_reception_one {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    leaderClosingMenu σ D .one (currentView .one (h++[⟨x,y,.right,(),()⟩])) =
      blindClosingUpdateOne (leaderClosingMenu σ (D+1) .one (currentView .one h)) x := by
  ext plan
  constructor
  · rintro ⟨k,obs,eq⟩
    obtain ⟨past,z,oldObs,rfl⟩ := (nonreceiving_one_history_fiber h k x y).mp obs
    refine ⟨closingPlanOfStrategy σ past (D+1),⟨past,oldObs,rfl⟩,z,?_⟩
    simpa only [advanceClosingPlan_ofStrategy] using eq
  · rintro ⟨old,⟨past,obs,rfl⟩,z,eq⟩
    refine ⟨past++[⟨x,z,.right,(),()⟩],?_,?_⟩
    · exact (nonreceiving_one_history_fiber h _ x y).mpr ⟨past,z,obs,rfl⟩
    · simpa only [advanceClosingPlan_ofStrategy] using eq

theorem nonreceiving_two_history_fiber {I₁ I₂ : Type*}
    (h k : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    currentView .two k = currentView .two (h++[⟨x,y,.left,(),()⟩]) ↔
      ∃ past z, currentView .two past = currentView .two h ∧
        k = past++[⟨z,y,.left,(),()⟩] := by
  constructor
  · intro same
    rcases List.eq_nil_or_concat' k with rfl | ⟨past,r,rfl⟩
    · change View.empty .two = currentView .two (History.append h _) at same
      rw [currentView_two_append] at same
      cases same
    · rcases r with ⟨a,b,g,⟨⟩,⟨⟩⟩
      change currentView .two (History.append past _) = currentView .two (History.append h _) at same
      rw [currentView_two_append,currentView_two_append] at same
      cases g with
      | right => cases same
      | both => cases same
      | left =>
        simp only [View.noRecv.injEq, PSum.inr.injEq] at same
        obtain ⟨obs,rfl⟩ := same
        exact ⟨past,a,obs,rfl⟩
  · rintro ⟨past,z,obs,rfl⟩
    change currentView .two (History.append past _) = currentView .two (History.append h _)
    rw [currentView_two_append,currentView_two_append]
    exact congrArg (fun v => View.noRecv v (.inr y)) obs

def blindClosingUpdateTwo {I₁ I₂ O₁ O₂ : Type*} {D : Nat}
    (menu : ClosingMenu I₁ I₂ O₁ O₂ (D+1)) (y : I₂) : ClosingMenu I₁ I₂ O₁ O₂ D :=
  {plan | ∃ old ∈ menu, ∃ x, advanceClosingPlan old (x,y,.left) = plan}

theorem closing_menu_no_reception_two {I₁ I₂ O₁ O₂ : Type*}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (D : Nat)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    leaderClosingMenu σ D .two (currentView .two (h++[⟨x,y,.left,(),()⟩])) =
      blindClosingUpdateTwo (leaderClosingMenu σ (D+1) .two (currentView .two h)) y := by
  ext plan
  constructor
  · rintro ⟨k,obs,eq⟩
    obtain ⟨past,z,oldObs,rfl⟩ := (nonreceiving_two_history_fiber h k x y).mp obs
    refine ⟨closingPlanOfStrategy σ past (D+1),⟨past,oldObs,rfl⟩,z,?_⟩
    simpa only [advanceClosingPlan_ofStrategy] using eq
  · rintro ⟨old,⟨past,obs,rfl⟩,z,eq⟩
    refine ⟨past++[⟨z,y,.left,(),()⟩],?_,?_⟩
    · exact (nonreceiving_two_history_fiber h _ x y).mpr ⟨past,z,obs,rfl⟩
    · simpa only [advanceClosingPlan_ofStrategy] using eq

end Characterisation
