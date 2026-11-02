/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RecentPieces

/-! The common older information is an entire coordinator view, not merely
its own input word. This is a semantic perfect-recall statement. -/
namespace Characterisation
open DistributedSynthesis

def lagView {I₁ I₂ : Type*} {p : Proc} : Nat → View I₁ I₂ p → View I₁ I₂ p
  | 0,v => v
  | d+1,v => lagView d v.nonFringe.previousView

@[simp] theorem lagView_empty {I₁ I₂ : Type*} (p : Proc) (d : Nat) :
    lagView d (View.empty (In₁:=I₁) (In₂:=I₂) p) = .empty p := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

@[simp] theorem lagView_append {I₁ I₂ : Type*} (p : Proc) (d : Nat)
    (h : EnvHistory I₁ I₂) (r : RoundRecord I₁ I₂ Graph Unit Unit) :
    lagView (d+1) (currentView p (h++[r])) = lagView d (currentView p h) := by
  change lagView d (currentView p (History.append h r)).nonFringe.previousView = _
  cases p
  · rw [currentView_one_append]
    cases r.graph <;> rfl
  · rw [currentView_two_append]
    cases r.graph <;> rfl

/-- A recent reception lets a process identify both processes' views d
rounds ago. The receiving message contains the other previous view. -/
theorem shared_recent_lag {I₁ I₂ : Type*} (d : Nat)
    (h k : EnvHistory I₁ I₂) (p q : Proc)
    (eq : currentView q h = currentView q k)
    (recent : silentAge (currentView q h) < d) :
    lagView d (currentView p h) = lagView d (currentView p k) := by
  induction d generalizing h k p q with
  | zero => omega
  | succ d ih =>
    by_cases same : p = q
    · subst p
      rw [eq]
    · cases h using List.reverseRecOn with
      | nil =>
        cases k using List.reverseRecOn with
        | nil => rfl
        | append_singleton k s =>
          change currentView q [] = currentView q (History.append k s) at eq
          cases q
          · rw [currentView_one_append] at eq
            cases sg : s.graph <;> simp [sg, currentView, viewPair] at eq
          · rw [currentView_two_append] at eq
            cases sg : s.graph <;> simp [sg, currentView, viewPair] at eq
      | append_singleton h r =>
        cases k using List.reverseRecOn with
        | nil =>
          change currentView q (History.append h r) = currentView q [] at eq
          cases q
          · rw [currentView_one_append] at eq
            cases rg : r.graph <;> simp [rg, currentView, viewPair] at eq
          · rw [currentView_two_append] at eq
            cases rg : r.graph <;> simp [rg, currentView, viewPair] at eq
        | append_singleton k s =>
          rw [lagView_append,lagView_append]
          change currentView q (History.append h r) = currentView q (History.append k s) at eq
          change silentAge (currentView q (History.append h r)) < d+1 at recent
          cases q <;> cases p
          all_goals try contradiction
          · rw [currentView_one_append,currentView_one_append] at eq
            rw [currentView_one_append] at recent
            cases rg : r.graph <;> cases sg : s.graph <;>
              simp only [rg, sg, Proc.other, View.recv.injEq, View.noRecv.injEq,
                reduceCtorEq, silentAge] at eq recent
            all_goals first
              | contradiction
              | exact congrArg (lagView d) eq.2.2.1
              | exact ih h k .two .one eq.1 (by omega)
          · rw [currentView_two_append,currentView_two_append] at eq
            rw [currentView_two_append] at recent
            cases rg : r.graph <;> cases sg : s.graph <;>
              simp only [rg, sg, Proc.other, View.recv.injEq, View.noRecv.injEq,
                reduceCtorEq, silentAge] at eq recent
            all_goals first
              | contradiction
              | exact congrArg (lagView d) eq.2.2.1
              | exact ih h k .one .two eq.1 (by omega)

theorem selected_lag_shared_view {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h k : EnvHistory I₁ I₂) (p q : Proc)
    (recent : RecentOther P d (History.graphSequence h) p)
    (eq : currentView q h = currentView q k) :
    lagView d (currentView p h) = lagView d (currentView p k) := by
  by_cases same : q = p
  · subst q
    rw [eq]
  · have age : silentAge (currentView q h) < d := by
      by_contra bad
      exact same (old_view_owner P d h p q recent (by omega))
    exact shared_recent_lag d h k p q eq age

/-- The selected coordinator's entire view d rounds ago is common on the
input-dependent component. No finite-memory implementation is assumed. -/
theorem selected_lag_component {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (p : Proc) {h k : EnvHistory I₁ I₂}
    (recent : RecentOther P d (History.graphSequence h) p)
    (conn : InputConnected P h k) :
    lagView d (currentView p h) = lagView d (currentView p k) := by
  induction conn with
  | refl => rfl
  | @tail a b conn step ih =>
    have recentA := (recentOther_component_invariant P d (inputConnected_projects P conn) p).mp recent
    apply ih.trans
    rcases step.2.2 with eq | eq
    · exact selected_lag_shared_view P d a b p .one recentA eq
    · exact selected_lag_shared_view P d a b p .two recentA eq

theorem holes_common_past_view {I₁ I₂ : Type*}
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      ∃ p, ∀ k, InputConnected (LivePrefix A) h k →
        lagView d (currentView p h) = lagView d (currentView p k) := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d,?_⟩
  intro h live
  obtain ⟨p,hp⟩ := recent _ live
  exact ⟨p,fun k conn => selected_lag_component _ d p hp conn⟩

end Characterisation
