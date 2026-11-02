/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderPhases

/-! A leader change or delayed checkpoint is an agreed boundary with bounded
input uncertainty. The leader's contingent instructions have finite menus at
such boundaries; the global strategy construction remains a separate task. -/
namespace Characterisation
open DistributedSynthesis

theorem leaderBoundary_component {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (h k : EnvHistory I₁ I₂)
    (recent : RecentOther P d (History.graphSequence h)
      (componentLeader P d (History.graphSequence h)))
    (conn : InputConnected P h k) : leaderBoundary P d h = leaderBoundary P d k := by
  have graphs := inputConnected_projects P conn
  have current := componentLeader_component_invariant P d graphs
  have previous := componentLeader_component_invariant P d (connected_parent P closed graphs)
  rw [← graphSequence_dropLast,← graphSequence_dropLast] at previous
  have checkpoint := leaderCheckpoint_component P d h k recent conn
  unfold leaderBoundary
  rw [checkpoint,current,previous]

theorem leaderBoundary_local {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ h, P h → ∃ p, RecentOther P d h p) :
    ∃ test : StrategyPair I₁ I₂ Bool Bool, ∀ h : EnvHistory I₁ I₂,
      P (History.graphSequence h) →
      test.one (currentView .one h) = leaderBoundary P d h ∧
      test.two (currentView .two h) = leaderBoundary P d h := by
  let H := {h : EnvHistory I₁ I₂ // P (History.graphSequence h)}
  have coherent : ∀ q (h k : H), currentView q h.val = currentView q k.val →
      leaderBoundary P d h.val = leaderBoundary P d k.val := by
    intro q h k eq
    have adjacent : InputAdjacent h.val k.val := by
      cases q <;> [exact Or.inl eq; exact Or.inr eq]
    exact leaderBoundary_component P closed d h.val k.val
      (componentLeader_correct P d _ (recent _ h.property))
      (Relation.ReflTransGen.single ⟨h.property,k.property,adjacent⟩)
  obtain ⟨one,hOne⟩ := factor_local_response (fun h : H => currentView .one h.val)
    (fun h : H => leaderBoundary P d h.val) (coherent .one)
  obtain ⟨two,hTwo⟩ := factor_local_response (fun h : H => currentView .two h.val)
    (fun h : H => leaderBoundary P d h.val) (coherent .two)
  exact ⟨⟨one,two⟩,fun h live => ⟨hOne ⟨h,live⟩,hTwo ⟨h,live⟩⟩⟩

/-- Explicit bound for a fixed graph-component bound. This is the same
bound used by `bounded_leader_boundaries`, before existential packaging. -/
theorem bounded_leader_boundaries_of_bound {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (K : Nat)
    (bound : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
    (d : Nat) (recent : ∀ h, P h → ∃ p, RecentOther P d h p) :
    ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) → leaderBoundary P d h = true →
      Finite (InputHistoryComponent P h) ∧ Nat.card (InputHistoryComponent P h) ≤
        K * (Nat.card (Fin d → Option (PSum I₁ I₂)))^2 +
        K * (Nat.card (Fin (d+1) → Option (PSum I₁ I₂)))^2 := by
  let small := K * (Nat.card (Fin d → Option (PSum I₁ I₂)))^2
  let large := K * (Nat.card (Fin (d+1) → Option (PSum I₁ I₂)))^2
  intro h live boundary
  have current := componentLeader_correct P d _ (recent _ live)
  have parentLive : P (History.graphSequence h.dropLast) := by
    rw [graphSequence_dropLast]
    exact live_parent P closed live
  have previous := componentLeader_correct P d _ (recent _ parentLive)
  by_cases within : d ≤ List.length h
  · have alternatives : leaderCheckpoint P d h = true ∨
        componentLeader P d (History.graphSequence h.dropLast) ≠
          componentLeader P d (History.graphSequence h) := by
      simpa [leaderBoundary] using boundary
    rcases alternatives with checkpoint | changed
    · have result := finite_leader_checkpoint P ⟨K,bound⟩ d h _ live current within
        (of_decide_eq_true checkpoint)
      refine ⟨result.1,?_⟩
      have size : Nat.card (InputHistoryComponent P h) ≤ small :=
        result.2.trans (Nat.mul_le_mul_right _ (bound _ live).2)
      exact size.trans (Nat.le_add_right _ _)
    · have result := finite_component_of_common_prefixes P ⟨K,bound⟩ (d+1) h live
        (fun k conn => both_input_prefixes_at_switch P closed d _ _ changed previous current conn)
      refine ⟨result.1,?_⟩
      have size : Nat.card (InputHistoryComponent P h) ≤ large :=
        result.2.trans (Nat.mul_le_mul_right _ (bound _ live).2)
      omega
  · have common : ∀ k, InputConnected P h k →
        olderInputPrefix .one (d+1) h = olderInputPrefix .one (d+1) k ∧
        olderInputPrefix .two (d+1) h = olderInputPrefix .two (d+1) k := by
      intro k conn
      have len : List.length h = List.length k := by
        have eq := connected_same_depth P (inputConnected_projects P conn)
        simpa [History.graphSequence] using eq
      have eh : List.length h-(d+1) = 0 := by omega
      have ek : List.length k-(d+1) = 0 := by omega
      simp [olderInputPrefix,History.length,eh,ek]
    have result := finite_component_of_common_prefixes P ⟨K,bound⟩ (d+1) h live common
    refine ⟨result.1,?_⟩
    have size : Nat.card (InputHistoryComponent P h) ≤ large :=
      result.2.trans (Nat.mul_le_mul_right _ (bound _ live).2)
    omega

/-- Uniform bounds cover delayed checkpoints, leader changes, and the
initial histories shorter than d. No initial segment is discarded. -/
theorem bounded_leader_boundaries {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (bounded : BoundedViewComponents P)
    (d : Nat) (recent : ∀ h, P h → ∃ p, RecentOther P d h p) :
    ∃ B, ∀ h : EnvHistory I₁ I₂, P (History.graphSequence h) →
      leaderBoundary P d h = true →
      Finite (InputHistoryComponent P h) ∧ Nat.card (InputHistoryComponent P h) ≤ B := by
  obtain ⟨K,bound⟩ := bounded
  exact ⟨_,bounded_leader_boundaries_of_bound P closed K bound d recent⟩

/-- Both processes agree on each boundary, and its remaining uncertainty is
uniformly bounded. This includes both ways of ending a leader phase. -/
theorem holes_agreed_bounded_leader_boundaries {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∃ test : StrategyPair I₁ I₂ Bool Bool,
      ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
        (test.one (currentView .one h) = leaderBoundary (LivePrefix A) d h ∧
          test.two (currentView .two h) = leaderBoundary (LivePrefix A) d h) ∧
        (leaderBoundary (LivePrefix A) d h = true →
          Finite (InputHistoryComponent (LivePrefix A) h) ∧
            Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ B) := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨test,localTest⟩ := leaderBoundary_local (I₁:=I₁) (I₂:=I₂)
    (LivePrefix A) (livePrefix_closed A) d recent
  obtain ⟨B,bound⟩ := bounded_leader_boundaries (I₁:=I₁) (I₂:=I₂)
    (LivePrefix A) (livePrefix_closed A)
    ((omegaRegular_holes_iff_bounded_components A regular).mp holes) d recent
  exact ⟨d,B,test,fun h live => ⟨localTest h live,bound h live⟩⟩

/-- At each agreed boundary, contingent instructions covering d+1 rounds
have a finite menu. This is not a claim that the closing time is known there. -/
theorem holes_finite_boundary_instructions {I₁ I₂ O₁ O₂ : Type*}
    [Finite I₁] [Finite I₂] [Finite O₁] [Finite O₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      leaderBoundary (LivePrefix A) d h = true →
      Finite (WindowTable O₁ O₂ (fun k : InputHistoryComponent (LivePrefix A) h => k.val) (d+1)) := by
  obtain ⟨d,B,test,result⟩ := holes_agreed_bounded_leader_boundaries (I₁:=I₁) (I₂:=I₂)
    A regular holes
  refine ⟨d,?_⟩
  intro h live boundary
  letI : Finite (InputHistoryComponent (LivePrefix A) h) := ((result h live).2 boundary).1
  infer_instance

end Characterisation
