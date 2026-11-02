/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderInstructionReadback

/-! Delayed agreement on the leader's received information gives a bounded
checkpoint. This does not assume that a reception is commonly recognized
in the round when it occurs. -/
namespace Characterisation
open DistributedSynthesis

theorem lagView_suffix {I₁ I₂ : Type*} (p : Proc) (h u : EnvHistory I₁ I₂) :
    lagView (List.length u) (currentView p (h++u)) = currentView p h := by
  induction u using List.reverseRecOn with
  | nil => simp [lagView]
  | append_singleton u r ih =>
    rw [List.length_append,List.length_singleton,← List.append_assoc,lagView_append,ih]

theorem lagView_take {I₁ I₂ : Type*} (p : Proc) (h : EnvHistory I₁ I₂) (d : Nat)
    (within : d ≤ List.length h) :
    lagView d (currentView p h) = currentView p (h.take (List.length h-d)) := by
  have suffixLength : List.length (h.drop (List.length h-d)) = d := by
    simp only [List.length_drop]
    omega
  have eq := lagView_suffix p (h.take (List.length h-d)) (h.drop (List.length h-d))
  rw [List.take_append_drop,suffixLength] at eq
  exact eq

/-- A receiving view determines both complete input words. The empty view
also satisfies silent age zero; its input words are empty. -/
theorem same_zero_age_inputs {I₁ I₂ : Type*} (p : Proc) (h k : EnvHistory I₁ I₂)
    (same : currentView p h = currentView p k)
    (zero : silentAge (currentView p h) = 0) :
    inputWord .one h = inputWord .one k ∧ inputWord .two h = inputWord .two k := by
  have zeroK : silentAge (currentView p k) = 0 := by rwa [← same]
  have own : inputWord p h = inputWord p k := by
    rw [← ownInputs_current p h,← ownInputs_current p k,same]
  cases p
  · have eh := (otherInputs_history h).1.1
    have ek := (otherInputs_history k).1.1
    simp only [zero,zeroK,Nat.sub_zero] at eh ek
    simp [inputWord,History.length,← List.map_take] at eh ek
    refine ⟨own,?_⟩
    exact eh.symm.trans ((congrArg otherInputs same).trans ek)
  · have eh := (otherInputs_history h).2.1
    have ek := (otherInputs_history k).2.1
    simp only [zero,zeroK,Nat.sub_zero] at eh ek
    simp [inputWord,History.length,← List.map_take] at eh ek
    refine ⟨?_,own⟩
    exact eh.symm.trans ((congrArg otherInputs same).trans ek)

/-- When the commonly known past leader view has silent age zero, both old
input prefixes are common throughout the entire component. -/
theorem leader_checkpoint_prefixes {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (p : Proc)
    (recent : RecentOther P d (History.graphSequence h) p)
    (within : d ≤ List.length h)
    (checkpoint : silentAge (lagView d (currentView p h)) = 0)
    (k : EnvHistory I₁ I₂) (conn : InputConnected P h k) :
    olderInputPrefix .one d h = olderInputPrefix .one d k ∧
      olderInputPrefix .two d h = olderInputPrefix .two d k := by
  have len : List.length h = List.length k := by
    have eq := connected_same_depth P (inputConnected_projects P conn)
    simpa [History.graphSequence] using eq
  have withinK : d ≤ List.length k := by omega
  have same := selected_lag_component P d p recent conn
  rw [lagView_take p h d within,lagView_take p k d withinK] at same
  rw [lagView_take p h d within] at checkpoint
  have words := same_zero_age_inputs p _ _ same checkpoint
  simpa [inputWord,olderInputPrefix,History.length,List.map_take] using words

/-- A delayed checkpoint has a uniform finite bound for fixed alphabets,
graph-component bound, and delay. It need not be a leader change. -/
theorem finite_leader_checkpoint {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (d : Nat) (h : EnvHistory I₁ I₂) (p : Proc)
    (live : P (History.graphSequence h))
    (recent : RecentOther P d (History.graphSequence h) p)
    (within : d ≤ List.length h)
    (checkpoint : silentAge (lagView d (currentView p h)) = 0) :
    Finite (InputHistoryComponent P h) ∧
      Nat.card (InputHistoryComponent P h) ≤
        Nat.card (HistoryComponent P (History.graphSequence h)) *
          (Nat.card (Fin d → Option (PSum I₁ I₂)))^2 :=
  finite_component_of_common_prefixes P bounded d h live
    (leader_checkpoint_prefixes P d h p recent within checkpoint)

/-- If the process selected at the end has received at the start of the d
following rounds, its received knowledge now forms a bounded checkpoint.
The leader need not know that its message was delivered in the first round. -/
theorem checkpoint_after_leader_reception {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P) (d : Nat)
    (h u : EnvHistory I₁ I₂) (p : Proc)
    (delay : List.length u = d) (received : silentAge (currentView p h) = 0)
    (live : P (History.graphSequence (h++u)))
    (recent : RecentOther P d (History.graphSequence (h++u)) p) :
    Finite (InputHistoryComponent P (h++u)) ∧
      Nat.card (InputHistoryComponent P (h++u)) ≤
        Nat.card (HistoryComponent P (History.graphSequence (h++u))) *
          (Nat.card (Fin d → Option (PSum I₁ I₂)))^2 := by
  apply finite_leader_checkpoint P bounded d (h++u) p live recent
  · simp only [List.length_append]
    omega
  · rw [← delay,lagView_suffix]
    exact received

/-- Both processes will recognize this delayed checkpoint from their own
views; they are not told the leader's current reception bit. -/
noncomputable def leaderCheckpoint {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) : Bool :=
  decide (silentAge (lagView d (currentView
    (componentLeader P d (History.graphSequence h)) h)) = 0)

theorem leaderCheckpoint_component {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h k : EnvHistory I₁ I₂)
    (recent : RecentOther P d (History.graphSequence h)
      (componentLeader P d (History.graphSequence h)))
    (conn : InputConnected P h k) : leaderCheckpoint P d h = leaderCheckpoint P d k := by
  have leader := componentLeader_component_invariant P d (inputConnected_projects P conn)
  have past := selected_lag_component P d _ recent conn
  unfold leaderCheckpoint
  rw [← leader,past]

/-- The delayed checkpoint is an agreed event, determined by each local
view. This is a perfect-recall implementability theorem, not a finite-state
implementation of the checkpoint test. -/
theorem leaderCheckpoint_local {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat)
    (recent : ∀ h, P h → ∃ p, RecentOther P d h p) :
    ∃ test : StrategyPair I₁ I₂ Bool Bool, ∀ h : EnvHistory I₁ I₂,
      P (History.graphSequence h) →
      test.one (currentView .one h) = leaderCheckpoint P d h ∧
      test.two (currentView .two h) = leaderCheckpoint P d h := by
  let H := {h : EnvHistory I₁ I₂ // P (History.graphSequence h)}
  have coherent : ∀ q (h k : H), currentView q h.val = currentView q k.val →
      leaderCheckpoint P d h.val = leaderCheckpoint P d k.val := by
    intro q h k eq
    have adjacent : InputAdjacent h.val k.val := by
      cases q <;> [exact Or.inl eq; exact Or.inr eq]
    exact leaderCheckpoint_component P d h.val k.val
      (componentLeader_correct P d _ (recent _ h.property))
      (Relation.ReflTransGen.single ⟨h.property,k.property,adjacent⟩)
  obtain ⟨one,hOne⟩ := factor_local_response (fun h : H => currentView .one h.val)
    (fun h : H => leaderCheckpoint P d h.val) (coherent .one)
  obtain ⟨two,hTwo⟩ := factor_local_response (fun h : H => currentView .two h.val)
    (fun h : H => leaderCheckpoint P d h.val) (coherent .two)
  exact ⟨⟨one,two⟩,fun h live => ⟨hOne ⟨h,live⟩,hTwo ⟨h,live⟩⟩⟩

theorem leaderCheckpoint_after_reception {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h u : EnvHistory I₁ I₂) (p : Proc)
    (delay : List.length u = d) (received : silentAge (currentView p h) = 0)
    (leader : componentLeader P d (History.graphSequence (h++u)) = p) :
    leaderCheckpoint P d (h++u) = true := by
  unfold leaderCheckpoint
  rw [leader,← delay,lagView_suffix,received]
  rfl

/-- Under holes, both processes recognize the same delayed checkpoints,
and every checkpoint after the initial delay has uniformly bounded input
uncertainty. The bound is independent of the time of the checkpoint. -/
theorem holes_agreed_leader_checkpoints {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∃ test : StrategyPair I₁ I₂ Bool Bool,
      ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
        (test.one (currentView .one h) = leaderCheckpoint (LivePrefix A) d h ∧
          test.two (currentView .two h) = leaderCheckpoint (LivePrefix A) d h) ∧
        (d ≤ List.length h → leaderCheckpoint (LivePrefix A) d h = true →
          Finite (InputHistoryComponent (LivePrefix A) h) ∧
            Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ B) := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bound⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  obtain ⟨test,localTest⟩ := leaderCheckpoint_local (I₁:=I₁) (I₂:=I₂) (LivePrefix A) d recent
  refine ⟨d,K * (Nat.card (Fin d → Option (PSum I₁ I₂)))^2,test,?_⟩
  intro h live
  refine ⟨localTest h live,?_⟩
  intro within checkpoint
  have zero : silentAge (lagView d (currentView
      (componentLeader (LivePrefix A) d (History.graphSequence h)) h)) = 0 :=
    of_decide_eq_true checkpoint
  have result := finite_leader_checkpoint (LivePrefix A) ⟨K,bound⟩ d h _ live
    (componentLeader_correct _ _ _ (recent _ live)) within zero
  exact ⟨result.1,result.2.trans (Nat.mul_le_mul_right _ (bound _ live).2)⟩

end Characterisation
