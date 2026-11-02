/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingBoundaryCertificates

/-! At an agreed boundary, the ancestors before the last d+1 rounds lie in
one uniformly bounded family with fixed input words. That family need not be
the full input component at the earlier depth. Its coverage is relative to
the later boundary; no advance knowledge of the boundary is asserted. -/
namespace Characterisation
open DistributedSynthesis

theorem inputConnected_take {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P)
    {h k : EnvHistory I₁ I₂} (conn : InputConnected P h k) (n : Nat) :
    InputConnected P (h.take n) (k.take n) := by
  have viewTake : ∀ p (h : EnvHistory I₁ I₂),
      lagView (h.length-n) (currentView p h) = currentView p (h.take n) := by
    intro p h
    by_cases small : n ≤ h.length
    · have smallList : n ≤ List.length h := small
      simpa only [History.length, Nat.sub_sub_self smallList] using
        lagView_take p h (h.length-n) (Nat.sub_le _ _)
    · have large : h.length ≤ n := by omega
      simp [Nat.sub_eq_zero_of_le large,List.take_of_length_le large,lagView]
  apply Relation.ReflTransGen.lift (List.take n) _ conn
  intro a b edge
  have liveTake : ∀ (h : EnvHistory I₁ I₂), P (History.graphSequence h) →
      P (History.graphSequence (h.take n)) := by
    intro h live
    apply closed _ (History.graphSequence (h.drop n))
    simpa [History.graphSequence,← List.map_append] using live
  refine ⟨liveTake a edge.1,liveTake b edge.2.1,?_⟩
  have len : a.length = b.length := by
    have eq := adjacent_same_depth (inputAdjacent_projects edge.2.2)
    simpa [History.graphSequence] using eq
  rcases edge.2.2 with one | two
  · left
    rw [← viewTake .one a,← viewTake .one b]
    simp only [History.length,len,one]
  · right
    rw [← viewTake .two a,← viewTake .two b]
    simp only [History.length,len,two]

/-- Both types of agreed boundary have common private-input prefixes
through depth max(length h-(d+1),0), including short initial histories. -/
theorem leaderBoundary_common_inputs {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (boundary : leaderBoundary P d h = true)
    (k : EnvHistory I₁ I₂) (conn : InputConnected P h k) :
    olderInputPrefix .one (d+1) h = olderInputPrefix .one (d+1) k ∧
      olderInputPrefix .two (d+1) h = olderInputPrefix .two (d+1) k := by
  have len : h.length = k.length := by
    have eq := connected_same_depth P (inputConnected_projects P conn)
    simpa [History.graphSequence] using eq
  by_cases within : d ≤ h.length
  · have alternatives : leaderCheckpoint P d h = true ∨
        componentLeader P d (History.graphSequence h.dropLast) ≠
          componentLeader P d (History.graphSequence h) := by
      simpa [leaderBoundary] using boundary
    have current := componentLeader_correct P d _ (recent _ live)
    rcases alternatives with checkpoint | changed
    · have common := leader_checkpoint_prefixes P d h _ current within
        (of_decide_eq_true checkpoint) k conn
      have shorten : ∀ p, olderInputPrefix p d h = olderInputPrefix p d k →
          olderInputPrefix p (d+1) h = olderInputPrefix p (d+1) k := by
        intro p eq
        have cut := congrArg (List.take (h.length-(d+1))) eq
        unfold olderInputPrefix at cut ⊢
        rw [← len] at cut ⊢
        simpa only [List.take_take,min_eq_left (by omega : h.length-(d+1) ≤ h.length-d)] using cut
      exact ⟨shorten .one common.1,shorten .two common.2⟩
    · have parentLive : P (History.graphSequence h.dropLast) := by
        rw [graphSequence_dropLast]
        exact live_parent P closed live
      exact both_input_prefixes_at_switch P closed d _ _ changed
        (componentLeader_correct P d _ (recent _ parentLive)) current conn
  · have zeroH : h.length-(d+1) = 0 := by omega
    have zeroK : k.length-(d+1) = 0 := by omega
    simp [olderInputPrefix,zeroH,zeroK]

/-- The histories in a component that use one fixed pair of complete input
words. The full component can contain arbitrarily many other input words. -/
def InputFiber {I₁ I₂ : Type*} (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :=
  {k : EnvHistory I₁ I₂ // InputConnected P h k ∧
    inputWord .one h = inputWord .one k ∧ inputWord .two h = inputWord .two k}

theorem inputFiber_bounded {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h)) :
    Finite (InputFiber P h) ∧ Nat.card (InputFiber P h) ≤
      Nat.card (HistoryComponent P (History.graphSequence h)) := by
  have result := finite_family_of_common_prefixes P bounded 0 h live
    (fun k => InputConnected P h k ∧
      inputWord .one h = inputWord .one k ∧ inputWord .two h = inputWord .two k)
    (fun _ hk => hk.1) (fun k hk => by
      simpa [olderInputPrefix,inputWord,History.length,← List.map_take] using hk.2)
  simpa [InputFiber] using result

/-- Every sufficiently old ancestor of the target component belongs to one
fixed-input family. This supplies coverage of the target without assuming
that the family covers the entire source component. -/
theorem leaderBoundary_ancestors_in_fiber {I₁ I₂ : Type*}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (boundary : leaderBoundary P d h = true)
    (c : Nat) (early : c ≤ h.length-(d+1))
    (k : EnvHistory I₁ I₂) (conn : InputConnected P h k) :
    ∃ s : InputFiber P (h.take c), s.val = k.take c := by
  have common := leaderBoundary_common_inputs P closed d recent h live boundary k conn
  have len : h.length = k.length := by
    have eq := connected_same_depth P (inputConnected_projects P conn)
    simpa [History.graphSequence] using eq
  have words : ∀ p, olderInputPrefix p (d+1) h = olderInputPrefix p (d+1) k →
      inputWord p (h.take c) = inputWord p (k.take c) := by
    intro p eq
    have cut := congrArg (List.take c) eq
    unfold olderInputPrefix at cut
    rw [← len] at cut
    simpa only [List.take_take,min_eq_left early,inputWord,List.map_take] using cut
  exact ⟨⟨k.take c,inputConnected_take P closed conn c,
    words .one common.1,words .two common.2⟩,rfl⟩

theorem closingLayer_contains_append {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (s : H) (n : Nat)
    (u : EnvHistory I₁ I₂) (length : u.length = n) :
    ∃ t : ClosingLayer H I₁ I₂ n, closingLayerHistory past n t = past s ++ u := by
  induction n generalizing u with
  | zero =>
    have empty : u = [] := List.length_eq_zero_iff.mp length
    exact ⟨s,by simp [empty,closingLayerHistory]⟩
  | succ n ih =>
    have nonempty : u ≠ [] := by intro empty; simp [empty,History.length] at length
    obtain ⟨v,r,rfl⟩ := (List.eq_nil_or_concat' u).resolve_left nonempty
    have len : v.length = n := by simpa [History.length] using length
    obtain ⟨t,eq⟩ := ih v len
    rcases r with ⟨x,y,g,⟨⟩,⟨⟩⟩
    exact ⟨(t,x,y,g),by simp [closingLayerHistory,scenarioHistory,eq,List.append_assoc]⟩

/-- Uniformly bounded source width for the last d+1 rounds of a boundary.
The cutoff is retrospective. The theorem supplies the complete target's
coverage, not a locally observable instruction to start closing at that time. -/
theorem leaderBoundary_fiber_closing_coverage {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
    (boundary : leaderBoundary P d h = true)
    (k : EnvHistory I₁ I₂) (conn : InputConnected P h k) :
    let c := h.length-(d+1)
    ∃ t : ClosingLayer (InputFiber P (h.take c)) I₁ I₂ (h.length-c),
      closingLayerHistory (fun s => s.val) (h.length-c) t = k := by
  dsimp only
  let c := h.length-(d+1)
  obtain ⟨s,eq⟩ := leaderBoundary_ancestors_in_fiber P closed d recent h live boundary c le_rfl k conn
  have len : h.length = k.length := by
    have eq := connected_same_depth P (inputConnected_projects P conn)
    simpa [History.graphSequence] using eq
  change List.length h = List.length k at len
  obtain ⟨t,ht⟩ := closingLayer_contains_append (fun s : InputFiber P (h.take c) => s.val)
    s (h.length-c) (k.drop c) (by simp [len,History.length])
  exact ⟨t,by simpa [eq] using ht⟩

/-- The number of source slots is bounded by the graph-component bound,
independently of the duration of the preceding phase. The remaining closing
length is at most d+1. Arbitrary finite private inputs are retained. -/
theorem holes_bounded_boundary_fiber_sources {I₁ I₂ : Type}
    [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d K, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      leaderBoundary (LivePrefix A) d h = true →
      let c := h.length-(d+1)
      h.length-c ≤ d+1 ∧
      Finite (InputFiber (LivePrefix A) (h.take c)) ∧
      Nat.card (InputFiber (LivePrefix A) (h.take c)) ≤ K ∧
      ∀ k, InputConnected (LivePrefix A) h k →
        ∃ t : ClosingLayer (InputFiber (LivePrefix A) (h.take c)) I₁ I₂ (h.length-c),
          closingLayerHistory (fun s => s.val) (h.length-c) t = k := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bound⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  refine ⟨d,K,fun h live boundary => ?_⟩
  dsimp only
  let c := h.length-(d+1)
  have sourceLive : LivePrefix A (History.graphSequence (h.take c)) := by
    apply livePrefix_closed A _ (History.graphSequence (h.drop c))
    simpa [History.graphSequence,← List.map_append] using live
  have fiber := inputFiber_bounded (LivePrefix A) ⟨K,bound⟩ (h.take c) sourceLive
  refine ⟨by omega,fiber.1,fiber.2.trans (bound _ sourceLive).2,?_⟩
  exact fun k conn => leaderBoundary_fiber_closing_coverage (LivePrefix A)
    (livePrefix_closed A) d recent h live boundary k conn

end Characterisation
