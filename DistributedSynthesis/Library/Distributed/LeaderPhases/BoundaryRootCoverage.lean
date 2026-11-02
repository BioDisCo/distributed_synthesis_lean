/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryPhaseWord

/-! Carry the full finite root family from the preceding agreed boundary.
After the common one-way word, its bounded closing layer covers the entire
next-boundary component, even though it need not cover the source component
at the intermediate closing cut. -/
namespace Characterisation
open DistributedSynthesis

def boundaryPhaseSources {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (a : Nat) : InputHistoryComponent P (h.take a) → EnvHistory I₁ I₂ :=
  fun s => s.val ++ boundaryPhaseWord d h a

theorem boundaryPhaseSources_injective {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (a : Nat) : Function.Injective (boundaryPhaseSources P d h a) := by
  intro s t same
  apply Subtype.ext
  exact List.append_cancel_right same

theorem boundaryPhaseSources_depth {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
    (s : InputHistoryComponent P (h.take a)) :
    List.length (boundaryPhaseSources P d h a s) = phaseClosingCut d h a := by
  have bounds := phaseClosingCut_bounds P d h a phase
  have rootLength : List.length s.val = a := by
    have len := inputConnected_length P s.property
    simpa only [List.length_take,min_eq_left (Nat.le_of_lt phase.start_lt)] using len.symm
  simp only [boundaryPhaseSources,List.length_append,rootLength,boundaryPhaseWord,
    List.length_drop,List.length_take,min_eq_left (Nat.le_of_lt bounds.2.1)]
  omega

/-- Every target ancestor at the closing cut is represented by an original
boundary root followed by the same common one-way word. -/
theorem boundaryRoots_cover_ancestors {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a) :
    ∃ s : InputHistoryComponent P (h.take a),
      boundaryPhaseSources P d h a s = k.take (phaseClosingCut d h a) := by
  let s : InputHistoryComponent P (h.take a) := ⟨k.take a,inputConnected_take P closed conn a⟩
  have common := boundaryPhaseWord_component P closed d recent live conn a phase
  have len := inputConnected_length P conn
  have cut : phaseClosingCut d h a = phaseClosingCut d k a := by simp only [phaseClosingCut,len]
  have sameWord : boundaryPhaseWord d h a = (k.take (phaseClosingCut d h a)).drop a := by
    rw [common]
    simp only [boundaryPhaseWord,cut]
  have split := List.take_append_drop a (k.take (phaseClosingCut d h a))
  rw [List.take_take,min_eq_left (phaseClosingCut_bounds P d h a phase).1] at split
  exact ⟨s,by change k.take a ++ boundaryPhaseWord d h a = _; rw [sameWord]; exact split⟩

/-- The original boundary roots suffice for exact target coverage after
at most d+1 closing rounds. The family does not depend on a retrospective
choice of an input fiber. -/
theorem boundaryRoots_closing_coverage {I₁ I₂ : Type}
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    {h k : EnvHistory I₁ I₂} (live : P (History.graphSequence h))
    (conn : InputConnected P h k) (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a) :
    ∃ s : ClosingLayer (InputHistoryComponent P (h.take a)) I₁ I₂
        (List.length h-phaseClosingCut d h a),
      closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) s = k := by
  obtain ⟨s,old⟩ := boundaryRoots_cover_ancestors P closed d recent live conn a phase
  have len := inputConnected_length P conn
  obtain ⟨t,eq⟩ := closingLayer_contains_append (boundaryPhaseSources P d h a) s
    (List.length h-phaseClosingCut d h a) (k.drop (phaseClosingCut d h a))
    (by simp only [History.length,List.length_drop,len])
  exact ⟨t,by simpa only [old,List.take_append_drop] using eq⟩

/-- Uniform bounds for both boundary components, together with coverage
using the roots of the previous boundary. Private inputs remain arbitrary. -/
theorem holes_boundary_root_closing_coverage {I₁ I₂ : Type} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∀ (h : EnvHistory I₁ I₂), LivePrefix A (History.graphSequence h) →
      ∀ a, ConsecutiveLeaderBoundaries (LivePrefix A) d h a →
      Finite (InputHistoryComponent (LivePrefix A) (h.take a)) ∧
      Nat.card (InputHistoryComponent (LivePrefix A) (h.take a)) ≤ B ∧
      Finite (InputHistoryComponent (LivePrefix A) h) ∧
      Nat.card (InputHistoryComponent (LivePrefix A) h) ≤ B ∧
      0 < List.length h-phaseClosingCut d h a ∧
      List.length h-phaseClosingCut d h a ≤ d+1 ∧
      ∀ k, InputConnected (LivePrefix A) h k →
        ∃ s : ClosingLayer (InputHistoryComponent (LivePrefix A) (h.take a)) I₁ I₂
            (List.length h-phaseClosingCut d h a),
          closingLayerHistory (boundaryPhaseSources (LivePrefix A) d h a)
            (List.length h-phaseClosingCut d h a) s = k := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨B,bound⟩ := bounded_leader_boundaries (I₁:=I₁) (I₂:=I₂) (LivePrefix A)
    (livePrefix_closed A) ((omegaRegular_holes_iff_bounded_components A regular).mp holes) d recent
  refine ⟨d,B,fun h live a phase => ?_⟩
  have start := bound (h.take a) (live_history_take _ (livePrefix_closed A) h live a) phase.start_boundary
  have target := bound h live phase.end_boundary
  have bounds := phaseClosingCut_bounds (LivePrefix A) d h a phase
  exact ⟨start.1,start.2,target.1,target.2,by omega,bounds.2.2,
    fun k conn => boundaryRoots_closing_coverage _ (livePrefix_closed A) d recent live conn a phase⟩

/-- A rightward common word is precisely the input-tree word consumed by
the existing rolling leader tables. -/
theorem outgoing_history_as_right {I₁ I₂ : Type} (h : EnvHistory I₁ I₂)
    (outgoing : ∀ r ∈ h, r.graph = .right) :
    rightInputHistory (h.map (fun r => (r.inputTwo,r.inputOne))) = h := by
  induction h with
  | nil => rfl
  | cons r h ih =>
    have graph := outgoing r (by simp)
    have tail : ∀ s ∈ h, s.graph = .right := fun s hs => outgoing s (by simp [hs])
    rcases r with ⟨x,y,g,⟨⟩,⟨⟩⟩
    change g = .right at graph
    subst g
    simpa only [List.map_cons,rightInputHistory] using congrArg
      (List.cons (⟨x,y,.right,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) (ih tail)

theorem boundaryPhaseSources_as_rolling {I₁ I₂ : Type}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (phase : ConsecutiveLeaderBoundaries P d h a)
    (leader : componentLeader P d (History.graphSequence (h.take a)) = .one) :
    boundaryPhaseSources P d h a =
      rollingSourceHistory (fun s : InputHistoryComponent P (h.take a) => s.val)
        ((boundaryPhaseWord d h a).map (fun r => (r.inputTwo,r.inputOne))) := by
  have outgoing : ∀ r ∈ boundaryPhaseWord d h a, r.graph = .right := by
    intro r member
    have graph := boundaryPhaseWord_outgoing P d h a phase r member
    simpa only [leader,leaderOutgoingGraph] using graph
  funext s
  simp only [boundaryPhaseSources,rollingSourceHistory,outgoing_history_as_right _ outgoing]

end Characterisation
