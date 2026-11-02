/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryRootCoverage

/-! Feed the fixed boundary-root coverage theorem into the existing finite
closing checker. A passing enumeration represents the complete next agreed
boundary component; intermediate source components need not be fully covered. -/
namespace Characterisation
open DistributedSynthesis

abbrev BoundaryPhaseLayer {I₁ I₂ : Type} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (a : Nat) :=
  ClosingLayer (InputHistoryComponent P (h.take a)) I₁ I₂ (List.length h-phaseClosingCut d h a)

section Boundary
variable {I₁ I₂ O₁ O₂ Q : Type}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (h : EnvHistory I₁ I₂) (liveH : P (History.graphSequence h))
variable (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
variable [Fintype (InputHistoryComponent P (h.take a))]
variable [DecidableEq (InputHistoryComponent P (h.take a))]
variable (shape : InputShape (InputHistoryComponent P (h.take a)))
variable (rep : RepresentsInputShape (boundaryPhaseSources P d h a) shape)
variable (live : BoundaryPhaseLayer P d h a → Bool)
variable (liveExact : ∀ s, live s = true ↔ P (History.graphSequence
  (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) s)))

include closed recent liveH phase rep liveExact in
/-- The finite reachability mask selects exactly the next actual boundary
component, including all its private-input histories. -/
theorem boundaryRoots_component_mask_exact :
    ∃ root : BoundaryPhaseLayer P d h a,
      closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root = h ∧
      ∀ s, closingComponentMask (closingLayerShape shape (List.length h-phaseClosingCut d h a)) live root s = true ↔
        InputConnected P h (closingLayerHistory (boundaryPhaseSources P d h a)
          (List.length h-phaseClosingCut d h a) s) := by
  obtain ⟨root,rootEq⟩ := boundaryRoots_closing_coverage P closed d recent liveH
    (Relation.ReflTransGen.refl : InputConnected P h h) a phase
  have coverage : ∀ k, InputConnected P
      (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root) k →
      ∃ s : BoundaryPhaseLayer P d h a,
        closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) s = k := by
    intro k conn
    rw [rootEq] at conn
    exact boundaryRoots_closing_coverage P closed d recent liveH conn a phase
  refine ⟨root,rootEq,fun s => ?_⟩
  have exactMask := closingComponentMask_exact P
    (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a))
    (closingLayerShape shape (List.length h-phaseClosingCut d h a))
    (closingLayerShape_exact _ shape rep _) live liveExact root (by rwa [rootEq]) coverage s
  simpa only [rootEq] using exactMask

variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]

include closed recent liveH phase rep liveExact in
/-- Every coherent closing policy has a checked certificate for the complete
next boundary. The root family is the one fixed at the previous boundary.
Labels are replayed from the supplied source labels by the existing checker. -/
theorem boundaryRoots_checked_certificate
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (initial : InputHistoryComponent P (h.take a) → Q)
    (out : ClosingPolicy (InputHistoryComponent P (h.take a)) I₁ I₂ O₁ O₂ (d+1))
    (coherent : ClosingPolicyCoherent shape out)
    (B : Nat) (small : Nat.card (InputHistoryComponent P h) ≤ B) :
    ∃ root : BoundaryPhaseLayer P d h a,
      closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root = h ∧
      ∃ move : ClosingBoundaryCertificate (InputHistoryComponent P (h.take a)) I₁ I₂ O₁ O₂ Q
          B (d+1) (List.length h-phaseClosingCut d h a),
        move.2.1 = out ∧
        checkClosingBoundaryCertificate shape step initial (phaseClosingCut_bounds P d h a phase).2.2
          live root (fun _ => True) move = true ∧
        Function.Injective (closingLayerHistory (boundaryPhaseSources P d h a)
          (List.length h-phaseClosingCut d h a) ∘ move.2.2.1) ∧
        ∀ k, InputConnected P h k ↔ ∃ s,
          closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a)
            (move.2.2.1 s) = k := by
  obtain ⟨root,rootEq⟩ := boundaryRoots_closing_coverage P closed d recent liveH
    (Relation.ReflTransGen.refl : InputConnected P h h) a phase
  have coverage : ∀ k, InputConnected P
      (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root) k →
      ∃ s : BoundaryPhaseLayer P d h a,
        closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) s = k := by
    intro k conn
    rw [rootEq] at conn
    exact boundaryRoots_closing_coverage P closed d recent liveH conn a phase
  have rootLive : P (History.graphSequence
      (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root)) := by
    rwa [rootEq]
  have smallRoot : Nat.card (InputHistoryComponent P
      (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) root)) ≤ B := by
    rwa [rootEq]
  obtain ⟨move,policy,valid⟩ := exists_checked_closing_boundary_of_target_coverage P
    (boundaryPhaseSources P d h a) (boundaryPhaseSources_injective P d h a)
    shape rep (phaseClosingCut d h a) (boundaryPhaseSources_depth P d h a phase)
    step initial out coherent (phaseClosingCut_bounds P d h a phase).2.2
    live liveExact root rootLive coverage smallRoot
  have correct := (checkClosingBoundaryCertificate_correct_of_target_coverage P
    (boundaryPhaseSources P d h a) (boundaryPhaseSources_injective P d h a)
    shape rep (phaseClosingCut d h a) (boundaryPhaseSources_depth P d h a phase)
    step initial (phaseClosingCut_bounds P d h a phase).2.2 live liveExact root rootLive coverage
    (fun _ => True) move).mp valid
  refine ⟨root,rootEq,move,policy,valid,correct.2.1,?_⟩
  simpa only [rootEq] using correct.2.2

end Boundary
end Characterisation
