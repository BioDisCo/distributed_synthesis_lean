/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryLabelTransport

/-! A truthful boundary-to-boundary certificate for one actual strategy:
fixed roots at the preceding boundary, complete next-component coverage,
and monitor labels obtained from the actual full-history run. The global
choice of compatible phase strategies remains a separate game obligation. -/
namespace Characterisation
open DistributedSynthesis

/-- The boundary transition is bound to the same strategy at every closing
position and to its full-history monitor state at every retained history.
The allowed-target predicate is unrestricted here; winning target selection
is not hidden in the certificate's existence statement. -/
theorem strategy_boundary_transition {I₁ I₂ O₁ O₂ Q : Type}
    [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
    [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (closed : PrefixClosed P) (d : Nat)
    (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
    (h : EnvHistory I₁ I₂) (liveH : P (History.graphSequence h))
    (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
    [Fintype (InputHistoryComponent P (h.take a))]
    [DecidableEq (InputHistoryComponent P (h.take a))]
    (shape : InputShape (InputHistoryComponent P (h.take a)))
    (rep : RepresentsInputShape (boundaryPhaseSources P d h a) shape)
    (live : BoundaryPhaseLayer P d h a → Bool)
    (liveExact : ∀ s, live s = true ↔ P (History.graphSequence
      (closingLayerHistory (boundaryPhaseSources P d h a) (List.length h-phaseClosingCut d h a) s)))
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (q₀ : Q)
    (B : Nat) (small : Nat.card (InputHistoryComponent P h) ≤ B) :
    let past := boundaryPhaseSources P d h a
    let initial := fun s => strategyHistoryLabel σ step q₀ (past s)
    let out := closingPolicyOfBank (fun s => closingPlanOfStrategy σ (past s) (d+1))
    ∃ root : BoundaryPhaseLayer P d h a,
      closingLayerHistory past (List.length h-phaseClosingCut d h a) root = h ∧
      ∃ move : ClosingBoundaryCertificate (InputHistoryComponent P (h.take a)) I₁ I₂ O₁ O₂ Q
          B (d+1) (List.length h-phaseClosingCut d h a),
        move.2.1 = out ∧
        checkClosingBoundaryCertificate shape step initial (phaseClosingCut_bounds P d h a phase).2.2
          live root (fun _ => True) move = true ∧
        Function.Injective (closingLayerHistory past (List.length h-phaseClosingCut d h a) ∘ move.2.2.1) ∧
        (∀ k, InputConnected P h k ↔ ∃ s,
          closingLayerHistory past (List.length h-phaseClosingCut d h a) (move.2.2.1 s) = k) ∧
        ∀ s, move.2.2.2.2 s = strategyHistoryLabel σ step q₀
          (closingLayerHistory past (List.length h-phaseClosingCut d h a) (move.2.2.1 s)) := by
  dsimp only
  let past := boundaryPhaseSources P d h a
  let initial := fun s => strategyHistoryLabel σ step q₀ (past s)
  let out := closingPolicyOfBank (fun s => closingPlanOfStrategy σ (past s) (d+1))
  have coherent : ClosingPolicyCoherent shape out :=
    closingBankOfStrategy_coherent σ past shape rep
  obtain ⟨root,rootEq,move,policy,valid,unique,complete⟩ :=
    boundaryRoots_checked_certificate P closed d recent h liveH a phase shape rep live liveExact
      step initial out coherent B small
  have implements : ∀ t s, move.2.1 t s =
      (σ.one (currentView .one (closingLayerHistory past (t.val+1) s)),
       σ.two (currentView .two (closingLayerHistory past (t.val+1) s))) := by
    intro t s
    rw [policy]
    exact closingPolicyOfBank_implements σ past _ (fun _ => rfl) t s
  have labels := checkedClosingCertificate_strategy_labels σ past shape step q₀ initial (fun _ => rfl)
    (phaseClosingCut_bounds P d h a phase).2.2 live root (fun _ => True) move valid implements
  exact ⟨root,rootEq,move,policy,valid,unique,complete,labels⟩

end Characterisation
