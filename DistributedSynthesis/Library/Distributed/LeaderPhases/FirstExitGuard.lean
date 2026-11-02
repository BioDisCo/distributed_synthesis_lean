/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FirstExitCertificates

/-! Finite bundles carry one coherent phase policy and a proposed successor
certificate at each bounded first exit. Non-exits impose no successor check.
The existing sticky guard and narrowing construction are reused unchanged. -/
namespace Characterisation
open DistributedSynthesis

abbrev FirstExitBundle (H I₁ I₂ O₁ O₂ Q : Type) (B D : Nat) :=
  ClosingPolicy H I₁ I₂ O₁ O₂ D ×
    ((n : Fin D) → ClosingLayer H I₁ I₂ (n.val+1) →
      ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1))

instance firstExitBundle_fintype {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (B D : Nat) :
    Fintype (FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) := by
  unfold FirstExitBundle ClosingPolicy
  infer_instance

section Check
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (shape : InputShape H)
variable (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (Allowed : SwitchInterface Q B → Prop) [DecidablePred Allowed]

/-- Boundary and live flags are source data, not chosen by the certificate.
A demanded successor must use exactly the bundle's shared output policy. -/
def checkFirstExitBundle (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) : Bool :=
  decide (ClosingPolicyCoherent shape bundle.1 ∧ ∀ (n : Fin D) s,
    closingFlagAt live (n.val+1) s = true →
    closingFirstExit (closingFlagAt boundary) (n.val+1) s = true →
      (bundle.2 n s).2.1 = bundle.1 ∧
      checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
        (closingFlagAt live (n.val+1)) s Allowed (bundle.2 n s) = true)

theorem checkFirstExitBundle_correct (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) :
    checkFirstExitBundle shape boundary live step initial Allowed bundle = true ↔
      ClosingPolicyCoherent shape bundle.1 ∧ ∀ (n : Fin D) s,
        closingFlagAt live (n.val+1) s = true →
        closingFirstExit (closingFlagAt boundary) (n.val+1) s = true →
          (bundle.2 n s).2.1 = bundle.1 ∧
          checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
            (closingFlagAt live (n.val+1)) s Allowed (bundle.2 n s) = true := by
  simp only [checkFirstExitBundle,decide_eq_true_eq]

/-- Entries for non-exits do not constrain successor selection. This does
not remove the current boundary output or the full policy coherence check. -/
theorem checkFirstExitBundle_nonexit_irrelevant
    (bundle other : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)
    (policy : bundle.1 = other.1)
    (same : ∀ (n : Fin D) s, closingFlagAt live (n.val+1) s = true →
      closingFirstExit (closingFlagAt boundary) (n.val+1) s = true → bundle.2 n s = other.2 n s) :
    checkFirstExitBundle shape boundary live step initial Allowed bundle =
      checkFirstExitBundle shape boundary live step initial Allowed other := by
  apply Bool.eq_iff_iff.mpr
  rw [checkFirstExitBundle_correct,checkFirstExitBundle_correct]
  constructor
  · rintro ⟨coherent,valid⟩
    refine ⟨by simpa only [← policy] using coherent,fun n s alive exit => ?_⟩
    have result := valid n s alive exit
    refine ⟨(congrArg (fun move => move.2.1) (same n s alive exit)).symm.trans (result.1.trans policy),?_⟩
    simpa only [same n s alive exit] using result.2
  · rintro ⟨coherent,valid⟩
    refine ⟨by simpa only [policy] using coherent,fun n s alive exit => ?_⟩
    have result := valid n s alive exit
    refine ⟨(congrArg (fun move => move.2.1) (same n s alive exit)).trans (result.1.trans policy.symm),?_⟩
    simpa only [← same n s alive exit] using result.2

/-- Tie the certificate bundle to the policy carried by the phase table.
The guard cannot replace that policy by an unrelated coherent witness. -/
def checkFirstExitBundleFor (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) : Bool :=
  decide (bundle.1 = expected) && checkFirstExitBundle shape boundary live step initial Allowed bundle

theorem checkFirstExitBundleFor_correct (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D) :
    checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true ↔
      bundle.1 = expected ∧ checkFirstExitBundle shape boundary live step initial Allowed bundle = true := by
  simp only [checkFirstExitBundleFor,Bool.and_eq_true,decide_eq_true_eq]

variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)

/-- Reuse the existing parity-visible sticky guard. It enforces all bounded
first-exit certificates emitted along every private-input thread. -/
theorem firstExitGuard_wins_iff {RIn SIn ROut SOut Index : Type} [Fintype Index]
    (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index (FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)) SOut) :
    (M.indexedAllowedTargetGuard
      (fun bundle => checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true)).WinsPlay play ↔
      M.WinsPlay (indexedTargetPhysicalPlay play) ∧
      ∀ t i, checkFirstExitBundleFor shape boundary live step initial Allowed expected ((play t).2.1.target i) = true := by
  constructor
  · intro wins
    exact ⟨M.indexedAllowedTargetGuard_base_wins_of_wins _ play wins,
      M.indexedAllowedTargetGuard_target_allowed_of_wins _ play wins⟩
  · rintro ⟨physical,valid⟩
    exact M.indexedAllowedTargetGuard_wins_of_base_wins_of_allowed _ play physical valid

/-- A phase realizable with these finite certificates admits a finite
leader controller by the same narrowing theorem as the earlier guard. -/
theorem firstExitGuard_finite_controller {RIn SIn ROut SOut Index : Type}
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [Fintype Index]
    [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq RIn] [DecidableEq SIn]
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Inhabited (FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)]
    (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
    (receiver : ReceiverBlockStrategy RIn SIn
      (IndexedTargetReceiverOutput ROut Index (FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)))
    (sender : SenderBlockStrategy SIn SOut)
    (physical : ∀ env, M.WinsPlay (indexedTargetPhysicalPlay (pairPlay receiver sender env)))
    (valid : ∀ env t i,
      checkFirstExitBundleFor shape boundary live step initial Allowed expected ((pairPlay receiver sender env t).2.1.target i) = true) :
    ∃ controller : TransitionRationalTree.{0,0,0} SIn
      (NarrowedBlockLabel RIn SIn
        (IndexedTargetReceiverOutput ROut Index (FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)) SOut
        (M.indexedAllowedTargetGuard
          (fun bundle => checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true)).State),
      NarrowedAllThreadsWin
        (M.indexedAllowedTargetGuard
          (fun bundle => checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true))
        controller.labeledTree := by
  apply M.exists_indexedAllowedTarget_controller_of_realizable (Index:=Index)
    (fun bundle => checkFirstExitBundleFor shape boundary live step initial Allowed expected bundle = true)
  exact ⟨receiver,sender,fun env =>
    (firstExitGuard_wins_iff shape boundary live step initial Allowed expected M _).mpr ⟨physical env,valid env⟩⟩

end Check
end Characterisation
