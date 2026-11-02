/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingTransitionCompiler
import DistributedSynthesis.Formalizations.Lemma.LemFinitePolicyAllowedTargetBlockMonitor

/-! Use the existing sticky target guard with the computed closing-move
checker. The trusted source interface is fixed here; a global game still has
to link each invocation to its actual source state and select complete child
components. -/
namespace Characterisation
open DistributedSynthesis

section Check
variable {H S I₁ I₂ O₁ O₂ Q : Type}
variable [Fintype H] [Fintype S] [Fintype I₁] [Fintype I₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (shape : InputShape H)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable {D n : Nat} (bound : n ≤ D)
variable (Allowed : InputShape S × (S → Q) → Prop) [DecidablePred Allowed]

def ValidClosingMove (move : ClosingMove H S I₁ I₂ O₁ O₂ Q D n) : Prop :=
  checkClosingMove shape step initial move.1 bound move.2.1 move.2.2 Allowed = true

instance validClosingMove_decidable :
    DecidablePred (ValidClosingMove shape step initial bound Allowed) := by
  intro move
  unfold ValidClosingMove
  infer_instance

/-- The existing parity-visible guard rejects an incorrect closing target
at any time, even on an otherwise winning infinite one-way play. Conversely,
valid moves leave exactly the original physical parity obligation. -/
theorem closingMoveGuard_wins_iff {RIn SIn ROut SOut Index : Type} [Fintype Index]
    (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index (ClosingMove H S I₁ I₂ O₁ O₂ Q D n)) SOut) :
    (M.indexedAllowedTargetGuard (ValidClosingMove shape step initial bound Allowed)).WinsPlay play ↔
      M.WinsPlay (indexedTargetPhysicalPlay play) ∧
      ∀ t i, ValidClosingMove shape step initial bound Allowed ((play t).2.1.target i) := by
  constructor
  · intro wins
    exact ⟨M.indexedAllowedTargetGuard_base_wins_of_wins _ play wins,
      M.indexedAllowedTargetGuard_target_allowed_of_wins _ play wins⟩
  · rintro ⟨physical,valid⟩
    exact M.indexedAllowedTargetGuard_wins_of_base_wins_of_allowed _ play physical valid

/-- Receiver-output certificates can now enter the existing narrowing
construction unchanged. The controller is finite and branches only on the
leader inputs; every emitted closing certificate passes the concrete check. -/
theorem closingMoveGuard_finite_controller {RIn SIn ROut SOut Index : Type}
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [Fintype Index]
    [Fintype O₁] [Fintype O₂] [Fintype Q] [DecidableEq H] [DecidableEq S]
    [DecidableEq RIn] [DecidableEq SIn]
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Inhabited (ClosingMove H S I₁ I₂ O₁ O₂ Q D n)]
    (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
    (receiver : ReceiverBlockStrategy RIn SIn
      (IndexedTargetReceiverOutput ROut Index (ClosingMove H S I₁ I₂ O₁ O₂ Q D n)))
    (sender : SenderBlockStrategy SIn SOut)
    (physical : ∀ env, M.WinsPlay (indexedTargetPhysicalPlay (pairPlay receiver sender env)))
    (valid : ∀ env t i, ValidClosingMove shape step initial bound Allowed
      ((pairPlay receiver sender env t).2.1.target i)) :
    ∃ controller : TransitionRationalTree.{0,0,0} SIn
      (NarrowedBlockLabel RIn SIn
        (IndexedTargetReceiverOutput ROut Index (ClosingMove H S I₁ I₂ O₁ O₂ Q D n)) SOut
        (M.indexedAllowedTargetGuard (ValidClosingMove shape step initial bound Allowed)).State),
      NarrowedAllThreadsWin
        (M.indexedAllowedTargetGuard (ValidClosingMove shape step initial bound Allowed))
        controller.labeledTree := by
  apply M.exists_indexedAllowedTarget_controller_of_realizable (Index:=Index)
    (ValidClosingMove shape step initial bound Allowed)
  exact ⟨receiver,sender,fun env =>
    (closingMoveGuard_wins_iff shape step initial bound Allowed M _).mpr
      ⟨physical env,valid env⟩⟩

end Check
end Characterisation
