/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FinitePhaseOffers
import DistributedSynthesis.Library.Distributed.LeaderPhases.FinitePhaseReadback

/-! Extract exact joint offers from the original narrowed controller. The
sender control follows only sender inputs; the receiver's monitor state
follows the full input word. Both are needed for exact reachability. -/
namespace Characterisation
open DistributedSynthesis

section Narrowed
variable {RIn SIn ROut SOut Outcome : Type}
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
variable (T : TransitionRationalTree.{0,0,0} SIn
  (NarrowedBlockLabel RIn SIn ROut SOut M.State))

def narrowedPhaseStep (state : T.Control × M.State) (input : RIn × SIn) :
    T.Control × M.State :=
  (T.step state.1 input.2,
    M.step state.2 (narrowedRecord M (T.labelOf state.1) state.2 input))

/-- The finite runtime represents the actual node, including its full
receiver history through the supplied monitor. -/
theorem narrowedPhaseRun_exact (node : List (RIn × SIn)) :
    node.foldl (narrowedPhaseStep M T) (T.initial, M.initial) =
      (T.controlAt (senderWord node), narrowedControl M T.labeledTree node) := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node input ih =>
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [ih, senderWord_append, narrowedControl_append]
    simp only [narrowedPhaseStep, TransitionRationalTree.controlAt,
      TransitionRationalTree.labeledTree, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

variable [Fintype RIn] [Fintype SIn] [DecidableEq Outcome]

/-- The collector sees one current monitor state and one complete realized
round, so all entries of an outcome have a common witness. -/
def narrowedPhaseOffers
    (collect : M.State → RealizedBlockRound RIn SIn ROut SOut → Finset Outcome) :
    Finset Outcome :=
  finitePhaseOffers (narrowedPhaseStep M T) (T.initial, M.initial)
    (fun state input => collect state.2
      (narrowedRecord M (T.labelOf state.1) state.2 input))

theorem mem_narrowedPhaseOffers_iff
    (collect : M.State → RealizedBlockRound RIn SIn ROut SOut → Finset Outcome)
    (outcome : Outcome) :
    outcome ∈ narrowedPhaseOffers M T collect ↔
      ∃ node : List (RIn × SIn), ∃ input,
        outcome ∈ collect (narrowedControl M T.labeledTree node)
          (narrowedRecord M (T.labeledTree (senderWord node))
            (narrowedControl M T.labeledTree node) input) := by
  simp only [narrowedPhaseOffers, mem_finitePhaseOffers_iff, narrowedPhaseRun_exact]
  rfl

/-- Readback does not change which current receiver outputs are offered. -/
theorem narrowedPhaseOffers_receiver_iff
    (collect : M.State → (RIn × SIn) → ROut → Finset Outcome)
    (outcome : Outcome) :
    outcome ∈ narrowedPhaseOffers M T (fun q letter => collect q letter.1 letter.2.1) ↔
      ∃ node : List (RIn × SIn), ∃ input,
        outcome ∈ collect (narrowedControl M T.labeledTree node) input
          (receiverOfTree (narrowedInducedTree M T.labeledTree) node input) := by
  rw [mem_narrowedPhaseOffers_iff]
  rfl

end Narrowed

section Coherent
variable {H I₁ I₂ O₁ O₂ Outcome : Type} {D : Nat}
variable [Fintype H] [DecidableEq H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [DecidableEq Outcome]
variable (M : BlockRecordMonitor.{0,0,0,0,0} I₂ I₁ (H → O₂) O₁)
variable (shape : InputShape H)

/-- Specialization to the already-proved finite leader tables. Any
computational content here is relative to their finite representation;
selecting a winning table remains a separate obligation. -/
noncomputable def coherentMoveOffers (move : CoherentLeaderPhaseMove (D:=D) M shape)
    (collect : (coherentRollingMonitor M shape move.1).State → (I₂ × I₁) →
      RollingReceiverOutput H I₁ I₂ O₁ O₂ D → Finset Outcome) : Finset Outcome :=
  narrowedPhaseOffers (coherentRollingMonitor M shape move.1)
    (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
      move.2.toTransitionRationalTree ())
    (fun q letter => collect q letter.1 letter.2.1)

/-- The whole rolling bank in an offer is emitted by the actual readback
on one word. The equivalence also forbids dropping any emitted outcome. -/
theorem coherentMoveOffers_exact (move : CoherentLeaderPhaseMove (D:=D) M shape)
    (collect : (coherentRollingMonitor M shape move.1).State → (I₂ × I₁) →
      RollingReceiverOutput H I₁ I₂ O₁ O₂ D → Finset Outcome)
    (outcome : Outcome) :
    outcome ∈ coherentMoveOffers M shape move collect ↔
      ∃ node : List (I₂ × I₁), ∃ input,
        outcome ∈ collect
          (narrowedControl (coherentRollingMonitor M shape move.1)
            (finiteRootMemberController (fun _ : Unit => coherentRollingMonitor M shape move.1)
              move.2.toTransitionRationalTree ()).labeledTree node)
          input (coherentMoveReceiver M shape move node input) := by
  exact narrowedPhaseOffers_receiver_iff _ _ collect outcome

end Coherent
end Characterisation
