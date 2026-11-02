/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhase
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderGroupsCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedJointPhaseObjectiveCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabetCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedRoleExchangeCorrect

/-! The assembled phase compiler uses precisely the groups in the existing
numbered leader interface, with no extra observation or group certificate. -/
namespace Characterisation.EncodedLeaderPhase
open DistributedSynthesis

variable {Q : Type} {N B : Nat} (stateNumber : Q ≃ Fin N) (header : SwitchInterface Q B)

theorem headerGroups_one : headerGroups (EncodedLeaderAlphabet.headerEncode stateNumber header) true =
    EncodedLeaderGroups.dataEncode (Equiv.refl (Fin header.1.val)) header.2.1 .one := by
  rfl

theorem headerGroups_two : headerGroups (EncodedLeaderAlphabet.headerEncode stateNumber header) false =
    EncodedLeaderGroups.dataEncode (Equiv.refl (Fin header.1.val)) header.2.1 .two := by
  rfl

variable {H : Type} {R : Nat} [Fintype H] [DecidableEq H]
variable (o : EncodedRoundObjectives.Data) (root : H ≃ Fin R) (shape : InputShape H)
variable (start : H → (EncodedLeaderObjective.automaton o).State)
local notation "groups" => EncodedLeaderGroups.dataEncode root shape Proc.one
local notation "input" => (o,groups,List.ofFn (fun h => Fin.val (start (Equiv.symm root h))))
local notation "groupNumber" => EncodedLeaderGroups.number root shape Proc.one
local notation "group" => shapeLeaderGroup shape Proc.one

omit [Fintype H] [DecidableEq H] in
theorem phaseData_encode : phaseData input =
    EncodedJointPhaseObjective.dataEncode o root groupNumber start group := by
  unfold phaseData
  rw [EncodedLeaderGroups.assignment_encode]
  rfl

omit [Fintype H] [DecidableEq H] in
theorem compile_encode : compile input =
    EncodedJointPhaseObjective.compile (EncodedJointPhaseObjective.dataEncode o root groupNumber start group) := by
  rw [compile,phaseData_encode]

noncomputable def automaton : DetParityAutomaton
    (EncodedJointPhaseObjective.PhaseLetter (H:=H) (G:=ShapeLeaderGroup shape .one) o) :=
  (EncodedParityConjunction.read (compile input)
    (EncodedJointPhaseObjective.letters (phaseData input)).length).comap
    (EncodedJointPhaseObjective.number o root groupNumber start group)

omit [DecidableEq H] in
/-- Exact endless-phase acceptance for the leader's original information
partition, now with all groups generated from the numeric matrix. -/
theorem accepts_iff (word : OmegaWord
    (EncodedJointPhaseObjective.PhaseLetter (H:=H) (G:=ShapeLeaderGroup shape .one) o)) :
    (automaton o root shape start).Accepts word ↔
      (jointPhaseObjective (EncodedLeaderObjective.automaton o) start group).WinsPlay word := by
  unfold automaton
  rw [compile_encode]
  exact EncodedJointPhaseObjective.accepts_jointPhaseObjective_iff o root groupNumber start group word

omit [DecidableEq H] in
/-- The same compiler handles process two's leadership after the existing
role exchange. The original physical objective and residual states are kept. -/
theorem accepts_left_iff (word : OmegaWord
    (EncodedJointPhaseObjective.PhaseLetter (H:=H) (G:=ShapeLeaderGroup shape .two) (EncodedRoleExchange.swap o))) :
    (automaton (EncodedRoleExchange.swap o) root (exchangeShape shape) start).Accepts word ↔
      (jointPhaseObjective ((EncodedLeaderObjective.automaton o).comap exchangeLetter) start
        (shapeLeaderGroup shape .two)).WinsPlay word := by
  have correct := accepts_iff (EncodedRoleExchange.swap o) root (exchangeShape shape) start word
  apply correct.trans
  rw [jointPhaseObjective_wins_iff,jointPhaseObjective_wins_iff]
  apply forall_congr'
  intro h
  exact EncodedRoleExchange.acceptsFrom_swap o (start h) _

end Characterisation.EncodedLeaderPhase
