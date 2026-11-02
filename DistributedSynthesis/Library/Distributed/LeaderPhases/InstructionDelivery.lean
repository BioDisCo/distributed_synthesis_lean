/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoordinatorDelivery

/-! Full-information delivery carries any prescribed instruction computed
from the sender's previous view and current input. It does not carry a choice
that depends on the sender's not-yet-completed current reception. -/
namespace Characterisation
open DistributedSynthesis

/-- Recover the sender's instruction from a delivered full-information view.
The instruction function is part of the fixed protocol. -/
def receivedInstruction {I₁ I₂ C : Type*} {p : Proc}
    (instruction : View I₁ I₂ p.other → PSum I₁ I₂ → C) : View I₁ I₂ p → Option C
  | .empty _ => none
  | .noRecv _ _ => none
  | .recv _ _ sender input => some (instruction sender input)

/-- A message from process one conveys a function of its previous view and
fresh input, regardless of whether process one also receives in this round. -/
theorem instruction_from_one {I₁ I₂ O₁ O₂ C : Type*}
    (instruction : View I₁ I₂ .one → PSum I₁ I₂ → C)
    (h : History I₁ I₂ Graph O₁ O₂) (r : RoundRecord I₁ I₂ Graph O₁ O₂)
    (delivered : r.graph = .right ∨ r.graph = .both) :
    receivedInstruction instruction (currentView .two (History.append h r)) =
      some (instruction (currentView .one h) (.inl r.inputOne)) := by
  rw [currentView_two_append]
  rcases delivered with eq | eq <;> rw [eq] <;> rfl

theorem instruction_from_two {I₁ I₂ O₁ O₂ C : Type*}
    (instruction : View I₁ I₂ .two → PSum I₁ I₂ → C)
    (h : History I₁ I₂ Graph O₁ O₂) (r : RoundRecord I₁ I₂ Graph O₁ O₂)
    (delivered : r.graph = .left ∨ r.graph = .both) :
    receivedInstruction instruction (currentView .one (History.append h r)) =
      some (instruction (currentView .two h) (.inr r.inputTwo)) := by
  rw [currentView_one_append]
  rcases delivered with eq | eq <;> rw [eq] <;> rfl

/-- An incoming-only process cannot send a new instruction back in the same
round: the other process's view has no received-message constructor. -/
theorem no_instruction_back_on_left {I₁ I₂ O₁ O₂ C : Type*}
    (instruction : View I₁ I₂ .one → PSum I₁ I₂ → C)
    (h : History I₁ I₂ Graph O₁ O₂) (r : RoundRecord I₁ I₂ Graph O₁ O₂)
    (graph : r.graph = .left) :
    receivedInstruction instruction (currentView .two (History.append h r)) = none := by
  rw [currentView_two_append, graph]
  rfl

/-- Responses can share one received instruction while retaining different
private-input-dependent table entries. No extra message field is required. -/
theorem same_instruction_right_both {I₁ I₂ C : Type*}
    (instruction : View I₁ I₂ .one → PSum I₁ I₂ → C)
    (h : EnvHistory I₁ I₂) (x : I₁) (y : I₂) :
    receivedInstruction instruction
      (currentView .two (History.append h ⟨x,y,.right,(),()⟩)) =
    receivedInstruction instruction
      (currentView .two (History.append h ⟨x,y,.both,(),()⟩)) := by
  rw [instruction_from_one instruction h _ (Or.inl rfl),
    instruction_from_one instruction h _ (Or.inr rfl)]

end Characterisation
