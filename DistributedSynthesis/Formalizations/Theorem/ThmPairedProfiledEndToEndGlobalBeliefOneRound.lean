/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndGlobalBeliefMachine
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalLocalCongruence

/-!
# One-round local output laws for the one-policy global machine

At a right-oriented source, process one cannot distinguish `left` from
`both`, and process two cannot distinguish `right` from `both`.  The hybrid
output was chosen precisely so the corresponding output components agree.
The left-oriented statements are the mirror.  These laws are the output-level
base of the multi-round two-shadow belief invariant; they do not assert the
false equality of the hidden proof-side phase constructors.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

theorem endToEndGlobalRightRound_left_both_output_one
    (state : EndToEndGlobalPhaseState A package)
    (inputOne : In₁) (inputTwo : In₂) :
    (endToEndGlobalRightRound A package state
      ⟨inputOne, inputTwo, .left⟩).output.1 =
    (endToEndGlobalRightRound A package state
      ⟨inputOne, inputTwo, .both⟩).output.1 := by
  simp [endToEndGlobalRightRound, endToEndBothPhysicalOutput]

theorem endToEndGlobalRightRound_right_both_output_two
    (state : EndToEndGlobalPhaseState A package)
    (inputOne : In₁) (inputTwo : In₂) :
    (endToEndGlobalRightRound A package state
      ⟨inputOne, inputTwo, .right⟩).output.2 =
    (endToEndGlobalRightRound A package state
      ⟨inputOne, inputTwo, .both⟩).output.2 := by
  simp [endToEndGlobalRightRound, endToEndBothPhysicalOutput]

theorem endToEndGlobalLeftRound_left_both_output_one
    (state : EndToEndGlobalPhaseState A package)
    (inputOne : In₁) (inputTwo : In₂) :
    (endToEndGlobalLeftRound A package state
      ⟨inputOne, inputTwo, .left⟩).output.1 =
    (endToEndGlobalLeftRound A package state
      ⟨inputOne, inputTwo, .both⟩).output.1 := by
  simp [endToEndGlobalLeftRound, endToEndBothPhysicalOutput]

theorem endToEndGlobalLeftRound_right_both_output_two
    (state : EndToEndGlobalPhaseState A package)
    (inputOne : In₁) (inputTwo : In₂) :
    (endToEndGlobalLeftRound A package state
      ⟨inputOne, inputTwo, .right⟩).output.2 =
    (endToEndGlobalLeftRound A package state
      ⟨inputOne, inputTwo, .both⟩).output.2 := by
  simp [endToEndGlobalLeftRound, endToEndBothPhysicalOutput]

end


end DetParityAutomaton

end DistributedSynthesis
