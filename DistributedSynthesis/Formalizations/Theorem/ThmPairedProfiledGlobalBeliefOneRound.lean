/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGlobalBeliefMachine
import DistributedSynthesis.Formalizations.Theorem.ThmFiniteGlobalLocalCongruence

/-!
# The one-round local-observation boundary of the profiled belief machine

At a right-oriented source, process one cannot distinguish `left` from
`both`, while process two cannot distinguish `right` from `both`.  The hybrid
output uses exactly those two components.  The left-oriented statements are
the mirror image.  These equalities are the first, output-level part of the
reachable-belief uniformity proof.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (firstBank : FiniteProfiledGuardedFirstControllerBank A)

theorem profiledGlobalRightRound_left_both_output_one
    (state : ProfiledGlobalPhaseState A firstBank)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledGlobalRightRound A firstBank state
      ⟨inputOne, inputTwo, .left⟩).output.1 =
    (profiledGlobalRightRound A firstBank state
      ⟨inputOne, inputTwo, .both⟩).output.1 := by
  simp [profiledGlobalRightRound, profiledBothPhysicalOutput]

theorem profiledGlobalRightRound_right_both_output_two
    (state : ProfiledGlobalPhaseState A firstBank)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledGlobalRightRound A firstBank state
      ⟨inputOne, inputTwo, .right⟩).output.2 =
    (profiledGlobalRightRound A firstBank state
      ⟨inputOne, inputTwo, .both⟩).output.2 := by
  simp [profiledGlobalRightRound, profiledBothPhysicalOutput]

theorem profiledGlobalLeftRound_left_both_output_one
    (state : ProfiledGlobalPhaseState A firstBank)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledGlobalLeftRound A firstBank state
      ⟨inputOne, inputTwo, .left⟩).output.1 =
    (profiledGlobalLeftRound A firstBank state
      ⟨inputOne, inputTwo, .both⟩).output.1 := by
  simp [profiledGlobalLeftRound, profiledBothPhysicalOutput]

theorem profiledGlobalLeftRound_right_both_output_two
    (state : ProfiledGlobalPhaseState A firstBank)
    (inputOne : In₁) (inputTwo : In₂) :
    (profiledGlobalLeftRound A firstBank state
      ⟨inputOne, inputTwo, .right⟩).output.2 =
    (profiledGlobalLeftRound A firstBank state
      ⟨inputOne, inputTwo, .both⟩).output.2 := by
  simp [profiledGlobalLeftRound, profiledBothPhysicalOutput]

end


end


end DetParityAutomaton

end DistributedSynthesis
