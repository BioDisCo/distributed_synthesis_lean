/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit

/-!
# Direct acceptance supplies every physical regime field

The four-way physical-acceptance package is useful when the recurrent and
trapped regimes have different proofs.  Sometimes a concrete finite carrier
already has a direct acceptance proof for its complete physical word.  In
that case the same min-even run, at start zero, supplies all three tail fields
and the identity-cut epoch coupling.  This adapter records that fact once.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- DPA acceptance is the min-even condition on the explicit run-priority
sequence. -/
theorem accepts_iff_runPriority_minEven
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)) :
    A.Accepts word ↔
      NatSeqMinEvenParity (fun n ↦ A.priority (A.run word n)) := by
  rfl

/-- A direct acceptance proof fills the complete four-regime physical
package.  The graph-regime hypotheses are intentionally unused: they are
only selectors for consumers that do not have a uniform proof. -/
noncomputable def finiteGlobalMachinePhysicalAcceptance_of_accepts
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (haccepts :
      A.Accepts (G.globalMachineTraceWord outputOne outputTwo env)) :
    A.FiniteGlobalMachinePhysicalAcceptance G outputOne outputTwo env := by
  let word := G.globalMachineTraceWord outputOne outputTwo env
  have hparity : NatSeqMinEvenParity
      (fun n ↦ A.priority (A.run word n)) :=
    (A.accepts_iff_runPriority_minEven word).mp haccepts
  exact {
    recurrent := fun _ ↦
      A.finiteGlobalMachineEpochCoupling_of_tailParity G outputOne outputTwo
        env 0 (by simpa [word])
    alternatingTail := fun _ ↦ ⟨0, by simpa [word]⟩
    strictRightTail := fun _ ↦ ⟨0, by simpa [word]⟩
    strictLeftTail := fun _ ↦ ⟨0, by simpa [word]⟩ }

end DetParityAutomaton

end DistributedSynthesis
