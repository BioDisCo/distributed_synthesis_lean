/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedGuardedStagedActivation

/-!
# Finite local carriers for the guarded phase machine

The two processes need not agree on a global phase tag.  Each carrier lists
only locally meaningful modes.  Blind modes contain an owner control;
receiving modes contain the finite monitor/controller control and the staged
key that can be retained locally or transmitted as part of the previous
summary on the next round.

The root constructor is the only pre-observation state.  A `recv` or
`noRecv` step chooses the first local mode.  No constructor records the strict
leader or the communication graph.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfileGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfileGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (bank : FiniteGuardedFirstControllerBank A)

/-- Process one while receiving in the initial-left contingency.  The optional
key is staged by the previous table lookup. -/
abbrev GuardedInitialLeftReceiverControl :=
  GuardedInitialLeftFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers ×
    Option (GuardedFirstRightMacro A)

/-- Process two mirror. -/
abbrev GuardedInitialRightReceiverControl :=
  GuardedInitialRightFiniteReadbackState A strategy hwin rightBasis leftBasis
      controllers ×
    Option (GuardedFirstLeftMacro A)

/-- All finite states process one can hold.  From left to right after `PUnit`:
initial-left receiver, initial-right blind owner, exceptional first-right
owner, exceptional first-left receiver, ordinary right owner, ordinary left
receiver. -/
abbrev GuardedPhaseOneControl :=
  PUnit ⊕
    GuardedInitialLeftReceiverControl A strategy hwin rightBasis leftBasis
      controllers ⊕
    controllers.rightController.Control ⊕
    GuardedFirstRightOwnerControl A bank ⊕
    GuardedFirstLeftReceiverControl A ⊕
    BankRightOwnerControl A ⊕
    BankLeftReceiverControl A

/-- Process-two mirror: initial-left blind owner, initial-right receiver,
exceptional first-right receiver, exceptional first-left owner, ordinary
right receiver, ordinary left owner. -/
abbrev GuardedPhaseTwoControl :=
  PUnit ⊕
    controllers.leftController.Control ⊕
    GuardedInitialRightReceiverControl A strategy hwin rightBasis leftBasis
      controllers ⊕
    GuardedFirstRightReceiverControl A ⊕
    GuardedFirstLeftOwnerControl A bank ⊕
    BankRightReceiverControl A ⊕
    BankLeftOwnerControl A

noncomputable instance : Fintype
    (GuardedInitialLeftReceiverControl A strategy hwin rightBasis leftBasis
      controllers) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (GuardedInitialRightReceiverControl A strategy hwin rightBasis leftBasis
      controllers) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (GuardedPhaseOneControl A strategy hwin rightBasis leftBasis controllers
      bank) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (GuardedPhaseTwoControl A strategy hwin rightBasis leftBasis controllers
      bank) := by
  classical
  infer_instance

/-- Common pre-observation state of process one. -/
def initialGuardedPhaseOneControl :
    GuardedPhaseOneControl A strategy hwin rightBasis leftBasis controllers
      bank :=
  .inl PUnit.unit

/-- Common pre-observation state of process two. -/
def initialGuardedPhaseTwoControl :
    GuardedPhaseTwoControl A strategy hwin rightBasis leftBasis controllers
      bank :=
  .inl PUnit.unit

end


end DetParityAutomaton

end DistributedSynthesis
