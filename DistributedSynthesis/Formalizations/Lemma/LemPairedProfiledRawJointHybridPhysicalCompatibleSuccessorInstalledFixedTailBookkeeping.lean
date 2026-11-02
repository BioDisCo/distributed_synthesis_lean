/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorInstalledFixedTail
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorResolvedControllerReadback

/-!
# Installed fixed tails at the resolved-controller boundary

The fixed-tail acceptance argument is independent of the controller that
produced the physical word.  The trace-specific construction only has to
locate, after an eventually homogeneous cut, one installed physical sibling
table whose canonical suffix is the actual suffix.

`EventuallyInstalledFixedTailBookkeeping` records precisely those two
alignment obligations for an arbitrary physical word.  Its parity adapters
consume the universal winning monitors already stored in the installed
tables.  The final constructor plugs the adapters into the exact
`LiteralCompatibleSuccessorResolvedControllerBookkeeping` fields; no
orientation or strict-leader bit is exposed to a local transition map.
-/

namespace DistributedSynthesis

universe u v x y s w

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The minimal trace-specific obligation for the two eventually fixed
regimes.  The word is arbitrary: in the final application it is the physical
word of the newly constructed finite paired controller.

Both fields are proof-side consequences of the graph tail.  They do not add
an orientation test to either endpoint. -/
structure EventuallyInstalledFixedTailBookkeeping
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (graphs : Nat → Graph) : Prop where
  strictRight : EventuallyStrictRight graphs →
    ∃ (move : ProfiledRawJointRightPhysicalSiblingMove A)
      (row : PairedEntryRow) (tableEnv : Nat → In₂ × In₁)
      (tableCut start : Nat),
      ProfiledRawJointHybridPhysicalCompatibleRightInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start
  strictLeft : EventuallyStrictLeft graphs →
    ∃ (move : ProfiledRawJointLeftPhysicalSiblingMove A)
      (row : PairedEntryRow) (tableEnv : Nat → In₁ × In₂)
      (tableCut start : Nat),
      ProfiledRawJointHybridPhysicalCompatibleLeftInstalledPhysicalTailAligned
        A move row tableEnv tableCut word start

namespace EventuallyInstalledFixedTailBookkeeping

variable {word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂)}
variable {graphs : Nat → Graph}

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- An eventual strict-right alignment supplies exactly the tail-parity field
expected by physical readback. -/
theorem rightTailParity
    (bookkeeping : EventuallyInstalledFixedTailBookkeeping A word graphs)
    (hstrict : EventuallyStrictRight graphs) :
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority (A.run word (start + n))) := by
  rcases bookkeeping.strictRight hstrict with
    ⟨move, row, tableEnv, tableCut, start, aligned⟩
  exact ⟨start, aligned.tailParity A move row tableEnv tableCut word start⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror. -/
theorem leftTailParity
    (bookkeeping : EventuallyInstalledFixedTailBookkeeping A word graphs)
    (hstrict : EventuallyStrictLeft graphs) :
    ∃ start : Nat, NatSeqMinEvenParity
      (fun n ↦ A.priority (A.run word (start + n))) := by
  rcases bookkeeping.strictLeft hstrict with
    ⟨move, row, tableEnv, tableCut, start, aligned⟩
  exact ⟨start, aligned.tailParity A move row tableEnv tableCut word start⟩

end EventuallyInstalledFixedTailBookkeeping

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable
  {policy :
    ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
      initial}
variable {controller :
  FinitePairedPhysicalController.{u, v, x, y, w, w}
    In₁ In₂ Out₁ Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- Fill the exact resolved-controller bookkeeping from its hard-regime
streams and an installed-fixed-tail alignment package for the *same*
controller word. -/
noncomputable def
    LiteralCompatibleSuccessorResolvedControllerBookkeeping.ofInstalledFixedTails
    (recurrent : GraphBothRecurrent (fun n ↦ (env n).graph) →
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A
          strategy hwin policy controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env))
    (reversal : PersistentStrictReversalTail (fun n ↦ (env n).graph) →
      Nonempty
        (ProfiledRawJointHybridPhysicalCompatibleResolvedMemberStream A
          strategy hwin policy controller.globalMachine
          controller.globalOutputOne controller.globalOutputTwo env))
    (fixed : EventuallyInstalledFixedTailBookkeeping A
      (controller.globalMachine.globalMachineTraceWord
        controller.globalOutputOne controller.globalOutputTwo env)
      (fun n ↦ (env n).graph)) :
    LiteralCompatibleSuccessorResolvedControllerBookkeeping A strategy hwin
      initial policy controller env where
  recurrent := recurrent
  reversal := reversal
  strictRight := fixed.rightTailParity A
  strictLeft := fixed.leftTailParity A

end

end DetParityAutomaton

end DistributedSynthesis
