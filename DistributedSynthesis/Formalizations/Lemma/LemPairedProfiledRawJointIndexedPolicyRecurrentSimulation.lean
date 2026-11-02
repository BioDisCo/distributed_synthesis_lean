/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointIndexedPolicyLeaderFreeKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointLeaderFreeReadback
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachineReroot

/-!
# Recurrent simulation for an indexed raw-joint policy

Once the finite front has selected a child key, the indexed carrier is
literally the already verified fixed-policy carrier at that key.  This file
makes that reuse precise.  Its proof-side relation has the three possible
recurrent joint shapes: matched right, matched left, and the locally
unmarked receiver/receiver cross.

Every physical round preserves the selected key and commutes with erasing
that key to `Unit`.  Consequently, two machines re-rooted at related
recurrent states have equal physical words.  Acceptance or any stronger
word property already proved for the fixed-policy machine can therefore be
transported to the indexed machine.  No local control is given a graph,
orientation, or leader bit.
-/

namespace DistributedSynthesis

universe u v x y s k i₁ i₂ e₁ e₂

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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (ChildCode : Type k)
  (source : ChildCode →
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : (key : ChildCode) →
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((source key).code A))
  (bank : (key : ChildCode) →
    ProfiledRawJointUnitPolicyControllerBank A strategy (source key)
      (policy key))

/-! ## Exact same-key equations -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The equality-sensitive right continuation takes its real-owner branch
when the two recurrent keys agree. -/
@[simp] theorem profiledRawJointIndexedPolicyContinueRightReceiver_sameKey
    [DecidableEq ChildCode] (key : ChildCode)
    (receiver : ProfiledRawJointIndexedPolicyRightReceiver A strategy
      ChildCode source policy key)
    (owner : ProfiledRawJointIndexedPolicyRightOwner A strategy ChildCode
      source policy bank key) (move : In₂ × In₁) :
    profiledRawJointIndexedPolicyContinueRightReceiver A strategy ChildCode
        source policy bank key key receiver owner move =
      let next := continueProfiledRawJointUnitRightPolicyReceiver A strategy
        (source key) (policy key) (bank key) receiver owner move
      (next.1, ⟨key, next.2⟩) := by
  simp [profiledRawJointIndexedPolicyContinueRightReceiver]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-oriented same-key continuation. -/
@[simp] theorem profiledRawJointIndexedPolicyContinueLeftReceiver_sameKey
    [DecidableEq ChildCode] (key : ChildCode)
    (receiver : ProfiledRawJointIndexedPolicyLeftReceiver A strategy
      ChildCode source policy key)
    (owner : ProfiledRawJointIndexedPolicyLeftOwner A strategy ChildCode
      source policy bank key) (move : In₁ × In₂) :
    profiledRawJointIndexedPolicyContinueLeftReceiver A strategy ChildCode
        source policy bank key key receiver owner move =
      let next := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
        (source key) (policy key) (bank key) receiver owner move
      (next.1, ⟨key, next.2⟩) := by
  simp [profiledRawJointIndexedPolicyContinueLeftReceiver]

/-! ## The recurrent same-key relation -/

/-- Relation between an indexed recurrent joint state at `key` and the
corresponding fixed-policy (`Unit`-indexed) joint state.  The stored Moore
outputs are required to be literal equalities, so physical words transfer
without an additional output invariant. -/
inductive ProfiledRawJointIndexedPolicyRecurrentAt
    (InitialOne : Type i₁) (InitialTwo : Type i₂)
    (ExceptionalOne : Type e₁) (ExceptionalTwo : Type e₂)
    (key : ChildCode) :
    ((ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂)) →
    ((ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂)) → Prop where
  | matchedRight
      (owner : ProfiledRawJointIndexedPolicyRightOwner A strategy ChildCode
        source policy bank key)
      (receiver : ProfiledRawJointIndexedPolicyRightReceiver A strategy
        ChildCode source policy key) (outputOne : Out₁) (outputTwo : Out₂) :
      ProfiledRawJointIndexedPolicyRecurrentAt InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo key
        (((.rightOwner key owner), outputOne),
          ((.rightReceiver key receiver), outputTwo))
        (((.rightOwner () owner), outputOne),
          ((.rightReceiver () receiver), outputTwo))
  | matchedLeft
      (receiver : ProfiledRawJointIndexedPolicyLeftReceiver A strategy
        ChildCode source policy key)
      (owner : ProfiledRawJointIndexedPolicyLeftOwner A strategy ChildCode
        source policy bank key) (outputOne : Out₁) (outputTwo : Out₂) :
      ProfiledRawJointIndexedPolicyRecurrentAt InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo key
        (((.leftReceiver key receiver), outputOne),
          ((.leftOwner key owner), outputTwo))
        (((.leftReceiver () receiver), outputOne),
          ((.leftOwner () owner), outputTwo))
  | cross
      (left : ProfiledRawJointIndexedPolicyLeftReceiver A strategy ChildCode
        source policy key)
      (right : ProfiledRawJointIndexedPolicyRightReceiver A strategy ChildCode
        source policy key) (outputOne : Out₁) (outputTwo : Out₂) :
      ProfiledRawJointIndexedPolicyRecurrentAt InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo key
        (((.leftReceiver key left), outputOne),
          ((.rightReceiver key right), outputTwo))
        (((.leftReceiver () left), outputOne),
          ((.rightReceiver () right), outputTwo))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Related recurrent states store the same two Moore outputs. -/
theorem ProfiledRawJointIndexedPolicyRecurrentAt.outputs_eq
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    {key : ChildCode}
    {indexedControls :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂)}
    {unitControls :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂)}
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedControls unitControls) :
    (indexedControls.1.2, indexedControls.2.2) =
      (unitControls.1.2, unitControls.2.2) := by
  cases hrel <;> rfl

/-! ## One-round recurrent simulation -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every physical graph round preserves the common child key and is the
literal fixed-policy transition at that key.  The graph is proof-side input
to the joint physical scheduler; neither local transition receives it. -/
theorem ProfiledRawJointIndexedPolicyRecurrentAt.advanceControls
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    {indexedControls :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂)}
    {unitControls :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂)}
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedControls unitControls)
    (round : EnvironmentRound In₁ In₂) :
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode source policy
      bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo key
      ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter).physicalController.advanceControls
          indexedControls round)
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
        (policy key) (bank key) unitAdapter).physicalController.advanceControls
          unitControls round) := by
  cases hrel <;> cases round with
  | mk inputOne inputTwo graph =>
      cases graph <;>
        simp [FinitePairedPhysicalController.advanceControls,
          ProfiledRawJointLeaderFreeKernel.physicalController,
          ProfiledRawJointLeaderFreeKernel.noRecvOne,
          ProfiledRawJointLeaderFreeKernel.noRecvTwo,
          ProfiledRawJointLeaderFreeKernel.recvOne,
          ProfiledRawJointLeaderFreeKernel.recvTwo,
          profiledRawJointIndexedPolicyLeaderFreeKernel,
          profiledRawJointUnitPolicyLeaderFreeKernel,
          profiledRawJointIndexedPolicyContinueRightReceiver_sameKey,
          profiledRawJointIndexedPolicyContinueLeftReceiver_sameKey]
      all_goals
        first
        | rw [profiledRawJointIndexedPolicyContinueRightReceiver_sameKey]
        | rw [profiledRawJointIndexedPolicyContinueLeftReceiver_sameKey]
        | skip
      all_goals constructor

/-! ## Infinite recurrent trace reuse -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The one-round simulation iterates from any related recurrent re-root.
In particular, the common key cannot change anywhere in the suffix. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_globalStateTrace
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (indexedState :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂))
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedState unitState)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode source policy
      bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo key
      (((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
          source policy bank indexedAdapter).globalMachine.reroot
            indexedState).globalStateTrace env n)
      (((profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
          (policy key) (bank key) unitAdapter).globalMachine.reroot
            unitState).globalStateTrace env n) := by
  intro n
  induction n with
  | zero =>
      simpa [FiniteGlobalRoundMachine.reroot] using hrel
  | succ n ih =>
      rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
        FiniteGlobalRoundMachine.globalStateTrace_succ]
      simpa [ProfiledRawJointLeaderFreeKernel.globalMachine,
        FiniteGlobalRoundMachine.reroot] using
        ih.advanceControls A strategy ChildCode source policy bank
          indexedAdapter key unitAdapter (env n)

/-- Re-rooting the indexed and fixed-policy machines at related recurrent
states produces literally the same physical word. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (indexedState :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂))
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedState unitState)
    (env : EnvironmentSequence In₁ In₂) :
    let indexedKernel :=
      profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
        (policy key) (bank key) unitAdapter
    (indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env =
      (unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo env := by
  dsimp only
  funext n
  have hstate :=
    profiledRawJointIndexedPolicyRecurrentAt_globalStateTrace A strategy
      ChildCode source policy bank indexedAdapter key unitAdapter indexedState
        unitState hrel env (n + 1)
  have houtputs := hstate.outputs_eq A strategy ChildCode source policy bank
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  simp only [ProfiledRawJointLeaderFreeKernel.globalOutputOne,
    ProfiledRawJointLeaderFreeKernel.globalOutputTwo,
    ProfiledRawJointLeaderFreeKernel.physicalController]
  injection houtputs with hOne hTwo
  rw [hOne, hTwo]

/-- One finite entry round may precede the recurrent relation.  If the two
machines enter related same-key states after that round, their complete
Moore-timed physical words already agree, including the entry round itself. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq_of_advance
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (indexedState :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂))
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (env : EnvironmentSequence In₁ In₂)
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key
        ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
          source policy bank indexedAdapter).physicalController.advanceControls
            indexedState (env 0))
        ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
          (policy key) (bank key) unitAdapter).physicalController.advanceControls
            unitState (env 0))) :
    let indexedKernel :=
      profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
        (policy key) (bank key) unitAdapter
    (indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env =
      (unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo env := by
  dsimp only
  let indexedKernel :=
    profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode source
      policy bank indexedAdapter
  let unitKernel :=
    profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
      (policy key) (bank key) unitAdapter
  have hstate : ∀ n : Nat,
      ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode source
        policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo key
        ((indexedKernel.globalMachine.reroot indexedState).globalStateTrace env
          (n + 1))
        ((unitKernel.globalMachine.reroot unitState).globalStateTrace env
          (n + 1)) := by
    intro n
    induction n with
    | zero =>
        simpa [FiniteGlobalRoundMachine.globalStateTrace_succ,
          ProfiledRawJointLeaderFreeKernel.globalMachine,
          FiniteGlobalRoundMachine.reroot, indexedKernel, unitKernel] using hrel
    | succ n ih =>
        rw [FiniteGlobalRoundMachine.globalStateTrace_succ,
          FiniteGlobalRoundMachine.globalStateTrace_succ]
        simpa [ProfiledRawJointLeaderFreeKernel.globalMachine,
          FiniteGlobalRoundMachine.reroot, indexedKernel, unitKernel] using
          ih.advanceControls A strategy ChildCode source policy bank
            indexedAdapter key unitAdapter (env (n + 1))
  funext n
  have houtputs :=
    (hstate n).outputs_eq A strategy ChildCode source policy bank
  simp only [FiniteGlobalRoundMachine.globalMachineTraceWord]
  simp only [ProfiledRawJointLeaderFreeKernel.globalOutputOne,
    ProfiledRawJointLeaderFreeKernel.globalOutputTwo,
    ProfiledRawJointLeaderFreeKernel.physicalController]
  injection houtputs with hOne hTwo
  rw [hOne, hTwo]

/-- Any word property proved for the fixed-policy suffix transfers unchanged
to the indexed suffix.  This is the generic reuse interface for the existing
operational, epoch-coupling, and parity theorems. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_wordProperty_iff
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (indexedState :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂))
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedState unitState)
    (env : EnvironmentSequence In₁ In₂)
    (P : (Nat → RoundRecord In₁ In₂ Graph Out₁ Out₂) → Prop) :
    let indexedKernel :=
      profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
        (policy key) (bank key) unitAdapter
    P ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
        indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env) ↔
      P ((unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
        unitKernel.globalOutputOne unitKernel.globalOutputTwo env) := by
  dsimp only
  rw [profiledRawJointIndexedPolicyRecurrentAt_traceWord_eq A strategy
    ChildCode source policy bank indexedAdapter key unitAdapter indexedState
      unitState hrel env]

/-- In particular, DPA acceptance from the actual post-prefix state can be
proved entirely in the old fixed-policy carrier and transported back. -/
theorem profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (indexedState :
      (ProfiledRawJointIndexedPolicyOneControl A strategy ChildCode source
          policy bank InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointIndexedPolicyTwoControl A strategy ChildCode source
          policy bank InitialTwo ExceptionalTwo × Out₂))
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key indexedState unitState)
    (env : EnvironmentSequence In₁ In₂) (state : A.State) :
    let indexedKernel :=
      profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter
    let unitKernel :=
      profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
        (policy key) (bank key) unitAdapter
    A.AcceptsFrom state
        ((indexedKernel.globalMachine.reroot indexedState).globalMachineTraceWord
          indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env) ↔
      A.AcceptsFrom state
        ((unitKernel.globalMachine.reroot unitState).globalMachineTraceWord
          unitKernel.globalOutputOne unitKernel.globalOutputTwo env) := by
  apply profiledRawJointIndexedPolicyRecurrentAt_wordProperty_iff A strategy
    ChildCode source policy bank indexedAdapter key unitAdapter indexedState
      unitState hrel env (A.AcceptsFrom state)

end

/-! ## Finite-prefix handoff -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Once an actual indexed execution reaches a synchronized recurrent state,
acceptance of the corresponding fixed-policy suffix from the *actual* DPA
state closes acceptance of the complete indexed word.  This combines the
same-key recurrent simulation with the generic finite-machine reroot lemma;
no checker state is restarted and the discarded prefix is genuinely finite. -/
theorem profiledRawJointIndexedPolicy_accepts_of_recurrentAt
    [Fintype ChildCode] [DecidableEq ChildCode]
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (indexedAdapter : ProfiledRawJointIndexedPolicyExceptionalAdapter A
      strategy ChildCode source policy bank InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (key : ChildCode)
    (unitAdapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      (source key) (policy key) (bank key) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (unitState :
      (ProfiledRawJointUnitPolicyOneControl A strategy (source key) (policy key)
          (bank key) InitialOne ExceptionalOne × Out₁) ×
      (ProfiledRawJointUnitPolicyTwoControl A strategy (source key) (policy key)
          (bank key) InitialTwo ExceptionalTwo × Out₂))
    (hrel : ProfiledRawJointIndexedPolicyRecurrentAt A strategy ChildCode
      source policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo
        key
        ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
          source policy bank indexedAdapter).globalMachine.globalStateTrace
            env start)
        unitState)
    (haccepts :
      A.AcceptsFrom
        (A.run
          ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
            source policy bank indexedAdapter).globalMachine.globalMachineTraceWord
                (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
                  ChildCode source policy bank indexedAdapter).globalOutputOne
                (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy
                  ChildCode source policy bank indexedAdapter).globalOutputTwo
                env) start)
        (((profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
          (policy key) (bank key) unitAdapter).globalMachine.reroot unitState
            ).globalMachineTraceWord
              (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
                (source key) (policy key) (bank key) unitAdapter
                  ).globalOutputOne
              (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
                (source key) (policy key) (bank key) unitAdapter
                  ).globalOutputTwo
              (OmegaWord.drop env start))) :
    A.Accepts
      ((profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
        source policy bank indexedAdapter).globalMachine.globalMachineTraceWord
          (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
            source policy bank indexedAdapter).globalOutputOne
          (profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode
            source policy bank indexedAdapter).globalOutputTwo env) := by
  let indexedKernel :=
    profiledRawJointIndexedPolicyLeaderFreeKernel A strategy ChildCode source
      policy bank indexedAdapter
  let unitKernel :=
    profiledRawJointUnitPolicyLeaderFreeKernel A strategy (source key)
      (policy key) (bank key) unitAdapter
  apply A.accepts_of_rerootedGlobalMachine_acceptsFrom indexedKernel.globalMachine
    indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env start
  exact
    (profiledRawJointIndexedPolicyRecurrentAt_acceptsFrom_iff A strategy
      ChildCode source policy bank indexedAdapter key unitAdapter
        (indexedKernel.globalMachine.globalStateTrace env start) unitState hrel
        (OmegaWord.drop env start)
        (A.run
          (indexedKernel.globalMachine.globalMachineTraceWord
            indexedKernel.globalOutputOne indexedKernel.globalOutputTwo env)
          start)).mpr haccepts

end

end DetParityAutomaton

end DistributedSynthesis
