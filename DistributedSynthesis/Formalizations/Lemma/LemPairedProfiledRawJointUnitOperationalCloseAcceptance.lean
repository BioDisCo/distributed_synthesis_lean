/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts

/-!
# Unit-policy acceptance over operational close cuts

The literal close-query interface only needs a fresh matched control when a
block contains an open strict record.  A zero-open block has an empty record
slice, so its `PhysicalSlice` follows from entry-state and length alignment
alone.  This distinction is essential for consecutive `.both` rounds: after
the first simultaneous receive the verified Unit kernel has cross shape, and
another simultaneous receive keeps that shape.

This file records the minimal repair without adding a graph, direction, or
leader flag to either local controller.  The operational close clock consumes
each `.both` as a zero-open singleton.  At such a cut no matched-control
premise is requested.  At a strict cut the existing `OperationalAt` premise
is retained unchanged.  The resulting alignment supplies the full scheduled
physical-slice family and hence an unconditional acceptance theorem once the
remaining strict-cut carrier invariants are provided.
-/

namespace DistributedSynthesis

universe u v w x y s i₁ i₂ e₁ e₂

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- Under Moore timing, equality after the first transition makes the whole
rerooted output words equal.  The pre-transition states themselves may be
different. -/
theorem reroot_globalMachineTraceWord_eq_of_first_step_eq
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) (left right : G.State)
    (hfirst : G.step left (env 0) = G.step right (env 0)) :
    (G.reroot left).globalMachineTraceWord outputOne outputTwo env =
      (G.reroot right).globalMachineTraceWord outputOne outputTwo env := by
  have hstate : ∀ n : Nat,
      (G.reroot left).globalStateTrace env (n + 1) =
        (G.reroot right).globalStateTrace env (n + 1) := by
    intro n
    induction n with
    | zero =>
        exact hfirst
    | succ n ih =>
        change G.step ((G.reroot left).globalStateTrace env (n + 1))
            (env (n + 1)) =
          G.step ((G.reroot right).globalStateTrace env (n + 1))
            (env (n + 1))
        rw [ih]
  funext n
  simp only [globalMachineTraceWord]
  rw [hstate n]

end FiniteGlobalRoundMachine

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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

private abbrev UnitKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

/-! ## Why the old cut interface fails on a cross -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A concrete fresh matched-right state is constructor-disjoint from the
receiver/receiver cross. -/
theorem profiledRawJointUnitFreshMatchedRightState_not_cross
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    ¬ ProfiledRawJointLeaderFreeKernel.HasCrossShape
      (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
        bank adapter source row oldOutputOne oldOutputTwo) := by
  rintro ⟨oneKey, left, outputOne, twoKey, right, outputTwo, hcross⟩
  have hone := congrArg (fun controls ↦ controls.1.1) hcross
  simp [profiledRawJointUnitFreshMatchedRightState] at hone

/-- Matched-left mirror of the constructor disjointness. -/
theorem profiledRawJointUnitFreshMatchedLeftState_not_cross
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    ¬ ProfiledRawJointLeaderFreeKernel.HasCrossShape
      (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy bank
        adapter source row oldOutputOne oldOutputTwo) := by
  rintro ⟨oneKey, left, outputOne, twoKey, right, outputTwo, hcross⟩
  have htwo := congrArg (fun controls ↦ controls.2.1) hcross
  simp [profiledRawJointUnitFreshMatchedLeftState] at htwo

/-- The old `OperationalAt` premise cannot hold at any receiver/receiver
cross, independently of the query orientation.  Together with
`matchedRight_both_hasCrossShape`, `matchedLeft_both_hasCrossShape`, and
`cross_both_hasCrossShape`, this is the exact formal obstruction for the
second member of a consecutive `.both` run. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.not_operationalAt_of_cross
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcross : ProfiledRawJointLeaderFreeKernel.HasCrossShape
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
        physicalEnv (base + cuts k))) :
    ¬ query.OperationalAt A strategy initial policy bank adapter physicalEnv
      base cuts k := by
  intro hoperational
  cases query with
  | right source row past move =>
      rcases hoperational with
        ⟨oldOutputOne, oldOutputTwo, hcontrol, _⟩
      rw [hcontrol] at hcross
      exact profiledRawJointUnitFreshMatchedRightState_not_cross A strategy
        initial policy bank adapter source row oldOutputOne oldOutputTwo hcross
  | left source row past move =>
      rcases hoperational with
        ⟨oldOutputOne, oldOutputTwo, hcontrol, _⟩
      rw [hcontrol] at hcross
      exact profiledRawJointUnitFreshMatchedLeftState_not_cross A strategy
        initial policy bank adapter source row oldOutputOne oldOutputTwo hcross

end

/-! ## A strict selection from the cross is a fresh target execution -/

/-- Concrete receiver/receiver state used only in the proof-side trace
argument.  It is not a new local-control constructor. -/
noncomputable def profiledRawJointUnitCrossState
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.State :=
  (((.leftReceiver () left, oldOutputOne),
    (.rightReceiver () right, oldOutputTwo)))

/-- Arbitrary matched-right state at the end of a completed right block. -/
noncomputable def profiledRawJointUnitMatchedRightState
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.State :=
  (((.rightOwner () owner, oldOutputOne),
    (.rightReceiver () right, oldOutputTwo)))

/-- Arbitrary matched-left mirror at the end of a completed left block. -/
noncomputable def profiledRawJointUnitMatchedLeftState
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.State :=
  (((.leftReceiver () left, oldOutputOne),
    (.leftOwner () owner, oldOutputTwo)))

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- On a strict-left selection, the cross and the fresh matched-left state
named by the right receiver have literally the same first post-transition
Moore state.  The unused left receiver cannot influence either local event. -/
theorem profiledRawJointUnitCross_left_step_eq_freshMatchedLeft
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } =
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right)
            right.2.1 oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } := by
  rfl

/-- Strict-right mirror: the left receiver alone determines the restarted
fresh matched-right execution. -/
theorem profiledRawJointUnitCross_right_step_eq_freshMatchedRight
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } =
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left)
            left.2.1 oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } := by
  rfl

/-- A strict-left switch from a completed matched-right state has the same
first post-transition state as the fresh staged-left target. -/
theorem profiledRawJointUnitMatchedRight_left_step_eq_freshMatchedLeft
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } =
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right)
            right.2.1 oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } := by
  rfl

/-- Completed matched-left to fresh staged-right mirror. -/
theorem profiledRawJointUnitMatchedLeft_right_step_eq_freshMatchedRight
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (inputOne : In₁) (inputTwo : In₂) :
    (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } =
      (UnitKernel A strategy initial policy bank adapter).globalMachine.step
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left)
            left.2.1 oldOutputOne oldOutputTwo)
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } := by
  rfl

/-- Therefore a cross selected by an all-left suffix emits exactly the fresh
matched-left physical word of the staged target, from its first Moore-timed
letter onward. -/
theorem profiledRawJointUnitCross_left_traceWord_eq_freshMatchedLeft
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitCrossState A strategy initial policy bank adapter
        left right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment env) =
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right)
            right.2.1 oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment env) := by
  apply FiniteGlobalRoundMachine.reroot_globalMachineTraceWord_eq_of_first_step_eq
  exact profiledRawJointUnitCross_left_step_eq_freshMatchedLeft A strategy
    initial policy bank adapter left right oldOutputOne oldOutputTwo
      (env 0).1 (env 0).2

/-- All-right mirror of the cross-to-fresh trace equality. -/
theorem profiledRawJointUnitCross_right_traceWord_eq_freshMatchedRight
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitCrossState A strategy initial policy bank adapter
        left right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment env) =
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left)
            left.2.1 oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment env) := by
  apply FiniteGlobalRoundMachine.reroot_globalMachineTraceWord_eq_of_first_step_eq
  exact profiledRawJointUnitCross_right_step_eq_freshMatchedRight A strategy
    initial policy bank adapter left right oldOutputOne oldOutputTwo
      (env 0).2 (env 0).1

/-- The same fresh-target reroot equality holds when the preselection state is
the completed matched-right pair rather than the cross. -/
theorem profiledRawJointUnitMatchedRight_left_traceWord_eq_freshMatchedLeft
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitMatchedRightState A strategy initial policy bank
        adapter owner right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment env) =
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedLeftState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right)
            right.2.1 oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictLeftEnvironment env) := by
  apply FiniteGlobalRoundMachine.reroot_globalMachineTraceWord_eq_of_first_step_eq
  exact profiledRawJointUnitMatchedRight_left_step_eq_freshMatchedLeft A
    strategy initial policy bank adapter owner right oldOutputOne oldOutputTwo
      (env 0).1 (env 0).2

/-- Completed matched-left mirror. -/
theorem profiledRawJointUnitMatchedLeft_right_traceWord_eq_freshMatchedRight
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
        adapter left owner oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment env) =
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        (profiledRawJointUnitFreshMatchedRightState A strategy initial policy
          bank adapter
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left)
            left.2.1 oldOutputOne oldOutputTwo)).globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          (profiledRawJointUnitStrictRightEnvironment env) := by
  apply FiniteGlobalRoundMachine.reroot_globalMachineTraceWord_eq_of_first_step_eq
  exact profiledRawJointUnitMatchedLeft_right_step_eq_freshMatchedRight A
    strategy initial policy bank adapter left owner oldOutputOne oldOutputTwo
      (env 0).2 (env 0).1

/-- Closed certificate word for a strict-left selection from matched-right. -/
theorem profiledRawJointUnitMatchedRight_left_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitMatchedRightState A strategy initial policy bank
        adapter owner right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment env) =
      fun n ↦ pairedLeftRecordForRow right.2.1
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right) env n)) := by
  rw [profiledRawJointUnitMatchedRight_left_traceWord_eq_freshMatchedLeft A
    strategy initial policy bank adapter owner right oldOutputOne oldOutputTwo
      env]
  exact profiledRawJointUnitFreshMatchedLeft_traceWord A strategy initial
    policy bank adapter
      (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial policy
        bank right) right.2.1 oldOutputOne oldOutputTwo env

/-- Closed certificate word for a strict-right selection from matched-left. -/
theorem profiledRawJointUnitMatchedLeft_right_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitMatchedLeftState A strategy initial policy bank
        adapter left owner oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment env) =
      fun n ↦ pairedRightRecordForRow left.2.1
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left) env n)) := by
  rw [profiledRawJointUnitMatchedLeft_right_traceWord_eq_freshMatchedRight A
    strategy initial policy bank adapter left owner oldOutputOne oldOutputTwo
      env]
  exact profiledRawJointUnitFreshMatchedRight_traceWord A strategy initial
    policy bank adapter
      (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial policy
        bank left) left.2.1 oldOutputOne oldOutputTwo env

/-- Closed form of the cross-selected left trace, ready for the finite-prefix
physical-slice argument. -/
theorem profiledRawJointUnitCross_left_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₁ × In₂) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitCrossState A strategy initial policy bank adapter
        left right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictLeftEnvironment env) =
      fun n ↦ pairedLeftRecordForRow right.2.1
        (profiledRawJointUnitLeftPhysicalLetter A
          (profiledRawJointUnitLeftPolicyOmegaPlay A bank
            (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
              policy bank right) env n)) := by
  rw [profiledRawJointUnitCross_left_traceWord_eq_freshMatchedLeft A strategy
    initial policy bank adapter left right oldOutputOne oldOutputTwo env]
  exact profiledRawJointUnitFreshMatchedLeft_traceWord A strategy initial
    policy bank adapter
      (profiledRawJointUnitPolicyRightReceiverTarget A strategy initial policy
        bank right) right.2.1 oldOutputOne oldOutputTwo env

/-- Closed all-right mirror. -/
theorem profiledRawJointUnitCross_right_traceWord
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (env : Nat → In₂ × In₁) :
    ((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
      (profiledRawJointUnitCrossState A strategy initial policy bank adapter
        left right oldOutputOne oldOutputTwo)).globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        (profiledRawJointUnitStrictRightEnvironment env) =
      fun n ↦ pairedRightRecordForRow left.2.1
        (profiledRawJointUnitRightPhysicalLetter A
          (profiledRawJointUnitRightPolicyOmegaPlay A bank
            (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
              policy bank left) env n)) := by
  rw [profiledRawJointUnitCross_right_traceWord_eq_freshMatchedRight A strategy
    initial policy bank adapter left right oldOutputOne oldOutputTwo env]
  exact profiledRawJointUnitFreshMatchedRight_traceWord A strategy initial
    policy bank adapter
      (profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial policy
        bank left) left.2.1 oldOutputOne oldOutputTwo env

end

/-! ## Trace-level operational alignment -/

/-- Exact trace premise at one strict scheduled cut.  Unlike the old
`OperationalAt`, this formulation permits the actual pre-round state to be a
completed opposite matched pair or the receiver/receiver cross; it asks only
that selecting the query's strict direction reroots to its literal
certificate word. -/
def ProfiledRawJointUnitPolicyCloseQuery.TraceOperationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat) : Prop :=
  match query with
  | .right source row past move =>
      let blockEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k))).globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            (profiledRawJointUnitStrictRightEnvironment blockEnv) =
          fun n ↦ pairedRightRecordForRow row
            (profiledRawJointUnitRightPhysicalLetter A
              (profiledRawJointUnitRightPolicyOmegaPlay A bank source blockEnv
                n))) ∧
        ∀ j : Nat, j < past.length →
          OmegaWord.drop physicalEnv (base + cuts k) j =
            profiledRawJointUnitStrictRightEnvironment blockEnv j
  | .left source row past move =>
      let blockEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
      (((UnitKernel A strategy initial policy bank adapter).globalMachine.reroot
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k))).globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            (profiledRawJointUnitStrictLeftEnvironment blockEnv) =
          fun n ↦ pairedLeftRecordForRow row
            (profiledRawJointUnitLeftPhysicalLetter A
              (profiledRawJointUnitLeftPolicyOmegaPlay A bank source blockEnv
                n))) ∧
        ∀ j : Nat, j < past.length →
          OmegaWord.drop physicalEnv (base + cuts k) j =
            profiledRawJointUnitStrictLeftEnvironment blockEnv j

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Trace-level operational alignment is exactly sufficient for the physical
slice.  This is the reusable causality argument shared by fresh, switched,
and cross-selected starts. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.physicalSlice_of_traceOperationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (htrace : query.TraceOperationalAt A strategy initial policy bank adapter
      physicalEnv base cuts k)
    (hentry :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv)
          (base + cuts k) = query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1) :
    query.PhysicalSlice A strategy initial policy bank
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) base cuts k := by
  refine ⟨hentry, hlength, ?_⟩
  let G := (UnitKernel A strategy initial policy bank adapter).globalMachine
  let outputOne :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
  let outputTwo :=
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
  cases query with
  | right source row past move =>
      let blockEnv : Nat → In₂ × In₁ := omegaOfList (past ++ [move])
      rcases htrace with ⟨hword, henv⟩
      have hreroot := G.reroot_globalMachineTraceWord_drop outputOne outputTwo
        physicalEnv (base + cuts k)
      have hcausal :=
        (G.reroot (G.globalStateTrace physicalEnv (base + cuts k))).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
          outputOne outputTwo (OmegaWord.drop physicalEnv (base + cuts k))
            (profiledRawJointUnitStrictRightEnvironment blockEnv) past.length
              (by simpa [blockEnv] using henv)
      rw [hword] at hcausal
      rw [← hreroot]
      simp only [ProfiledRawJointUnitPolicyCloseQuery.records]
      rw [show (profiledRawJointUnitRightPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitRightPolicyPlay A strategy initial policy
                bank source past move) past.length)).length = past.length by
        simp [profiledRawJointUnitRightPhysicalPrefixRecords, omegaPrefix]]
      rw [hcausal]
      simp [profiledRawJointUnitRightPhysicalPrefixRecords,
        profiledRawJointUnitRightPolicyPlay,
        profiledRawJointUnitRightPolicyOmegaPlay, omegaPrefix,
        Function.comp_def]
  | left source row past move =>
      let blockEnv : Nat → In₁ × In₂ := omegaOfList (past ++ [move])
      rcases htrace with ⟨hword, henv⟩
      have hreroot := G.reroot_globalMachineTraceWord_drop outputOne outputTwo
        physicalEnv (base + cuts k)
      have hcausal :=
        (G.reroot (G.globalStateTrace physicalEnv (base + cuts k))).omegaPrefix_globalMachineTraceWord_eq_of_forall_lt
          outputOne outputTwo (OmegaWord.drop physicalEnv (base + cuts k))
            (profiledRawJointUnitStrictLeftEnvironment blockEnv) past.length
              (by simpa [blockEnv] using henv)
      rw [hword] at hcausal
      rw [← hreroot]
      simp only [ProfiledRawJointUnitPolicyCloseQuery.records]
      rw [show (profiledRawJointUnitLeftPhysicalPrefixRecords A row
            (omegaPrefix
              (profiledRawJointUnitLeftPolicyPlay A strategy initial policy
                bank source past move) past.length)).length = past.length by
        simp [profiledRawJointUnitLeftPhysicalPrefixRecords, omegaPrefix]]
      rw [hcausal]
      simp [profiledRawJointUnitLeftPhysicalPrefixRecords,
        profiledRawJointUnitLeftPolicyPlay,
        profiledRawJointUnitLeftPolicyOmegaPlay, omegaPrefix,
        Function.comp_def]

/-! ## Transition-table constructors for trace alignment -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The old fresh-matched invariant is a special case of trace-level
alignment. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.traceOperationalAt_of_operationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hoperational : query.OperationalAt A strategy initial policy bank adapter
      physicalEnv base cuts k) :
    query.TraceOperationalAt A strategy initial policy bank adapter physicalEnv
      base cuts k := by
  cases query with
  | right source row past move =>
      rcases hoperational with
        ⟨oldOutputOne, oldOutputTwo, hcontrol, henv⟩
      constructor
      · rw [hcontrol]
        exact profiledRawJointUnitFreshMatchedRight_traceWord A strategy
          initial policy bank adapter source row oldOutputOne oldOutputTwo
            (omegaOfList (past ++ [move]))
      · exact henv
  | left source row past move =>
      rcases hoperational with
        ⟨oldOutputOne, oldOutputTwo, hcontrol, henv⟩
      constructor
      · rw [hcontrol]
        exact profiledRawJointUnitFreshMatchedLeft_traceWord A strategy initial
          policy bank adapter source row oldOutputOne oldOutputTwo
            (omegaOfList (past ++ [move]))
      · exact henv

/-- A right query is trace-operational when its staged target and row are
carried by the left receiver of an actual completed matched-left state. -/
theorem profiledRawJointUnitRightQuery_traceOperationalAt_of_matchedLeft
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
      policy bank)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitMatchedLeftState A strategy initial policy bank
          adapter left owner oldOutputOne oldOutputTwo)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = row)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictRightEnvironment
          (omegaOfList (past ++ [move])) j) :
    (ProfiledRawJointUnitPolicyCloseQuery.right source row past move).TraceOperationalAt
      A strategy initial policy bank adapter physicalEnv base cuts k := by
  constructor
  · rw [hcontrol, ← htarget, ← hrow]
    exact profiledRawJointUnitMatchedLeft_right_traceWord A strategy initial
      policy bank adapter left owner oldOutputOne oldOutputTwo
        (omegaOfList (past ++ [move]))
  · exact henv

/-- A right query can equally be selected from the receiver/receiver cross. -/
theorem profiledRawJointUnitRightQuery_traceOperationalAt_of_cross
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitRightPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
    (htarget : profiledRawJointUnitPolicyLeftReceiverTarget A strategy initial
      policy bank left = source)
    (hrow : left.2.1 = row)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictRightEnvironment
          (omegaOfList (past ++ [move])) j) :
    (ProfiledRawJointUnitPolicyCloseQuery.right source row past move).TraceOperationalAt
      A strategy initial policy bank adapter physicalEnv base cuts k := by
  constructor
  · rw [hcontrol, ← htarget, ← hrow]
    exact profiledRawJointUnitCross_right_traceWord A strategy initial policy
      bank adapter left right oldOutputOne oldOutputTwo
        (omegaOfList (past ++ [move]))
  · exact henv

/-- Left-query mirror from a completed matched-right state. -/
theorem profiledRawJointUnitLeftQuery_traceOperationalAt_of_matchedRight
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
      policy bank)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitMatchedRightState A strategy initial policy bank
          adapter owner right oldOutputOne oldOutputTwo)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = row)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictLeftEnvironment
          (omegaOfList (past ++ [move])) j) :
    (ProfiledRawJointUnitPolicyCloseQuery.left source row past move).TraceOperationalAt
      A strategy initial policy bank adapter physicalEnv base cuts k := by
  constructor
  · rw [hcontrol, ← htarget, ← hrow]
    exact profiledRawJointUnitMatchedRight_left_traceWord A strategy initial
      policy bank adapter owner right oldOutputOne oldOutputTwo
        (omegaOfList (past ++ [move]))
  · exact henv

/-- Left-query mirror from the cross. -/
theorem profiledRawJointUnitLeftQuery_traceOperationalAt_of_cross
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
      (initial.code A) policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂)
    (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
      policy)
    (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy initial
      policy)
    (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hcontrol :
      (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
          physicalEnv (base + cuts k) =
        profiledRawJointUnitCrossState A strategy initial policy bank adapter
          left right oldOutputOne oldOutputTwo)
    (htarget : profiledRawJointUnitPolicyRightReceiverTarget A strategy initial
      policy bank right = source)
    (hrow : right.2.1 = row)
    (henv : ∀ j : Nat, j < past.length →
      OmegaWord.drop physicalEnv (base + cuts k) j =
        profiledRawJointUnitStrictLeftEnvironment
          (omegaOfList (past ++ [move])) j) :
    (ProfiledRawJointUnitPolicyCloseQuery.left source row past move).TraceOperationalAt
      A strategy initial policy bank adapter physicalEnv base cuts k := by
  constructor
  · rw [hcontrol, ← htarget, ← hrow]
    exact profiledRawJointUnitCross_left_traceWord A strategy initial policy
      bank adapter left right oldOutputOne oldOutputTwo
        (omegaOfList (past ++ [move]))
  · exact henv

end

/-! ## Empty blocks need no control-shape premise -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A close query whose represented record list is empty has its exact
physical slice from entry-state and numerical length alignment alone.  In
particular the joint controller may have cross shape at this cut. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.physicalSlice_of_records_eq_nil
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (word : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (hempty : query.records A strategy initial policy bank = [])
    (hentry : A.run word (base + cuts k) =
      query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1) :
    query.PhysicalSlice A strategy initial policy bank word base cuts k := by
  refine ⟨hentry, hlength, ?_⟩
  rw [hempty]
  simp [omegaPrefix]

/-- At one cut it suffices either to have an empty represented block or the
existing fresh-matched operational invariant. -/
def ProfiledRawJointUnitPolicyCloseQuery.OperationalOrEmptyAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat) : Prop :=
  query.records A strategy initial policy bank = [] ∨
    query.OperationalAt A strategy initial policy bank adapter physicalEnv
      base cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The weakened operational premise still gives the complete physical
slice. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.physicalSlice_of_operationalOrEmptyAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (halignment : query.OperationalOrEmptyAt A strategy initial policy bank
      adapter physicalEnv base cuts k)
    (hentry :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv)
          (base + cuts k) = query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1) :
    query.PhysicalSlice A strategy initial policy bank
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) base cuts k := by
  rcases halignment with hempty | hoperational
  · exact query.physicalSlice_of_records_eq_nil A strategy initial policy
      bank _ base cuts k hempty hentry hlength
  · exact query.physicalSlice_of_operationalAt A strategy initial policy
      bank adapter physicalEnv base cuts k hoperational hentry hlength

/-- Empty-or-trace form used by the actual switching carrier. -/
def ProfiledRawJointUnitPolicyCloseQuery.TraceOperationalOrEmptyAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat) : Prop :=
  query.records A strategy initial policy bank = [] ∨
    query.TraceOperationalAt A strategy initial policy bank adapter physicalEnv
      base cuts k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Empty-or-trace alignment supplies a physical slice. -/
theorem ProfiledRawJointUnitPolicyCloseQuery.physicalSlice_of_traceOperationalOrEmptyAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat)
    (halignment : query.TraceOperationalOrEmptyAt A strategy initial policy
      bank adapter physicalEnv base cuts k)
    (hentry :
      A.run
          ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
            (UnitKernel A strategy initial policy bank adapter).globalOutputOne
            (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
            physicalEnv)
          (base + cuts k) = query.entryState A strategy initial policy)
    (hlength : (query.records A strategy initial policy bank).length =
      cuts (k + 1) - cuts k - 1) :
    query.PhysicalSlice A strategy initial policy bank
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) base cuts k := by
  rcases halignment with hempty | htrace
  · exact query.physicalSlice_of_records_eq_nil A strategy initial policy
      bank _ base cuts k hempty hentry hlength
  · exact query.physicalSlice_of_traceOperationalAt A strategy initial
      policy bank adapter physicalEnv base cuts k htrace hentry hlength

/-! ## Canonical operational-cut alignment -/

/-- The graph tail seen from a physical reroot. -/
def profiledRawJointPhysicalGraphTail
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat) : Nat → Graph :=
  fun n ↦ (physicalEnv (base + n)).graph

/-- Exact residual carrier invariant for the canonical operational close
clock.  Strict blocks use the Moore-timed trace invariant proved by the
switch/cross selection lemmas above.  Simultaneous blocks deliberately
request no control-shape fact because their open record list is empty. -/
structure ProfiledRawJointUnitPolicyOperationalCloseAlignment
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Prop where
  entryStateAt : ∀ k : Nat,
    A.run
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv)
        (base + operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm k) =
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).entryState A strategy initial policy
  recordsLengthAt : ∀ k : Nat,
    ((schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)).records A strategy initial policy bank).length =
      operationalCloseOpenLength
        (profiledRawJointPhysicalGraphTail physicalEnv base) hterm k
  traceOperationalAt_of_strict : ∀ k : Nat,
    profiledRawJointPhysicalGraphTail physicalEnv base
        (operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm k) ≠ .both →
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).TraceOperationalAt A strategy initial policy bank
            adapter physicalEnv base
              (operationalCloseCuts
                (profiledRawJointPhysicalGraphTail physicalEnv base) hterm) k

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The operational-close alignment supplies the scheduled physical slices.
The `.both` branch is discharged solely by `zero_open_of_both`; therefore the
proof applies unchanged to every member of a consecutive `.both` run. -/
theorem ProfiledRawJointUnitPolicyOperationalCloseAlignment.toPhysicalSlices
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    (alignment : ProfiledRawJointUnitPolicyOperationalCloseAlignment A
      strategy initial policy bank adapter physicalEnv base hterm seed
        schedule) :
    ProfiledRawJointUnitPolicyScheduledPhysicalSlices A strategy initial policy
      bank (UnitKernel A strategy initial policy bank adapter).globalMachine
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv seed schedule base
          (operationalCloseCuts
            (profiledRawJointPhysicalGraphTail physicalEnv base) hterm) where
  sliceAt k := by
    let graphs := profiledRawJointPhysicalGraphTail physicalEnv base
    let cuts := operationalCloseCuts graphs hterm
    let query := schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)
    have hlength :
        (query.records A strategy initial policy bank).length =
          cuts (k + 1) - cuts k - 1 := by
      simpa [query, cuts, graphs, operationalCloseOpenLength] using
        alignment.recordsLengthAt k
    have hweak : query.TraceOperationalOrEmptyAt A strategy initial policy bank
        adapter physicalEnv base cuts k := by
      by_cases hgraph : graphs (cuts k) = .both
      · apply Or.inl
        apply List.length_eq_zero_iff.mp
        rw [alignment.recordsLengthAt k,
          operationalCloseOpenLength_eq_zero_of_both graphs hterm k hgraph]
      · exact Or.inr (alignment.traceOperationalAt_of_strict k hgraph)
    exact query.physicalSlice_of_traceOperationalOrEmptyAt A strategy initial policy
      bank adapter physicalEnv base cuts k hweak (alignment.entryStateAt k)
        hlength

/-! ## Acceptance endpoints -/

/-- The canonical operational cuts and the weakened alignment produce the
exact epoch coupling used by the physical acceptance layer. -/
noncomputable def profiledRawJointUnitPolicyOperationalCloseEpochCoupling
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (alignment : ProfiledRawJointUnitPolicyOperationalCloseAlignment A
      strategy initial policy bank adapter physicalEnv base hterm seed
        schedule) :
    A.FiniteGlobalMachineEpochCoupling
      (UnitKernel A strategy initial policy bank adapter).globalMachine
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv :=
  profiledRawJointUnitPolicyScheduledSlicesEpochCoupling A strategy initial
    policy bank
      (UnitKernel A strategy initial policy bank adapter).globalMachine
      (UnitKernel A strategy initial policy bank adapter).globalOutputOne
      (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
      physicalEnv seed schedule hseed base
        (operationalCloseCuts
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm)
        (operationalCloseCuts_strictMono
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm)
        (operationalCloseCuts_zero
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm)
        alignment.toPhysicalSlices

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Once the strict-cut carrier alignment is supplied, the verified Unit
policy kernel accepts the complete physical word.  No further case split on
consecutive simultaneous rounds remains. -/
theorem profiledRawJointUnitPolicy_accepts_of_operationalCloseAlignment
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy)
    (hseed : ProfiledRawJointUnitFixedPolicyRoot.state A policy seed =
      policy.run [])
    (alignment : ProfiledRawJointUnitPolicyOperationalCloseAlignment A
      strategy initial policy bank adapter physicalEnv base hterm seed
        schedule) :
    A.Accepts
      ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
        (UnitKernel A strategy initial policy bank adapter).globalOutputOne
        (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
        physicalEnv) := by
  exact A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling
    (UnitKernel A strategy initial policy bank adapter).globalMachine
    (UnitKernel A strategy initial policy bank adapter).globalOutputOne
    (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
    physicalEnv
      (profiledRawJointUnitPolicyOperationalCloseEpochCoupling A strategy
        initial policy bank adapter physicalEnv base hterm seed schedule hseed
          alignment)

end

end DetParityAutomaton

end DistributedSynthesis
