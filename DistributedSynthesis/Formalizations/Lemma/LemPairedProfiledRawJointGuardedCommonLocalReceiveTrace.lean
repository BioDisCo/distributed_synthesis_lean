/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedInitialCommonLocalBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedForeverCommonAcceptance

/-!
# Local receive traces of the guarded common bank

The paired state in this file is proof-side only.  Its two components are the
independently executable finite local states from the common bank, and its
last field records their synchronization invariant.  Neither local
transition is given a graph, hierarchy direction, leader bit, or semantic
world.

The main result identifies the outputs produced by the two local receive
transitions at every round with the physical simultaneous output selected by
the occurrence-sensitive rational policy.  It also proves that the local
bank controls follow `ControlNext` exactly.
-/

namespace DistributedSynthesis

universe u v x y s

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
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

/-! ## One synchronized proof-side pair of genuinely local states -/

structure ProfiledRawJointGuardedCommonLocalPairState where
  one : ProfiledRawJointGuardedInitialCommonOneState A strategy hwin
  two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin
  agree : ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin one
    two

noncomputable instance profiledRawJointGuardedCommonLocalPairStateFintype :
    Fintype (ProfiledRawJointGuardedCommonLocalPairState A strategy hwin) := by
  classical
  let Rep := Σ one :
      ProfiledRawJointGuardedInitialCommonOneState A strategy hwin,
    { two : ProfiledRawJointGuardedInitialCommonTwoState A strategy hwin //
      ProfiledRawJointGuardedInitialCommonStatesAgree A strategy hwin one
        two }
  let equiv :
      ProfiledRawJointGuardedCommonLocalPairState A strategy hwin ≃ Rep :=
    { toFun := fun state ↦ ⟨state.one, state.two, state.agree⟩
      invFun := fun state ↦ ⟨state.1, state.2.1, state.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; rcases state with ⟨one, two, h⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Fresh simultaneous receive by the two local machines. -/
noncomputable def profiledRawJointGuardedCommonLocalPairStart
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLocalPairState A strategy hwin :=
  let one := profiledRawJointGuardedInitialCommonStartOne A strategy hwin
    control input
  let two := profiledRawJointGuardedInitialCommonStartTwo A strategy hwin
    control input
  ((one.1, two.1), ⟨one.2, two.2,
    profiledRawJointGuardedInitialCommonStart_states_agree A strategy hwin
      control input⟩)

/-- Another simultaneous receive.  The process-one and process-two functions
are called separately on their own local component and the delivered partner
component. -/
noncomputable def profiledRawJointGuardedCommonLocalPairRecv
    (state : ProfiledRawJointGuardedCommonLocalPairState A strategy hwin)
    (input : In₁ × In₂) :
    (Out₁ × Out₂) ×
      ProfiledRawJointGuardedCommonLocalPairState A strategy hwin :=
  let one := profiledRawJointGuardedInitialCommonOneRecv A strategy hwin
    state.one state.two input.1 input.2
  let two := profiledRawJointGuardedInitialCommonTwoRecv A strategy hwin
    state.two state.one input.2 input.1
  ((one.1, two.1), ⟨one.2, two.2,
    profiledRawJointGuardedInitialCommonRecv_states_agree A strategy hwin
      state.one state.two state.agree input⟩)

@[simp] theorem profiledRawJointGuardedCommonLocalPairStart_one_control
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairStart A strategy hwin control
      input).2.one.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLocalPairStart_two_control
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairStart A strategy hwin control
      input).2.two.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin control
        input :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLocalPairRecv_one_control
    (state : ProfiledRawJointGuardedCommonLocalPairState A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairRecv A strategy hwin state
      input).2.one.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin
        state.one.control input :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLocalPairRecv_two_control
    (state : ProfiledRawJointGuardedCommonLocalPairState A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairRecv A strategy hwin state
      input).2.two.control =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin
        state.two.control input :=
  rfl

/-- Fresh local receive outputs are the physical simultaneous output of the
current policy-selected guarded pair. -/
theorem profiledRawJointGuardedCommonLocalPairStart_outputs
    (control : CommonControl A strategy hwin) (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairStart A strategy hwin control
      input).1 =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          control) input := by
  exact profiledRawJointGuardedInitialCommonStart_outputs A strategy hwin
    control input

/-- Repeated local receive outputs are the physical simultaneous output of
the pair selected by the current shared policy control. -/
theorem profiledRawJointGuardedCommonLocalPairRecv_outputs
    (state : ProfiledRawJointGuardedCommonLocalPairState A strategy hwin)
    (input : In₁ × In₂) :
    (profiledRawJointGuardedCommonLocalPairRecv A strategy hwin state
      input).1 =
      profiledRawJointGuardedCommonPairBothOutput A strategy hwin
        (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
          state.one.control) input := by
  rw [profiledRawJointGuardedCommonLocalPairRecv]
  rw [profiledRawJointGuardedInitialCommonRecv_outputs A strategy hwin
    state.one state.two state.agree input]
  rw [state.one.common_eq]
  rfl

/-! ## Infinite local receive trace -/

/-- The abstract finite bank-control path before each physical receive. -/
def profiledRawJointGuardedCommonLocalControlTrace
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    Nat → CommonControl A strategy hwin
  | 0 => control
  | n + 1 =>
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin
        (profiledRawJointGuardedCommonLocalControlTrace control inputs n)
        (inputs n)

@[simp] theorem profiledRawJointGuardedCommonLocalControlTrace_zero
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonLocalControlTrace A strategy hwin control
      inputs 0 = control :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonLocalControlTrace_succ
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂)
    (n : Nat) :
    profiledRawJointGuardedCommonLocalControlTrace A strategy hwin control
        inputs (n + 1) =
      profiledRawJointGuardedInitialCommonControlNext A strategy hwin
        (profiledRawJointGuardedCommonLocalControlTrace A strategy hwin
          control inputs n) (inputs n) :=
  rfl

/-- Synchronized local states after processing physical input `inputs n`. -/
noncomputable def profiledRawJointGuardedCommonLocalStateTrace
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    Nat → ProfiledRawJointGuardedCommonLocalPairState A strategy hwin
  | 0 =>
      (profiledRawJointGuardedCommonLocalPairStart A strategy hwin control
        (inputs 0)).2
  | n + 1 =>
      (profiledRawJointGuardedCommonLocalPairRecv A strategy hwin
        (profiledRawJointGuardedCommonLocalStateTrace control inputs n)
        (inputs (n + 1))).2

/-- Actual pair of outputs returned by the two local receive functions. -/
noncomputable def profiledRawJointGuardedCommonLocalOutputTrace
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    Nat → Out₁ × Out₂
  | 0 =>
      (profiledRawJointGuardedCommonLocalPairStart A strategy hwin control
        (inputs 0)).1
  | n + 1 =>
      (profiledRawJointGuardedCommonLocalPairRecv A strategy hwin
        (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin control
          inputs n)
        (inputs (n + 1))).1

/-- The process-one local control after round `n` is exactly the abstract
policy control after the first `n+1` input pairs. -/
theorem profiledRawJointGuardedCommonLocalStateTrace_one_control
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ∀ n,
      (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin control
        inputs n).one.control =
      profiledRawJointGuardedCommonLocalControlTrace A strategy hwin control
        inputs (n + 1) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [profiledRawJointGuardedCommonLocalStateTrace,
        profiledRawJointGuardedCommonLocalPairRecv_one_control,
        profiledRawJointGuardedCommonLocalControlTrace]
      rw [ih]
      rfl

/-- Process two carries the same exact control path. -/
theorem profiledRawJointGuardedCommonLocalStateTrace_two_control
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ∀ n,
      (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin control
        inputs n).two.control =
      profiledRawJointGuardedCommonLocalControlTrace A strategy hwin control
        inputs (n + 1) := by
  intro n
  rw [← (profiledRawJointGuardedCommonLocalStateTrace A strategy hwin control
    inputs n).agree]
  exact profiledRawJointGuardedCommonLocalStateTrace_one_control A strategy
    hwin control inputs n

/-- **Local receive-trace readback.**  At every round, the two independently
computed receive outputs are exactly the physical output selected by the
current occurrence-sensitive finite policy control. -/
theorem profiledRawJointGuardedCommonLocalOutputTrace_eq_pairBothOutput
    (control : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ∀ n,
      profiledRawJointGuardedCommonLocalOutputTrace A strategy hwin control
          inputs n =
        profiledRawJointGuardedCommonPairBothOutput A strategy hwin
          (profiledRawJointGuardedInitialCommonControlPair A strategy hwin
            (profiledRawJointGuardedCommonLocalControlTrace A strategy hwin
              control inputs n))
          (inputs n) := by
  intro n
  cases n with
  | zero =>
      exact profiledRawJointGuardedCommonLocalPairStart_outputs A strategy hwin
        control (inputs 0)
  | succ n =>
      rw [profiledRawJointGuardedCommonLocalOutputTrace]
      rw [profiledRawJointGuardedCommonLocalPairRecv_outputs A strategy hwin]
      rw [profiledRawJointGuardedCommonLocalStateTrace_one_control A strategy
        hwin control inputs n]

end

end DetParityAutomaton

end DistributedSynthesis
