/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalRecurrentReality

/-!
# Parity of the actual alternating root thread

The end-to-end construction uses simultaneous finite tables to prove local
consistency.  Those tables need not select one globally coherent root.  The
parity argument therefore follows a separate proof-only thread of actual
recurrent roots below one fixed rational policy.

The root orientation alternates at every strict reversal.  More importantly,
each transition is an `Allowed` edge of the *same* policy.  This is exactly
the hypothesis under which `PairedProfiledRationalPolicy.accepts_of_allowed_path`
reconstructs one accepting branch.  No orientation or strict-leader bit is
made available to either process at run time.
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
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- One actual recurrent root below a fixed policy.  This is proof data, not
an observable controller mode. -/
inductive ProfiledFixedPolicyRoot where
  | right (source : ProfiledPolicyRightMacro A policy)
  | left (source : ProfiledPolicyLeftMacro A policy)

namespace ProfiledFixedPolicyRoot

/-- Embed an oriented recurrent root back into the policy's tree state. -/
def state : ProfiledFixedPolicyRoot A policy → PairedProfiledTreeState A
  | .right source => .inr (.inl source.1)
  | .left source => .inr (.inr source.1)

/-- Successive actual roots alternate orientation and use one exact policy
edge.  The relation intentionally excludes arbitrary mosaics of reachable
states. -/
inductive AlternatingStep :
    ProfiledFixedPolicyRoot A policy →
      ProfiledFixedPolicyRoot A policy → Prop where
  | rightToLeft
      (source : ProfiledPolicyRightMacro A policy)
      (target : ProfiledPolicyLeftMacro A policy)
      (allowed : PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inl source.1)) (.inr (.inr target.1))) :
      AlternatingStep (.right source) (.left target)
  | leftToRight
      (source : ProfiledPolicyLeftMacro A policy)
      (target : ProfiledPolicyRightMacro A policy)
      (allowed : PairedProfiledRationalPolicy.Allowed A policy
        (.inr (.inr source.1)) (.inr (.inl target.1))) :
      AlternatingStep (.left source) (.right target)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Forgetting orientation from an alternating root step leaves an exact
`Allowed` edge of the fixed policy. -/
theorem AlternatingStep.allowed
    {source target : ProfiledFixedPolicyRoot A policy}
    (hstep : AlternatingStep A policy source target) :
    PairedProfiledRationalPolicy.Allowed A policy
      (state A policy source) (state A policy target) := by
  cases hstep with
  | rightToLeft _ _ hallowed => exact hallowed
  | leftToRight _ _ hallowed => exact hallowed

/-- An explicit infinite thread of actual roots.  `initial` pins it to the
root of the restricted child policy; `step` prevents policy switching and
root mosaics. -/
structure AlternatingThread where
  root : Nat → ProfiledFixedPolicyRoot A policy
  initial : state A policy (root 0) = policy.run []
  step : ∀ n, AlternatingStep A policy (root n) (root (n + 1))

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- The alternating actual-root thread inherits parity from its single
rational policy. -/
theorem AlternatingThread.epochParity
    (thread : AlternatingThread A policy) :
    NatSeqMinEvenParity (fun n =>
      pairedProfiledEntryPriority A (state A policy (thread.root n))) := by
  apply PairedProfiledRationalPolicy.accepts_of_allowed_path A policy
  · exact thread.initial
  · intro n
    exact (thread.step n).allowed A policy

/-! ## Operational constructors for the two alternating cases -/

/-- Every real right close supplies the next left root together with an
alternating edge of the same policy. -/
theorem exists_left_step_of_real_right_close
    (source : ProfiledPolicyRightMacro A policy) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : ProfiledPolicyLeftMacro A policy,
      (stepProfiledPolicyRightReceiverFor A policy source
        (profiledPolicyRightFiniteStateAfter A policy source past).1 row
        (profiledPolicyRightFiniteStateAfter A policy source past).2
        move).2.2 = some target ∧
      AlternatingStep A policy (.right source) (.left target) := by
  rcases profiledPolicyRight_real_close_allowed A policy source row past move
    with ⟨target, htarget, hallowed⟩
  exact ⟨target, htarget, .rightToLeft source target hallowed⟩

/-- Every real left close supplies the next right root together with the
mirror alternating edge of the same policy. -/
theorem exists_right_step_of_real_left_close
    (source : ProfiledPolicyLeftMacro A policy) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : ProfiledPolicyRightMacro A policy,
      (stepProfiledPolicyLeftReceiverFor A policy source
        (profiledPolicyLeftFiniteStateAfter A policy source past).1 row
        (profiledPolicyLeftFiniteStateAfter A policy source past).2
        move).2.2 = some target ∧
      AlternatingStep A policy (.left source) (.right target) := by
  rcases profiledPolicyLeft_real_close_allowed A policy source row past move
    with ⟨target, htarget, hallowed⟩
  exact ⟨target, htarget, .leftToRight source target hallowed⟩

end ProfiledFixedPolicyRoot

/-! ## Exceptional-prefix split

These two theorems identify the exact first root of the ordinary recurrent
suffix.  The preceding initial/first-block segment is finite and can therefore
be discarded by suffix invariance of parity. -/

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

variable (package : PairedInitialProfiledRationalPackage A)

/-- A real exceptional right close produces a left root which is exactly the
initial state of its guarded child's restricted policy. -/
theorem exists_firstRight_recurrent_initialRoot
    (key : EndToEndInitialLeftBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ∃ target : EndToEndGuardedRightRecurrentLeftMacro A
        (rightGuarded :=
          (endToEndInitialLeftBoundaryActivation A package key).policy),
      (stepEndToEndGuardedFirstRightReceiverFor A package key
        (endToEndFirstRightFiniteStateAfter A package key past).1 row
        (endToEndFirstRightFiniteStateAfter A package key past).2 move).2.2 =
          some target ∧
      ProfiledFixedPolicyRoot.state A (target.1.policy A)
          (.left target.2) = (target.1.policy A).run [] := by
  have hsome := endToEndFirstRight_real_close_staged A package key row past move
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  exact stepEndToEndGuardedFirstRightReceiverFor_initial_of_staged A package
    key (endToEndFirstRightFiniteStateAfter A package key past).1 row
    (endToEndFirstRightFiniteStateAfter A package key past).2 move target hstage

/-- Process-swapped exceptional-prefix split. -/
theorem exists_firstLeft_recurrent_initialRoot
    (key : EndToEndInitialRightBoundaryKey A package) (row : PairedEntryRow)
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ∃ target : EndToEndGuardedLeftRecurrentRightMacro A
        (leftGuarded :=
          (endToEndInitialRightBoundaryActivation A package key).policy),
      (stepEndToEndGuardedFirstLeftReceiverFor A package key
        (endToEndFirstLeftFiniteStateAfter A package key past).1 row
        (endToEndFirstLeftFiniteStateAfter A package key past).2 move).2.2 =
          some target ∧
      ProfiledFixedPolicyRoot.state A (target.1.policy A)
          (.right target.2) = (target.1.policy A).run [] := by
  have hsome := endToEndFirstLeft_real_close_staged A package key row past move
  rw [Option.isSome_iff_exists] at hsome
  rcases hsome with ⟨target, hstage⟩
  refine ⟨target, hstage, ?_⟩
  exact stepEndToEndGuardedFirstLeftReceiverFor_initial_of_staged A package
    key (endToEndFirstLeftFiniteStateAfter A package key past).1 row
    (endToEndFirstLeftFiniteStateAfter A package key past).2 move target hstage

end

end DetParityAutomaton

end DistributedSynthesis
