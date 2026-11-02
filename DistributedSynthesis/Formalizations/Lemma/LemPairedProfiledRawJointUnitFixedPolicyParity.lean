/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitLeftPolicyHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPolicyEpochAcceptance

/-!
# Parity of one alternating raw-joint fixed-policy thread

This file is the proof-side recurrent spine of the construction.  An actual
root is either a reachable right macro or a reachable left macro.  Successive
roots must alternate orientation and must be related by `AllowedTarget` for
one unchanged finite-code policy.  Forgetting the orientation therefore
produces one coherent policy path, never a mosaic of independently accepted
fragments.

The orientation is a theorem-level tag on the actual root.  It is not an
argument of either local controller and does not tell a process which side is
the strict leader.
-/

namespace DistributedSynthesis

universe u v w x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- One actual recurrent root under the fixed raw-joint policy.  `Sum.inl`
is the right macro and `Sum.inr` is the left macro. -/
abbrev ProfiledRawJointUnitFixedPolicyRoot
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      initialCode) :=
  ProfiledRawJointUnitRightPolicyMacro A strategy initialCode policy ⊕
    ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode policy

namespace ProfiledRawJointUnitFixedPolicyRoot

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
variable (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
  initialCode)

/-- Forget the proof-side orientation tag and retain the complete policy
state. -/
def state :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy →
      ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode
  | .inl source => source.state
  | .inr source => source.state

/-- Proof-side orientation of an actual recurrent root. -/
def side :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy →
      IndexedLineageSide
  | .inl _ => .right
  | .inr _ => .left

/-- Successive roots alternate and use one exact finite-image edge of the
same policy. -/
inductive AlternatingStep :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy →
        Prop where
  | rightToLeft
      (source : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
        policy)
      (target : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
        policy)
      (allowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
        initialCode policy source.state target.state) :
      AlternatingStep (.inl source) (.inr target)
  | leftToRight
      (source : ProfiledRawJointUnitLeftPolicyMacro A strategy initialCode
        policy)
      (target : ProfiledRawJointUnitRightPolicyMacro A strategy initialCode
        policy)
      (allowed : ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy
        initialCode policy source.state target.state) :
      AlternatingStep (.inr source) (.inl target)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Erasing orientation from an alternating step leaves an exact
`AllowedTarget` edge of the unchanged policy. -/
theorem AlternatingStep.allowed
    {source target : ProfiledRawJointUnitFixedPolicyRoot A strategy
      initialCode policy}
    (hstep : AlternatingStep A policy source target) :
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy (state A policy source) (state A policy target) := by
  cases hstep with
  | rightToLeft _ _ hallowed => exact hallowed
  | leftToRight _ _ hallowed => exact hallowed

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The orientation flips at every actual recurrent close. -/
theorem AlternatingStep.side_eq_other
    {source target : ProfiledRawJointUnitFixedPolicyRoot A strategy
      initialCode policy}
    (hstep : AlternatingStep A policy source target) :
    side A policy target = (side A policy source).other := by
  cases hstep <;> rfl

/-- A root-started infinite thread of actual recurrent macros. -/
structure AlternatingThread where
  root : Nat → ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode
    policy
  initial : state A policy (root 0) = policy.run []
  step : ∀ n : Nat, AlternatingStep A policy (root n) (root (n + 1))

namespace AlternatingThread

/-- The complete policy-state sequence underlying the alternating thread. -/
def states
    (thread : AlternatingThread A policy) : Nat →
      ProfiledRawJointOneSidedProvenancePolicyState A strategy initialCode :=
  fun n ↦ state A policy (thread.root n)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem states_zero
    (thread : AlternatingThread A policy) :
    thread.states A policy 0 = policy.run [] :=
  thread.initial

/-- Every consecutive state is an allowed edge of the same policy. -/
theorem states_allowed
    (thread : AlternatingThread A policy) (n : Nat) :
    ProfiledRawJointOneSidedProvenanceAllowedTarget A strategy initialCode
      policy (thread.states A policy n) (thread.states A policy (n + 1)) :=
  (thread.step n).allowed A policy

/-- The positive-time code word of the actual alternating roots is accepted
by the raw-joint code DPA. -/
theorem codeWord_accepts
    (thread : AlternatingThread A policy) :
    (profiledRawJointOneSidedCodeParityDPA A initialCode).Accepts
      (fun n ↦ (thread.states A policy (n + 1)).1) :=
  SourceFreeBeliefFiniteCodePolicyImage.accepts_of_allowedTarget_path
    (profiledRawJointOneSidedCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    policy (thread.states A policy) (thread.states_zero A policy)
      (thread.states_allowed A policy)

/-- The proof-side side tag alternates at every recurrent edge. -/
theorem side_succ
    (thread : AlternatingThread A policy) (n : Nat) :
    side A policy (thread.root (n + 1)) =
      (side A policy (thread.root n)).other :=
  (thread.step n).side_eq_other A policy

end

/-- Package an alternating thread and an exact physical block-minimum law as
the generic raw policy/epoch coupling. -/
noncomputable def toPolicyEpochCoupling
    (thread : AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (offset start : Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (fun n ↦ (thread.states A policy (n + 1)).1)
            initialSide () (offset + k))) :
    ProfiledRawJointUnitPolicyEpochCoupling A strategy initialCode policy G
      outputOne outputTwo env where
  state := thread.states A policy
  initial := thread.initial
  allowed := thread.states_allowed A policy
  initialSide := initialSide
  offset := offset
  start := start
  cuts := cuts
  cuts_strictMono := cuts_strictMono
  cuts_zero := cuts_zero
  blockMin_eq_threadPriority := blockMin_eq_threadPriority

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end physical acceptance once the operational construction supplies
the exact epoch cuts and block minima for its alternating macro thread. -/
theorem physicalTrace_accepts
    (thread : AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (offset start : Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_threadPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        (codedAlternatingIndexedLineageCodeThreadSystem initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (profiledRawJointThreadRootPriority A)).priority
          (codedAlternatingIndexedLineageCodeRun initialCode
            (profiledRawJointOneSidedCurrentSlots A)
            (fun n ↦ (thread.states A policy (n + 1)).1)
            initialSide () (offset + k))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (thread.toPolicyEpochCoupling A policy G outputOne outputTwo env initialSide
    offset start cuts cuts_strictMono cuts_zero
    blockMin_eq_threadPriority).physicalTrace_accepts A

end AlternatingThread

end ProfiledRawJointUnitFixedPolicyRoot

end


end DetParityAutomaton

end DistributedSynthesis
