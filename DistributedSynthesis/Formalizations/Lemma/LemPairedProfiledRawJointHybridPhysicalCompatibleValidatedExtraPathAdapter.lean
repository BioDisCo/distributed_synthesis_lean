/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedExtraAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraPathAcceptance

/-!
# Accepted paths from the current-valid joint policy

The current-valid parent link is strictly stronger than the original joint
parent link.  This file weakens one already selected rational policy, keeping
its run and successor table literally unchanged.  It does **not** perform a
second rationalization and therefore cannot switch semantic representatives.

A root-started path of the validated policy consequently projects to the
existing `ExtraAllowedPath`.  All path acceptance and parity results can then
be reused without duplicating their proofs.  The unvalidated policy appears
only as this proof-only weakening of the validated policy; it is never chosen
independently and is not an executable controller input.
-/

namespace DistributedSynthesis

universe u v w z

namespace SourceFreeBeliefCodeParityRationalPolicy

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- Monotonicity of a selected code-policy under weakening of move validity.
The finite run and its complete successor table are preserved definitionally.
-/
def weakenValid
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Strong Weak : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (hweak : ∀ code move, Strong code move → Weak code move)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Strong
      next) :
    SourceFreeBeliefCodeParityRationalPolicy D initialCode Weak next where
  run := policy.run
  accepts := by
    constructor
    · constructor
      · exact policy.accepts.1.1
      · intro node
        have hlegal := policy.accepts.1.2 node
        change ∃ move, Strong (policy.run node).1 move ∧
          ∀ direction,
            (fun b ↦ policy.run (node ++ [b])) direction =
              (next (policy.run node).1 move direction,
                D.step (policy.run node).2
                  (next (policy.run node).1 move direction)) at hlegal
        rcases hlegal with ⟨move, hstrong, hchildren⟩
        change ∃ move, Weak (policy.run node).1 move ∧
          ∀ direction,
            (fun b ↦ policy.run (node ++ [b])) direction =
              (next (policy.run node).1 move direction,
                D.step (policy.run node).2
                  (next (policy.run node).1 move direction))
        exact ⟨move, hweak _ _ hstrong, hchildren⟩
    · exact policy.accepts.2
  successor := policy.successor
  successor_at := policy.successor_at
  legal_at := by
    intro node
    have hlegal := policy.legal_at node
    change ∃ move, Strong (policy.run node).1 move ∧
      ∀ direction,
        policy.successor (policy.run node) direction =
          (next (policy.run node).1 move direction,
            D.step (policy.run node).2
              (next (policy.run node).1 move direction)) at hlegal
    rcases hlegal with ⟨move, hstrong, hchildren⟩
    change ∃ move, Weak (policy.run node).1 move ∧
      ∀ direction,
        policy.successor (policy.run node) direction =
          (next (policy.run node).1 move direction,
            D.step (policy.run node).2
              (next (policy.run node).1 move direction))
    exact ⟨move, hweak _ _ hstrong, hchildren⟩

@[simp] theorem weakenValid_run
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Strong Weak : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (hweak : ∀ code move, Strong code move → Weak code move)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Strong
      next) (node : TreeNode Direction) :
    (weakenValid D initialCode Strong Weak next hweak policy).run node =
      policy.run node :=
  rfl

@[simp] theorem weakenValid_successor
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Strong Weak : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (hweak : ∀ code move, Strong code move → Weak code move)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Strong
      next) (state) (direction) :
    (weakenValid D initialCode Strong Weak next hweak policy).successor state
        direction =
      policy.successor state direction :=
  rfl

end SourceFreeBeliefCodeParityRationalPolicy

universe x y s b

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

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

variable {Extra : Type b} [Fintype Extra]

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev ValidatedPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (ExtraValid : HybridState A strategy → Extra → Prop)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy A
    strategy hwin initial initialExtra ExtraValid extraAdvance

private abbrev ExtraPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy hwin
    initial initialExtra extraAdvance

/-! ## The proof-only policy weakening -/

/-- Drop current-extra validity from one already selected validated policy.
The run and transition table are unchanged. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy.toExtraPolicy
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ValidatedPolicy A strategy hwin initial initialExtra ExtraValid
      extraAdvance) :
    ExtraPolicy A strategy hwin initial initialExtra extraAdvance := by
  refine SourceFreeBeliefCodeParityRationalPolicy.weakenValid
    (sourceFreeBeliefParentLinkedCodeParityDPA
      (Annotation :=
        ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra)
      (profiledRawJointHybridCodeParityDPA A
        (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
          A))))
    ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
      profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
        strategy hwin ExtraValid extraAdvance))
    (sourceFreeBeliefParentLinkedValid
      (ProfiledRawJointHybridProvenanceValid A strategy)
      (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A strategy
        hwin extraAdvance))
    (sourceFreeBeliefFiniteCodeNext
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
    ?_ policy
  intro code move hstrong
  rcases hstrong with ⟨hprovenance, hlink⟩
  refine ⟨hprovenance, ?_⟩
  rcases hlink with
    ⟨source, hcode, hmove, hphysical, _hextra, hchildren⟩
  exact ⟨source, hcode, hmove, hphysical, hchildren⟩

@[simp] theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy.toExtraPolicy_run
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ValidatedPolicy A strategy hwin initial initialExtra ExtraValid
      extraAdvance) (node : TreeNode
        (SourceFreeBeliefParentLinkedCode
          (BeliefCode := ProfiledRawJointHybridCode A)
          (Annotation :=
            ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
              Extra))) :
    (policy.toExtraPolicy A strategy hwin).run node = policy.run node :=
  by
    simp only [toExtraPolicy,
      SourceFreeBeliefCodeParityRationalPolicy.weakenValid_run]

@[simp] theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraRationalPolicy.toExtraPolicy_successor
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ValidatedPolicy A strategy hwin initial initialExtra ExtraValid
      extraAdvance) (state) (childCode) :
    (policy.toExtraPolicy A strategy hwin).successor state childCode =
      policy.successor state childCode :=
  by
    simp only [toExtraPolicy,
      SourceFreeBeliefCodeParityRationalPolicy.weakenValid_successor]

/-! ## Validated paths and projection to the existing acceptance endpoint -/

/-- A root-started path through one validated policy.  Allowed edges are
still its finite child-code image; no semantic witness is reselected here. -/
structure ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {ExtraValid : HybridState A strategy → Extra → Prop}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ValidatedPolicy A strategy hwin initial initialExtra ExtraValid
      extraAdvance) where
  state : Nat →
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraPolicyState A
      strategy hwin initial initialExtra ExtraValid extraAdvance
  initial_state : state 0 = policy.run []
  allowed : ∀ n : Nat, ∃ childCode :
      SourceFreeBeliefParentLinkedCode
        (BeliefCode := ProfiledRawJointHybridCode A)
        (Annotation :=
          ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra),
    policy.successor (state n) childCode = state (n + 1)

namespace
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {initialExtra : Extra}
variable {ExtraValid : HybridState A strategy → Extra → Prop}
variable {extraAdvance : HybridState A strategy → Extra →
  HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
variable {policy : ValidatedPolicy A strategy hwin initial initialExtra
  ExtraValid extraAdvance}

/-- The same states and child-code witnesses form a path of the proof-only
weakened policy. -/
noncomputable def toExtraAllowedPath
    (path :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A
        strategy hwin policy) :
    ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A strategy hwin
      (policy.toExtraPolicy A strategy hwin) where
  state := path.state
  initial_state := by simpa using path.initial_state
  allowed := fun n ↦ by
    rcases path.allowed n with ⟨childCode, hchild⟩
    exact ⟨childCode, by simpa using hchild⟩

/-- Acceptance is inherited from the existing one-policy anti-mosaic theorem.
The old policy is not selected independently: it is the literal weakening of
`policy` above. -/
theorem bareCodeWord_accepts
    (path :
      ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A
        strategy hwin policy) :
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A))).Accepts
      ((path.toExtraAllowedPath A strategy hwin).bareCodeWord A strategy
        hwin) :=
  (path.toExtraAllowedPath A strategy hwin).bareCodeWord_accepts A strategy
    hwin

end
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath

end

end DetParityAutomaton

end DistributedSynthesis
