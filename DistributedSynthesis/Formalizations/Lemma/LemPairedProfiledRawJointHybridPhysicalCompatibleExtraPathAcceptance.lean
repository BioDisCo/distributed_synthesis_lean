/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleExtraAnnotation
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodePolicyImage

/-!
# Paths in one jointly annotated physical-compatible policy

This file is the policy-level anti-mosaic endpoint for an arbitrary finite
extra annotation.  An allowed target is a successor of one fixed joint
`PhysicalCompatibleExtraRationalPolicy`; a path may choose such targets
relationally, but it never changes that policy.

The complete state is retained.  In particular, its second projection is the
actual linked-DPA control, not a control reconstructed from a separately
rationalized policy.  Along every root-started allowed path this control is
exactly the run of the original hybrid code DPA on the positive-time bare-code
word.  Consequently that bare-code word is accepted.

No runtime direction, hierarchy side, strict-leader bit, or cross-selection
hypothesis occurs in this interface.
-/

namespace DistributedSynthesis

universe u v x y s b

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

variable {Extra : Type b} [Fintype Extra]

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev ExtraAnnotation :=
  ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A Extra

private abbrev ExtraLinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation := ExtraAnnotation A (Extra := Extra))

private noncomputable abbrev BareDPA
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  profiledRawJointHybridCodeParityDPA A
    (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A))

private noncomputable abbrev LinkedDPA
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := ExtraAnnotation A (Extra := Extra))
    (BareDPA A strategy initial)

private abbrev ExtraPolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraRationalPolicy A strategy hwin
    initial initialExtra extraAdvance

private abbrev ExtraState
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra) :=
  ProfiledRawJointHybridPhysicalCompatibleExtraPolicyState A strategy hwin
    initial initialExtra extraAdvance

/-! ## One-policy allowed targets -/

/-- A target is allowed when it is one finite child-code response of the
same jointly annotated rational policy. -/
def ProfiledRawJointHybridPhysicalCompatibleExtraAllowedTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance)
    (source target :
      ExtraState A strategy hwin initial initialExtra extraAdvance) : Prop :=
  ∃ childCode : ExtraLinkedCode A (Extra := Extra),
    policy.successor source childCode = target

/-- Allowed edges preserve reachability in the very same rational policy. -/
theorem
    profiledRawJointHybridPhysicalCompatibleExtra_reachable_of_allowedTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance)
    {source target :
      ExtraState A strategy hwin initial initialExtra extraAdvance}
    (hsource :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy source)
    (hedge :
      ProfiledRawJointHybridPhysicalCompatibleExtraAllowedTarget A strategy
        hwin initial initialExtra extraAdvance policy source target) :
    ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
      initial initialExtra extraAdvance policy target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hedge with ⟨childCode, hchild⟩
  refine ⟨node ++ [childCode], ?_⟩
  rw [← policy.successor_at node childCode, hnode, hchild]

/-- At a reachable source, an allowed edge advances the actual retained
control by the bare code stored in its target.  This exposes explicitly that
the relational interface neither resets nor reconstructs the DPA state. -/
theorem
    profiledRawJointHybridPhysicalCompatibleExtra_allowedTarget_control_eq_step
    (initial : ProfiledRawJointCommonBaseWorld A strategy)
    (initialExtra : Extra)
    (extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra)
    (policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance)
    {source target :
      ExtraState A strategy hwin initial initialExtra extraAdvance}
    (hsource :
      ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
        initial initialExtra extraAdvance policy source)
    (hedge :
      ProfiledRawJointHybridPhysicalCompatibleExtraAllowedTarget A strategy
        hwin initial initialExtra extraAdvance policy source target) :
    target.2 =
      (BareDPA A strategy initial).step source.2 target.1.1 := by
  rcases hedge with ⟨childCode, hchild⟩
  obtain ⟨move, _hvalid, hsuccessor⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (LinkedDPA A strategy (Extra := Extra) initial)
      ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A)),
        profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A
          strategy hwin extraAdvance))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
      policy source hsource
  rw [← hchild, hsuccessor childCode]
  rfl

/-! ## Root-started allowed paths -/

/-- A coherent infinite path through the image of one joint policy.  The
whole jointly annotated state is kept at every time. -/
structure ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {initialExtra : Extra}
    {extraAdvance : HybridState A strategy → Extra →
      HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
    (policy : ExtraPolicy A strategy hwin initial initialExtra extraAdvance)
    where
  state : Nat →
    ExtraState A strategy hwin initial initialExtra extraAdvance
  initial_state : state 0 = policy.run []
  allowed : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleExtraAllowedTarget A strategy hwin
      initial initialExtra extraAdvance policy (state n) (state (n + 1))

namespace ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {initialExtra : Extra}
variable {extraAdvance : HybridState A strategy → Extra →
  HybridDirection (In₁ := In₁) (In₂ := In₂) → Extra}
variable {policy : ExtraPolicy A strategy hwin initial initialExtra
  extraAdvance}

/-- A chosen finite child-code witness for each relational allowed edge. -/
noncomputable def childCode
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) (n : Nat) : ExtraLinkedCode A (Extra := Extra) :=
  Classical.choose (path.allowed n)

theorem successor_childCode
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) (n : Nat) :
    path.state (n + 1) =
      policy.successor (path.state n) (path.childCode A strategy hwin n) := by
  exact (Classical.choose_spec (path.allowed n)).symm

/-- The generic code-policy path carried by the relational interface. -/
noncomputable def toCodePolicyPath
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) :
    SourceFreeBeliefCodeParityPolicyPath
      (LinkedDPA A strategy (Extra := Extra) initial)
      ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
        profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A
          strategy hwin extraAdvance))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
      policy :=
  { state := path.state
    direction := path.childCode A strategy hwin
    initial := path.initial_state
    successor := path.successor_childCode A strategy hwin }

/-- Positive-time word of complete linked codes, including the joint
annotation. -/
def linkedCodeWord
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) : OmegaWord (ExtraLinkedCode A (Extra := Extra)) :=
  fun n ↦ (path.state (n + 1)).1

/-- Positive-time word after erasing both finite annotations. -/
def bareCodeWord
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) : OmegaWord (ProfiledRawJointHybridCode A) :=
  fun n ↦ (path.state (n + 1)).1.1

@[simp] theorem linkedCodeWord_fst
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) :
    OmegaWord.map Prod.fst (path.linkedCodeWord A strategy hwin) =
      path.bareCodeWord A strategy hwin := by
  rfl

/-- Every path state remains reachable in the one selected joint policy. -/
theorem reachable
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) : ∀ n,
    ProfiledRawJointHybridPhysicalCompatibleExtraReachable A strategy hwin
      initial initialExtra extraAdvance policy (path.state n) := by
  intro n
  induction n with
  | zero =>
      refine ⟨[], ?_⟩
      exact path.initial_state.symm
  | succ n ih =>
      exact
        profiledRawJointHybridPhysicalCompatibleExtra_reachable_of_allowedTarget
          A strategy hwin initial initialExtra extraAdvance policy ih
            (path.allowed n)

/-- The retained control is literally the linked-DPA run on the complete
positive-time linked-code word. -/
theorem linkedControl_eq_run
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) (n : Nat) :
    (path.state n).2 =
      (LinkedDPA A strategy (Extra := Extra) initial).run
        (path.linkedCodeWord A strategy hwin) n := by
  simpa only [toCodePolicyPath, linkedCodeWord,
    SourceFreeBeliefCodeParityPolicyPath.childCodeWord] using
    (path.toCodePolicyPath A strategy hwin).control_eq_run
      (LinkedDPA A strategy (Extra := Extra) initial)
      ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A)),
        profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A
          strategy hwin extraAdvance))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
      policy n

/-- After erasing the annotations, the very same retained control is the run
of the original hybrid code DPA.  There is no reset or reconstructed monitor
state at a path boundary. -/
theorem bareControl_eq_run
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) (n : Nat) :
    (path.state n).2 =
      (BareDPA A strategy initial).run
        (path.bareCodeWord A strategy hwin) n := by
  rw [path.linkedControl_eq_run A strategy hwin n]
  change
    ((BareDPA A strategy initial).comap Prod.fst).run
        (path.linkedCodeWord A strategy hwin) n = _
  rw [DetParityAutomaton.comap_run]
  rw [path.linkedCodeWord_fst A strategy hwin]

/-- Each adjacent edge therefore advances the actual retained DPA state by
the bare code stored at its target. -/
theorem target_control_eq_step
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) (n : Nat) :
    (path.state (n + 1)).2 =
      (BareDPA A strategy initial).step (path.state n).2
        (path.state (n + 1)).1.1 := by
  rw [path.bareControl_eq_run A strategy hwin (n + 1),
    (BareDPA A strategy initial).run_succ,
    ← path.bareControl_eq_run A strategy hwin n]
  rfl

/-- The positive-time bare-code word of every root-started path through the
one jointly annotated policy is accepted by the original hybrid code DPA. -/
theorem bareCodeWord_accepts
    (path : ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath A
      strategy hwin policy) :
    (BareDPA A strategy initial).Accepts
      (path.bareCodeWord A strategy hwin) := by
  have hlinked :=
    (path.toCodePolicyPath A strategy hwin).accepts
      (LinkedDPA A strategy (Extra := Extra) initial)
      ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode
        A)),
        profiledRawJointHybridPhysicalCompatibleExtraInitial A initialExtra)
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleExtraParentLinkValid A
          strategy hwin extraAdvance))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
      policy
  change ((BareDPA A strategy initial).comap Prod.fst).Accepts _ at hlinked
  rw [DetParityAutomaton.comap_accepts_iff] at hlinked
  simpa only [toCodePolicyPath, linkedCodeWord, bareCodeWord,
    SourceFreeBeliefCodeParityPolicyPath.childCodeWord] using hlinked

end ProfiledRawJointHybridPhysicalCompatibleExtraAllowedPath

end

end DetParityAutomaton

end DistributedSynthesis
