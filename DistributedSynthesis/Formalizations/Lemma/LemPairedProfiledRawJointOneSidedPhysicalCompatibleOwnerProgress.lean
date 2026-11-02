/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleExactEffectOwnerTrace
import DistributedSynthesis.Formalizations.Lemma.LemSharedParityProgress

/-!
# A replacement-aware local acceptance certificate for the owner kernel

The invariant below checks the actual kernel step and actual objective-DPA
coordinate. Its single rank family applies to all three graph directions,
including direct reversals and close/reopen transitions. Thus acceptance does
not require equality with an execution of the original strategy, nor a
forward-only path through semantic bank parents.

Soundness is valid for arbitrary bank memory and well-founded rank orders.
The certificate is proof-side: none of its information is added to the
endpoint controllers. Constructing such a certificate from `hwin` for a
jointly chosen replacement remains a separate mathematical obligation.
-/

namespace DistributedSynthesis

universe u v x y s m r

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
variable (A : DetParityAutomaton.{max u v x y, s}
  (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

namespace ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable (tables :
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy)

/-- Decoder closure and a single parity rank certificate on the invariant's
actual transitions. There is no finiteness assumption on either memory or
the proof-side ranks. -/
structure OwnerProgressInvariant (Rank : Type r) [LinearOrder Rank] where
  holds : LiveState (Memory := Memory) A strategy → Prop
  decodes : ∀ live, holds live →
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy live.1.1 live.1.2
  step : ∀ live, holds live → ∀ direction : Direction (In₁ := In₁) (In₂ := In₂),
    holds (tables.ownerFibreSafetyLiveStep A strategy hwin live direction)
  progress : SharedParityProgress A Prod.snd
    (fun source target ↦ holds source ∧
      ∃ direction : Direction (In₁ := In₁) (In₂ := In₂),
        target = tables.ownerFibreSafetyLiveStep A strategy hwin source direction)
    Rank

variable {Rank : Type r} [LinearOrder Rank] [WellFoundedLT Rank]

omit [WellFoundedLT Rank] in
theorem OwnerProgressInvariant.holds_stateAt
    (certificate : tables.OwnerProgressInvariant A strategy hwin Rank)
    (initial : LiveState (Memory := Memory) A strategy)
    (hinitial : certificate.holds initial)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    certificate.holds
      (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial node) := by
  induction node using List.reverseRecOn with
  | nil => exact hinitial
  | append_singleton node direction ih =>
    rw [tables.ownerFibreSafetyLiveStateAt_append A strategy hwin]
    exact certificate.step _ ih direction

/-- The shared certificate accepts every literal output word of the owner
kernel, including branches with infinitely many direct reversals. -/
theorem OwnerProgressInvariant.accepts_word
    (certificate : tables.OwnerProgressInvariant A strategy hwin Rank)
    (initial : LiveState (Memory := Memory) A strategy)
    (hinitial : certificate.holds initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    A.AcceptsFrom initial.2
      (tables.ownerFibreSafetyWord A strategy hwin initial branch) := by
  let path := fun n ↦ tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
    (branchNode branch n)
  apply certificate.progress.acceptsFrom path ?_ initial.2
    (tables.ownerFibreSafetyWord A strategy hwin initial branch)
    (tables.ownerFibreSafetyLiveStateAt_dpa A strategy hwin initial branch)
  intro n
  refine ⟨certificate.holds_stateAt A strategy hwin tables initial hinitial _,
    branch n, ?_⟩
  exact tables.ownerFibreSafetyLiveStateAt_append A strategy hwin initial
    (branchNode branch n) (branch n)

/-- Decoder closure and the replacement-aware progress proof together close
the guarded raw-table verifier. -/
theorem OwnerProgressInvariant.ownerFibreSafe
    (certificate : tables.OwnerProgressInvariant A strategy hwin Rank)
    (initial : LiveState (Memory := Memory) A strategy)
    (hinitial : certificate.holds initial) :
    tables.OwnerFibreSafe A strategy hwin (some initial) := by
  apply (tables.ownerFibreSafe_iff_exists_live_decodes_and_acceptsFrom
    A strategy hwin (some initial)).mpr
  refine ⟨initial, rfl, ?_, ?_⟩
  · intro branch n
    exact certificate.decodes _
      (certificate.holds_stateAt A strategy hwin tables initial hinitial _)
  · exact certificate.accepts_word A strategy hwin tables initial hinitial

end ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

namespace ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-- A replacement-aware invariant covering all honest entries is enough to
finish all three exact-table checks. This is a soundness theorem, not a claim
that `hwin` has already supplied that invariant. -/
theorem exactEffectTable_effectEnrichedChecksUnrestricted_of_ownerProgress
    {Rank : Type r} [LinearOrder Rank] [WellFoundedLT Rank]
    (key : ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy)
    (certificate : ((exactEffectTable A strategy hwin key).family A strategy key
      ).OwnerProgressInvariant A strategy hwin Rank)
    (hentry : ∀ context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy key,
      ∀ live,
        ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key (exactEffectTable A strategy hwin key)
          context = some live → certificate.holds live) :
    EffectEnrichedChecksUnrestricted A strategy hwin
      (exactInitialMemory A strategy) key (exactEffectTable A strategy hwin key) := by
  apply (exactEffectTable_effectEnrichedChecksUnrestricted_iff_ownerSafe
    A strategy hwin key).mpr
  intro context
  obtain ⟨live, hinitial, _⟩ :=
    exactEffectTable_ownerFibreInitialState_live_decodes A strategy hwin key context
  rw [hinitial]
  exact certificate.ownerFibreSafe A strategy hwin _ live
    (hentry context live hinitial)

end ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

end DetParityAutomaton

end DistributedSynthesis
