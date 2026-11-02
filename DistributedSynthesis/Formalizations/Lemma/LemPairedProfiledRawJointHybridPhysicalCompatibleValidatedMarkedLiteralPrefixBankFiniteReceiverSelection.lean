/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteReceiverResolution
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetHandoff

/-!
# Selecting one finite marked-bank receiver resolution

The receiver resolver stores all finite same-bank successors with the emitted
public target.  This file proves the exact *policy-layer* fact about an
arbitrary member: it expands to a genuine raw direction of the current
validated move, carries the marked child annotation of that direction, and
is an allowed reachable edge of the same fixed rational policy.

This is deliberately not claimed to identify the actual receiver-control
path that emitted a bare target.  Bare-target equality forgets the literal
row and parent-linked annotation, and therefore cannot justify installing an
arbitrary candidate in the physical controller.  The operational consumer
must instead narrow an exact activation with the finite next `BankControl`
already linked into its row-exact target.  The selectors below remain useful
for policy/path reasoning and make the exact limitation explicit.
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
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev BankPolicyState
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world

private abbrev BankReachable
    (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PublicTarget :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))

private abbrev ResolutionAt
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (next : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
    A strategy hwin state target next

/-! ## Every finite candidate is one exact raw child -/

/-- The raw representative selected by the finite-code rationalization for
one resolution witness. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.direction
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  sourceFreeBeliefRawDirectionOfChildCode
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    state.2.1 packet.move resolution.childCode

/-- A resolution's requested finite tag and its selected raw direction have
the same normalized child code. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.childCode_eq_finiteNext
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable) =
      sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
        state.2.1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin state.1 state.2 hreachable).move
        resolution.childCode := by
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
      A strategy hwin state hreachable]
  rfl

/-- Arbitrary candidate selection is exact inside the rational policy: every
resolution is the successor along one genuine raw direction of the current
validated move.  It does not assert that this direction is the receiver path
that emitted the bare target. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.successor_eq_direction
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    next =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
        strategy hwin state
          (state.childCode A strategy hwin
            (resolution.direction A strategy hwin hreachable)) := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  let direction := resolution.direction A strategy hwin hreachable
  let normalized := sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    state.2.1 packet.move resolution.childCode
  have hrequested := packet.successor resolution.childCode
  have hnormalized := packet.successor normalized
  have hidempotent :
      sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
          state.2.1 packet.move normalized = normalized := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      state.2.1 packet.move direction
  rw [hidempotent] at hnormalized
  have hpolicy :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
          hwin state.1).successor state.2 resolution.childCode =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A
          strategy hwin state.1).successor state.2 normalized :=
    hrequested.trans hnormalized.symm
  have hbank :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state resolution.childCode =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin direction) := by
    have hpolicy' :
        (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
            hwin state.1).successor state.2 resolution.childCode =
          (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A
            strategy hwin state.1).successor state.2
              (state.childCode A strategy hwin direction) := by
      rw [resolution.childCode_eq_finiteNext A strategy hwin hreachable]
      exact hpolicy
    exact congrArg
      (fun policyState : BankPolicyState A strategy hwin state.1 ↦
        (⟨state.1, policyState⟩ : BankControl A strategy hwin)) hpolicy'
  exact resolution.successor.trans hbank

/-- The exact reconstructed child has the public target emitted by the
receiver table. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.direction_publicTarget
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    (state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable)).1 =
      .oneSided target := by
  have hcode :=
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
      A strategy hwin state hreachable
        (resolution.direction A strategy hwin hreachable)
  have hnext := resolution.successor_eq_direction A strategy hwin hreachable
  calc
    (state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable)).1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin
              (resolution.direction A strategy hwin hreachable))).2.1.1 :=
      congrArg Prod.fst hcode.symm
    _ = next.2.1.1 := by rw [← hnext]
    _ = .oneSided target := resolution.publicTarget

/-- The selected candidate's stored literal record is exactly the marked
literal advance of its reconstructed raw direction. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.literal_eq_direction
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable
    next.literal A strategy hwin =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source (state.literal A strategy hwin)
          (resolution.direction A strategy hwin hreachable) := by
  dsimp only
  have hnext := resolution.successor_eq_direction A strategy hwin hreachable
  calc
    next.literal A strategy hwin =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin
              (resolution.direction A strategy hwin hreachable))).literal A
                strategy hwin :=
      congrArg
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.literal
          A strategy hwin) hnext
    _ = _ :=
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_literal
        A strategy hwin state hreachable
          (resolution.direction A strategy hwin hreachable)

/-- A reachable resolution is an actual one-edge extension of a root-started
finite-code path in the same fixed bank entry. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.exists_path_edge
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution : ResolutionAt A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    ∃ node : List (LinkedCode A),
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
          hwin state.1).run node = state.2 ∧
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state resolution.childCode = next := by
  rcases hreachable with ⟨node, hnode⟩
  exact ⟨node, hnode, resolution.successor.symm⟩

/-! ## Deterministic finite choice -/

/-- Total deterministic selector.  The current state is used only on an
empty target set; live receiver cells are accompanied by a nonemptiness proof
below, so that fallback is unreachable in executions. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice
    (state : BankControl A strategy hwin) (target : PublicTarget A) :
    BankControl A strategy hwin := by
  classical
  let candidates :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
      strategy hwin state target
  exact if h : candidates.Nonempty then h.choose else state

/-- On a nonempty target set the deterministic selector is one of its
members. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice_mem
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target).Nonempty) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
          strategy hwin state target ∈
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target := by
  classical
  simp only
    [profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice]
  split
  · exact hnonempty.choose_spec
  · contradiction

/-- A real raw direction reporting this public target proves that the finite
selector's target set is nonempty. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates_nonempty_of_direction
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (target : PublicTarget A)
    (hpublic : (state.childCode A strategy hwin direction).1 =
      .oneSided target) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
      strategy hwin state target).Nonempty :=
  ⟨_, state.advance_mem_targetCandidates A strategy hwin hreachable direction
    target hpublic⟩

/-- Any selected live target carries an exact resolution witness. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoiceResolution
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target).Nonempty) :
    ResolutionAt A strategy hwin state target
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
        strategy hwin state target) :=
  Classical.choice
    ((mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates_iff
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
          strategy hwin state target) target).mp
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice_mem A
        strategy hwin state target hnonempty))

/-- The arbitrary deterministic choice preserves the reachable invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice_reachable
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (target : PublicTarget A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target).Nonempty) :
    BankReachable A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
        strategy hwin state target) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoiceResolution
    A strategy hwin state target hnonempty).reachable A strategy hwin
      hreachable

/-- The selector remains in the same fixed bank entry. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice_index
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target).Nonempty) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
      strategy hwin state target).1 = state.1 :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoiceResolution
    A strategy hwin state target hnonempty).same_index A strategy hwin

/-- The selector's public code is exactly the receiver's emitted target. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice_publicTarget
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target).Nonempty) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoice A
      strategy hwin state target).2.1.1 = .oneSided target :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetChoiceResolution
    A strategy hwin state target hnonempty).publicTarget

/-! ## Mode-aware public-code resolution

The one-sided resolver above is the strict-close specialization.  A
simultaneous close is different: its two endpoint targets are intentionally
different, and their ordered merge is the common child.  The common and
strict cases are therefore unified below at the finite hybrid-code boundary.
-/

/-- One finite same-bank successor whose complete public hybrid code is
`publicCode`.  This covers both `.oneSided target` and
`.common (profiledRawJointBothTargetMerge ...)`. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (next : BankControl A strategy hwin) where
  childCode : LinkedCode A
  successor : next =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin state childCode
  publicCode_eq : next.2.1.1 = publicCode

private abbrev CodeResolutionAt
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (next : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt A
    strategy hwin state publicCode next

/-- Exact finite materialization of all successors with one complete public
hybrid code. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A) :
    Finset (BankControl A strategy hwin) := by
  classical
  exact Finset.univ.filter fun next ↦
    Nonempty (CodeResolutionAt A strategy hwin state publicCode next)

theorem
    mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_iff
    (state next : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A) :
    next ∈
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
          strategy hwin state publicCode ↔
      Nonempty (CodeResolutionAt A strategy hwin state publicCode next) := by
  classical
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates]

/-- The old strict resolver is definitionally characterized by the generic
resolver at `.oneSided target`. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_oneSided
    (state : BankControl A strategy hwin) (target : PublicTarget A) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state (.oneSided target) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target := by
  classical
  ext next
  rw [mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_iff,
    mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates_iff]
  constructor
  · rintro ⟨resolution⟩
    exact ⟨
      { childCode := resolution.childCode
        successor := resolution.successor
        publicTarget := resolution.publicCode_eq }⟩
  · rintro ⟨resolution⟩
    exact ⟨
      { childCode := resolution.childCode
        successor := resolution.successor
        publicCode_eq := resolution.publicTarget }⟩

/-- A strict close uses its one-sided incidence target as complete public
code. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankStrictPublicCode
    (target : PublicTarget A) : ProfiledRawJointHybridCode A :=
  .oneSided target

/-- A simultaneous close uses the ordered merge of the right-block target
and left-block target as complete public common code. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankBothPublicCode
    (input : In₁ × In₂) (rightTarget leftTarget : PublicTarget A) :
    ProfiledRawJointHybridCode A :=
  .common (profiledRawJointBothTargetMerge A input rightTarget leftTarget)

/-- Generic raw representative selected for one mode-aware resolution. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.direction
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  sourceFreeBeliefRawDirectionOfChildCode
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    state.2.1 packet.move resolution.childCode

theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.childCode_eq_finiteNext
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable) =
      sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
        state.2.1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin state.1 state.2 hreachable).move
        resolution.childCode := by
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
      A strategy hwin state hreachable]
  rfl

/-- Every mode-aware candidate is the exact successor along one raw direction
of the current validated move, at the policy layer only. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.successor_eq_direction
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    next =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
        strategy hwin state
          (state.childCode A strategy hwin
            (resolution.direction A strategy hwin hreachable)) := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  let direction := resolution.direction A strategy hwin hreachable
  let normalized := sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    state.2.1 packet.move resolution.childCode
  have hrequested := packet.successor resolution.childCode
  have hnormalized := packet.successor normalized
  have hidempotent :
      sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
          state.2.1 packet.move normalized = normalized := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      state.2.1 packet.move direction
  rw [hidempotent] at hnormalized
  have hpolicy :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
          hwin state.1).successor state.2 resolution.childCode =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A
          strategy hwin state.1).successor state.2 normalized :=
    hrequested.trans hnormalized.symm
  have hpolicy' :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
          hwin state.1).successor state.2 resolution.childCode =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A
          strategy hwin state.1).successor state.2
            (state.childCode A strategy hwin direction) := by
    rw [resolution.childCode_eq_finiteNext A strategy hwin hreachable]
    exact hpolicy
  have hbank :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state resolution.childCode =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin direction) :=
    congrArg
      (fun policyState : BankPolicyState A strategy hwin state.1 ↦
        (⟨state.1, policyState⟩ : BankControl A strategy hwin)) hpolicy'
  exact resolution.successor.trans hbank

/-- Exact public-code equation of the reconstructed raw child. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.direction_publicCode
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    (state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable)).1 = publicCode := by
  have hcode :=
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
      A strategy hwin state hreachable
        (resolution.direction A strategy hwin hreachable)
  have hnext := resolution.successor_eq_direction A strategy hwin hreachable
  calc
    (state.childCode A strategy hwin
        (resolution.direction A strategy hwin hreachable)).1 =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin
              (resolution.direction A strategy hwin hreachable))).2.1.1 :=
      congrArg Prod.fst hcode.symm
    _ = next.2.1.1 := by rw [← hnext]
    _ = publicCode := resolution.publicCode_eq

/-- Exact marked literal record of an arbitrary mode-aware candidate. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.literal_eq_direction
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable
    next.literal A strategy hwin =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source (state.literal A strategy hwin)
          (resolution.direction A strategy hwin hreachable) := by
  dsimp only
  have hnext := resolution.successor_eq_direction A strategy hwin hreachable
  calc
    next.literal A strategy hwin =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state
            (state.childCode A strategy hwin
              (resolution.direction A strategy hwin hreachable))).literal A
                strategy hwin :=
      congrArg
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.literal
          A strategy hwin) hnext
    _ = _ :=
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_literal
        A strategy hwin state hreachable
          (resolution.direction A strategy hwin hreachable)

/-- Generic resolution preserves the fixed bank index. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.same_index
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next) :
    next.1 = state.1 := by
  rw [resolution.successor]
  rfl

/-- Generic resolution preserves reachability. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeResolutionAt.reachable
    {state next : BankControl A strategy hwin}
    {publicCode : ProfiledRawJointHybridCode A}
    (resolution : CodeResolutionAt A strategy hwin state publicCode next)
    (hreachable : BankReachable A strategy hwin state) :
    BankReachable A strategy hwin next := by
  rw [resolution.successor]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_reachable A
      strategy hwin state hreachable resolution.childCode

/-- Every genuine raw child makes its complete mode-aware target set
nonempty.  This is used for strict children with `.oneSided` and simultaneous
children with `.common` alike. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_nonempty_of_direction
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (publicCode : ProfiledRawJointHybridCode A)
    (hpublic : (state.childCode A strategy hwin direction).1 = publicCode) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
      strategy hwin state publicCode).Nonempty := by
  let next :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin state (state.childCode A strategy hwin direction)
  refine ⟨next, ?_⟩
  rw [mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_iff]
  refine ⟨
    { childCode := state.childCode A strategy hwin direction
      successor := rfl
      publicCode_eq := ?_ }⟩
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
    A strategy hwin state hreachable direction]
  exact hpublic

/-- Total deterministic selector for both public modes. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A) :
    BankControl A strategy hwin := by
  classical
  let candidates :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
      strategy hwin state publicCode
  exact if h : candidates.Nonempty then h.choose else state

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice_mem
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode).Nonempty) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A strategy
          hwin state publicCode ∈
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode := by
  classical
  simp only
    [profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice]
  split
  · exact hnonempty.choose_spec
  · contradiction

/-- Resolution witness selected by the generic deterministic choice. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoiceResolution
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode).Nonempty) :
    CodeResolutionAt A strategy hwin state publicCode
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A
        strategy hwin state publicCode) :=
  Classical.choice
    ((mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates_iff
      A strategy hwin state
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A
          strategy hwin state publicCode) publicCode).mp
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice_mem A
        strategy hwin state publicCode hnonempty))

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice_reachable
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (publicCode : ProfiledRawJointHybridCode A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode).Nonempty) :
    BankReachable A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A
        strategy hwin state publicCode) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoiceResolution A
    strategy hwin state publicCode hnonempty).reachable A strategy hwin
      hreachable

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice_index
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode).Nonempty) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A
      strategy hwin state publicCode).1 = state.1 :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoiceResolution A
    strategy hwin state publicCode hnonempty).same_index A strategy hwin

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice_publicCode
    (state : BankControl A strategy hwin)
    (publicCode : ProfiledRawJointHybridCode A)
    (hnonempty :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeCandidates A
        strategy hwin state publicCode).Nonempty) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoice A
      strategy hwin state publicCode).2.1.1 = publicCode :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankCodeChoiceResolution A
    strategy hwin state publicCode hnonempty).publicCode_eq

end

end DetParityAutomaton

end DistributedSynthesis
