/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedFixedPolicyTable
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Installing a code-policy move with semantic provenance

The weak indexed validity predicate checks only finite carrier and pattern
conditions.  Consequently a rational policy extracted with that predicate
need not choose a move which is the public move of any semantic point.  This
file records the minimal repair: rationalize the already available optional
fresh semantic tree with a validity predicate which also retains the
existence of a same-code, same-move semantic representative.

The witness remains proof-only.  The policy state and move alphabets are the
same finite types as before.  At every reachable policy state, the selected
move can then be installed in an optional controlled semantic point whose
descriptor has exactly the policy code, policy DPA control, and selected move.
The ordinary witnessed-table initial-candidate constructor therefore supplies
a source-aware candidate with those exact three coordinates.

No graph orientation, strict leader, lineage, or hidden bit is exposed to a
process.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Provenance-strengthened finite validity -/

/-- The weak finite validity together with one proof-side optional-fresh
semantic representative having exactly the advertised code and move. -/
def ProfiledOpenIndexedProvenanceValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  ProfiledOpenIndexedBiBeliefValid A code move ∧
    ∃ point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
        basis (I := I),
      point.state.code A strategy hwin basis = code ∧
        point.state.move A strategy hwin basis = move

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every optional-fresh semantic point supplies the strengthened validity
witness at its literal public node. -/
theorem profiledOpenIndexedProvenanceValid_of_point
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedProvenanceValid A strategy hwin basis
      (point.state.code A strategy hwin basis)
      (point.state.move A strategy hwin basis) := by
  exact ⟨ProfiledOpenIndexedCorrelatedSemanticState.valid A strategy hwin
      basis point.state, point, rfl, rfl⟩

/-! ## The optional-fresh code-policy tree -/

/-- The finite-tag semantic tree retaining optional fresh provenance and the
literal code-DPA control. -/
noncomputable def profiledOpenIndexedOptionalControlledFiniteTagSemanticTree
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedFiniteDirectionTag A (I := I))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I)) where
  Semantic := ProfiledOpenIndexedOptionalControlledSemanticState A strategy
    hwin basis (initial.state.code A strategy hwin basis)
  initial := profiledOpenIndexedOptionalControlledSemanticInitial A strategy
    hwin basis initial
  step := profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
    basis (initial.state.code A strategy hwin basis)
  code := fun point ↦ point.1.state.code A strategy hwin basis
  move := fun point ↦ point.1.state.move A strategy hwin basis

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The optional-fresh tree is a complete code-parity certificate for the
provenance-strengthened validity predicate. -/
theorem profiledOpenIndexedOptionalControlledFiniteTag_codeParityCertificate
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    let initialCode := initial.state.code A strategy hwin basis
    let raw :=
      profiledOpenIndexedOptionalControlledFiniteTagSemanticTree A strategy
        hwin basis initial
    SourceFreeBeliefCodeParityCertificate
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) raw := by
  let initialCode := initial.state.code A strategy hwin basis
  let raw := profiledOpenIndexedOptionalControlledFiniteTagSemanticTree A
    strategy hwin basis initial
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact profiledOpenIndexedProvenanceValid_of_point A strategy hwin basis
      (raw.stateAt node).1
  · intro node tag
    exact profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis
      (raw.stateAt node).1.state tag
  · intro branch
    simpa [raw, initialCode,
      profiledOpenIndexedOptionalControlledFiniteTagSemanticTree,
      SourceFreeBeliefSemanticTree.childCodeWord,
      SourceFreeBeliefSemanticTree.stateAt] using
        (profiledOpenIndexedOptionalControlledSemanticBranch_accepts A
          strategy hwin basis initial branch)

/-! ## Finite rational policy and installation -/

/-- The provenance-strengthened rational code policy.  Its runtime state and
move types are unchanged; only the proof predicate used at extraction is
stronger. -/
abbrev ProfiledOpenIndexedProvenanceCodeRationalPolicy
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A)

/-- Complete finite state of the strengthened policy. -/
abbrev ProfiledOpenIndexedProvenanceCodePolicyState
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A)).State

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The optional-fresh semantic certificate and the finite direction alphabet
produce a nonempty provenance-strengthened rational policy unconditionally. -/
theorem nonempty_profiledOpenIndexedProvenanceCodeRationalPolicy
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    Nonempty
      (ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin basis
        (initial.state.code A strategy hwin basis)) := by
  let initialCode := initial.state.code A strategy hwin basis
  let raw := profiledOpenIndexedOptionalControlledFiniteTagSemanticTree A
    strategy hwin basis initial
  apply SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (raw := raw)
  · exact
      profiledOpenIndexedOptionalControlledFiniteTag_codeParityCertificate A
        strategy hwin basis initial
  · exact InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _

/-- A move realizes a strengthened policy transition at one finite state. -/
def ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.MoveRealizesAt
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A)
    policy state move

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The strengthened policy starts at the literal code-DPA root. -/
theorem profiledOpenIndexedProvenanceCodePolicy_run_nil
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode) :
    policy.run [] =
      (initialCode,
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).initial) := by
  simpa [sourceFreeBeliefCodeParityRunAutomaton] using policy.accepts.1.1

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachability is closed under every policy successor. -/
theorem profiledOpenIndexedProvenanceCodePolicy_successor_reachable
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy state)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy
      (policy.successor state tag) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [tag], ?_⟩
  rw [← policy.successor_at node tag, hnode]

section
omit [Inhabited I]

/-- At every reachable strengthened-policy state, the selected move is the
literal move of an optional controlled semantic point with exactly the policy
code and control.  Its standard witnessed-table candidate is live and has
exactly that descriptor. -/
theorem exists_profiledOpenIndexedProvenanceCodePolicyInstalledCandidate
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy state) :
    ∃ move : ProfiledOpenIndexedBiBeliefMove A,
      ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode,
        ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
            basis initialCode policy state move ∧
          profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
              hwin basis initialCode point = (state, move) ∧
          let candidate :=
            profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin
              basis initialCode point
          candidate.2 = (state, move) ∧
            ProfiledOpenWitnessedTableBaseLive A strategy hwin basis
              initialCode candidate.2 candidate.1 := by
  obtain ⟨move, hmove⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A)
      policy state hreachable
  rcases hmove.1.2 with ⟨fresh, hcode, hsemanticMove⟩
  let point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode := (fresh, state.2)
  refine ⟨move, point, hmove, ?_, ?_, ?_⟩
  · apply Prod.ext
    · apply Prod.ext
      · exact hcode
      · rfl
    · exact hsemanticMove
  · apply Prod.ext
    · apply Prod.ext
      · exact hcode
      · rfl
    · exact hsemanticMove
  · exact profiledOpenActiveLaneWitnessedInitialCandidate_live A strategy
      hwin basis initialCode point

/-- Root-specialized installation.  This is the initial candidate required by
the policy-retagged relational table. -/
theorem exists_profiledOpenIndexedProvenanceCodePolicyInitialCandidate
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode) :
    ∃ move : ProfiledOpenIndexedBiBeliefMove A,
      ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode,
        ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
            basis initialCode policy (policy.run []) move ∧
          profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
              hwin basis initialCode point =
            ((initialCode,
                (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).initial),
              move) ∧
          let candidate :=
            profiledOpenActiveLaneWitnessedInitialCandidate A strategy hwin
              basis initialCode point
          candidate.2 =
              ((initialCode,
                  (profiledOpenIndexedBiBeliefCodeParityDPA A
                    initialCode).initial), move) ∧
            ProfiledOpenWitnessedTableBaseLive A strategy hwin basis
              initialCode candidate.2 candidate.1 := by
  obtain ⟨move, point, hmove, hdescriptor, hcandidate, hlive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInstalledCandidate A
      strategy hwin basis initialCode policy (policy.run []) ⟨[], rfl⟩
  have hroot := profiledOpenIndexedProvenanceCodePolicy_run_nil A strategy
    hwin basis initialCode policy
  refine ⟨move, point, hmove, ?_, ?_, hlive⟩
  · simpa [hroot] using hdescriptor
  · simpa [hroot] using hcandidate

/-- One policy step can immediately install the move selected at its
successor.  The successor descriptor is the literal policy successor, so its
code and control also satisfy the current realizing move's transition
equation. -/
theorem
    exists_profiledOpenIndexedProvenanceCodePolicySuccessorInstalledCandidate
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy state)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (hmove : ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
      hwin basis initialCode policy state move)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ∃ nextMove : ProfiledOpenIndexedBiBeliefMove A,
      ∃ point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
          hwin basis initialCode,
        ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin
            basis initialCode policy (policy.successor state tag) nextMove ∧
          profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
              hwin basis initialCode point =
            (policy.successor state tag, nextMove) ∧
          policy.successor state tag =
            (profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move tag,
              (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
                state.2
                (profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move
                  tag)) := by
  have hsuccessorReachable :=
    profiledOpenIndexedProvenanceCodePolicy_successor_reachable A strategy
      hwin basis initialCode policy state hreachable tag
  obtain ⟨nextMove, point, hnextMove, hdescriptor, _hcandidate, _hlive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInstalledCandidate A
      strategy hwin basis initialCode policy (policy.successor state tag)
      hsuccessorReachable
  exact ⟨nextMove, point, hnextMove, hdescriptor, hmove.2 tag⟩

/-- The current installed semantic representative and the independently
installed successor representative are joined by the exact coordinates which
the objective reads.  The literal semantic child of the current point has
the successor candidate's code and DPA control; its move is intentionally not
identified with the next policy move.  This is the policy-install replacement
for the invalid full-descriptor splicing step. -/
theorem exists_profiledOpenIndexedProvenancePolicyAlignedSemanticStep
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (state : ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode)
    (hreachable : SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy state)
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (hmove : ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
      hwin basis initialCode policy state move)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ∃ sourcePoint :
        ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
          basis initialCode,
      ∃ targetMove : ProfiledOpenIndexedBiBeliefMove A,
        ∃ targetPoint :
            ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
              basis initialCode,
          profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
              hwin basis initialCode sourcePoint = (state, move) ∧
            profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
                hwin basis initialCode targetPoint =
              (policy.successor state tag, targetMove) ∧
            ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy
                hwin basis initialCode policy (policy.successor state tag)
                  targetMove ∧
            let child :=
              profiledOpenIndexedOptionalControlledSemanticNext A strategy
                hwin basis initialCode sourcePoint tag
            child.1.state.code A strategy hwin basis =
                targetPoint.1.state.code A strategy hwin basis ∧
              child.2 = targetPoint.2 := by
  rcases hmove.1.2 with ⟨fresh, hcode, hsemanticMove⟩
  let sourcePoint :
      ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
        initialCode := (fresh, state.2)
  obtain ⟨targetMove, targetPoint, htargetMove, htargetDescriptor,
      _hcandidate, _htargetLive⟩ :=
    exists_profiledOpenIndexedProvenanceCodePolicyInstalledCandidate A
      strategy hwin basis initialCode policy (policy.successor state tag)
      (profiledOpenIndexedProvenanceCodePolicy_successor_reachable A strategy
        hwin basis initialCode policy state hreachable tag)
  have hsourceDescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode sourcePoint = (state, move) := by
    apply Prod.ext
    · apply Prod.ext
      · exact hcode
      · rfl
    · exact hsemanticMove
  let child := profiledOpenIndexedOptionalControlledSemanticNext A strategy
    hwin basis initialCode sourcePoint tag
  have hchildCode :
      child.1.state.code A strategy hwin basis =
        profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move tag := by
    change
      (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
        fresh.state tag).code A strategy hwin basis = _
    rw [profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis,
      hcode, hsemanticMove]
  have hpolicySuccessor := hmove.2 tag
  have htargetCode :
      targetPoint.1.state.code A strategy hwin basis =
        (policy.successor state tag).1 := by
    exact congrArg
      (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
          (I := I) initialCode ↦ descriptor.code)
      htargetDescriptor
  have htargetControl : targetPoint.2 =
      (policy.successor state tag).2 := by
    exact congrArg
      (fun descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A
          (I := I) initialCode ↦ descriptor.control)
      htargetDescriptor
  refine ⟨sourcePoint, targetMove, targetPoint, hsourceDescriptor,
    htargetDescriptor, htargetMove, ?_, ?_⟩
  · rw [htargetCode, hpolicySuccessor]
    exact hchildCode
  · rw [htargetControl, hpolicySuccessor]
    change
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
          (child.1.state.code A strategy hwin basis) =
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
          (profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move tag)
    rw [hchildCode]

end

/-! ## One installed semantic point along every policy path -/

/-- Literal finite policy state reached after the first `n` finite tags. -/
def profiledOpenIndexedProvenanceCodePolicyStateAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode :=
  policy.run (branchNode tag n)

section
omit [Inhabited I]

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedProvenanceCodePolicyStateAt_zero
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
      initialCode policy tag 0 = policy.run [] :=
  rfl

/-- The literal path state follows the policy successor table exactly. -/
theorem profiledOpenIndexedProvenanceCodePolicyStateAt_succ
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag (n + 1) =
      policy.successor
        (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
          initialCode policy tag n) (tag n) := by
  change policy.run (branchNode tag (n + 1)) =
    policy.successor (policy.run (branchNode tag n)) (tag n)
  rw [show branchNode tag (n + 1) =
      branchNode tag n ++ [tag n] from rfl]
  exact (policy.successor_at (branchNode tag n) (tag n)).symm

/-- Every literal state on the path is reachable in the selected rational
run. -/
theorem profiledOpenIndexedProvenanceCodePolicyStateAt_reachable
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy
      (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag n) :=
  ⟨branchNode tag n, rfl⟩

end

end

/-- Canonical proof-side move selected at depth `n`.  The choice is over the
finite public move type and is not made by either process at runtime. -/
noncomputable def profiledOpenIndexedProvenanceCodePolicyMoveAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) : ProfiledOpenIndexedBiBeliefMove A :=
  Classical.choose
    (SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A)
      policy
      (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag n)
      (profiledOpenIndexedProvenanceCodePolicyStateAt_reachable A strategy
        hwin basis initialCode policy tag n))

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The canonical move realizes the complete policy successor table. -/
theorem profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin basis
      initialCode policy
      (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag n)
      (profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin basis
        initialCode policy tag n) :=
  Classical.choose_spec
    (SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A)
      policy
      (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag n)
      (profiledOpenIndexedProvenanceCodePolicyStateAt_reachable A strategy
        hwin basis initialCode policy tag n))

/-- Proof-side optional-fresh representative of the canonical policy move. -/
noncomputable def profiledOpenIndexedProvenanceCodePolicyFreshPointAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  Classical.choose
    ((profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes A strategy hwin
      basis initialCode policy tag n).1.2)

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The chosen fresh point has the literal policy code and selected move. -/
theorem profiledOpenIndexedProvenanceCodePolicyFreshPointAt_spec
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    let state :=
      profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
        initialCode policy tag n
    let move :=
      profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin basis
        initialCode policy tag n
    let point :=
      profiledOpenIndexedProvenanceCodePolicyFreshPointAt A strategy hwin basis
        initialCode policy tag n
    point.state.code A strategy hwin basis = state.1 ∧
      point.state.move A strategy hwin basis = move :=
  Classical.choose_spec
    ((profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes A strategy hwin
      basis initialCode policy tag n).1.2)

/-- Install the policy control on the selected optional-fresh representative. -/
noncomputable def profiledOpenIndexedProvenanceCodePolicyPointAt
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  (profiledOpenIndexedProvenanceCodePolicyFreshPointAt A strategy hwin basis
      initialCode policy tag n,
    (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
      initialCode policy tag n).2)

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

/-- Each installed point's complete hidden descriptor is exactly its policy
state and selected move. -/
theorem profiledOpenIndexedProvenanceCodePolicyPointAt_descriptor
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode
        (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
          initialCode policy tag n) =
      (profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
          initialCode policy tag n,
        profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin basis
          initialCode policy tag n) := by
  obtain ⟨hcode, hmove⟩ :=
    profiledOpenIndexedProvenanceCodePolicyFreshPointAt_spec A strategy hwin
      basis initialCode policy tag n
  apply Prod.ext
  · apply Prod.ext
    · exact hcode
    · rfl
  · exact hmove

/-- The literal semantic child of the installed point at depth `n` has the
code of the independently installed point at depth `n+1`. -/
theorem profiledOpenIndexedProvenanceCodePolicyPointAt_child_code
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    let child := profiledOpenIndexedOptionalControlledSemanticNext A strategy
      hwin basis initialCode
      (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
        initialCode policy tag n) (tag n)
    child.1.state.code A strategy hwin basis =
      (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
        initialCode policy tag (n + 1)).1.state.code A strategy hwin basis := by
  let state := profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin
    basis initialCode policy tag n
  let nextState := profiledOpenIndexedProvenanceCodePolicyStateAt A strategy
    hwin basis initialCode policy tag (n + 1)
  let move := profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin
    basis initialCode policy tag n
  let point := profiledOpenIndexedProvenanceCodePolicyFreshPointAt A strategy
    hwin basis initialCode policy tag n
  let nextPoint := profiledOpenIndexedProvenanceCodePolicyFreshPointAt A
    strategy hwin basis initialCode policy tag (n + 1)
  obtain ⟨hcode, hmove⟩ :=
    profiledOpenIndexedProvenanceCodePolicyFreshPointAt_spec A strategy hwin
      basis initialCode policy tag n
  have hnextCode :=
    (profiledOpenIndexedProvenanceCodePolicyFreshPointAt_spec A strategy hwin
      basis initialCode policy tag (n + 1)).1
  have hpolicy :=
    (profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes A strategy hwin
      basis initialCode policy tag n).2 (tag n)
  have hsuccessor :=
    profiledOpenIndexedProvenanceCodePolicyStateAt_succ A strategy hwin basis
      initialCode policy tag n
  change
    (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
      point.state (tag n)).code A strategy hwin basis =
        nextPoint.state.code A strategy hwin basis
  rw [profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis,
    hcode, hmove, hnextCode]
  calc
    profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move (tag n) =
        (policy.successor state (tag n)).1 :=
      congrArg Prod.fst hpolicy.symm
    _ = nextState.1 := congrArg Prod.fst hsuccessor.symm

/-- The same literal child and next installed point have identical code-DPA
control.  Thus retagging changes only the semantic move/family coordinates. -/
theorem profiledOpenIndexedProvenanceCodePolicyPointAt_child_control
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    let child := profiledOpenIndexedOptionalControlledSemanticNext A strategy
      hwin basis initialCode
      (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
        initialCode policy tag n) (tag n)
    child.2 =
      (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
        initialCode policy tag (n + 1)).2 := by
  let state := profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin
    basis initialCode policy tag n
  let nextState := profiledOpenIndexedProvenanceCodePolicyStateAt A strategy
    hwin basis initialCode policy tag (n + 1)
  let move := profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin
    basis initialCode policy tag n
  have hpolicy :=
    (profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes A strategy hwin
      basis initialCode policy tag n).2 (tag n)
  have hsuccessor :=
    profiledOpenIndexedProvenanceCodePolicyStateAt_succ A strategy hwin basis
      initialCode policy tag n
  change
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
        ((profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
          basis initialCode
          (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
            initialCode policy tag n) (tag n)).1.state.code A strategy hwin
              basis) = nextState.2
  have hchildExpected :
      (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode
        (profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
          initialCode policy tag n) (tag n)).1.state.code A strategy hwin
            basis =
        profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move (tag n) := by
    have hchild :=
      profiledOpenIndexedProvenanceCodePolicyPointAt_child_code A strategy hwin
        basis initialCode policy tag n
    have hnextCode :=
      (profiledOpenIndexedProvenanceCodePolicyFreshPointAt_spec A strategy hwin
        basis initialCode policy tag (n + 1)).1
    rw [hchild]
    change
      (profiledOpenIndexedProvenanceCodePolicyFreshPointAt A strategy hwin
        basis initialCode policy tag (n + 1)).state.code A strategy hwin
          basis = _
    rw [hnextCode]
    calc
      nextState.1 = (policy.successor state (tag n)).1 :=
        congrArg Prod.fst hsuccessor
      _ = profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move (tag n) :=
        congrArg Prod.fst hpolicy
  rw [hchildExpected]
  calc
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step state.2
        (profiledOpenIndexedBiBeliefNextFiniteTag A state.1 move (tag n)) =
        (policy.successor state (tag n)).2 :=
      congrArg Prod.snd hpolicy.symm
    _ = nextState.2 := congrArg Prod.snd hsuccessor.symm

end

/-- Complete Nat-indexed installed semantic path.  Families and class tags are
deliberately absent from its coherence fields: each boundary may install the
next representative's own finite family. -/
structure ProfiledOpenIndexedProvenanceInstalledPolicyPath
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) where
  state : Nat →
    ProfiledOpenIndexedProvenanceCodePolicyState A strategy hwin basis
      initialCode
  move : Nat → ProfiledOpenIndexedBiBeliefMove A
  point : Nat →
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode
  initial : state 0 = policy.run []
  successor : ∀ n, state (n + 1) = policy.successor (state n) (tag n)
  reachable : ∀ n,
    SourceFreeBeliefCodeParityRationalPolicy.Reachable
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy (state n)
  realizes : ∀ n,
    ProfiledOpenIndexedProvenanceCodePolicyMoveRealizesAt A strategy hwin basis
      initialCode policy (state n) (move n)
  descriptor : ∀ n,
    profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode (point n) = (state n, move n)
  child_code : ∀ n,
    let child := profiledOpenIndexedOptionalControlledSemanticNext A strategy
      hwin basis initialCode (point n) (tag n)
    child.1.state.code A strategy hwin basis =
      (point (n + 1)).1.state.code A strategy hwin basis
  child_control : ∀ n,
    let child := profiledOpenIndexedOptionalControlledSemanticNext A strategy
      hwin basis initialCode (point n) (tag n)
    child.2 = (point (n + 1)).2

/-- Canonical installed path for a fixed strengthened policy and arbitrary tag
sequence. -/
noncomputable def profiledOpenIndexedProvenanceInstalledPolicyPath
    (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode)
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedProvenanceInstalledPolicyPath A strategy hwin basis
      initialCode policy tag where
  state := profiledOpenIndexedProvenanceCodePolicyStateAt A strategy hwin basis
    initialCode policy tag
  move := profiledOpenIndexedProvenanceCodePolicyMoveAt A strategy hwin basis
    initialCode policy tag
  point := profiledOpenIndexedProvenanceCodePolicyPointAt A strategy hwin basis
    initialCode policy tag
  initial := rfl
  successor := profiledOpenIndexedProvenanceCodePolicyStateAt_succ A strategy
    hwin basis initialCode policy tag
  reachable := profiledOpenIndexedProvenanceCodePolicyStateAt_reachable A
    strategy hwin basis initialCode policy tag
  realizes := profiledOpenIndexedProvenanceCodePolicyMoveAt_realizes A strategy
    hwin basis initialCode policy tag
  descriptor := profiledOpenIndexedProvenanceCodePolicyPointAt_descriptor A
    strategy hwin basis initialCode policy tag
  child_code := profiledOpenIndexedProvenanceCodePolicyPointAt_child_code A
    strategy hwin basis initialCode policy tag
  child_control :=
    profiledOpenIndexedProvenanceCodePolicyPointAt_child_control A strategy hwin
      basis initialCode policy tag

/-- Forget installed semantic witnesses and obtain the generic coherent policy
path consumed by the anti-mosaic acceptance theorem. -/
def ProfiledOpenIndexedProvenanceInstalledPolicyPath.toCodePolicyPath
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode}
    {tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)}
    (path : ProfiledOpenIndexedProvenanceInstalledPolicyPath A strategy hwin
      basis initialCode policy tag) :
    SourceFreeBeliefCodeParityPolicyPath
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
      initialCode
      (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) policy where
  state := path.state
  direction := tag
  initial := path.initial
  successor := path.successor

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every installed path reads an accepted word of positive-time policy
codes.  This is acceptance of one coherent policy run, not a mosaic of
independently accepted semantic blocks. -/
theorem ProfiledOpenIndexedProvenanceInstalledPolicyPath.accepts
    {initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I)}
    {policy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initialCode}
    {tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)}
    (path : ProfiledOpenIndexedProvenanceInstalledPolicyPath A strategy hwin
      basis initialCode policy tag) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
      (fun n ↦ (path.state (n + 1)).1) := by
  exact (path.toCodePolicyPath A strategy hwin basis).accepts
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    initialCode
    (ProfiledOpenIndexedProvenanceValid A strategy hwin basis)
    (profiledOpenIndexedBiBeliefNextFiniteTag A) policy

/-- Canonical strengthened policy selected from the unconditional finite-tag
rationalization. -/
noncomputable def profiledOpenIndexedProvenanceCodePolicyOfInitial
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin basis
      (initial.state.code A strategy hwin basis) :=
  Classical.choice
    (nonempty_profiledOpenIndexedProvenanceCodeRationalPolicy A strategy hwin
      basis initial)

/-- Fully unconditional installed path below an initial live-fresh semantic
point and an arbitrary finite-tag environment sequence. -/
noncomputable def profiledOpenIndexedProvenanceInstalledPolicyPathOfInitial
    (initial : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (tag : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedProvenanceInstalledPolicyPath A strategy hwin basis
      (initial.state.code A strategy hwin basis)
      (profiledOpenIndexedProvenanceCodePolicyOfInitial A strategy hwin basis
        initial) tag :=
  profiledOpenIndexedProvenanceInstalledPolicyPath A strategy hwin basis
    (initial.state.code A strategy hwin basis)
    (profiledOpenIndexedProvenanceCodePolicyOfInitial A strategy hwin basis
      initial) tag

end

end DetParityAutomaton

end DistributedSynthesis
