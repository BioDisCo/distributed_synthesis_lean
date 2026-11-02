/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedFixedPolicyTable

/-!
# The code/control part of witnessed re-anchoring is coherent

The witnessed sidewise edge may reselect a semantic representative with the
same full finite descriptor before taking a step.  This file records exactly
what descriptor equality makes independent of that reselection: the child
indexed-belief code and the child code-DPA control.

This is the largest unconditional congruence available at this interface.
It deliberately does not claim equality of the child's installed move or
public family.  Those coordinates depend on the newly constructed semantic
lanes and are precisely what is needed to identify successive re-anchored
witnesses with one literal semantic fold.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev BridgePoint :=
  ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
    initialCode

private abbrev BridgeDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Once code and control agree, equality of full hidden descriptors is
exactly equality of the installed-move coordinate.  This elementary fact is
useful below because it makes the residual left by re-anchoring explicit. -/
theorem bridgeDescriptor_eq_iff_moveIdentity_eq
    (left right : BridgeDescriptor A initialCode)
    (hcode : left.code = right.code)
    (hcontrol : left.control = right.control) :
    left = right ↔ left.moveIdentity = right.moveIdentity := by
  constructor
  · intro h
    exact congrArg HiddenCodeControlDescriptor.moveIdentity h
  · intro hmove
    apply Prod.ext
    · apply Prod.ext
      · exact hcode
      · exact hcontrol
    · exact hmove

/-! ## Finite-tag congruence -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal full finite source descriptors give equal child belief codes under
the same finite direction tag.  The semantic histories themselves need not
be equal. -/
theorem
    profiledOpenIndexedOptionalControlledSemanticNext_code_eq_of_descriptor_eq
    (left right : BridgePoint A strategy hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode left =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode right) :
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode left tag).1.state.code A strategy hwin basis =
      (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode right tag).1.state.code A strategy hwin basis := by
  have hcode := congrArg
    (fun descriptor : BridgeDescriptor A initialCode ↦ descriptor.code)
    hdescriptor
  have hmove := congrArg
    (fun descriptor : BridgeDescriptor A initialCode ↦
      descriptor.moveIdentity) hdescriptor
  change
    (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
      left.1.state
      (profiledOpenIndexedRawDirectionOfFiniteTag A
        (left.1.state.code A strategy hwin basis)
        (left.1.state.move A strategy hwin basis) tag)).code A strategy hwin
        basis =
      (profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis
        right.1.state
        (profiledOpenIndexedRawDirectionOfFiniteTag A
          (right.1.state.code A strategy hwin basis)
          (right.1.state.move A strategy hwin basis) tag)).code A strategy hwin
        basis
  rw [profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis,
    profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis]
  have hcode' : left.1.state.code A strategy hwin basis =
      right.1.state.code A strategy hwin basis := by
    simpa using hcode
  have hmove' : left.1.state.move A strategy hwin basis =
      right.1.state.move A strategy hwin basis := by
    simpa using hmove
  rw [hcode', hmove']

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The literal code-DPA controls after the same finite tag are equal as
well. -/
theorem
    profiledOpenIndexedOptionalControlledSemanticNext_control_eq_of_descriptor_eq
    (left right : BridgePoint A strategy hwin basis initialCode)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hdescriptor :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode left =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode right) :
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode left tag).2 =
      (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
        initialCode right tag).2 := by
  have hcontrol := congrArg
    (fun descriptor : BridgeDescriptor A initialCode ↦ descriptor.control)
    hdescriptor
  have hcode :=
    profiledOpenIndexedOptionalControlledSemanticNext_code_eq_of_descriptor_eq
      A strategy hwin basis initialCode left right tag hdescriptor
  change
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step left.2
        ((profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
          basis initialCode left tag).1.state.code A strategy hwin basis) =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step right.2
        ((profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin
          basis initialCode right tag).1.state.code A strategy hwin basis)
  exact congrArg₂
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).step
    (by simpa using hcontrol) hcode

/-! ## Application to the witnessed contextual edge -/

/-- A witnessed re-anchored edge's advertised target code and control are
exactly those obtained by stepping its original semantic source.  The edge
may use a different same-descriptor representative to produce the remaining
target coordinates. -/
theorem
    profiledOpenFixedSidewiseWitnessedReanchoredExactEdge_code_control
    {sourceFamily :
      SidewiseTaggedFamily
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
          initialCode)}
    {source : BridgeDescriptor A initialCode}
    {bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenActiveLaneSideClass A initialCode)
      (ProfiledOpenActiveLaneSideClass A initialCode)}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode}
    {targetFamily :
      SidewiseTaggedFamily
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
          initialCode)}
    {target : BridgeDescriptor A initialCode}
    (hedge : ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
      hwin basis initialCode sourceFamily source bank query targetFamily
        target) :
    ∃ sourceState : BridgePoint A strategy hwin basis initialCode,
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode sourceState = source ∧
      let child := profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
        initialCode sourceState query.1
      child.1.state.code A strategy hwin basis = target.code ∧
        child.2 = target.control := by
  rcases hedge with
    ⟨sourceState, stepState, hsource, _hsourceFamily, _hsourceTag, _hvalid,
      _hstep, hstepSource, _htargetFamily, htarget, _htargetTag⟩
  refine ⟨sourceState, hsource, ?_⟩
  have hsame :
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode sourceState =
        profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
          hwin basis initialCode stepState :=
    hsource.trans hstepSource.symm
  have hcode :=
    profiledOpenIndexedOptionalControlledSemanticNext_code_eq_of_descriptor_eq
      A strategy hwin basis initialCode sourceState stepState query.1.2 hsame
  have hcontrol :=
    profiledOpenIndexedOptionalControlledSemanticNext_control_eq_of_descriptor_eq
      A strategy hwin basis initialCode sourceState stepState query.1.2 hsame
  have htargetCode := congrArg
    (fun descriptor : BridgeDescriptor A initialCode ↦ descriptor.code)
    htarget
  have htargetControl := congrArg
    (fun descriptor : BridgeDescriptor A initialCode ↦ descriptor.control)
    htarget
  constructor
  · exact hcode.trans (by simpa using htargetCode)
  · exact hcontrol.trans (by simpa using htargetControl)

/-- Consequently, full descriptor coherence of a witnessed re-anchored edge
has only one additional content: the installed move of the original-source
child must equal the installed move of the advertised target.  Code and
control require no extra hypothesis. -/
theorem
    profiledOpenFixedSidewiseWitnessedReanchoredExactEdge_descriptor_eq_iff_move
    {sourceFamily :
      SidewiseTaggedFamily
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
          initialCode)}
    {source : BridgeDescriptor A initialCode}
    {bank : ProfiledOpenFixedSidewisePinnedBank A initialCode
      (ProfiledOpenActiveLaneSideClass A initialCode)
      (ProfiledOpenActiveLaneSideClass A initialCode)}
    {query : ProfiledOpenFixedSidewiseReachablePointedQuery A initialCode}
    {targetFamily :
      SidewiseTaggedFamily
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenActiveLaneSideClass A initialCode)
        (ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
          initialCode)}
    {target : BridgeDescriptor A initialCode}
    (hedge : ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy
      hwin basis initialCode sourceFamily source bank query targetFamily
        target) :
    ∃ sourceState : BridgePoint A strategy hwin basis initialCode,
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode sourceState = source ∧
      let child := profiledOpenFixedSidewiseSemanticNext A strategy hwin basis
        initialCode sourceState query.1
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
          basis initialCode child = target ↔
        child.1.state.move A strategy hwin basis = target.moveIdentity) := by
  obtain ⟨sourceState, hsource, hcode, hcontrol⟩ :=
    profiledOpenFixedSidewiseWitnessedReanchoredExactEdge_code_control A
      strategy hwin basis initialCode hedge
  refine ⟨sourceState, hsource, ?_⟩
  apply bridgeDescriptor_eq_iff_moveIdentity_eq A initialCode
  · simpa using hcode
  · simpa using hcontrol

/-! ## The exact candidate thread really carries the code-DPA run -/

private abbrev BridgeFamily :=
  ProfiledOpenWitnessedTableFamily A initialCode

private abbrev BridgeBank :=
  ProfiledOpenWitnessedTableBank A initialCode

private abbrev BridgeQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

private abbrev BridgeExactThread
    (initial : Finset
      (RelationalFamilyCandidate (BridgeFamily A initialCode)
        (BridgeDescriptor A initialCode)))
    (move : Nat → BridgeBank A initialCode)
    (query : Nat → BridgeQuery A initialCode) :=
  SourceAwareRelationalFamilyExactThread
    (ProfiledOpenFixedSidewiseWitnessedReanchoredExactEdge A strategy hwin
      basis initialCode)
    (ProfiledOpenFixedSidewiseControlStep A initialCode) initial move query

/-- Child codes read from one coherent source-aware candidate thread. -/
def profiledOpenWitnessedExactThreadChildCodeWord
    {initial : Finset
      (RelationalFamilyCandidate (BridgeFamily A initialCode)
        (BridgeDescriptor A initialCode))}
    {move : Nat → BridgeBank A initialCode}
    {query : Nat → BridgeQuery A initialCode}
    (thread : BridgeExactThread A strategy hwin basis initialCode initial move
      query) : OmegaWord (ProfiledOpenIndexedBiBeliefCode A (I := I)) :=
  fun n ↦ (thread.candidate (n + 1)).2.code

/-- The descriptor control stored at depth `n` is definitionally the state
reached by the code DPA after the first `n` child codes.  Thus re-anchoring
does not break run consistency; what it does not provide is parity of this
run. -/
theorem profiledOpenWitnessedExactThread_control_eq_run
    {initial : Finset
      (RelationalFamilyCandidate (BridgeFamily A initialCode)
        (BridgeDescriptor A initialCode))}
    {move : Nat → BridgeBank A initialCode}
    {query : Nat → BridgeQuery A initialCode}
    (thread : BridgeExactThread A strategy hwin basis initialCode initial move
      query)
    (hinitial : (thread.candidate 0).2.control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).initial) : ∀ n,
    (thread.candidate n).2.control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).run
        (profiledOpenWitnessedExactThreadChildCodeWord A strategy hwin basis
          initialCode thread) n := by
  intro n
  induction n with
  | zero =>
      simpa using hinitial
  | succ n ih =>
      rw [(profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).run_succ,
        ← ih]
      exact thread.control n

/-- Exact characterization of the remaining objective on a candidate thread:
acceptance of its child-code word is equivalent to min-even parity of its
already stored controls.  Local exact edges provide the run equation above,
but no local edge law can manufacture this omega condition. -/
theorem profiledOpenWitnessedExactThread_accepts_iff_control_minEven
    {initial : Finset
      (RelationalFamilyCandidate (BridgeFamily A initialCode)
        (BridgeDescriptor A initialCode))}
    {move : Nat → BridgeBank A initialCode}
    {query : Nat → BridgeQuery A initialCode}
    (thread : BridgeExactThread A strategy hwin basis initialCode initial move
      query)
    (hinitial : (thread.candidate 0).2.control =
      (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).initial) :
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).Accepts
        (profiledOpenWitnessedExactThreadChildCodeWord A strategy hwin basis
          initialCode thread) ↔
      NatSeqMinEvenParity (fun n ↦
        (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).priority
          (thread.candidate n).2.control) := by
  rw [(profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    |>.accepts_iff_natSeqMinEvenParity]
  apply Iff.intro
  · intro h
    convert h using 1
    funext n
    rw [profiledOpenWitnessedExactThread_control_eq_run A strategy hwin basis
      initialCode thread hinitial n]
  · intro h
    convert h using 1
    funext n
    rw [profiledOpenWitnessedExactThread_control_eq_run A strategy hwin basis
      initialCode thread hinitial n]

end

end DetParityAutomaton

end DistributedSynthesis
