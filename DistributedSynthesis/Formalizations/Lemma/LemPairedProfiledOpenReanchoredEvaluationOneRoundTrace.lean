/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenWitnessedPhysicalRoundAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenDependentMemberPairTest
import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryBranchFlatten

/-!
# Exact one-round trace of a re-anchored row evaluation

Semantic provenance of a re-anchored receiver row supplies one literal past
of the original distributed strategy.  This file opens that proof-only past
and records the strongest exact physical statement that survives finite-tree
rationalization: the informed receiver output is the raw strategy's output at
that past, using the row fixed at epoch entry.

The blind sender coordinate is deliberately absent from the conclusion.
Rational-tree extraction preserves the monitor language and the complete
receiver-table law, but may replace the raw sender tree by another accepted
rational sender tree.  Consequently there is no general full-pair equality
with the raw strategy.  Likewise the semantic past need not be empty, so the
current round is the final round of the block ending at the current move, not
in general the head of that block.
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
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

/-! ## The physical scan survives sender rationalization -/

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- On an arbitrary play, not only on the semantic lambda used before
rational extraction, the scan coordinate of the open right monitor is the
literal fold of the physical letters that were emitted.  In particular this
coordinate sees the rationalized blind-sender output; it does not silently
substitute the raw sender from the realizing strategy. -/
theorem profiledOpenRightBlockMonitor_run_scan_eq_physicalFold
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (play : Nat → RealizedBlockRound In₂ In₁
      (ProfiledRightReceiverOutput A) Out₁) : ∀ n,
    ((profiledOpenRightBlockMonitor A code minimum profile).run play n).2.1 =
      (omegaPrefix play n).foldl
        (fun scan letter ↦
          pairedRightScanStep A scan (profiledRightPhysicalLetter A letter))
        (pairedRightScanInitial A code) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, omegaPrefix_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change pairedRightScanStep A
          (((profiledOpenRightBlockMonitor A code minimum profile).run
            play n).2.1)
          (profiledRightPhysicalLetter A (play n)) = _
      rw [ih]

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of the arbitrary-play physical scan theorem. -/
theorem profiledOpenLeftBlockMonitor_run_scan_eq_physicalFold
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (play : Nat → RealizedBlockRound In₁ In₂
      (ProfiledLeftReceiverOutput A) Out₂) : ∀ n,
    ((profiledOpenLeftBlockMonitor A code minimum profile).run play n).2.1 =
      (omegaPrefix play n).foldl
        (fun scan letter ↦
          pairedLeftScanStep A scan (profiledLeftPhysicalLetter A letter))
        (pairedLeftScanInitial A code) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, omegaPrefix_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change pairedLeftScanStep A
          (((profiledOpenLeftBlockMonitor A code minimum profile).run
            play n).2.1)
          (profiledLeftPhysicalLetter A (play n)) = _
      rw [ih]

/-! ## Coupled finite execution of an installed overlay -/

/-- Execute an installed right overlay through a finite physical input word.
Every step advances both coordinates of its query: the blind controller on
`inputOne` and the pinned-union monitor on the literal emitted record. -/
noncomputable def profiledOpenWitnessedRightRoundOverlayRun :
    ProfiledOpenWitnessedRightRoundOverlay A initialCode →
      List (In₁ × In₂) →
        ProfiledOpenWitnessedRightRoundOverlay A initialCode
  | overlay, [] => overlay
  | overlay, input :: rest =>
      profiledOpenWitnessedRightRoundOverlayRun
        (overlay.step A initialCode input.1 input.2) rest

/-- Left executable overlay run. -/
noncomputable def profiledOpenWitnessedLeftRoundOverlayRun :
    ProfiledOpenWitnessedLeftRoundOverlay A initialCode →
      List (In₁ × In₂) →
        ProfiledOpenWitnessedLeftRoundOverlay A initialCode
  | overlay, [] => overlay
  | overlay, input :: rest =>
      profiledOpenWitnessedLeftRoundOverlayRun
        (overlay.step A initialCode input.1 input.2) rest

/-- Literal pinned-union records emitted while executing one right overlay.
The member/root tag is unchanged by `step`, so all records inhabit the one
fixed union alphabet determined by the initial overlay's value. -/
noncomputable def profiledOpenWitnessedRightRoundOverlayRecords
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) :
    List (In₁ × In₂) → List
      (RealizedBlockRound
        ((Sigma fun member : ProfiledOpenHiddenDescriptorRightCarrier A
          overlay.value.1 ↦
            ProfiledOpenHiddenDescriptorRightRoot A member.1) × In₂)
        In₁ (ProfiledOpenRightClassifiedOutput A) Out₁)
  | [] => []
  | input :: rest =>
      profiledOpenWitnessedRightRoundRecord A initialCode overlay input.1
          input.2 ::
        profiledOpenWitnessedRightRoundOverlayRecords
          (overlay.step A initialCode input.1 input.2) rest

/-- Literal left pinned-union record trace. -/
noncomputable def profiledOpenWitnessedLeftRoundOverlayRecords
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :
    List (In₁ × In₂) → List
      (RealizedBlockRound
        ((Sigma fun member : ProfiledOpenHiddenDescriptorLeftCarrier A
          overlay.value.1 ↦
            ProfiledOpenHiddenDescriptorLeftRoot A member.1) × In₁)
        In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂)
  | [] => []
  | input :: rest =>
      profiledOpenWitnessedLeftRoundRecord A initialCode overlay input.1
          input.2 ::
        profiledOpenWitnessedLeftRoundOverlayRecords
          (overlay.step A initialCode input.1 input.2) rest

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- The carried right monitor coordinate is exactly the finite monitor run
over the records actually emitted by the rationalized controller.  No raw
sender equality or semantic-history assumption occurs in this statement. -/
theorem profiledOpenWitnessedRightRoundOverlayRun_query_monitor
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) :
    ∀ inputs : List (In₁ × In₂),
      HEq
        (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay
          inputs).query.2
      ((profiledOpenWitnessedRightRoundOverlayRecords A initialCode overlay
        inputs).foldl
          (ProfiledOpenHiddenDescriptorRightPinnedUnionMonitor A
            overlay.value.1 overlay.value.2.1).step overlay.query.2) := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => rfl
  | cons input rest ih =>
      simpa only [profiledOpenWitnessedRightRoundOverlayRun,
        profiledOpenWitnessedRightRoundOverlayRecords, List.foldl_cons] using
        (ih (overlay := overlay.step A initialCode input.1 input.2))

omit [Inhabited I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left coupled monitor-coordinate run. -/
theorem profiledOpenWitnessedLeftRoundOverlayRun_query_monitor
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) :
    ∀ inputs : List (In₁ × In₂),
      HEq
        (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay
          inputs).query.2
      ((profiledOpenWitnessedLeftRoundOverlayRecords A initialCode overlay
        inputs).foldl
          (ProfiledOpenHiddenDescriptorLeftPinnedUnionMonitor A
            overlay.value.1 overlay.value.2.1).step overlay.query.2) := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => rfl
  | cons input rest ih =>
      simpa only [profiledOpenWitnessedLeftRoundOverlayRun,
        profiledOpenWitnessedLeftRoundOverlayRecords, List.foldl_cons] using
        (ih (overlay := overlay.step A initialCode input.1 input.2))

/-! ## Exact semantic invariant and its one-step boundary -/

/-- A right member/root pair is backed by a re-anchored semantic row, while
the displayed root is allowed to be *any* root of that member.  The complete
semantic table law already quantifies over every concrete source root; forcing
the displayed root to be the lane's distinguished pivot would therefore lose
exactly the roots retained by physical recutting and root deduplication. -/
def ProfiledOpenFixedRightReanchoredRetainedRoot
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (memberRoot : ProfiledOpenFixedRightDependentMemberRoot A initialCode
      value) : Prop :=
  ∃ witness : ProfiledOpenFixedRightReanchoredQuery A strategy hwin basis
      initialCode current value query,
    witness.member = memberRoot.1 ∧
      ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
          (I := I),
        ∃ _hright : witness.state.1.state.right = some lane,
          ∃ _hdescriptor :
              profiledOpenIndexedOptionalControlledSemanticDescriptor A
                  strategy hwin basis initialCode witness.state =
                memberRoot.1.1,
            let table := ((lane.realization.coherentTable A).table
              |>.toClassified A lane.source)
            ∃ hmove : memberRoot.1.1.moveIdentity.1 =
                ProfiledOpenClassifiedMove.right lane.source table,
              ProfiledOpenRightSemanticTableAllowed A lane.source strategy
                hwin lane.realization.entry basis (fun input ↦
                  profiledOpenFixedRightQueryResponses A initialCode value
                    query memberRoot.1
                    ((profiledOpenHiddenDescriptorRightRootOfEq A
                        memberRoot.1.1 lane.source table hmove input.1.1,
                      input.1.2), input.2))

/-- Left arbitrary-retained-root mirror. -/
def ProfiledOpenFixedLeftReanchoredRetainedRoot
    (current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (memberRoot : ProfiledOpenFixedLeftDependentMemberRoot A initialCode
      value) : Prop :=
  ∃ witness : ProfiledOpenFixedLeftReanchoredQuery A strategy hwin basis
      initialCode current value query,
    witness.member = memberRoot.1 ∧
      ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
          (I := I),
        ∃ _hleft : witness.state.1.state.left = some lane,
          ∃ _hdescriptor :
              profiledOpenIndexedOptionalControlledSemanticDescriptor A
                  strategy hwin basis initialCode witness.state =
                memberRoot.1.1,
            let table := ((lane.realization.coherentTable A).table
              |>.toClassified A lane.source)
            ∃ hmove : memberRoot.1.1.moveIdentity.2 =
                ProfiledOpenClassifiedMove.left lane.source table,
              ProfiledOpenLeftSemanticTableAllowed A lane.source strategy
                hwin lane.realization.entry basis (fun input ↦
                  profiledOpenFixedLeftQueryResponses A initialCode value
                    query memberRoot.1
                    ((profiledOpenHiddenDescriptorLeftRootOfEq A
                        memberRoot.1.1 lane.source table hmove input.1.1,
                      input.1.2), input.2))

section
omit [Inhabited I]

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The earlier pivot-root projection is a special case of the exact retained
root law. -/
theorem profiledOpenFixedRightReanchoredRetainedRoot_of_pivotRoot
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    {memberRoot : ProfiledOpenFixedRightDependentMemberRoot A initialCode
      value}
    (hroot : ProfiledOpenFixedRightReanchoredPivotRoot A strategy hwin basis
      initialCode current value query memberRoot) :
    ProfiledOpenFixedRightReanchoredRetainedRoot A strategy hwin basis
      initialCode current value query memberRoot := by
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, _hpivot, hsemantic⟩
  exact ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hsemantic⟩

/-- Left pivot-root compatibility. -/
theorem profiledOpenFixedLeftReanchoredRetainedRoot_of_pivotRoot
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    {memberRoot : ProfiledOpenFixedLeftDependentMemberRoot A initialCode
      value}
    (hroot : ProfiledOpenFixedLeftReanchoredPivotRoot A strategy hwin basis
      initialCode current value query memberRoot) :
    ProfiledOpenFixedLeftReanchoredRetainedRoot A strategy hwin basis
      initialCode current value query memberRoot := by
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, _hpivot, hsemantic⟩
  exact ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hsemantic⟩

/-- Transport the complete right semantic row along equality of finite fibre
members.  Isolating this transport keeps the dependent re-anchored witness
itself out of equality elimination. -/
theorem profiledOpenFixedRightReanchoredSemanticAllowed_congr_member
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    {left right : ProfiledOpenHiddenDescriptorRightCarrier A value.1}
    (hmember : left = right)
    (hsemantic : ProfiledOpenFixedRightReanchoredSemanticAllowed A strategy
      hwin basis initialCode state left
        (profiledOpenFixedRightQueryResponses A initialCode value query left)) :
    ProfiledOpenFixedRightReanchoredSemanticAllowed A strategy hwin basis
      initialCode state right
        (profiledOpenFixedRightQueryResponses A initialCode value query
          right) := by
  cases hmember
  exact hsemantic

/-- Left member transport. -/
theorem profiledOpenFixedLeftReanchoredSemanticAllowed_congr_member
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (state : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode)
    {left right : ProfiledOpenHiddenDescriptorLeftCarrier A value.1}
    (hmember : left = right)
    (hsemantic : ProfiledOpenFixedLeftReanchoredSemanticAllowed A strategy hwin
      basis initialCode state left
        (profiledOpenFixedLeftQueryResponses A initialCode value query left)) :
    ProfiledOpenFixedLeftReanchoredSemanticAllowed A strategy hwin basis
      initialCode state right
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          right) := by
  cases hmember
  exact hsemantic

end

end

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Re-anchor an exact right member and retain its literal root across an
arbitrary reachable query.  No equality with the semantic pivot is needed. -/
theorem profiledOpenFixedRightReanchoredRetainedRoot_of_hasReanchoredRows
    (value : ProfiledOpenFixedRightPinnedValue A initialCode)
    (hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode value)
    (member : ProfiledOpenHiddenDescriptorRightCarrier A value.1)
    (root : ProfiledOpenHiddenDescriptorRightRoot A member.1)
    (query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value)
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query) :
    ProfiledOpenFixedRightReanchoredRetainedRoot A strategy hwin basis
      initialCode member.1 value query ⟨member, root⟩ := by
  obtain ⟨witness⟩ := hrows member.1 member.2 query reachable
  have hmember : witness.member = member := by
    apply Subtype.ext
    exact witness.member_eq
  have hsemanticExact :
      ProfiledOpenFixedRightReanchoredSemanticAllowed A strategy hwin basis
        initialCode witness.state member
          (profiledOpenFixedRightQueryResponses A initialCode value query
            member) := by
    exact profiledOpenFixedRightReanchoredSemanticAllowed_congr_member A
      strategy hwin basis initialCode query witness.state hmember
        witness.semantic
  rcases hsemanticExact with
    ⟨lane, hlane, hdescriptor, hmove, hsemantic⟩
  exact ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hsemantic⟩

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left exact-root re-anchoring. -/
theorem profiledOpenFixedLeftReanchoredRetainedRoot_of_hasReanchoredRows
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode)
    (hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode value)
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A value.1)
    (root : ProfiledOpenHiddenDescriptorLeftRoot A member.1)
    (query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value)
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query) :
    ProfiledOpenFixedLeftReanchoredRetainedRoot A strategy hwin basis
      initialCode member.1 value query ⟨member, root⟩ := by
  obtain ⟨witness⟩ := hrows member.1 member.2 query reachable
  have hmember : witness.member = member := by
    apply Subtype.ext
    exact witness.member_eq
  have hsemanticExact :
      ProfiledOpenFixedLeftReanchoredSemanticAllowed A strategy hwin basis
        initialCode witness.state member
          (profiledOpenFixedLeftQueryResponses A initialCode value query
            member) := by
    exact profiledOpenFixedLeftReanchoredSemanticAllowed_congr_member A
      strategy hwin basis initialCode query witness.state hmember
        witness.semantic
  rcases hsemanticExact with
    ⟨lane, hlane, hdescriptor, hmove, hsemantic⟩
  exact ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hsemantic⟩

/-- The finite fields of an installed right overlay are backed by a literal
re-anchored semantic evaluation at that same member and root.  This is the
proof component intentionally omitted from the executable overlay structure. -/
def ProfiledOpenWitnessedRightRoundOverlay.SemanticallyReanchored
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode) : Prop :=
  ∃ current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode,
    ProfiledOpenFixedRightReanchoredRetainedRoot A strategy hwin basis
      initialCode current overlay.value overlay.query
        ⟨overlay.member, overlay.root⟩

/-- Left semantic-overlay invariant. -/
def ProfiledOpenWitnessedLeftRoundOverlay.SemanticallyReanchored
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode) : Prop :=
  ∃ current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode,
    ProfiledOpenFixedLeftReanchoredRetainedRoot A strategy hwin basis
      initialCode current overlay.value overlay.query
        ⟨overlay.member, overlay.root⟩

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The safe constructor from a right row evaluation carries the exact
semantic invariant, even though the executable overlay erases its proof. -/
theorem profiledOpenWitnessedRightRoundOverlayOfEvaluation_semanticallyReanchored
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin basis
      initialCode reachable evaluation entryRow).SemanticallyReanchored A
      strategy hwin basis initialCode := by
  exact ⟨current,
    profiledOpenFixedRightReanchoredRetainedRoot_of_pivotRoot A strategy hwin
      basis initialCode evaluation.2⟩

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left constructor invariant. -/
theorem profiledOpenWitnessedLeftRoundOverlayOfEvaluation_semanticallyReanchored
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) :
    (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin basis
      initialCode reachable evaluation entryRow).SemanticallyReanchored A
      strategy hwin basis initialCode := by
  exact ⟨current,
    profiledOpenFixedLeftReanchoredRetainedRoot_of_pivotRoot A strategy hwin
      basis initialCode evaluation.2⟩

/-- Minimal right one-step semantic obligation.  The executable step already
advances the controller and monitor exactly; this proposition asks only that
the *same* member/root tag still admits a re-anchored semantic evaluation at
the advanced query. -/
def ProfiledOpenWitnessedRightRoundOverlay.SemanticStepPreserving
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) : Prop :=
  overlay.SemanticallyReanchored A strategy hwin basis initialCode →
    (overlay.step A initialCode inputOne inputTwo).SemanticallyReanchored A
      strategy hwin basis initialCode

/-- Left one-step semantic obligation. -/
def ProfiledOpenWitnessedLeftRoundOverlay.SemanticStepPreserving
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂) : Prop :=
  overlay.SemanticallyReanchored A strategy hwin basis initialCode →
    (overlay.step A initialCode inputOne inputTwo).SemanticallyReanchored A
      strategy hwin basis initialCode

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

/-- Compatibility adapter for the earlier pivot-root evaluation API.  The
general preservation theorem below no longer needs an equality between the
retained root and the semantic lane's pivot. -/
theorem
    ProfiledOpenWitnessedRightRoundOverlay.semanticStepPreserving_of_exactEvaluation
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current
        (overlay.step A initialCode inputOne inputTwo).value
        (overlay.step A initialCode inputOne inputTwo).query)
    (hexact : evaluation.1 =
      ⟨(overlay.step A initialCode inputOne inputTwo).member,
        (overlay.step A initialCode inputOne inputTwo).root⟩) :
    overlay.SemanticStepPreserving A strategy hwin basis initialCode inputOne
      inputTwo := by
  intro _
  refine ⟨current, ?_⟩
  rw [← hexact]
  exact profiledOpenFixedRightReanchoredRetainedRoot_of_pivotRoot A strategy
    hwin basis initialCode evaluation.2

/-- Left exact-evaluation adapter. -/
theorem
    ProfiledOpenWitnessedLeftRoundOverlay.semanticStepPreserving_of_exactEvaluation
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (inputOne : In₁) (inputTwo : In₂)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current
        (overlay.step A initialCode inputOne inputTwo).value
        (overlay.step A initialCode inputOne inputTwo).query)
    (hexact : evaluation.1 =
      ⟨(overlay.step A initialCode inputOne inputTwo).member,
        (overlay.step A initialCode inputOne inputTwo).root⟩) :
    overlay.SemanticStepPreserving A strategy hwin basis initialCode inputOne
      inputTwo := by
  intro _
  refine ⟨current, ?_⟩
  rw [← hexact]
  exact profiledOpenFixedLeftReanchoredRetainedRoot_of_pivotRoot A strategy
    hwin basis initialCode evaluation.2

/-- The complete per-member row law preserves the literal right member/root
through one executable query step.  The old semantic invariant is not used:
the advanced row is rebuilt at `overlay.member.1`, while `step` retains the
value, member, and root definitionally and supplies reachable query data. -/
theorem
    ProfiledOpenWitnessedRightRoundOverlay.semanticStepPreserving_of_hasReanchoredRows
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode overlay.value)
    (inputOne : In₁) (inputTwo : In₂) :
    overlay.SemanticStepPreserving A strategy hwin basis initialCode inputOne
      inputTwo := by
  intro _hold
  refine ⟨overlay.member.1, ?_⟩
  exact profiledOpenFixedRightReanchoredRetainedRoot_of_hasReanchoredRows A
    strategy hwin basis initialCode overlay.value hrows overlay.member
      overlay.root (overlay.step A initialCode inputOne inputTwo).query
        (overlay.step A initialCode inputOne inputTwo).reachable

/-- Left unconditional-with-rows one-step preservation. -/
theorem
    ProfiledOpenWitnessedLeftRoundOverlay.semanticStepPreserving_of_hasReanchoredRows
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode overlay.value)
    (inputOne : In₁) (inputTwo : In₂) :
    overlay.SemanticStepPreserving A strategy hwin basis initialCode inputOne
      inputTwo := by
  intro _hold
  refine ⟨overlay.member.1, ?_⟩
  exact profiledOpenFixedLeftReanchoredRetainedRoot_of_hasReanchoredRows A
    strategy hwin basis initialCode overlay.value hrows overlay.member
      overlay.root (overlay.step A initialCode inputOne inputTwo).query
        (overlay.step A initialCode inputOne inputTwo).reachable

/-- If the named one-step semantic law is available along the executable
right run, semantic re-anchoring and the already unconditional monitor trace
remain coupled for every finite prefix. -/
theorem profiledOpenWitnessedRightRoundOverlayRun_semanticallyReanchored
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hstep : ∀ (current : ProfiledOpenWitnessedRightRoundOverlay A
        initialCode) inputOne inputTwo,
      ProfiledOpenWitnessedRightRoundOverlay.SemanticStepPreserving A strategy
        hwin basis initialCode current inputOne inputTwo) :
    ∀ inputs : List (In₁ × In₂),
    (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
      ).SemanticallyReanchored A strategy hwin basis initialCode := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => exact hstart
  | cons input rest ih =>
      exact ih (overlay := overlay.step A initialCode input.1 input.2)
        (hstep overlay input.1 input.2 hstart)

/-- Left conditional semantic run. -/
theorem profiledOpenWitnessedLeftRoundOverlayRun_semanticallyReanchored
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hstep : ∀ (current : ProfiledOpenWitnessedLeftRoundOverlay A
        initialCode) inputOne inputTwo,
      ProfiledOpenWitnessedLeftRoundOverlay.SemanticStepPreserving A strategy
        hwin basis initialCode current inputOne inputTwo) :
    ∀ inputs : List (In₁ × In₂),
    (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
      ).SemanticallyReanchored A strategy hwin basis initialCode := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => exact hstart
  | cons input rest ih =>
      exact ih (overlay := overlay.step A initialCode input.1 input.2)
        (hstep overlay input.1 input.2 hstart)

/-- One right per-member row law is enough to couple semantic re-anchoring
with the executable overlay for every finite physical prefix. -/
theorem
    profiledOpenWitnessedRightRoundOverlayRun_semanticallyReanchored_of_hasRows
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hrows : ProfiledOpenFixedRightValueHasReanchoredRows A strategy hwin
      basis initialCode overlay.value) :
    ∀ inputs : List (In₁ × In₂),
    (profiledOpenWitnessedRightRoundOverlayRun A initialCode overlay inputs
      ).SemanticallyReanchored A strategy hwin basis initialCode := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => exact hstart
  | cons input rest ih =>
      have hnext :=
        overlay.semanticStepPreserving_of_hasReanchoredRows A strategy hwin
          basis initialCode hrows input.1 input.2 hstart
      apply ih (overlay := overlay.step A initialCode input.1 input.2) hnext
      simpa only [profiledOpenWitnessedRightRoundOverlay_step_value] using hrows

/-- Left finite-run retained-root preservation. -/
theorem
    profiledOpenWitnessedLeftRoundOverlayRun_semanticallyReanchored_of_hasRows
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hstart : overlay.SemanticallyReanchored A strategy hwin basis initialCode)
    (hrows : ProfiledOpenFixedLeftValueHasReanchoredRows A strategy hwin basis
      initialCode overlay.value) :
    ∀ inputs : List (In₁ × In₂),
    (profiledOpenWitnessedLeftRoundOverlayRun A initialCode overlay inputs
      ).SemanticallyReanchored A strategy hwin basis initialCode := by
  intro inputs
  induction inputs generalizing overlay with
  | nil => exact hstart
  | cons input rest ih =>
      have hnext :=
        overlay.semanticStepPreserving_of_hasReanchoredRows A strategy hwin
          basis initialCode hrows input.1 input.2 hstart
      apply ih (overlay := overlay.step A initialCode input.1 input.2) hnext
      simpa only [profiledOpenWitnessedLeftRoundOverlay_step_value] using hrows

end

/-! ## Exact raw receiver round -/

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

/-- A semantically re-anchored right overlay executes the original receiver
at the concrete source root obtained by decoding its *literal retained hidden
root*.  This is the arbitrary-root form needed after physical recutting: the
decoded root need not be the lane's distinguished pivot. -/
theorem
    exists_profiledOpenWitnessedRightReceiverOutput_eq_rawReceiverAtRetainedRoot
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₂) × In₁)),
          profiledOpenWitnessedRightReceiverOutput A initialCode overlay
              inputOne inputTwo =
            procOnePairedEntryRightReceiverForRow strategy
                (lane.realization.entry decodedRoot) overlay.entryRow
              (taggedPast.map (fun old ↦ (old.1.2, old.2)))
              (inputTwo, inputOne) := by
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, taggedPast, hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorRightRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  refine ⟨lane, decodedRoot, taggedPast, ?_⟩
  change pairedRightInformedForRow overlay.entryRow
      (profiledOpenFixedRightQueryResponses A initialCode overlay.value
        overlay.query overlay.member
          ((overlay.root, inputTwo), inputOne)).1.physical = _
  have hinverse :
      profiledOpenHiddenDescriptorRightRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorRightRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  rw [← hinverse]
  have hat := congrFun hpast ((decodedRoot, inputTwo), inputOne)
  have hphysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow overlay.entryRow output.1.physical) hat
  cases hrow : overlay.entryRow <;>
    simpa [hrow, table, decodedRoot,
      profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenRightSemanticClassifiedReceiver,
      profiledRightReceiverStrategy, pairedRightReceiverStrategy,
      pairedRightInformedForRow, procOnePairedEntryRightReceiverForRow,
      ProcOnePairedEntryRep.lambdaOfStrategy] using hphysical

/-- Left arbitrary-retained-root receiver identity. -/
theorem
    exists_profiledOpenWitnessedLeftReceiverOutput_eq_rawReceiverAtRetainedRoot
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₁) × In₂)),
          profiledOpenWitnessedLeftReceiverOutput A initialCode overlay
              inputOne inputTwo =
            procTwoPairedEntryLeftReceiverForRow strategy
                (lane.realization.entry decodedRoot) overlay.entryRow
              (taggedPast.map (fun old ↦ (old.1.2, old.2)))
              (inputOne, inputTwo) := by
  rcases hsemantic with ⟨current, hroot⟩
  rcases hroot with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, taggedPast, hpast⟩
  let table := ((lane.realization.coherentTable A).table
    |>.toClassified A lane.source)
  let decodedRoot := profiledOpenHiddenDescriptorLeftRootToEq A
    overlay.member.1 lane.source table hmove overlay.root
  refine ⟨lane, decodedRoot, taggedPast, ?_⟩
  change pairedLeftInformedForRow overlay.entryRow
      (profiledOpenFixedLeftQueryResponses A initialCode overlay.value
        overlay.query overlay.member
          ((overlay.root, inputOne), inputTwo)).1.physical = _
  have hinverse :
      profiledOpenHiddenDescriptorLeftRootOfEq A overlay.member.1 lane.source
          table hmove decodedRoot = overlay.root :=
    profiledOpenHiddenDescriptorLeftRootOfEq_rootToEq A initialCode
      overlay.member.1 lane.source table hmove overlay.root
  rw [← hinverse]
  have hat := congrFun hpast ((decodedRoot, inputOne), inputTwo)
  have hphysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow overlay.entryRow output.1.physical) hat
  cases hrow : overlay.entryRow <;>
    simpa [hrow, table, decodedRoot,
      profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenLeftSemanticClassifiedReceiver,
      profiledLeftReceiverStrategy, pairedLeftReceiverStrategy,
      pairedLeftInformedForRow, procTwoPairedEntryLeftReceiverForRow,
      ProcTwoPairedEntryRep.lambdaOfStrategy] using hphysical

/-- A witnessed right row is literally the raw process-two receiver at one
semantic past.  The row is the sticky external epoch-entry row; it is not
reconstructed from a current receipt. -/
theorem exists_profiledOpenWitnessedRightReceiverOutput_eq_rawReceiver
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I),
      ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₂) × In₁)),
        profiledOpenWitnessedRightReceiverOutput A initialCode
            (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy
              hwin basis initialCode reachable evaluation entryRow)
            inputOne inputTwo =
          procOnePairedEntryRightReceiverForRow strategy
              (lane.realization.entry lane.realization.pivot) entryRow
            (taggedPast.map (fun old ↦ (old.1.2, old.2)))
            (inputTwo, inputOne) := by
  rcases evaluation with ⟨⟨member, root⟩, hevaluation⟩
  rcases hevaluation with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hroot,
      taggedPast, hpast⟩
  refine ⟨lane, taggedPast, ?_⟩
  change pairedRightInformedForRow entryRow
        (profiledOpenFixedRightQueryResponses A initialCode value query
          member ((root, inputTwo), inputOne)).1.physical = _
  change root =
      profiledOpenHiddenDescriptorRightRootOfEq A member.1 lane.source
        ((lane.realization.coherentTable A).table.toClassified A lane.source)
        hmove lane.realization.pivot at hroot
  rw [hroot]
  have hat := congrFun hpast
    ((lane.realization.pivot, inputTwo), inputOne)
  have hphysical := congrArg
    (fun output : ProfiledOpenRightClassifiedOutput A ↦
      pairedRightInformedForRow entryRow output.1.physical) hat
  cases entryRow <;>
    simpa [profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenRightSemanticClassifiedReceiver,
      profiledRightReceiverStrategy, pairedRightReceiverStrategy,
      pairedRightInformedForRow, procOnePairedEntryRightReceiverForRow,
      ProcOnePairedEntryRep.lambdaOfStrategy] using hphysical

/-- Left mirror: the witnessed process-one receiver is an exact output of
the original strategy at the provenance past and sticky entry row. -/
theorem exists_profiledOpenWitnessedLeftReceiverOutput_eq_rawReceiver
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I),
      ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₁) × In₂)),
        profiledOpenWitnessedLeftReceiverOutput A initialCode
            (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy
              hwin basis initialCode reachable evaluation entryRow)
            inputOne inputTwo =
          procTwoPairedEntryLeftReceiverForRow strategy
              (lane.realization.entry lane.realization.pivot) entryRow
            (taggedPast.map (fun old ↦ (old.1.2, old.2)))
            (inputOne, inputTwo) := by
  rcases evaluation with ⟨⟨member, root⟩, hevaluation⟩
  rcases hevaluation with
    ⟨witness, hmember, lane, hlane, hdescriptor, hmove, hroot,
      taggedPast, hpast⟩
  refine ⟨lane, taggedPast, ?_⟩
  change pairedLeftInformedForRow entryRow
        (profiledOpenFixedLeftQueryResponses A initialCode value query
          member ((root, inputOne), inputTwo)).1.physical = _
  change root =
      profiledOpenHiddenDescriptorLeftRootOfEq A member.1 lane.source
        ((lane.realization.coherentTable A).table.toClassified A lane.source)
        hmove lane.realization.pivot at hroot
  rw [hroot]
  have hat := congrFun hpast
    ((lane.realization.pivot, inputOne), inputTwo)
  have hphysical := congrArg
    (fun output : ProfiledOpenLeftClassifiedOutput A ↦
      pairedLeftInformedForRow entryRow output.1.physical) hat
  cases entryRow <;>
    simpa [profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, profiledOpenLeftSemanticClassifiedReceiver,
      profiledLeftReceiverStrategy, pairedLeftReceiverStrategy,
      pairedLeftInformedForRow, procTwoPairedEntryLeftReceiverForRow,
      ProcTwoPairedEntryRep.lambdaOfStrategy] using hphysical

end

/-! ## The same round as the final selected-block record -/

section
omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂]

/-- Arbitrary-retained-root right form of the selected-block projection. -/
theorem
    exists_profiledOpenWitnessedRightReceiverOutputAtRetainedRoot_eq_selectedBlockLast
    (overlay : ProfiledOpenWitnessedRightRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (closing : In₂ × In₁) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₂) × In₁)),
          let physicalPast := taggedPast.map (fun old ↦ (old.1.2, old.2))
          let memory : PairedStrategyMemory A strategy :=
            .processOne (lane.realization.entry decodedRoot)
              (lane.realization.minimum decodedRoot)
          let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
            .fromOne overlay.entryRow
              (physicalPast ++ [(inputTwo, inputOne)]) closing
          (PairedStrategyMemory.selectedBlockWord memory direction).getLast?.map
              RoundRecord.outputTwo =
            some (profiledOpenWitnessedRightReceiverOutput A initialCode
              overlay inputOne inputTwo) := by
  obtain ⟨lane, decodedRoot, taggedPast, houtput⟩ :=
    exists_profiledOpenWitnessedRightReceiverOutput_eq_rawReceiverAtRetainedRoot
      A strategy hwin basis initialCode overlay hsemantic inputOne inputTwo
  refine ⟨lane, decodedRoot, taggedPast, ?_⟩
  dsimp only
  rw [houtput]
  cases hrow : overlay.entryRow <;>
    simp [PairedStrategyMemory.selectedBlockWord,
      ProcOnePairedRightLambda.leftWord, ProcOnePairedRightLambda.bothWord,
      pairedRightWordFrom_append_singleton, rightRoundRecord,
      procOnePairedEntryRightReceiverForRow,
      ProcOnePairedEntryRep.lambdaOfStrategy]

/-- Left arbitrary-retained-root selected-block projection. -/
theorem
    exists_profiledOpenWitnessedLeftReceiverOutputAtRetainedRoot_eq_selectedBlockLast
    (overlay : ProfiledOpenWitnessedLeftRoundOverlay A initialCode)
    (hsemantic : overlay.SemanticallyReanchored A strategy hwin basis
      initialCode)
    (inputOne : In₁) (inputTwo : In₂) (closing : In₁ × In₂) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I),
      ∃ decodedRoot : {root // root ∈ lane.source.1},
        ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₁) × In₂)),
          let physicalPast := taggedPast.map (fun old ↦ (old.1.2, old.2))
          let memory : PairedStrategyMemory A strategy :=
            .processTwo (lane.realization.entry decodedRoot)
              (lane.realization.minimum decodedRoot)
          let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
            .fromTwo overlay.entryRow
              (physicalPast ++ [(inputOne, inputTwo)]) closing
          (PairedStrategyMemory.selectedBlockWord memory direction).getLast?.map
              RoundRecord.outputOne =
            some (profiledOpenWitnessedLeftReceiverOutput A initialCode
              overlay inputOne inputTwo) := by
  obtain ⟨lane, decodedRoot, taggedPast, houtput⟩ :=
    exists_profiledOpenWitnessedLeftReceiverOutput_eq_rawReceiverAtRetainedRoot
      A strategy hwin basis initialCode overlay hsemantic inputOne inputTwo
  refine ⟨lane, decodedRoot, taggedPast, ?_⟩
  dsimp only
  rw [houtput]
  cases hrow : overlay.entryRow <;>
    simp [PairedStrategyMemory.selectedBlockWord,
      ProcTwoPairedLeftLambda.rightWord, ProcTwoPairedLeftLambda.bothWord,
      pairedLeftWordFrom_append_singleton, leftRoundRecord,
      procTwoPairedEntryLeftReceiverForRow,
      ProcTwoPairedEntryRep.lambdaOfStrategy]

/-- The exact right receiver output is the process-two projection of the
last record of the raw selected block ending in the current move.  The next
closing input is irrelevant to `selectedBlockWord`; it is made explicit only
to form a complete paired direction. -/
theorem exists_profiledOpenWitnessedRightReceiverOutput_eq_selectedBlockLast
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂)
    (closing : In₂ × In₁) :
    ∃ lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I),
      ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₂) × In₁)),
        let physicalPast := taggedPast.map (fun old ↦ (old.1.2, old.2))
        let memory : PairedStrategyMemory A strategy :=
          .processOne (lane.realization.entry lane.realization.pivot)
            (lane.realization.minimum lane.realization.pivot)
        let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
          .fromOne entryRow (physicalPast ++ [(inputTwo, inputOne)]) closing
        (PairedStrategyMemory.selectedBlockWord memory direction).getLast?.map
            RoundRecord.outputTwo =
          some (profiledOpenWitnessedRightReceiverOutput A initialCode
            (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy
              hwin basis initialCode reachable evaluation entryRow)
            inputOne inputTwo) := by
  obtain ⟨lane, taggedPast, houtput⟩ :=
    exists_profiledOpenWitnessedRightReceiverOutput_eq_rawReceiver A strategy
      hwin basis initialCode reachable evaluation entryRow inputOne inputTwo
  refine ⟨lane, taggedPast, ?_⟩
  dsimp only
  rw [houtput]
  cases entryRow <;>
    simp [PairedStrategyMemory.selectedBlockWord,
      ProcOnePairedRightLambda.leftWord, ProcOnePairedRightLambda.bothWord,
      pairedRightWordFrom_append_singleton, rightRoundRecord,
      procOnePairedEntryRightReceiverForRow,
      ProcOnePairedEntryRep.lambdaOfStrategy]

/-- Left mirror of the selected-block final-round projection. -/
theorem exists_profiledOpenWitnessedLeftReceiverOutput_eq_selectedBlockLast
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (evaluation : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (entryRow : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂)
    (closing : In₁ × In₂) :
    ∃ lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I),
      ∃ taggedPast : List ((({root // root ∈ lane.source.1} × In₁) × In₂)),
        let physicalPast := taggedPast.map (fun old ↦ (old.1.2, old.2))
        let memory : PairedStrategyMemory A strategy :=
          .processTwo (lane.realization.entry lane.realization.pivot)
            (lane.realization.minimum lane.realization.pivot)
        let direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
          .fromTwo entryRow (physicalPast ++ [(inputOne, inputTwo)]) closing
        (PairedStrategyMemory.selectedBlockWord memory direction).getLast?.map
            RoundRecord.outputOne =
          some (profiledOpenWitnessedLeftReceiverOutput A initialCode
            (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy
              hwin basis initialCode reachable evaluation entryRow)
            inputOne inputTwo) := by
  obtain ⟨lane, taggedPast, houtput⟩ :=
    exists_profiledOpenWitnessedLeftReceiverOutput_eq_rawReceiver A strategy
      hwin basis initialCode reachable evaluation entryRow inputOne inputTwo
  refine ⟨lane, taggedPast, ?_⟩
  dsimp only
  rw [houtput]
  cases entryRow <;>
    simp [PairedStrategyMemory.selectedBlockWord,
      ProcTwoPairedLeftLambda.rightWord, ProcTwoPairedLeftLambda.bothWord,
      pairedLeftWordFrom_append_singleton, leftRoundRecord,
      procTwoPairedEntryLeftReceiverForRow,
      ProcTwoPairedEntryRep.lambdaOfStrategy]

end

end

end DetParityAutomaton

end DistributedSynthesis
