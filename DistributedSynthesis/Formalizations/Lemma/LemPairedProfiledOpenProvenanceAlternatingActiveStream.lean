/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceFiniteActivePivotStep
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedActiveLineage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDistinguishedSemanticEpochParity

/-!
# Infinite stream of finite active-pivot provenance steps

The one-step active selector chooses a literal member of the current finite
carrier and reselects from the nonempty opposite carrier after the exact
policy step.  This file iterates that selector on an infinite input-pair word.

The resulting query stream is aligned definitionally with the existing
distinguished-state recurrence, alternates its proof-side source orientation,
and selects an actually active pivot at every time.  Consequently it supplies
the two hypotheses of the fixed-lineage persistence theorem without using a
default lineage.  The side and pivot remain global proof coordinates; neither
is exposed to a process-local transition.
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
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable
  (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin
    basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable
  (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev ActiveStreamState :=
  ProfiledOpenProvenancePolicyAlternatingActiveState A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package

private abbrev ActiveStreamQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-- Iterate the finite active selector on the supplied physical input pairs. -/
noncomputable def profiledOpenProvenancePolicyAlternatingActiveStateAt
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) : Nat →
      ActiveStreamState A strategy hwin basis initialCode codePolicy fixedPolicy
        point initialRoot package
  | 0 => start
  | n + 1 =>
      (profiledOpenProvenancePolicyAlternatingActiveStateAt start input n).step
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package (input n).1 (input n).2

/-- The literal current-code query emitted at stream position `n`. -/
noncomputable def profiledOpenProvenancePolicyAlternatingActiveQueryAt
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
      ActiveStreamQuery A initialCode :=
  let current := profiledOpenProvenancePolicyAlternatingActiveStateAt A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
      package start input n
  current.query A strategy hwin basis initialCode codePolicy fixedPolicy point
    initialRoot package (input n).1 (input n).2

@[simp] theorem profiledOpenProvenancePolicyAlternatingActiveStateAt_zero
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) :
    profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
        0 = start :=
  rfl

theorem profiledOpenProvenancePolicyAlternatingActiveStateAt_succ
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
    profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          (n + 1) =
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input n).step A strategy hwin basis initialCode codePolicy fixedPolicy
            point initialRoot package (input n).1 (input n).2 :=
  rfl

/-- The emitted query uses exactly the selector's current proof-side source
orientation. -/
@[simp] theorem profiledOpenProvenancePolicyAlternatingActiveQueryAt_side
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
    (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
        n).1.1.1 =
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input n).side :=
  rfl

/-- The proof-side source orientation alternates at every finite step. -/
theorem profiledOpenProvenancePolicyAlternatingActiveStateAt_side_succ
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
    (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
        (n + 1)).side =
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input n).side.other := by
  rw [profiledOpenProvenancePolicyAlternatingActiveStateAt_succ]
  rfl

/-- Hence the emitted query word has the exact alternating-side law consumed
by active-lineage persistence. -/
theorem profiledOpenProvenancePolicyAlternatingActiveQuery_alternates
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) :
    ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
      (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input) := by
  refine
    profiledOpenProvenancePolicyDistinguishedQueryAlternates_of_side A
      initialCode
      (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input)
      (fun n =>
        (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            start input n).side) ?_ ?_
  · intro n
    exact profiledOpenProvenancePolicyAlternatingActiveQueryAt_side A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        start input n
  · intro n
    exact profiledOpenProvenancePolicyAlternatingActiveStateAt_side_succ A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package start input n

/-- The finite selector's current coordinate is exactly the pre-existing
distinguished recurrence started from the same finite state. -/
theorem profiledOpenProvenancePolicyAlternatingActiveStateAt_current
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) : ∀ n,
    (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
        n).current =
      profiledOpenProvenancePolicyDistinguishedStateAtFrom A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        start.current
        (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            start input) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledOpenProvenancePolicyAlternatingActiveStateAt_succ,
        ProfiledOpenProvenancePolicyAlternatingActiveState.step_current,
        profiledOpenProvenancePolicyDistinguishedStateAtFrom_succ, ih]
      rfl

/-- Root specialization of the current-state alignment. -/
theorem profiledOpenProvenancePolicyAlternatingActiveStateAt_current_root
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (hstart : start.current =
      profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
    (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
        n).current =
      profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
            start input) n := by
  rw [profiledOpenProvenancePolicyAlternatingActiveStateAt_current, hstart]
  rfl

/-- At every stream position the raw representative of the emitted finite
tag has the selected active-reflexive pivot. -/
theorem profiledOpenProvenancePolicyAlternatingActiveQuery_raw_active
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) (n : Nat) :
    let current := profiledOpenProvenancePolicyAlternatingActiveStateAt A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package start input n
    let descriptor :=
      profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package
          current.current
    let query := profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        start input n
    ProfiledOpenIndexedActiveReflexivePivot A descriptor.code current.side
      (profiledOpenIndexedRawDirectionOfFiniteTag A descriptor.code
        descriptor.moveIdentity query.1.2) := by
  dsimp only
  exact
    profiledOpenProvenancePolicyZeroOpenQueryOfActivePivot_raw_active A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          n).current
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          n).side
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          n).activePivot
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          n).activePivot.pivot
      (input n).1 (input n).2

/-- Root-aligned active selector streams discharge the literal pivot-activity
hypothesis of the fixed-lineage theorem. -/
theorem profiledOpenProvenancePolicyAlternatingActiveQuery_pivotActive
    (start : ActiveStreamState A strategy hwin basis initialCode codePolicy
      fixedPolicy point initialRoot package)
    (hstart : start.current =
      profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package)
    (input : Nat → In₁ × In₂) :
    ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input) := by
  intro n
  let current := profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy
    hwin basis initialCode codePolicy fixedPolicy point initialRoot package start
      input n
  have hcurrent :=
    profiledOpenProvenancePolicyAlternatingActiveStateAt_current_root A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        start hstart input n
  have hactive :=
    profiledOpenProvenancePolicyAlternatingActiveQuery_raw_active A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package start
        input n
  change
    match
      (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
          n).1.1.1 with
    | .right =>
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
            (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package start input) n)).code.rightSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
                basis initialCode codePolicy fixedPolicy point initialRoot
                  package
                  (profiledOpenProvenancePolicyAlternatingActiveQueryAt A
                    strategy hwin basis initialCode codePolicy fixedPolicy point
                      initialRoot package start input) n)).code
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
                basis initialCode codePolicy fixedPolicy point initialRoot
                  package
                  (profiledOpenProvenancePolicyAlternatingActiveQueryAt A
                    strategy hwin basis initialCode codePolicy fixedPolicy point
                      initialRoot package start input) n)).moveIdentity
            (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
                start input n).1.2).rightPivot.1 ≠ none
    | .left =>
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin basis
            initialCode codePolicy fixedPolicy point initialRoot package
            (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy
              hwin basis initialCode codePolicy fixedPolicy point initialRoot
                package start input) n)).code.leftSlots
          (profiledOpenIndexedRawDirectionOfFiniteTag A
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
                basis initialCode codePolicy fixedPolicy point initialRoot
                  package
                  (profiledOpenProvenancePolicyAlternatingActiveQueryAt A
                    strategy hwin basis initialCode codePolicy fixedPolicy point
                      initialRoot package start input) n)).code
            (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
              (profiledOpenProvenancePolicyDistinguishedStateAt A strategy hwin
                basis initialCode codePolicy fixedPolicy point initialRoot
                  package
                  (profiledOpenProvenancePolicyAlternatingActiveQueryAt A
                    strategy hwin basis initialCode codePolicy fixedPolicy point
                      initialRoot package start input) n)).moveIdentity
            (profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin
              basis initialCode codePolicy fixedPolicy point initialRoot package
                start input n).1.2).leftPivot.1 ≠ none
  rw [← hcurrent,
    profiledOpenProvenancePolicyAlternatingActiveQueryAt_side]
  cases hside :
      (profiledOpenProvenancePolicyAlternatingActiveStateAt A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package start
          input n).side with
  | right =>
      simp only [hside, ProfiledOpenIndexedActiveReflexivePivot] at hactive ⊢
      exact hactive.1
  | left =>
      simp only [hside, ProfiledOpenIndexedActiveReflexivePivot] at hactive ⊢
      exact hactive.1

/-! ## Root initialization and semantic parity -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every side of a live-both semantic point has a nonempty finite lineage
carrier.  This supplies the root seed without asking either process which
side the proof follows. -/
theorem profiledOpenIndexedLiveFresh_activeLineageCarrier_nonempty
    (live : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (side : IndexedLineageSide) :
    (profiledOpenIndexedActiveLineageCarrier A side
      (live.state.code A strategy hwin basis)).Nonempty := by
  classical
  cases side with
  | right =>
      let member := live.rightLane.realization.pivot
      let lineage := Classical.choose (live.rightLane.covers member)
      have hmember : live.rightLane.memberAt lineage = some member :=
        Classical.choose_spec (live.rightLane.covers member)
      refine ⟨lineage, ?_⟩
      rw [mem_profiledOpenIndexedActiveLineageCarrier_iff]
      change
        (live.state.right.slots A strategy hwin basis) lineage ≠ none
      rw [live.right_eq]
      simp only [ProfiledOpenIndexedRightSemanticShadow.slots, hmember,
        Option.map_some, ne_eq, Option.some_ne_none, not_false_eq_true]
  | left =>
      let member := live.leftLane.realization.pivot
      let lineage := Classical.choose (live.leftLane.covers member)
      have hmember : live.leftLane.memberAt lineage = some member :=
        Classical.choose_spec (live.leftLane.covers member)
      refine ⟨lineage, ?_⟩
      rw [mem_profiledOpenIndexedActiveLineageCarrier_iff]
      change
        (live.state.left.slots A strategy hwin basis) lineage ≠ none
      rw [live.left_eq]
      simp only [ProfiledOpenIndexedLeftSemanticShadow.slots, hmember,
        Option.map_some, ne_eq, Option.some_ne_none, not_false_eq_true]

/-- A live-both root code supplies a nonempty distinguished-root carrier on
either proof side.  The root equation is the only link needed between the
installed table point and the original live semantic point. -/
theorem
    profiledOpenProvenancePolicyDistinguishedInitial_carrier_nonempty_of_live
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (live : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hinitialCode : initialCode = live.state.code A strategy hwin basis)
    (side : IndexedLineageSide) :
    (profiledOpenIndexedActiveLineageCarrier A side
      (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
        (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package)
        ).code).Nonempty := by
  have hrootCode := congrArg Prod.fst hroot
  rw [profiledOpenIndexedProvenanceCodePolicy_run_nil A strategy hwin basis
    initialCode codePolicy] at hrootCode
  have hrootCode' :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).code = initialCode := by
    exact hrootCode
  have hlive :=
    profiledOpenIndexedLiveFresh_activeLineageCarrier_nonempty A strategy hwin
      basis live side
  rw [profiledOpenProvenancePolicyDistinguishedInitial_descriptor,
    hrootCode', hinitialCode]
  exact hlive

/-- Seed the infinite selector at the distinguished root from any nonempty
root carrier.  This is a proof-side choice of an active lineage/row candidate,
not a locally observable leader bit. -/
noncomputable def profiledOpenProvenancePolicyAlternatingActiveInitialState
    (side : IndexedLineageSide)
    (hnonempty :
      (profiledOpenIndexedActiveLineageCarrier A side
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package)
          ).code).Nonempty) :
    ActiveStreamState A strategy hwin basis initialCode codePolicy fixedPolicy
      point initialRoot package :=
  profiledOpenProvenancePolicyAlternatingActiveStateOfCarrier A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package
      (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package)
      side hnonempty

@[simp] theorem
    profiledOpenProvenancePolicyAlternatingActiveInitialState_current
    (side : IndexedLineageSide)
    (hnonempty :
      (profiledOpenIndexedActiveLineageCarrier A side
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package)
          ).code).Nonempty) :
    (profiledOpenProvenancePolicyAlternatingActiveInitialState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package side
        hnonempty).current =
      profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package :=
  rfl

/-- End-to-end strategy-level wrapper for the zero-open alternating branch:
the finite active selector produces a root-aligned query stream whose exact
semantic epoch block minima satisfy min-even parity. -/
theorem
    profiledOpenProvenancePolicyAlternatingActiveSemanticEpochBlockMinParity
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (side : IndexedLineageSide)
    (hnonempty :
      (profiledOpenIndexedActiveLineageCarrier A side
        (profiledOpenProvenancePolicyDistinguishedDescriptor A strategy hwin
          basis initialCode codePolicy fixedPolicy point initialRoot package
          (profiledOpenProvenancePolicyDistinguishedInitial A strategy hwin
            basis initialCode codePolicy fixedPolicy point initialRoot package)
          ).code).Nonempty)
    (input : Nat → In₁ × In₂) :
    let start :=
      profiledOpenProvenancePolicyAlternatingActiveInitialState A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package side
          hnonempty
    let query :=
      profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
    ∃ halternates :
        ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
          query,
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates := by
  let start :=
    profiledOpenProvenancePolicyAlternatingActiveInitialState A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package side
        hnonempty
  let query :=
    profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package start input
  have halternates :
      ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
        query :=
    profiledOpenProvenancePolicyAlternatingActiveQuery_alternates A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        start input
  have hactive :
      ProfiledOpenProvenancePolicyDistinguishedQueryPivotActive A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package
          query :=
    profiledOpenProvenancePolicyAlternatingActiveQuery_pivotActive A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        start (by rfl) input
  exact ⟨halternates,
    profiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity_of_query
      A strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package hroot query halternates hactive⟩

/-- Root-specialized live-both endpoint: the initial active carrier is now
discharged internally on either proof side. -/
theorem
    profiledOpenProvenancePolicyAlternatingActiveSemanticEpochBlockMinParity_of_live
    (hroot :
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point).1 = codePolicy.run [])
    (live : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hinitialCode : initialCode = live.state.code A strategy hwin basis)
    (side : IndexedLineageSide)
    (input : Nat → In₁ × In₂) :
    let hnonempty :=
      profiledOpenProvenancePolicyDistinguishedInitial_carrier_nonempty_of_live
        A strategy hwin basis initialCode codePolicy fixedPolicy point
          initialRoot package hroot live hinitialCode side
    let start :=
      profiledOpenProvenancePolicyAlternatingActiveInitialState A strategy hwin
        basis initialCode codePolicy fixedPolicy point initialRoot package side
          hnonempty
    let query :=
      profiledOpenProvenancePolicyAlternatingActiveQueryAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package start input
    ∃ halternates :
        ProfiledOpenProvenancePolicyDistinguishedQueryAlternates A initialCode
          query,
      ProfiledOpenProvenancePolicyDistinguishedSemanticEpochBlockMinParity A
        strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
          package query halternates := by
  exact
    profiledOpenProvenancePolicyAlternatingActiveSemanticEpochBlockMinParity A
      strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
        package hroot side
        (profiledOpenProvenancePolicyDistinguishedInitial_carrier_nonempty_of_live
          A strategy hwin basis initialCode codePolicy fixedPolicy point
            initialRoot package hroot live hinitialCode side)
        input

end

end DetParityAutomaton

end DistributedSynthesis
