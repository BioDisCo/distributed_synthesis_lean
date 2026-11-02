/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOperationalInitialSeam

/-!
# The finite local-summary automaton of the profiled readback

This is the executable distributed carrier.  `noRecv` branches inspect only
the local state and local input.  `recv` branches inspect the local state,
the delivered partner summary, and the two current inputs.  No transition is
parameterized by the current graph or by a strict-leader predicate.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (rightBasis : ∀ target profile,
    (rightProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (leftBasis : ∀ target profile,
    (leftProfiledGuardedAutomaton A target profile).RationalRunBasis)
  (controllers : LocallyConsistentProfiledGuardedInitialControllers
    A strategy hwin rightBasis leftBasis)
  (firstBank : FiniteProfiledGuardedFirstControllerBank A)

abbrev ProfiledOpOne := ProfiledOperationalOneControl A strategy hwin
  rightBasis leftBasis controllers firstBank

abbrev ProfiledOpTwo := ProfiledOperationalTwoControl A strategy hwin
  rightBasis leftBasis controllers firstBank

noncomputable def profiledOpOneMarker :
    ProfiledOperationalInitialLeft A strategy hwin rightBasis leftBasis
      controllers :=
  (profiledGuardedInitialLeftFiniteReadbackInitial A strategy hwin rightBasis
    leftBasis controllers, none)

noncomputable def profiledOpTwoMarker :
    ProfiledOperationalInitialRight A strategy hwin rightBasis leftBasis
      controllers :=
  (profiledGuardedInitialRightFiniteReadbackInitial A strategy hwin rightBasis
    leftBasis controllers, none)

def profiledOpOneOfPost
    (state : ProfiledOperationalPostOne A firstBank) :
    ProfiledOpOne A strategy hwin rightBasis leftBasis controllers firstBank :=
  match state with
  | .inl state => .post (profiledOpOneMarker A strategy hwin rightBasis
      leftBasis controllers) state
  | .inr state => .overlap (profiledOpOneMarker A strategy hwin rightBasis
      leftBasis controllers) state

def profiledOpTwoOfPost
    (state : ProfiledOperationalPostTwo A firstBank) :
    ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers firstBank :=
  match state with
  | .inl state => .post (profiledOpTwoMarker A strategy hwin rightBasis
      leftBasis controllers) state
  | .inr state => .overlap (profiledOpTwoMarker A strategy hwin rightBasis
      leftBasis controllers) state

/-! ## Local no-receive tables -/

noncomputable def profiledOperationalNoRecvOne
    (control : ProfiledOpOne A strategy hwin rightBasis leftBasis controllers
      firstBank) (input : In₁) :
    Out₁ × ProfiledOpOne A strategy hwin rightBasis leftBasis controllers
      firstBank :=
  match control with
  | .root _ =>
      let next := profiledInitialRightAnchorBlind A strategy hwin rightBasis
        leftBasis controllers controllers.rightController.initial input
      (next.1, .initialRightBlind next.2)
  | .initialLeft state =>
      match state.2 with
      | none => (default, .initialLeft state)
      | some key =>
          let next := stepProfiledGuardedFirstRightOwner A firstBank
            (initialProfiledGuardedFirstRightOwner A firstBank key) input
          (next.1, .post (profiledOpOneMarker A strategy hwin rightBasis
            leftBasis controllers) (.inl next.2))
  | .initialRightBlind state =>
      let next := profiledInitialRightAnchorBlind A strategy hwin rightBasis
        leftBasis controllers state input
      (next.1, .initialRightBlind next.2)
  | .rootHybrid state =>
      match state.1.2 with
      | none => (default, .rootHybrid state)
      | some key =>
          let next := stepProfiledGuardedFirstRightOwner A firstBank
            (initialProfiledGuardedFirstRightOwner A firstBank key) input
          (next.1, .post (profiledOpOneMarker A strategy hwin rightBasis
            leftBasis controllers) (.inl next.2))
  | .initialLeftSeam state =>
      let next := stepProfiledGuardedFirstRightOwner A firstBank state.2.1
        input
      (next.1, .post (profiledOpOneMarker A strategy hwin rightBasis
        leftBasis controllers) (.inl next.2))
  | .initialRightSeam state =>
      let next := profiledInitialRightAnchorBlind A strategy hwin rightBasis
        leftBasis controllers state.1 input
      (next.1, .initialRightBlind next.2)
  | .post marker state =>
      let next := profiledOperationalPostNoRecvOne A firstBank (.inl state)
        input
      (next.1, next.2.map (profiledOpOneOfPost A strategy hwin rightBasis
        leftBasis controllers firstBank) |>.getD (.post marker state))
  | .overlap marker state =>
      let next := profiledOperationalPostNoRecvOne A firstBank (.inr state)
        input
      (next.1, next.2.map (profiledOpOneOfPost A strategy hwin rightBasis
        leftBasis controllers firstBank) |>.getD (.overlap marker state))

noncomputable def profiledOperationalNoRecvTwo
    (control : ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers
      firstBank) (input : In₂) :
    Out₂ × ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers
      firstBank :=
  match control with
  | .root _ =>
      let next := profiledInitialLeftAnchorBlind A strategy hwin rightBasis
        leftBasis controllers controllers.leftController.initial input
      (next.1, .initialLeftBlind next.2)
  | .initialLeftBlind state =>
      let next := profiledInitialLeftAnchorBlind A strategy hwin rightBasis
        leftBasis controllers state input
      (next.1, .initialLeftBlind next.2)
  | .initialRight state =>
      match state.2 with
      | none => (default, .initialRight state)
      | some key =>
          let next := stepProfiledGuardedFirstLeftOwner A firstBank
            (initialProfiledGuardedFirstLeftOwner A firstBank key) input
          (next.1, .post (profiledOpTwoMarker A strategy hwin rightBasis
            leftBasis controllers) (.inr (.inl next.2)))
  | .rootHybrid state =>
      match state.2.2 with
      | none => (default, .rootHybrid state)
      | some key =>
          let next := stepProfiledGuardedFirstLeftOwner A firstBank
            (initialProfiledGuardedFirstLeftOwner A firstBank key) input
          (next.1, .post (profiledOpTwoMarker A strategy hwin rightBasis
            leftBasis controllers) (.inr (.inl next.2)))
  | .initialLeftSeam state =>
      let next := profiledInitialLeftAnchorBlind A strategy hwin rightBasis
        leftBasis controllers state.1 input
      (next.1, .initialLeftBlind next.2)
  | .initialRightSeam state =>
      let next := stepProfiledGuardedFirstLeftOwner A firstBank state.2.1 input
      (next.1, .post (profiledOpTwoMarker A strategy hwin rightBasis
        leftBasis controllers) (.inr (.inl next.2)))
  | .post marker state =>
      let next := profiledOperationalPostNoRecvTwo A firstBank (.inl state)
        input
      (next.1, next.2.map (profiledOpTwoOfPost A strategy hwin rightBasis
        leftBasis controllers firstBank) |>.getD (.post marker state))
  | .overlap marker state =>
      let next := profiledOperationalPostNoRecvTwo A firstBank (.inr state)
        input
      (next.1, next.2.map (profiledOpTwoOfPost A strategy hwin rightBasis
        leftBasis controllers firstBank) |>.getD (.overlap marker state))

/-! ## Receive classification and joint table -/

def profiledInitialLeftOneAnchor :
    ProfiledOpOne A strategy hwin rightBasis leftBasis controllers firstBank →
      Option (ProfiledOperationalInitialLeft A strategy hwin rightBasis
        leftBasis controllers)
  | .initialLeft state => some state
  | .rootHybrid state => some state.1
  | .initialLeftSeam state => some state.1
  | _ => none

def profiledInitialLeftTwoAnchor :
    ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers firstBank →
      Option (controllers.leftController.Control × Bool)
  | .initialLeftBlind state => some (state, false)
  | .rootHybrid state => some (state.1, true)
  | .initialLeftSeam state => some (state.1, true)
  | _ => none

def profiledInitialRightOneAnchor :
    ProfiledOpOne A strategy hwin rightBasis leftBasis controllers firstBank →
      Option (controllers.rightController.Control × Bool)
  | .initialRightBlind state => some (state, false)
  | .rootHybrid state => some (state.2, true)
  | .initialRightSeam state => some (state.1, true)
  | _ => none

def profiledInitialRightTwoAnchor :
    ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers firstBank →
      Option (ProfiledOperationalInitialRight A strategy hwin rightBasis
        leftBasis controllers)
  | .initialRight state => some state
  | .rootHybrid state => some state.2
  | .initialRightSeam state => some state.1
  | _ => none

noncomputable def profiledOperationalRecvPair
    (one : ProfiledOpOne A strategy hwin rightBasis leftBasis controllers
      firstBank)
    (two : ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers
      firstBank) (move : In₁ × In₂) :
    (ProfiledOpOne A strategy hwin rightBasis leftBasis controllers firstBank ×
      Out₁) ×
    (ProfiledOpTwo A strategy hwin rightBasis leftBasis controllers firstBank ×
      Out₂) := by
  let fallback :=
    (initialProfiledOperationalOneSummary A strategy hwin rightBasis leftBasis
        controllers firstBank,
      initialProfiledOperationalTwoSummary A strategy hwin rightBasis leftBasis
        controllers firstBank)
  match one, two with
  | .root _, .root _ =>
      let nextOne := profiledRootRecvOne A strategy hwin rightBasis leftBasis
        controllers move
      let nextTwo := profiledRootRecvTwo A strategy hwin rightBasis leftBasis
        controllers move
      exact ((.rootHybrid nextOne.2, nextOne.1),
        (.rootHybrid nextTwo.2, nextTwo.1))
  | .rootHybrid one, .rootHybrid two =>
      let next := profiledInitialLeftSeamRecv A strategy hwin rightBasis
        leftBasis controllers firstBank one.1 two.1 true move
      match next.2 with
      | none => exact fallback
      | some states =>
          exact ((.initialLeftSeam states.1,
              profiledRootHybridBothAgainOne A strategy hwin rightBasis
                leftBasis controllers one move),
            (.initialLeftSeam states.2,
              profiledRootHybridBothAgainTwo A strategy hwin rightBasis
                leftBasis controllers two move.2))
  | .post _ one, .initialLeftSeam two =>
      let next := profiledOperationalPostRecvRight A firstBank one
        (.inl two.2.2) move
      match next.2 with
      | none => exact fallback
      | some states => exact
          ((profiledOpOneOfPost A strategy hwin rightBasis leftBasis
              controllers firstBank states.1, next.1.1),
            (profiledOpTwoOfPost A strategy hwin rightBasis leftBasis
              controllers firstBank states.2, next.1.2))
  | .initialRightSeam one, .post _ two =>
      let next := profiledOperationalPostRecvLeft A firstBank
        (.inr (.inl one.2.2)) two move
      match next.2 with
      | none => exact fallback
      | some states => exact
          ((profiledOpOneOfPost A strategy hwin rightBasis leftBasis
              controllers firstBank states.1, next.1.1),
            (profiledOpTwoOfPost A strategy hwin rightBasis leftBasis
              controllers firstBank states.2, next.1.2))
  | _, _ =>
      let postOne : Option (ProfiledOperationalPostOne A firstBank) :=
        match one with
        | .post _ state => some (.inl state)
        | .overlap _ state => some (.inr state)
        | _ => none
      let postTwo : Option (ProfiledOperationalPostTwo A firstBank) :=
        match two with
        | .post _ state => some (.inl state)
        | .overlap _ state => some (.inr state)
        | _ => none
      match postOne, postTwo with
      | some postOne, some postTwo =>
          let next := profiledOperationalPostRecv A firstBank postOne postTwo
            move
          match next.2 with
          | none => exact fallback
          | some states => exact
              ((profiledOpOneOfPost A strategy hwin rightBasis leftBasis
                  controllers firstBank states.1, next.1.1),
                (profiledOpTwoOfPost A strategy hwin rightBasis leftBasis
                  controllers firstBank states.2, next.1.2))
      | _, _ =>
          match profiledInitialLeftOneAnchor A strategy hwin rightBasis
              leftBasis controllers firstBank one,
            profiledInitialLeftTwoAnchor A strategy hwin rightBasis leftBasis
              controllers firstBank two with
          | some anchorOne, some anchorTwo =>
              let next := profiledInitialLeftSeamRecv A strategy hwin
                rightBasis leftBasis controllers firstBank anchorOne
                anchorTwo.1 anchorTwo.2 move
              match next.2 with
              | none => exact fallback
              | some states => exact
                  ((.initialLeftSeam states.1, next.1.1),
                    (.initialLeftSeam states.2, next.1.2))
          | _, _ =>
              match profiledInitialRightOneAnchor A strategy hwin rightBasis
                  leftBasis controllers firstBank one,
                profiledInitialRightTwoAnchor A strategy hwin rightBasis
                  leftBasis controllers firstBank two with
              | some anchorOne, some anchorTwo =>
                  let next := profiledInitialRightSeamRecv A strategy hwin
                    rightBasis leftBasis controllers firstBank anchorOne.1
                    anchorTwo anchorOne.2 move
                  match next.2 with
                  | none => exact fallback
                  | some states => exact
                      ((.initialRightSeam states.1, next.1.1),
                        (.initialRightSeam states.2, next.1.2))
              | _, _ => exact fallback

/-! ## The packaged local-summary automaton -/

noncomputable def profiledOperationalSummaryAutomaton :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => ProfiledOperationalOneSummary A strategy hwin rightBasis
        leftBasis controllers firstBank
    | .two => ProfiledOperationalTwoSummary A strategy hwin rightBasis
        leftBasis controllers firstBank
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => initialProfiledOperationalOneSummary A strategy hwin rightBasis
        leftBasis controllers firstBank
    | .two => initialProfiledOperationalTwoSummary A strategy hwin rightBasis
        leftBasis controllers firstBank
  stepNoRecv
    | .one, summary, .inl input =>
        let next := profiledOperationalNoRecvOne A strategy hwin rightBasis
          leftBasis controllers firstBank summary.1 input
        (next.2, next.1)
    | .two, summary, .inr input =>
        let next := profiledOperationalNoRecvTwo A strategy hwin rightBasis
          leftBasis controllers firstBank summary.1 input
        (next.2, next.1)
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        (profiledOperationalRecvPair A strategy hwin rightBasis leftBasis
          controllers firstBank self.1 other.1 (inputOne, inputTwo)).1
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        (profiledOperationalRecvPair A strategy hwin rightBasis leftBasis
          controllers firstBank other.1 self.1 (inputOne, inputTwo)).2
    | _, self, _, _, _ => self

end

end

end DetParityAutomaton

end DistributedSynthesis
