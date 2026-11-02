/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndOperationalInitialCarrier
import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# The end-to-end finite local-summary automaton

This module joins the root-pinned initial streaming carrier to the verified
two-shadow post-initial kernel.  Every no-receive branch reads only local
finite state and local input.  Every receive branch reads the delivered
partner summary and both current inputs.  There is no graph argument and no
strict-leader bit.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 600000

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (bundle : EndToEndOperationalControllerPackage A)

/-! ## Full finite controls -/

inductive EndToEndOperationalOneControl where
  | root
  | initialLeft (state : EndToEndOperationalInitialLeft A bundle)
  | initialRightBlind (state : bundle.rightController.Control)
  | rootHybrid (state : EndToEndOperationalRootHybridOne A bundle)
  | initialLeftSeam (state :
      EndToEndOperationalInitialLeftSeamOne.{u, v, x, y, s,
        1} A bundle)
  | initialRightSeam (state :
      EndToEndOperationalInitialRightSeamOne.{u, v, x, y, s,
        1} A bundle)
  | post (state : EndToEndOperationalPostOne A bundle.rational)
  deriving Fintype

inductive EndToEndOperationalTwoControl where
  | root
  | initialLeftBlind (state : bundle.leftController.Control)
  | initialRight (state : EndToEndOperationalInitialRight A bundle)
  | rootHybrid (state : EndToEndOperationalRootHybridTwo A bundle)
  | initialLeftSeam (state :
      EndToEndOperationalInitialLeftSeamTwo.{u, v, x, y, s,
        1} A bundle)
  | initialRightSeam (state :
      EndToEndOperationalInitialRightSeamTwo.{u, v, x, y, s,
        1} A bundle)
  | post (state : EndToEndOperationalPostTwo A bundle.rational)
  deriving Fintype

abbrev EndToEndOperationalOneSummary :=
  EndToEndOperationalOneControl A bundle × Out₁

abbrev EndToEndOperationalTwoSummary :=
  EndToEndOperationalTwoControl A bundle × Out₂

noncomputable instance : Fintype
    (EndToEndOperationalOneSummary A bundle) := by
  classical
  infer_instance

noncomputable instance : Fintype
    (EndToEndOperationalTwoSummary A bundle) := by
  classical
  infer_instance

noncomputable def initialEndToEndOperationalOneSummary :
    EndToEndOperationalOneSummary A bundle := (.root, default)

noncomputable def initialEndToEndOperationalTwoSummary :
    EndToEndOperationalTwoSummary A bundle := (.root, default)

/-! ## Local no-receive tables -/

noncomputable def endToEndOperationalNoRecvOne
    (control : EndToEndOperationalOneControl A bundle) (input : In₁) :
    Out₁ × EndToEndOperationalOneControl A bundle :=
  match control with
  | .root =>
      let next := endToEndOperationalInitialRightBlind A bundle
        bundle.rightController.initial input
      (next.1, .initialRightBlind next.2)
  | .initialLeft state =>
      match state.2 with
      | none => (default, .initialLeft state)
      | some key =>
          let next := stepEndToEndGuardedFirstRightOwner A bundle.rational
            (initialEndToEndGuardedFirstRightOwner A bundle.rational key) input
          (next.1, .post (.inl (.inl next.2)))
  | .initialRightBlind state =>
      let next := endToEndOperationalInitialRightBlind A bundle state input
      (next.1, .initialRightBlind next.2)
  | .rootHybrid state =>
      match state.1.2 with
      | none => (default, .rootHybrid state)
      | some key =>
          let next := stepEndToEndGuardedFirstRightOwner A bundle.rational
            (initialEndToEndGuardedFirstRightOwner A bundle.rational key) input
          (next.1, .post (.inl (.inl next.2)))
  | .initialLeftSeam state =>
      let next := stepEndToEndGuardedFirstRightOwner A bundle.rational
        state.2.1 input
      (next.1, .post (.inl (.inl next.2)))
  | .initialRightSeam state =>
      let next := endToEndOperationalInitialRightBlind A bundle state.1 input
      (next.1, .initialRightBlind next.2)
  | .post state =>
      let next := endToEndOperationalPostNoRecvOne A bundle.rational state input
      (next.1, .post (next.2.getD state))

noncomputable def endToEndOperationalNoRecvTwo
    (control : EndToEndOperationalTwoControl A bundle) (input : In₂) :
    Out₂ × EndToEndOperationalTwoControl A bundle :=
  match control with
  | .root =>
      let next := endToEndOperationalInitialLeftBlind A bundle
        bundle.leftController.initial input
      (next.1, .initialLeftBlind next.2)
  | .initialLeftBlind state =>
      let next := endToEndOperationalInitialLeftBlind A bundle state input
      (next.1, .initialLeftBlind next.2)
  | .initialRight state =>
      match state.2 with
      | none => (default, .initialRight state)
      | some key =>
          let next := stepEndToEndGuardedFirstLeftOwner A bundle.rational
            (initialEndToEndGuardedFirstLeftOwner A bundle.rational key) input
          (next.1, .post (.inl (.inr (.inl next.2))))
  | .rootHybrid state =>
      match state.2.2 with
      | none => (default, .rootHybrid state)
      | some key =>
          let next := stepEndToEndGuardedFirstLeftOwner A bundle.rational
            (initialEndToEndGuardedFirstLeftOwner A bundle.rational key) input
          (next.1, .post (.inl (.inr (.inl next.2))))
  | .initialLeftSeam state =>
      let next := endToEndOperationalInitialLeftBlind A bundle state.1 input
      (next.1, .initialLeftBlind next.2)
  | .initialRightSeam state =>
      let next := stepEndToEndGuardedFirstLeftOwner A bundle.rational
        state.2.1 input
      (next.1, .post (.inl (.inr (.inl next.2))))
  | .post state =>
      let next := endToEndOperationalPostNoRecvTwo A bundle.rational state input
      (next.1, .post (next.2.getD state))

/-! ## Initial-anchor projections visible at receive -/

def endToEndOperationalInitialLeftOneAnchor :
    EndToEndOperationalOneControl A bundle →
      Option (EndToEndOperationalInitialLeft A bundle)
  | .initialLeft state => some state
  | .rootHybrid state => some state.1
  | .initialLeftSeam state => some state.1
  | _ => none

def endToEndOperationalInitialLeftTwoAnchor :
    EndToEndOperationalTwoControl A bundle →
      Option (bundle.leftController.Control × Bool)
  | .initialLeftBlind state => some (state, false)
  | .rootHybrid state => some (state.1, true)
  | .initialLeftSeam state => some (state.1, true)
  | _ => none

def endToEndOperationalInitialRightOneAnchor :
    EndToEndOperationalOneControl A bundle →
      Option (bundle.rightController.Control × Bool)
  | .initialRightBlind state => some (state, false)
  | .rootHybrid state => some (state.2, true)
  | .initialRightSeam state => some (state.1, true)
  | _ => none

def endToEndOperationalInitialRightTwoAnchor :
    EndToEndOperationalTwoControl A bundle →
      Option (EndToEndOperationalInitialRight A bundle)
  | .initialRight state => some state
  | .rootHybrid state => some state.2
  | .initialRightSeam state => some state.1
  | _ => none

noncomputable def endToEndOperationalRootHybridBothAgainOne
    (state : EndToEndOperationalRootHybridOne A bundle)
    (move : In₁ × In₂) : Out₁ :=
  (endToEndOperationalInitialLeftRecv A bundle state.1 move).1

noncomputable def endToEndOperationalRootHybridBothAgainTwo
    (state : EndToEndOperationalRootHybridTwo A bundle)
    (input : In₂) : Out₂ :=
  (endToEndOperationalInitialLeftBlind A bundle state.1 input).1

/-! ## Joint receive table -/

noncomputable def endToEndOperationalRecvPair
    (one : EndToEndOperationalOneControl A bundle)
    (two : EndToEndOperationalTwoControl A bundle) (move : In₁ × In₂) :
    EndToEndOperationalOneSummary A bundle ×
      EndToEndOperationalTwoSummary A bundle := by
  let fallback :=
    (initialEndToEndOperationalOneSummary A bundle,
      initialEndToEndOperationalTwoSummary A bundle)
  match one, two with
  | .root, .root =>
      let nextOne := endToEndOperationalRootRecvOne A bundle move
      let nextTwo := endToEndOperationalRootRecvTwo A bundle move
      exact ((.rootHybrid nextOne.2, nextOne.1),
        (.rootHybrid nextTwo.2, nextTwo.1))
  | .rootHybrid one, .rootHybrid two =>
      let next := endToEndOperationalInitialLeftSeamRecv A bundle one.1
        two.1 true move
      match next.2 with
      | none => exact fallback
      | some states =>
          exact ((.initialLeftSeam states.1,
              endToEndOperationalRootHybridBothAgainOne A bundle one move),
            (.initialLeftSeam states.2,
              endToEndOperationalRootHybridBothAgainTwo A bundle two move.2))
  | .post one, .initialLeftSeam two =>
      let next := endToEndOperationalPostRecv A bundle.rational one
        (.inl (.inl two.2.2)) move
      match next.2 with
      | none => exact fallback
      | some states => exact ((.post states.1, next.1.1),
          (.post states.2, next.1.2))
  | .initialRightSeam one, .post two =>
      let next := endToEndOperationalPostRecv A bundle.rational
        (.inl (.inr (.inl one.2.2))) two move
      match next.2 with
      | none => exact fallback
      | some states => exact ((.post states.1, next.1.1),
          (.post states.2, next.1.2))
  | .post one, .post two =>
      let next := endToEndOperationalPostRecv A bundle.rational one two move
      match next.2 with
      | none => exact fallback
      | some states => exact ((.post states.1, next.1.1),
          (.post states.2, next.1.2))
  | _, _ =>
      match endToEndOperationalInitialLeftOneAnchor A bundle one,
          endToEndOperationalInitialLeftTwoAnchor A bundle two with
      | some anchorOne, some anchorTwo =>
          let next := endToEndOperationalInitialLeftSeamRecv A bundle
            anchorOne anchorTwo.1 anchorTwo.2 move
          match next.2 with
          | none => exact fallback
          | some states => exact ((.initialLeftSeam states.1, next.1.1),
              (.initialLeftSeam states.2, next.1.2))
      | _, _ =>
          match endToEndOperationalInitialRightOneAnchor A bundle one,
              endToEndOperationalInitialRightTwoAnchor A bundle two with
          | some anchorOne, some anchorTwo =>
              let next := endToEndOperationalInitialRightSeamRecv A bundle
                anchorOne.1 anchorTwo anchorOne.2 move
              match next.2 with
              | none => exact fallback
              | some states => exact ((.initialRightSeam states.1, next.1.1),
                  (.initialRightSeam states.2, next.1.2))
          | _, _ => exact fallback

/-! ## Packaged local-summary automaton -/

noncomputable def endToEndOperationalSummaryAutomaton :
    LocalSummaryAutomaton In₁ In₂ where
  Summary
    | .one => EndToEndOperationalOneSummary A bundle
    | .two => EndToEndOperationalTwoSummary A bundle
  finite
    | .one => inferInstance
    | .two => inferInstance
  initial
    | .one => initialEndToEndOperationalOneSummary A bundle
    | .two => initialEndToEndOperationalTwoSummary A bundle
  stepNoRecv
    | .one, summary, .inl input =>
        let next := endToEndOperationalNoRecvOne A bundle summary.1 input
        (next.2, next.1)
    | .two, summary, .inr input =>
        let next := endToEndOperationalNoRecvTwo A bundle summary.1 input
        (next.2, next.1)
    | _, summary, _ => summary
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        (endToEndOperationalRecvPair A bundle self.1 other.1
          (inputOne, inputTwo)).1
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        (endToEndOperationalRecvPair A bundle other.1 self.1
          (inputOne, inputTwo)).2
    | _, self, _, _, _ => self

end

end DetParityAutomaton

end DistributedSynthesis
