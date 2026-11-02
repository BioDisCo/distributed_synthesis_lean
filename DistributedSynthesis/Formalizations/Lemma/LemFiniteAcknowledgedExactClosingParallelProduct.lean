/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDependentBank

/-!
# Parallel product of exact-closing blind families

The two literal seam orientations must be retained simultaneously.  This file
forms their pointwise product inside every fixed finite bank fibre.  Both
components advance on every local transition; the first component supplies
the physical output and the second is retained as a finite shadow.  The
semantic close relation and the two endpoint-local blind relations are
componentwise conjunctions.

The construction contains no runtime selector.  In particular none of its
executable maps receives a graph, orientation, hierarchy side, leader bit,
history, or view.  A concrete trace proof separately establishes that the
chosen physical projection is the required semantic output.
-/

namespace DistributedSynthesis

universe u v x y k c₁ c₂ d₁ d₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace FiniteExactClosingBlindFamily

variable {Key : Type k}
variable
  (first : FiniteExactClosingBlindFamily.{u, v, x, y, k, c₁, c₂}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) Key)
  (second : FiniteExactClosingBlindFamily.{u, v, x, y, k, d₁, d₂}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂) Key)

/-- The componentwise exact-close family.  Both components advance, while
the first component supplies the physical output. -/
noncomputable def parallelBase :
    FiniteExactClosingFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  ControlOne key :=
    first.base.ControlOne key × second.base.ControlOne key
  ControlTwo key :=
    first.base.ControlTwo key × second.base.ControlTwo key
  oneFinite key := by
    letI := first.base.oneFinite key
    letI := second.base.oneFinite key
    infer_instance
  twoFinite key := by
    letI := first.base.twoFinite key
    letI := second.base.twoFinite key
    infer_instance
  initialOne key :=
    (first.base.initialOne key, second.base.initialOne key)
  initialTwo key :=
    (first.base.initialTwo key, second.base.initialTwo key)
  noRecvOne key state input :=
    let firstNext := first.base.noRecvOne key state.1 input
    let secondNext := second.base.noRecvOne key state.2 input
    ((firstNext.1, secondNext.1), firstNext.2)
  noRecvTwo key state input :=
    let firstNext := first.base.noRecvTwo key state.1 input
    let secondNext := second.base.noRecvTwo key state.2 input
    ((firstNext.1, secondNext.1), firstNext.2)
  openRecvOne key one inputOne two inputTwo :=
    let firstNext := first.base.openRecvOne key one.1 inputOne two.1 inputTwo
    let secondNext :=
      second.base.openRecvOne key one.2 inputOne two.2 inputTwo
    ((firstNext.1, secondNext.1), firstNext.2)
  openRecvTwo key two inputTwo one inputOne :=
    let firstNext := first.base.openRecvTwo key two.1 inputTwo one.1 inputOne
    let secondNext :=
      second.base.openRecvTwo key two.2 inputTwo one.2 inputOne
    ((firstNext.1, secondNext.1), firstNext.2)
  close key one inputOne two inputTwo :=
    let firstNext := first.base.close key one.1 inputOne two.1 inputTwo
    let secondNext := second.base.close key one.2 inputOne two.2 inputTwo
    ((firstNext.1, secondNext.1), (firstNext.2, secondNext.2))
  Rel key one two :=
    first.base.Rel key one.1 two.1 ∧ second.base.Rel key one.2 two.2
  laws key := by
    refine {
      initial := ⟨(first.base.laws key).initial,
        (second.base.laws key).initial⟩
      strictRight := ?_
      strictLeft := ?_
      both := ?_ }
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).strictRight one.1 inputOne two.1
          inputTwo hrel.1,
        (second.base.laws key).strictRight one.2 inputOne two.2 inputTwo
          hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).strictLeft one.1 inputOne two.1
          inputTwo hrel.1,
        (second.base.laws key).strictLeft one.2 inputOne two.2 inputTwo
          hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).both one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.base.laws key).both one.2 inputOne two.2 inputTwo hrel.2⟩

/-- Parallel retention of two exact-closing blind families.  The relations
are componentwise; there is no active-orientation coordinate. -/
noncomputable def parallel :
    FiniteExactClosingBlindFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  base := first.parallelBase second
  BlindOne key left right :=
    first.BlindOne key left.1 right.1 ∧
      second.BlindOne key left.2 right.2
  BlindTwo key left right :=
    first.BlindTwo key left.1 right.1 ∧
      second.BlindTwo key left.2 right.2
  noRecvLaws key := by
    refine { one := ?_, two := ?_ }
    · intro left right input hblind
      have hfirst :=
        (first.noRecvLaws key).one left.1 right.1 input hblind.1
      have hsecond :=
        (second.noRecvLaws key).one left.2 right.2 input hblind.2
      exact ⟨hfirst.1, hfirst.2, hsecond.2⟩
    · intro left right input hblind
      have hfirst :=
        (first.noRecvLaws key).two left.1 right.1 input hblind.1
      have hsecond :=
        (second.noRecvLaws key).two left.2 right.2 input hblind.2
      exact ⟨hfirst.1, hfirst.2, hsecond.2⟩
  receiveLaws key := by
    refine { one := ?_, two := ?_ }
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.receiveLaws key).one one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.receiveLaws key).one one.2 inputOne two.2 inputTwo hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.receiveLaws key).two one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.receiveLaws key).two one.2 inputOne two.2 inputTwo hrel.2⟩

/-! ## Crossed endpoint-handler outputs

For the literal application, `first` is the seam whose homogeneous block uses
process one's receive and process two's no-receive handlers; `second` is its
mirror.  The following product therefore takes `openRecvOne` and `noRecvTwo`
outputs from `first`, and `noRecvOne` and `openRecvTwo` outputs from `second`.
This is a fixed property of the four local handler definitions, not a runtime
orientation test. -/

/-- Componentwise transitions with the explicit crossed physical-output
projection used by the two symmetric seam orientations. -/
noncomputable def crossedHandlerBase :
    FiniteExactClosingFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  ControlOne key :=
    first.base.ControlOne key × second.base.ControlOne key
  ControlTwo key :=
    first.base.ControlTwo key × second.base.ControlTwo key
  oneFinite key := by
    letI := first.base.oneFinite key
    letI := second.base.oneFinite key
    infer_instance
  twoFinite key := by
    letI := first.base.twoFinite key
    letI := second.base.twoFinite key
    infer_instance
  initialOne key :=
    (first.base.initialOne key, second.base.initialOne key)
  initialTwo key :=
    (first.base.initialTwo key, second.base.initialTwo key)
  noRecvOne key state input :=
    let firstNext := first.base.noRecvOne key state.1 input
    let secondNext := second.base.noRecvOne key state.2 input
    ((firstNext.1, secondNext.1), secondNext.2)
  noRecvTwo key state input :=
    let firstNext := first.base.noRecvTwo key state.1 input
    let secondNext := second.base.noRecvTwo key state.2 input
    ((firstNext.1, secondNext.1), firstNext.2)
  openRecvOne key one inputOne two inputTwo :=
    let firstNext := first.base.openRecvOne key one.1 inputOne two.1 inputTwo
    let secondNext :=
      second.base.openRecvOne key one.2 inputOne two.2 inputTwo
    ((firstNext.1, secondNext.1), firstNext.2)
  openRecvTwo key two inputTwo one inputOne :=
    let firstNext := first.base.openRecvTwo key two.1 inputTwo one.1 inputOne
    let secondNext :=
      second.base.openRecvTwo key two.2 inputTwo one.2 inputOne
    ((firstNext.1, secondNext.1), secondNext.2)
  close key one inputOne two inputTwo :=
    let firstNext := first.base.close key one.1 inputOne two.1 inputTwo
    let secondNext := second.base.close key one.2 inputOne two.2 inputTwo
    ((firstNext.1, secondNext.1), (firstNext.2, secondNext.2))
  Rel key one two :=
    first.base.Rel key one.1 two.1 ∧ second.base.Rel key one.2 two.2
  laws key := by
    refine {
      initial := ⟨(first.base.laws key).initial,
        (second.base.laws key).initial⟩
      strictRight := ?_
      strictLeft := ?_
      both := ?_ }
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).strictRight one.1 inputOne two.1
          inputTwo hrel.1,
        (second.base.laws key).strictRight one.2 inputOne two.2 inputTwo
          hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).strictLeft one.1 inputOne two.1
          inputTwo hrel.1,
        (second.base.laws key).strictLeft one.2 inputOne two.2 inputTwo
          hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.base.laws key).both one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.base.laws key).both one.2 inputOne two.2 inputTwo hrel.2⟩

/-- The simultaneous two-orientation family with fixed crossed handler
outputs.  No control contains or computes an active-orientation selector. -/
noncomputable def crossedHandlers :
    FiniteExactClosingBlindFamily (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂) Key where
  base := first.crossedHandlerBase second
  BlindOne key left right :=
    first.BlindOne key left.1 right.1 ∧
      second.BlindOne key left.2 right.2
  BlindTwo key left right :=
    first.BlindTwo key left.1 right.1 ∧
      second.BlindTwo key left.2 right.2
  noRecvLaws key := by
    refine { one := ?_, two := ?_ }
    · intro left right input hblind
      have hfirst :=
        (first.noRecvLaws key).one left.1 right.1 input hblind.1
      have hsecond :=
        (second.noRecvLaws key).one left.2 right.2 input hblind.2
      exact ⟨hsecond.1, hfirst.2, hsecond.2⟩
    · intro left right input hblind
      have hfirst :=
        (first.noRecvLaws key).two left.1 right.1 input hblind.1
      have hsecond :=
        (second.noRecvLaws key).two left.2 right.2 input hblind.2
      exact ⟨hfirst.1, hfirst.2, hsecond.2⟩
  receiveLaws key := by
    refine { one := ?_, two := ?_ }
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.receiveLaws key).one one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.receiveLaws key).one one.2 inputOne two.2 inputTwo hrel.2⟩
    · intro one inputOne two inputTwo hrel
      exact ⟨(first.receiveLaws key).two one.1 inputOne two.1 inputTwo
          hrel.1,
        (second.receiveLaws key).two one.2 inputOne two.2 inputTwo hrel.2⟩

end FiniteExactClosingBlindFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
