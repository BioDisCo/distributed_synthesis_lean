/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDeferredRelationalTransient

/-!
# The canonical selected trace of an exact-closing controller

The selected-trace interface is useful when a concrete runtime controller is
related to a simpler semantic controller.  The semantic controller itself
should not create an additional proof obligation: its actual deterministic
run is already a selected trace.

This file defines that run directly from the environment and proves the
corresponding `ExactClosingSelectedTraceLaws`.  The construction is entirely
proof-side.  Executable endpoint maps still receive only their local control
and locally available inputs; no graph, orientation, leader, history, or view
is added to them.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

section

variable
  (initialOne : Control₁) (initialTwo : Control₂)
  (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
  (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
  (openRecvOne : Control₁ → In₁ → Control₂ → In₂ →
    Control₁ × Out₁)
  (openRecvTwo : Control₂ → In₂ → Control₁ → In₁ →
    Control₂ × Out₂)
  (close : Control₁ → In₁ → Control₂ → In₂ →
    Control₁ × Control₂)
  (env : EnvironmentSequence In₁ In₂)

/-- The deterministic pair of semantic controls before round `n`. -/
def exactClosingSemanticPairTrace : Nat → Control₁ × Control₂
  | 0 => (initialOne, initialTwo)
  | n + 1 =>
      let prior := exactClosingSemanticPairTrace n
      match (env n).graph with
      | .right =>
          ((noRecvOne prior.1 (env n).inputOne).1,
            (openRecvTwo prior.2 (env n).inputTwo prior.1
              (env n).inputOne).1)
      | .left =>
          ((openRecvOne prior.1 (env n).inputOne prior.2
              (env n).inputTwo).1,
            (noRecvTwo prior.2 (env n).inputTwo).1)
      | .both =>
          close prior.1 (env n).inputOne prior.2 (env n).inputTwo

/-- Physical process-one output of the canonical semantic run. -/
def exactClosingSemanticOutputOne (n : Nat) : Out₁ :=
  let prior := exactClosingSemanticPairTrace initialOne initialTwo noRecvOne
    noRecvTwo openRecvOne openRecvTwo close env n
  match (env n).graph with
  | .right => (noRecvOne prior.1 (env n).inputOne).2
  | .left | .both =>
      (openRecvOne prior.1 (env n).inputOne prior.2 (env n).inputTwo).2

/-- Physical process-two output of the canonical semantic run. -/
def exactClosingSemanticOutputTwo (n : Nat) : Out₂ :=
  let prior := exactClosingSemanticPairTrace initialOne initialTwo noRecvOne
    noRecvTwo openRecvOne openRecvTwo close env n
  match (env n).graph with
  | .right | .both =>
      (openRecvTwo prior.2 (env n).inputTwo prior.1 (env n).inputOne).2
  | .left => (noRecvTwo prior.2 (env n).inputTwo).2

/-- A control pair is selected at time `n` exactly when it is the canonical
semantic pair reached before round `n`. -/
def ExactClosingCanonicalSelected
    (one : Control₁) (two : Control₂) (n : Nat) : Prop :=
  (one, two) = exactClosingSemanticPairTrace initialOne initialTwo noRecvOne
    noRecvTwo openRecvOne openRecvTwo close env n

/-- Every deterministic exact-closing semantic controller supplies its own
selected trace.  `Rel` is intentionally irrelevant here: a later relational
adapter uses it only to connect a different runtime presentation to this
canonical semantic run. -/
theorem exactClosingCanonicalSelectedTraceLaws
    (Rel : Control₁ → Control₂ → Prop) :
    ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel
      (ExactClosingCanonicalSelected initialOne initialTwo noRecvOne noRecvTwo
        openRecvOne openRecvTwo close env)
      env
      (exactClosingSemanticOutputOne initialOne initialTwo noRecvOne noRecvTwo
        openRecvOne openRecvTwo close env)
      (exactClosingSemanticOutputTwo initialOne initialTwo noRecvOne noRecvTwo
        openRecvOne openRecvTwo close env) := by
  refine {
    initial := rfl
    strictRight := ?_
    strictLeft := ?_
    both := ?_ }
  · intro n one two _hrel hselected hgraph
    change (one, two) = _ at hselected
    have hone : one = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hselected
    have htwo : two = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hselected
    rw [hone, htwo]
    simp only [ExactClosingCanonicalSelected,
      exactClosingSemanticPairTrace, hgraph,
      exactClosingSemanticOutputOne, exactClosingSemanticOutputTwo]
    exact ⟨trivial, trivial, trivial⟩
  · intro n one two _hrel hselected hgraph
    change (one, two) = _ at hselected
    have hone : one = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hselected
    have htwo : two = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hselected
    rw [hone, htwo]
    simp only [ExactClosingCanonicalSelected,
      exactClosingSemanticPairTrace, hgraph,
      exactClosingSemanticOutputOne, exactClosingSemanticOutputTwo]
    exact ⟨trivial, trivial, trivial⟩
  · intro n one two _hrel hselected hgraph
    change (one, two) = _ at hselected
    have hone : one = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).1 := by
      simpa only [Prod.fst] using congrArg Prod.fst hselected
    have htwo : two = (exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n).2 := by
      simpa only [Prod.snd] using congrArg Prod.snd hselected
    rw [hone, htwo]
    simp only [ExactClosingCanonicalSelected,
      exactClosingSemanticPairTrace, hgraph,
      exactClosingSemanticOutputOne, exactClosingSemanticOutputTwo]
    exact ⟨trivial, trivial, trivial⟩

end

/-! ## One-arrow joint-relational bank endpoint -/

universe k a b c d e f

namespace FiniteDeferredExactClosingFamily

variable {Key : Type k}
variable
  (family : FiniteDeferredExactClosingFamily.{u, v, x, y, k, a, b, c, d, e, f}
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      Key)

noncomputable section

/-- A joint relational simulation feeds the bank endpoint using the semantic
controller's canonical deterministic trace.  Concrete code no longer owes a
separate semantic selected-trace induction. -/
noncomputable def
    bankMealyTraceInvariant_of_joint_relational_canonical_fibre
    [Fintype Key]
    (key : Key)
    (semanticInitialOne : family.RecurrentOne key)
    (semanticInitialTwo : family.RecurrentTwo key)
    (semanticNoRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentOne key × Out₁)
    (semanticNoRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentTwo key × Out₂)
    (semanticOpenRecvOne : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ → family.RecurrentOne key × Out₁)
    (semanticOpenRecvTwo : family.RecurrentTwo key → In₂ →
      family.RecurrentOne key → In₁ → family.RecurrentTwo key × Out₂)
    (semanticClose : family.RecurrentOne key → In₁ →
      family.RecurrentTwo key → In₂ →
        family.RecurrentOne key × family.RecurrentTwo key)
    (JointRep :
      DeferredOrRecurrent (family.SharedOne key) (family.PayloadOne key)
          (family.RecurrentOne key) →
        DeferredOrRecurrent (family.SharedTwo key) (family.PayloadTwo key)
          (family.RecurrentTwo key) →
        family.RecurrentOne key → family.RecurrentTwo key → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (simulation : DeferredJointRelationalSimulationLaws
      (family.initialOne key) (family.initialTwo key)
      (deferredOrRecurrentNoRecv (family.pendingStepOne key)
        (family.recurrentStepOne key))
      (deferredOrRecurrentNoRecv (family.pendingStepTwo key)
        (family.recurrentStepTwo key))
      (family.openRecvOne key) (family.openRecvTwo key) (family.close key)
      (family.Rel key) semanticInitialOne semanticInitialTwo semanticNoRecvOne
      semanticNoRecvTwo semanticOpenRecvOne semanticOpenRecvTwo semanticClose
      JointRep) :
    (family.toExactClosingBlindFamily.base.bankPairedMealyController key
      ).LiteralCrossMealyTraceInvariant env :=
  family.bankMealyTraceInvariant_of_joint_relational_fibre key
    semanticInitialOne semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
    semanticOpenRecvOne semanticOpenRecvTwo semanticClose JointRep
    (ExactClosingCanonicalSelected semanticInitialOne semanticInitialTwo
      semanticNoRecvOne semanticNoRecvTwo semanticOpenRecvOne
      semanticOpenRecvTwo semanticClose env)
    env
    (exactClosingSemanticOutputOne semanticInitialOne semanticInitialTwo
      semanticNoRecvOne semanticNoRecvTwo semanticOpenRecvOne
      semanticOpenRecvTwo semanticClose env)
    (exactClosingSemanticOutputTwo semanticInitialOne semanticInitialTwo
      semanticNoRecvOne semanticNoRecvTwo semanticOpenRecvOne
      semanticOpenRecvTwo semanticClose env)
    simulation
    (exactClosingCanonicalSelectedTraceLaws semanticInitialOne
      semanticInitialTwo semanticNoRecvOne semanticNoRecvTwo
      semanticOpenRecvOne semanticOpenRecvTwo semanticClose env
      (fun _ _ ↦ True))

end

end FiniteDeferredExactClosingFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
