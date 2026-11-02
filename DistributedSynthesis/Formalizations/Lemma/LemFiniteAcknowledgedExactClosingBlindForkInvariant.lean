/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingRelationalInvariant

/-!
# Blind-fork bisimulation for acknowledged exact closing

The exact-close relay stores an open and a closed continuation whenever a
receive is locally ambiguous.  Selection proves which branch is semantically
actual, but it does not by itself justify the output emitted while the relay
stays blind.  This file supplies the missing reusable invariant.

A model provides one endpoint-local relation for each control type.  Related
controls emit equal no-receive outputs and advance to related controls.  At a
receive, the ordinary open continuation and the exact-close continuation are
required to be related whenever the selected model controls satisfy `Rel`.
These local facts imply output coherence at arbitrary blind depth and are
preserved by strict-right, strict-left, and simultaneous receives.

All direction words below name proof cases only.  No executable map receives
a graph, orientation, hierarchy side, leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂ c₃

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

/-- Endpoint-local bisimulation facts for blind no-receive evolution. -/
structure BlindNoRecvLaws
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop) : Prop where
  one : ∀ left right input,
    BlindOne left right →
      (noRecvOne left input).2 = (noRecvOne right input).2 ∧
      BlindOne (noRecvOne left input).1 (noRecvOne right input).1
  two : ∀ left right input,
    BlindTwo left right →
      (noRecvTwo left input).2 = (noRecvTwo right input).2 ∧
      BlindTwo (noRecvTwo left input).1 (noRecvTwo right input).1

/-- The ordinary open and exact-close branches created at one receive are
blind-related whenever the selected underlying controls satisfy `Rel`. -/
structure ExactClosingBlindReceiveLaws
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop) : Prop where
  one : ∀ one inputOne two inputTwo,
    Rel one two →
      BlindOne (openRecvOne one inputOne two inputTwo).1
        (close one inputOne two inputTwo).1
  two : ∀ one inputOne two inputTwo,
    Rel one two →
      BlindTwo (openRecvTwo two inputTwo one inputOne).1
        (close one inputOne two inputTwo).2

/-- Complete model-facing law bundle: semantic selected-pair preservation,
endpoint-local blind no-receive bisimulation, and open/exact receive
compatibility. -/
structure ExactClosingBlindForkLaws
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop) : Prop where
  relation : ExactClosingRelationLaws initialOne initialTwo noRecvOne noRecvTwo
    openRecvOne openRecvTwo close Rel
  noRecv : BlindNoRecvLaws noRecvOne noRecvTwo BlindOne BlindTwo
  receive : ExactClosingBlindReceiveLaws openRecvOne openRecvTwo close Rel
    BlindOne BlindTwo

/-- A finite acknowledged carrier is either already known or its unresolved
open/closed fork satisfies the endpoint's blind relation. -/
def SatisfiesBlindFork
    (Blind : Control₁ → Control₁ → Prop)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁) : Prop :=
  match state.current with
  | .known _ => True
  | .fork _ candidates =>
      Blind candidates.openControl candidates.closedControl

/-- A blind-related fork emits a coherent no-receive output. -/
theorem SatisfiesBlindFork.noRecvOutputCoherent
    (noRecv : Control₁ → In₁ → Control₁ × Out₁)
    (Blind : Control₁ → Control₁ → Prop)
    (hstep : ∀ left right input,
      Blind left right →
        (noRecv left input).2 = (noRecv right input).2 ∧
        Blind (noRecv left input).1 (noRecv right input).1)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (hblind : SatisfiesBlindFork Blind state)
    (input : In₁) :
    NoRecvOutputCoherent noRecv state input := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known control => trivial
  | fork id candidates =>
      exact (hstep candidates.openControl candidates.closedControl input
        hblind).1

/-- Branchwise no-receive advancement preserves the blind-fork relation. -/
theorem SatisfiesBlindFork.noRecv
    (noRecv : Control₁ → In₁ → Control₁ × Out₁)
    (Blind : Control₁ → Control₁ → Prop)
    (hstep : ∀ left right input,
      Blind left right →
        (noRecv left input).2 = (noRecv right input).2 ∧
        Blind (noRecv left input).1 (noRecv right input).1)
    (state : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (hblind : SatisfiesBlindFork Blind state)
    (input : In₁) :
    SatisfiesBlindFork Blind (noRecvMealy noRecv state input).1 := by
  rcases state with ⟨current, ack⟩
  cases current with
  | known control => trivial
  | fork id candidates =>
      exact (hstep candidates.openControl candidates.closedControl input
        hblind).2

/-- Reforking installs exactly the supplied candidate relation. -/
theorem satisfiesBlindFork_refork_iff
    {Target : Type c₃}
    (Blind : Target → Target → Prop)
    (own : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (partner : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (next : FiniteDelayedFork Target) :
    SatisfiesBlindFork Blind (refork own partner next) ↔
      Blind next.openControl next.closedControl :=
  Iff.rfl

/-- Mutual selection and both endpoint-local blind-fork relations. -/
structure ExactClosingBlindForkInvariant
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) : Prop where
  selected : ExactClosingRelaysSatisfy Rel one two
  blindOne : SatisfiesBlindFork BlindOne one
  blindTwo : SatisfiesBlindFork BlindTwo two

/-- The blind-fork invariant supplies the complete output-aware relational
invariant consumed by physical trace proofs. -/
theorem ExactClosingBlindForkInvariant.toRelayInvariant
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (blindLaws : BlindNoRecvLaws noRecvOne noRecvTwo BlindOne BlindTwo)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingRelayInvariant noRecvOne noRecvTwo Rel one two where
  selected := invariant.selected
  noRecvOneCoherent := fun input ↦
    invariant.blindOne.noRecvOutputCoherent noRecvOne BlindOne blindLaws.one
      one input
  noRecvTwoCoherent := fun input ↦
    invariant.blindTwo.noRecvOutputCoherent noRecvTwo BlindTwo blindLaws.two
      two input

/-- Known initial relays contain no unresolved fork. -/
theorem exactClosingBlindForkInvariant_initial
    (initialOne : Control₁) (initialTwo : Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (hrel : Rel initialOne initialTwo) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (⟨.known initialOne, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
      (⟨.known initialTwo, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) where
  selected := exactClosingRelaysSatisfy_initial initialOne initialTwo Rel hrel
  blindOne := trivial
  blindTwo := trivial

/-! ## Preservation by the three receive shapes -/

/-- Strict-right preservation: process one's old fork advances branchwise;
process two installs a fresh blind-related open/exact fork. -/
theorem ExactClosingBlindForkInvariant.strictRight
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (hrel : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (noRecvOne one inputOne).1
          (openRecvTwo two inputTwo one inputOne).1)
    (hblindNoRecv : ∀ left right input,
      BlindOne left right →
        (noRecvOne left input).2 = (noRecvOne right input).2 ∧
        BlindOne (noRecvOne left input).1 (noRecvOne right input).1)
    (hblindRecv : ∀ one inputOne two inputTwo,
      Rel one two →
        BlindTwo (openRecvTwo two inputTwo one inputOne).1
          (close one inputOne two inputTwo).2)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (noRecvMealy noRecvOne one inputOne).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hactual⟩ := invariant.selected
  refine {
    selected := invariant.selected.strictRight noRecvOne openRecvTwo close Rel
      hrel one two inputOne inputTwo
    blindOne := invariant.blindOne.noRecv noRecvOne BlindOne hblindNoRecv one
      inputOne
    blindTwo := ?_ }
  rcases hselects with ⟨hone, htwo⟩
  change resolvedControl one two = actualOne at hone
  change resolvedControl two one = actualTwo at htwo
  simp only [recvReforkMealy, hone, htwo]
  exact (satisfiesBlindFork_refork_iff BlindTwo two one
    (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo actualOne
      inputOne).1).2
    (hblindRecv actualOne inputOne actualTwo inputTwo hactual)

/-- Strict-left mirror of `strictRight`. -/
theorem ExactClosingBlindForkInvariant.strictLeft
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (hrel : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (openRecvOne one inputOne two inputTwo).1
          (noRecvTwo two inputTwo).1)
    (hblindNoRecv : ∀ left right input,
      BlindTwo left right →
        (noRecvTwo left input).2 = (noRecvTwo right input).2 ∧
        BlindTwo (noRecvTwo left input).1 (noRecvTwo right input).1)
    (hblindRecv : ∀ one inputOne two inputTwo,
      Rel one two →
        BlindOne (openRecvOne one inputOne two inputTwo).1
          (close one inputOne two inputTwo).1)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (noRecvMealy noRecvTwo two inputTwo).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hactual⟩ := invariant.selected
  refine {
    selected := invariant.selected.strictLeft noRecvTwo openRecvOne close Rel
      hrel one two inputOne inputTwo
    blindOne := ?_
    blindTwo := invariant.blindTwo.noRecv noRecvTwo BlindTwo hblindNoRecv two
      inputTwo }
  rcases hselects with ⟨hone, htwo⟩
  change resolvedControl one two = actualOne at hone
  change resolvedControl two one = actualTwo at htwo
  simp only [recvReforkMealy, hone, htwo]
  exact (satisfiesBlindFork_refork_iff BlindOne one two
    (exactClosingRecvForkOne openRecvOne close actualOne inputOne actualTwo
      inputTwo).1).2
    (hblindRecv actualOne inputOne actualTwo inputTwo hactual)

/-- Simultaneous receive installs two fresh blind-related open/exact forks. -/
theorem ExactClosingBlindForkInvariant.both
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (hrel : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (close one inputOne two inputTwo).1
          (close one inputOne two inputTwo).2)
    (hblindRecvOne : ∀ one inputOne two inputTwo,
      Rel one two →
        BlindOne (openRecvOne one inputOne two inputTwo).1
          (close one inputOne two inputTwo).1)
    (hblindRecvTwo : ∀ one inputOne two inputTwo,
      Rel one two →
        BlindTwo (openRecvTwo two inputTwo one inputOne).1
          (close one inputOne two inputTwo).2)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hactual⟩ := invariant.selected
  refine {
    selected := invariant.selected.both openRecvOne openRecvTwo close Rel hrel
      one two inputOne inputTwo
    blindOne := ?_
    blindTwo := ?_ }
  · rcases hselects with ⟨hone, htwo⟩
    change resolvedControl one two = actualOne at hone
    change resolvedControl two one = actualTwo at htwo
    simp only [recvReforkMealy, hone, htwo]
    exact (satisfiesBlindFork_refork_iff BlindOne one two
      (exactClosingRecvForkOne openRecvOne close actualOne inputOne actualTwo
        inputTwo).1).2
      (hblindRecvOne actualOne inputOne actualTwo inputTwo hactual)
  · rcases hselects with ⟨hone, htwo⟩
    change resolvedControl one two = actualOne at hone
    change resolvedControl two one = actualTwo at htwo
    simp only [recvReforkMealy, hone, htwo]
    exact (satisfiesBlindFork_refork_iff BlindTwo two one
      (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo actualOne
        inputOne).1).2
      (hblindRecvTwo actualOne inputOne actualTwo inputTwo hactual)

/-! ## Bundle-level consumption -/

/-- The complete law bundle initializes the combined invariant. -/
theorem ExactClosingBlindForkLaws.initial_invariant
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (laws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (⟨.known initialOne, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
      (⟨.known initialTwo, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) :=
  exactClosingBlindForkInvariant_initial initialOne initialTwo Rel BlindOne
    BlindTwo laws.relation.initial

/-- Bundle-level strict-right preservation. -/
theorem ExactClosingBlindForkLaws.strictRight
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (laws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (noRecvMealy noRecvOne one inputOne).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 :=
  invariant.strictRight noRecvOne openRecvTwo close Rel BlindOne BlindTwo
    laws.relation.strictRight laws.noRecv.one laws.receive.two one two inputOne
      inputTwo

/-- Bundle-level strict-left preservation. -/
theorem ExactClosingBlindForkLaws.strictLeft
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (laws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (noRecvMealy noRecvTwo two inputTwo).1 :=
  invariant.strictLeft noRecvTwo openRecvOne close Rel BlindOne BlindTwo
    laws.relation.strictLeft laws.noRecv.two laws.receive.one one two inputOne
      inputTwo

/-- Bundle-level simultaneous-receive preservation. -/
theorem ExactClosingBlindForkLaws.both
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (laws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (invariant : ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 :=
  invariant.both openRecvOne openRecvTwo close Rel BlindOne BlindTwo
    laws.relation.both laws.receive.one laws.receive.two one two inputOne
      inputTwo

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
