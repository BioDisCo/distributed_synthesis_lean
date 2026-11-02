/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingPairedMealyController

/-!
# Relational invariant for an acknowledged exact-close controller

The acknowledged relay hides a finite open/closed fork at each endpoint.  A
proof of the physical trace, however, should reason about one mutually
selected pair of underlying controls.  This file packages that proof pattern.

A caller supplies a relation on underlying endpoint controls and four local
closure laws: the initial pair, the two strict directions, and the exact joint
close.  The theorems below lift those laws through the five-colour
acknowledgement carrier.  In particular, stale and fresh fork identifiers are
handled once by `PairSelects`; model-specific seam proofs never inspect them.

All graph directions occur only as names of proof lemmas.  None of the
executable transition maps receives a graph, orientation, leader bit,
strict-leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

/-- The four model-specific closure facts needed below the generic
acknowledgement layer. -/
structure ExactClosingRelationLaws
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop) : Prop where
  initial : Rel initialOne initialTwo
  strictRight : ∀ one inputOne two inputTwo,
    Rel one two →
      Rel (noRecvOne one inputOne).1
        (openRecvTwo two inputTwo one inputOne).1
  strictLeft : ∀ one inputOne two inputTwo,
    Rel one two →
      Rel (openRecvOne one inputOne two inputTwo).1
        (noRecvTwo two inputTwo).1
  both : ∀ one inputOne two inputTwo,
    Rel one two →
      Rel (close one inputOne two inputTwo).1
        (close one inputOne two inputTwo).2

/-- Two acknowledged endpoint relays denote a related, mutually selected
pair of underlying controls.  The witnesses are proof-side only. -/
def ExactClosingRelaysSatisfy
    (Rel : Control₁ → Control₂ → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) : Prop :=
  ∃ actualOne actualTwo,
    PairSelects one two actualOne actualTwo ∧ Rel actualOne actualTwo

/-- The selected-pair relation together with the two output-coherence facts
needed while either acknowledged relay still contains an unresolved fork.
Selection alone is intentionally not presented as an output invariant. -/
structure ExactClosingRelayInvariant
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (Rel : Control₁ → Control₂ → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) : Prop where
  selected : ExactClosingRelaysSatisfy Rel one two
  noRecvOneCoherent : ∀ inputOne : In₁,
    NoRecvOutputCoherent noRecvOne one inputOne
  noRecvTwoCoherent : ∀ inputTwo : In₂,
    NoRecvOutputCoherent noRecvTwo two inputTwo

/-- Under the full relay invariant, process one's executable nonreceive output
is the output of the mutually selected underlying control. -/
theorem ExactClosingRelayInvariant.noRecvOne_output_eq
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (Rel : Control₁ → Control₂ → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (invariant : ExactClosingRelayInvariant noRecvOne noRecvTwo Rel one two)
    (inputOne : In₁) :
    (noRecvMealy noRecvOne one inputOne).2 =
      (noRecvOne (resolvedControl one two) inputOne).2 := by
  exact noRecvMealy_output_eq_resolvedControl noRecvOne one two inputOne
    (invariant.noRecvOneCoherent inputOne)

/-- Process-two mirror of `noRecvOne_output_eq`. -/
theorem ExactClosingRelayInvariant.noRecvTwo_output_eq
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (Rel : Control₁ → Control₂ → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (invariant : ExactClosingRelayInvariant noRecvOne noRecvTwo Rel one two)
    (inputTwo : In₂) :
    (noRecvMealy noRecvTwo two inputTwo).2 =
      (noRecvTwo (resolvedControl two one) inputTwo).2 := by
  exact noRecvMealy_output_eq_resolvedControl noRecvTwo two one inputTwo
    (invariant.noRecvTwoCoherent inputTwo)

/-- The two known initial relays select the supplied related initial pair. -/
theorem exactClosingRelaysSatisfy_initial
    (initialOne : Control₁) (initialTwo : Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (hrel : Rel initialOne initialTwo) :
    ExactClosingRelaysSatisfy Rel
      (⟨.known initialOne, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
      (⟨.known initialTwo, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) := by
  exact ⟨initialOne, initialTwo,
    pairSelects_known_known initialOne initialTwo none none, hrel⟩

/-- A strict-right physical round preserves the lifted relation.  Process one
advances locally; process two resolves the old pair and installs the open
receive continuation. -/
theorem ExactClosingRelaysSatisfy.strictRight
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (hstrict : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (noRecvOne one inputOne).1
          (openRecvTwo two inputTwo one inputOne).1)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (hinvariant : ExactClosingRelaysSatisfy Rel one two) :
    ExactClosingRelaysSatisfy Rel
      (noRecvMealy noRecvOne one inputOne).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hrel⟩ := hinvariant
  refine ⟨(noRecvOne actualOne inputOne).1,
    (openRecvTwo actualTwo inputTwo actualOne inputOne).1, ?_,
    hstrict actualOne inputOne actualTwo inputTwo hrel⟩
  rcases hselects with ⟨hone, htwo⟩
  change resolvedControl one two = actualOne at hone
  change resolvedControl two one = actualTwo at htwo
  simp only [recvReforkMealy]
  rw [hone, htwo]
  exact exactClosing_pairSelects_strictRight noRecvOne openRecvTwo close one
    two actualOne actualTwo inputOne inputTwo ⟨hone, htwo⟩

/-- Strict-left mirror of `ExactClosingRelaysSatisfy.strictRight`. -/
theorem ExactClosingRelaysSatisfy.strictLeft
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (hstrict : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (openRecvOne one inputOne two inputTwo).1
          (noRecvTwo two inputTwo).1)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (hinvariant : ExactClosingRelaysSatisfy Rel one two) :
    ExactClosingRelaysSatisfy Rel
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (noRecvMealy noRecvTwo two inputTwo).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hrel⟩ := hinvariant
  refine ⟨(openRecvOne actualOne inputOne actualTwo inputTwo).1,
    (noRecvTwo actualTwo inputTwo).1, ?_,
    hstrict actualOne inputOne actualTwo inputTwo hrel⟩
  rcases hselects with ⟨hone, htwo⟩
  change resolvedControl one two = actualOne at hone
  change resolvedControl two one = actualTwo at htwo
  simp only [recvReforkMealy]
  rw [hone, htwo]
  exact exactClosing_pairSelects_strictLeft noRecvTwo openRecvOne close one two
    actualOne actualTwo inputOne inputTwo ⟨hone, htwo⟩

/-- A simultaneous receive selects the two projections of one exact joint
close and therefore preserves any relation established by that close. -/
theorem ExactClosingRelaysSatisfy.both
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (hclose : ∀ one inputOne two inputTwo,
      Rel one two →
        Rel (close one inputOne two inputTwo).1
          (close one inputOne two inputTwo).2)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (inputOne : In₁) (inputTwo : In₂)
    (hinvariant : ExactClosingRelaysSatisfy Rel one two) :
    ExactClosingRelaysSatisfy Rel
      (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
        one inputOne two inputTwo).1
      (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
        two inputTwo one inputOne).1 := by
  obtain ⟨actualOne, actualTwo, hselects, hrel⟩ := hinvariant
  refine ⟨(close actualOne inputOne actualTwo inputTwo).1,
    (close actualOne inputOne actualTwo inputTwo).2, ?_,
    hclose actualOne inputOne actualTwo inputTwo hrel⟩
  rcases hselects with ⟨hone, htwo⟩
  change resolvedControl one two = actualOne at hone
  change resolvedControl two one = actualTwo at htwo
  simp only [recvReforkMealy]
  rw [hone, htwo]
  simpa only [exactClosingRecvForkOne, exactClosingRecvForkTwo] using
    (pairSelects_both one two
      (exactClosingRecvForkOne openRecvOne close actualOne inputOne actualTwo
        inputTwo).1
      (exactClosingRecvForkTwo openRecvTwo close actualTwo inputTwo actualOne
        inputOne).1)

/-- Bundle-level initial lifting. -/
theorem ExactClosingRelationLaws.initial_relays
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (laws : ExactClosingRelationLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel) :
    ExactClosingRelaysSatisfy Rel
      (⟨.known initialOne, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
      (⟨.known initialTwo, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) :=
  exactClosingRelaysSatisfy_initial initialOne initialTwo Rel laws.initial

/-- The complete invariant is automatic at two known initial controls: there
is no unresolved fork, so both blind-output coherence fields are vacuous. -/
theorem ExactClosingRelationLaws.initial_relayInvariant
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ → Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (laws : ExactClosingRelationLaws initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel) :
    ExactClosingRelayInvariant noRecvOne noRecvTwo Rel
      (⟨.known initialOne, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
      (⟨.known initialTwo, none⟩ :
        FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) where
  selected := laws.initial_relays initialOne initialTwo noRecvOne noRecvTwo
    openRecvOne openRecvTwo close Rel
  noRecvOneCoherent := by intro; trivial
  noRecvTwoCoherent := by intro; trivial

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
