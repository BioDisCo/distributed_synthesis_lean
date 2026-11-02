/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingBlindForkInvariant
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerLiteralCrossTraceInvariant

/-!
# Selected-control trace adapter for acknowledged exact closing

The acknowledged exact-close controller executes on finite endpoint relays,
whereas the model-facing trace argument is naturally stated for the mutually
selected underlying controls.  This module is the generic bridge between the
two levels.

A concrete component supplies:

* the existing exact-close blind-fork laws;
* an index-dependent semantic predicate on the selected control pair; and
* for each physical graph case, preservation of that predicate and the two
  selected-control output equations.

The adapter handles occurrence identifiers, acknowledgements, unresolved
forks, and no-receive output coherence.  Its result is exactly
`LiteralCrossMealyTraceInvariant`, and hence feeds the repository's canonical
literal-cross extraction through the existing Mooreization theorem.

All graph cases occur only in proof fields.  No executable transition receives
a graph, orientation, hierarchy side, leader bit, history, or view.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

noncomputable section

/-! ## The selected semantic invariant -/

/-- One relay pair denotes a related pair of underlying controls satisfying
the caller's index-dependent semantic invariant.  The final two fields are
the arbitrary-depth blind-fork facts needed to identify no-receive outputs
with the selected branch.

All witnesses in this structure are proof-side. -/
def ExactClosingSelectedRelayInvariant
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (Selected : Control₁ → Control₂ → Nat → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (n : Nat) : Prop :=
  ∃ actualOne actualTwo,
    PairSelects one two actualOne actualTwo ∧
      Rel actualOne actualTwo ∧
      Selected actualOne actualTwo n ∧
      SatisfiesBlindFork BlindOne one ∧
      SatisfiesBlindFork BlindTwo two

/-- Forget only the indexed semantic fact and recover the complete generic
blind-fork invariant. -/
def ExactClosingSelectedRelayInvariant.toBlindForkInvariant
    (Rel : Control₁ → Control₂ → Prop)
    (BlindOne : Control₁ → Control₁ → Prop)
    (BlindTwo : Control₂ → Control₂ → Prop)
    (Selected : Control₁ → Control₂ → Nat → Prop)
    (one : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (two : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (n : Nat)
    (invariant : ExactClosingSelectedRelayInvariant Rel BlindOne BlindTwo
      Selected one two n) :
    ExactClosingBlindForkInvariant Rel BlindOne BlindTwo one two := by
  rcases invariant with
    ⟨actualOne, actualTwo, hselects, hrel, _hsemantic, hblindOne, hblindTwo⟩
  exact {
    selected := ⟨actualOne, actualTwo, hselects, hrel⟩
    blindOne := hblindOne
    blindTwo := hblindTwo }

/-! ## The remaining concrete trace laws -/

/-- The smallest model-specific trace interface above a complete exact-close
blind-fork component.

Each graph field is stated only for the mutually selected underlying pair.
It returns the next indexed semantic fact and the two current physical output
equations.  Relay selection and blind output equality are deliberately absent:
the adapter proves them once from `ExactClosingBlindForkLaws`. -/
structure ExactClosingSelectedTraceLaws
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (Rel : Control₁ → Control₂ → Prop)
    (Selected : Control₁ → Control₂ → Nat → Prop)
    (env : EnvironmentSequence In₁ In₂)
    (expectedOutputOne : Nat → Out₁)
    (expectedOutputTwo : Nat → Out₂) : Prop where
  initial : Selected initialOne initialTwo 0
  strictRight : ∀ n one two,
    Rel one two → Selected one two n → (env n).graph = .right →
      Selected (noRecvOne one (env n).inputOne).1
          (openRecvTwo two (env n).inputTwo one (env n).inputOne).1 (n + 1) ∧
        (noRecvOne one (env n).inputOne).2 = expectedOutputOne n ∧
        (openRecvTwo two (env n).inputTwo one (env n).inputOne).2 =
          expectedOutputTwo n
  strictLeft : ∀ n one two,
    Rel one two → Selected one two n → (env n).graph = .left →
      Selected (openRecvOne one (env n).inputOne two (env n).inputTwo).1
          (noRecvTwo two (env n).inputTwo).1 (n + 1) ∧
        (openRecvOne one (env n).inputOne two (env n).inputTwo).2 =
          expectedOutputOne n ∧
        (noRecvTwo two (env n).inputTwo).2 = expectedOutputTwo n
  both : ∀ n one two,
    Rel one two → Selected one two n → (env n).graph = .both →
      Selected (close one (env n).inputOne two (env n).inputTwo).1
          (close one (env n).inputOne two (env n).inputTwo).2 (n + 1) ∧
        (openRecvOne one (env n).inputOne two (env n).inputTwo).2 =
          expectedOutputOne n ∧
        (openRecvTwo two (env n).inputTwo one (env n).inputOne).2 =
          expectedOutputTwo n

namespace ExactClosingSelectedTraceLaws

variable
  (initialOne : Control₁) (initialTwo : Control₂)
  (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
  (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
  (openRecvOne :
    Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
  (openRecvTwo :
    Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
  (close : Control₁ → In₁ → Control₂ → In₂ →
    Control₁ × Control₂)
  (Rel : Control₁ → Control₂ → Prop)
  (BlindOne : Control₁ → Control₁ → Prop)
  (BlindTwo : Control₂ → Control₂ → Prop)
  (Selected : Control₁ → Control₂ → Nat → Prop)
  (env : EnvironmentSequence In₁ In₂)
  (expectedOutputOne : Nat → Out₁)
  (expectedOutputTwo : Nat → Out₂)

private abbrev ExactController [Fintype Control₁] [Fintype Control₂] :=
  exactClosingPairedMealyController initialOne initialTwo noRecvOne noRecvTwo
    openRecvOne openRecvTwo close

/-- Lift selected-control preservation and output equations through the
acknowledged relay into the exact Mealy trace invariant consumed by the
canonical extraction route. -/
noncomputable def toMealyTraceInvariant
    [Fintype Control₁] [Fintype Control₂]
    (blindLaws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (traceLaws : ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel Selected env
        expectedOutputOne expectedOutputTwo) :
    (ExactController initialOne initialTwo noRecvOne noRecvTwo openRecvOne
      openRecvTwo close).LiteralCrossMealyTraceInvariant env where
  expectedOutputOne := expectedOutputOne
  expectedOutputTwo := expectedOutputTwo
  StateInvariant := fun controls n ↦
    ExactClosingSelectedRelayInvariant Rel BlindOne BlindTwo Selected
      controls.1 controls.2 n
  initial := ⟨initialOne, initialTwo,
    pairSelects_known_known initialOne initialTwo none none,
    blindLaws.relation.initial, traceLaws.initial, trivial, trivial⟩
  leftStep := by
    intro n controls invariant hgraph
    rcases invariant with
      ⟨one, two, hselectsOld, hrelation, hselected, hblindOne, hblindTwo⟩
    have hsemantic := traceLaws.strictLeft n one two hrelation hselected hgraph
    have hblindNext := blindLaws.strictLeft initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel BlindOne BlindTwo controls.1
        controls.2 (env n).inputOne (env n).inputTwo
          (ExactClosingSelectedRelayInvariant.toBlindForkInvariant Rel BlindOne
            BlindTwo Selected controls.1 controls.2 n
              ⟨one, two, hselectsOld, hrelation, hselected, hblindOne,
                hblindTwo⟩)
    have hselects := exactClosing_pairSelects_strictLeft noRecvTwo openRecvOne
      close controls.1 controls.2 one two (env n).inputOne (env n).inputTwo
        hselectsOld
    have honeOutput :
        (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
          controls.1 (env n).inputOne controls.2 (env n).inputTwo).2 =
          (openRecvOne one (env n).inputOne two (env n).inputTwo).2 := by
      rcases hselectsOld with ⟨hone, htwo⟩
      change resolvedControl controls.1 controls.2 = one at hone
      change resolvedControl controls.2 controls.1 = two at htwo
      simp only [recvReforkMealy, exactClosingRecvForkOne, hone, htwo]
    have htwoOutput :
        (noRecvMealy noRecvTwo controls.2 (env n).inputTwo).2 =
          (noRecvTwo two (env n).inputTwo).2 := by
      rcases hselectsOld with ⟨_hone, htwo⟩
      rw [noRecvMealy_output_eq_resolvedControl noRecvTwo controls.2 controls.1
        (env n).inputTwo
          (hblindTwo.noRecvOutputCoherent noRecvTwo BlindTwo
            blindLaws.noRecv.two controls.2 (env n).inputTwo)]
      exact congrArg (fun selected ↦ (noRecvTwo selected (env n).inputTwo).2)
        htwo
    exact ⟨
      ⟨(openRecvOne one (env n).inputOne two (env n).inputTwo).1,
        (noRecvTwo two (env n).inputTwo).1, by
          rcases hselectsOld with ⟨hone, htwo⟩
          change resolvedControl controls.1 controls.2 = one at hone
          change resolvedControl controls.2 controls.1 = two at htwo
          simpa only [ExactController, exactClosingPairedMealyController,
            pairedMealyController, recvReforkMealy, hone, htwo] using hselects,
        blindLaws.relation.strictLeft one (env n).inputOne two
          (env n).inputTwo hrelation,
        hsemantic.1, hblindNext.blindOne, hblindNext.blindTwo⟩,
      honeOutput.trans hsemantic.2.1,
      htwoOutput.trans hsemantic.2.2⟩
  rightStep := by
    intro n controls invariant hgraph
    rcases invariant with
      ⟨one, two, hselectsOld, hrelation, hselected, hblindOne, hblindTwo⟩
    have hsemantic := traceLaws.strictRight n one two hrelation hselected hgraph
    have hblindNext := blindLaws.strictRight initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel BlindOne BlindTwo controls.1
        controls.2 (env n).inputOne (env n).inputTwo
          (ExactClosingSelectedRelayInvariant.toBlindForkInvariant Rel BlindOne
            BlindTwo Selected controls.1 controls.2 n
              ⟨one, two, hselectsOld, hrelation, hselected, hblindOne,
                hblindTwo⟩)
    have hselects := exactClosing_pairSelects_strictRight noRecvOne openRecvTwo
      close controls.1 controls.2 one two (env n).inputOne (env n).inputTwo
        hselectsOld
    have honeOutput :
        (noRecvMealy noRecvOne controls.1 (env n).inputOne).2 =
          (noRecvOne one (env n).inputOne).2 := by
      rcases hselectsOld with ⟨hone, _htwo⟩
      rw [noRecvMealy_output_eq_resolvedControl noRecvOne controls.1 controls.2
        (env n).inputOne
          (hblindOne.noRecvOutputCoherent noRecvOne BlindOne
            blindLaws.noRecv.one controls.1 (env n).inputOne)]
      exact congrArg (fun selected ↦ (noRecvOne selected (env n).inputOne).2)
        hone
    have htwoOutput :
        (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
          controls.2 (env n).inputTwo controls.1 (env n).inputOne).2 =
          (openRecvTwo two (env n).inputTwo one (env n).inputOne).2 := by
      rcases hselectsOld with ⟨hone, htwo⟩
      change resolvedControl controls.1 controls.2 = one at hone
      change resolvedControl controls.2 controls.1 = two at htwo
      simp only [recvReforkMealy, exactClosingRecvForkTwo, hone, htwo]
    exact ⟨
      ⟨(noRecvOne one (env n).inputOne).1,
        (openRecvTwo two (env n).inputTwo one (env n).inputOne).1, by
          rcases hselectsOld with ⟨hone, htwo⟩
          change resolvedControl controls.1 controls.2 = one at hone
          change resolvedControl controls.2 controls.1 = two at htwo
          simpa only [ExactController, exactClosingPairedMealyController,
            pairedMealyController, recvReforkMealy, hone, htwo] using hselects,
        blindLaws.relation.strictRight one (env n).inputOne two
          (env n).inputTwo hrelation,
        hsemantic.1, hblindNext.blindOne, hblindNext.blindTwo⟩,
      honeOutput.trans hsemantic.2.1,
      htwoOutput.trans hsemantic.2.2⟩
  bothStep := by
    intro n controls invariant hgraph
    rcases invariant with
      ⟨one, two, hselectsOld, hrelation, hselected, hblindOne, hblindTwo⟩
    have hsemantic := traceLaws.both n one two hrelation hselected hgraph
    have hblindNext := blindLaws.both initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo controls.1 controls.2
        (env n).inputOne (env n).inputTwo
          (ExactClosingSelectedRelayInvariant.toBlindForkInvariant Rel BlindOne
            BlindTwo Selected controls.1 controls.2 n
              ⟨one, two, hselectsOld, hrelation, hselected, hblindOne,
                hblindTwo⟩)
    have hselects := exactClosing_pairSelects_both openRecvOne openRecvTwo close
      controls.1 controls.2 (env n).inputOne (env n).inputTwo
    have honeOutput :
        (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
          controls.1 (env n).inputOne controls.2 (env n).inputTwo).2 =
          (openRecvOne one (env n).inputOne two (env n).inputTwo).2 := by
      rcases hselectsOld with ⟨hone, htwo⟩
      change resolvedControl controls.1 controls.2 = one at hone
      change resolvedControl controls.2 controls.1 = two at htwo
      simp only [recvReforkMealy, exactClosingRecvForkOne, hone, htwo]
    have htwoOutput :
        (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
          controls.2 (env n).inputTwo controls.1 (env n).inputOne).2 =
          (openRecvTwo two (env n).inputTwo one (env n).inputOne).2 := by
      rcases hselectsOld with ⟨hone, htwo⟩
      change resolvedControl controls.1 controls.2 = one at hone
      change resolvedControl controls.2 controls.1 = two at htwo
      simp only [recvReforkMealy, exactClosingRecvForkTwo, hone, htwo]
    have hselects' : PairSelects
        (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
          controls.1 (env n).inputOne controls.2 (env n).inputTwo).1
        (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
          controls.2 (env n).inputTwo controls.1 (env n).inputOne).1
        (close one (env n).inputOne two (env n).inputTwo).1
        (close one (env n).inputOne two (env n).inputTwo).2 := by
      rcases hselectsOld with ⟨hone, htwo⟩
      change resolvedControl controls.1 controls.2 = one at hone
      change resolvedControl controls.2 controls.1 = two at htwo
      simpa only [recvReforkMealy, hone, htwo] using hselects
    exact ⟨
      ⟨(close one (env n).inputOne two (env n).inputTwo).1,
        (close one (env n).inputOne two (env n).inputTwo).2, hselects',
        blindLaws.relation.both one (env n).inputOne two
          (env n).inputTwo hrelation,
        hsemantic.1, hblindNext.blindOne, hblindNext.blindTwo⟩,
      honeOutput.trans hsemantic.2.1,
      htwoOutput.trans hsemantic.2.2⟩

/-- The exact-closing transition table with an arbitrary pair of initial
acknowledged relays.  This is a pure rerooting operation: every local
transition remains the canonical exact-closing transition. -/
noncomputable def exactClosingPairedMealyControllerFromRelays
    [Fintype Control₁] [Fintype Control₂]
    (rootOne : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (rootTwo : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂) :
    FinitePairedMealyController In₁ In₂ Out₁ Out₂ :=
  { exactClosingPairedMealyController initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close with
    initialOne := rootOne
    initialTwo := rootTwo }

/-- Reroot `toMealyTraceInvariant` at any finite acknowledged pair selecting
the same semantic initial controls.  The three transition obligations are
literally the canonical proof; only the initial relay selection and blind
fork certificates are new. -/
noncomputable def toMealyTraceInvariantFromRelays
    [Fintype Control₁] [Fintype Control₂]
    (rootOne : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₁)
    (rootTwo : FiniteAcknowledgedDelayedCarrier (Fin 5) Control₂)
    (hselects : PairSelects rootOne rootTwo initialOne initialTwo)
    (hblindOne : SatisfiesBlindFork BlindOne rootOne)
    (hblindTwo : SatisfiesBlindFork BlindTwo rootTwo)
    (blindLaws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (traceLaws : ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel Selected env
        expectedOutputOne expectedOutputTwo) :
    (exactClosingPairedMealyControllerFromRelays initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close rootOne rootTwo
      ).LiteralCrossMealyTraceInvariant env := by
  let canonical :=
    traceLaws.toMealyTraceInvariant initialOne initialTwo noRecvOne noRecvTwo
      openRecvOne openRecvTwo close Rel BlindOne BlindTwo Selected env
        expectedOutputOne expectedOutputTwo blindLaws
  refine {
    expectedOutputOne := expectedOutputOne
    expectedOutputTwo := expectedOutputTwo
    StateInvariant := canonical.StateInvariant
    initial := ?_
    leftStep := ?_
    rightStep := ?_
    bothStep := ?_ }
  · exact ⟨initialOne, initialTwo, hselects, blindLaws.relation.initial,
      traceLaws.initial, hblindOne, hblindTwo⟩
  · intro n controls invariant hgraph
    simpa [canonical, exactClosingPairedMealyControllerFromRelays,
      ExactController] using canonical.leftStep n controls invariant hgraph
  · intro n controls invariant hgraph
    simpa [canonical, exactClosingPairedMealyControllerFromRelays,
      ExactController] using canonical.rightStep n controls invariant hgraph
  · intro n controls invariant hgraph
    simpa [canonical, exactClosingPairedMealyControllerFromRelays,
      ExactController] using canonical.bothStep n controls invariant hgraph

/-- Direct Moore-facing form of `toMealyTraceInvariant`.  A concrete outer
product can use this theorem and then invoke
`globalMachineTraceWord_eq_referenceWord` without inspecting relay IDs. -/
noncomputable def toMooreTraceInvariant
    [Fintype Control₁] [Fintype Control₂]
    [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁] [Inhabited Out₂]
    (blindLaws : ExactClosingBlindForkLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel BlindOne BlindTwo)
    (traceLaws : ExactClosingSelectedTraceLaws initialOne initialTwo noRecvOne
      noRecvTwo openRecvOne openRecvTwo close Rel Selected env
        expectedOutputOne expectedOutputTwo) :
    ((ExactController initialOne initialTwo noRecvOne noRecvTwo openRecvOne
      openRecvTwo close).mooreize).LiteralCrossGraphTraceInvariant env :=
  (traceLaws.toMealyTraceInvariant initialOne initialTwo noRecvOne noRecvTwo
    openRecvOne openRecvTwo close Rel BlindOne BlindTwo Selected env
      expectedOutputOne expectedOutputTwo blindLaws).toMooreTraceInvariant _

end ExactClosingSelectedTraceLaws

end


end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
