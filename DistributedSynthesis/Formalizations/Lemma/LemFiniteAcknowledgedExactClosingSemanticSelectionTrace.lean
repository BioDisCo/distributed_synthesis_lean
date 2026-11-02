/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingCanonicalSelectedTrace
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyControllerTrace

/-!
# The acknowledged relay selects its canonical semantic trace

The exact-closing paired controller executes on two acknowledgement relays,
whereas its proof-side deterministic semantics executes on the underlying
controls.  At every time the two physical relays mutually select exactly the
canonical semantic pair.  This fact needs no blind-output coherence: it is a
control-selection theorem and follows solely from the five-colour relay
protocol.

The distinction is useful at one-way activation cuts.  Selection remains
valid even while one receive fork temporarily has candidates in two phases;
after both endpoints receive again, those candidates can be flushed to a
diagonal recurrent fork.
-/

namespace DistributedSynthesis

universe u v x y c₁ c₂

namespace FiniteAcknowledgedDelayedCarrier

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Control₁ : Type c₁} {Control₂ : Type c₂}

noncomputable section

variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype Control₁] [Fintype Control₂]

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited Out₁]
    [Inhabited Out₂] in
/-- At time `n`, the two acknowledged relay controls mutually select the
canonical exact-closing semantic controls before round `n`. -/
theorem exactClosingPairedMealyController_semanticControlTrace_pairSelects
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (env : EnvironmentSequence In₁ In₂) : ∀ n : Nat,
    let controller := exactClosingPairedMealyController initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close
    let semantic := exactClosingSemanticPairTrace initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close env n
    PairSelects
      (controller.semanticControlTrace env n).1
      (controller.semanticControlTrace env n).2
      semantic.1 semantic.2 := by
  intro n
  induction n with
  | zero =>
      exact pairSelects_known_known initialOne initialTwo none none
  | succ n ih =>
      let controller := exactClosingPairedMealyController initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close
      let relays := controller.semanticControlTrace env n
      let semantic := exactClosingSemanticPairTrace initialOne initialTwo
        noRecvOne noRecvTwo openRecvOne openRecvTwo close env n
      change PairSelects relays.1 relays.2 semantic.1 semantic.2 at ih
      rcases ih with ⟨honeSelect, htwoSelect⟩
      change resolvedControl relays.1 relays.2 = semantic.1 at honeSelect
      change resolvedControl relays.2 relays.1 = semantic.2 at htwoSelect
      cases hgraph : (env n).graph with
      | right =>
          have hnext := exactClosing_pairSelects_strictRight noRecvOne
            openRecvTwo close relays.1 relays.2 semantic.1 semantic.2
              (env n).inputOne (env n).inputTwo ⟨honeSelect, htwoSelect⟩
          simp only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            exactClosingSemanticPairTrace]
          change PairSelects
            (noRecvMealy noRecvOne relays.1 (env n).inputOne).1
            (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
              relays.2 (env n).inputTwo relays.1 (env n).inputOne).1
            (noRecvOne semantic.1 (env n).inputOne).1
            (openRecvTwo semantic.2 (env n).inputTwo semantic.1
              (env n).inputOne).1
          simp only [recvReforkMealy]
          rw [honeSelect, htwoSelect]
          simpa only [recvReforkMealy] using hnext
      | left =>
          have hnext := exactClosing_pairSelects_strictLeft noRecvTwo
            openRecvOne close relays.1 relays.2 semantic.1 semantic.2
              (env n).inputOne (env n).inputTwo ⟨honeSelect, htwoSelect⟩
          simp only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            exactClosingSemanticPairTrace]
          change PairSelects
            (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
              relays.1 (env n).inputOne relays.2 (env n).inputTwo).1
            (noRecvMealy noRecvTwo relays.2 (env n).inputTwo).1
            (openRecvOne semantic.1 (env n).inputOne semantic.2
              (env n).inputTwo).1
            (noRecvTwo semantic.2 (env n).inputTwo).1
          simp only [recvReforkMealy]
          rw [honeSelect, htwoSelect]
          simpa only [recvReforkMealy] using hnext
      | both =>
          have hnext := exactClosing_pairSelects_both openRecvOne openRecvTwo
            close relays.1 relays.2 (env n).inputOne (env n).inputTwo
          rw [honeSelect, htwoSelect] at hnext
          simp only [FinitePairedMealyController.semanticControlTrace,
            FinitePairedMealyController.semanticAdvanceControls, hgraph,
            exactClosingSemanticPairTrace]
          change PairSelects
            (recvReforkMealy (exactClosingRecvForkOne openRecvOne close)
              relays.1 (env n).inputOne relays.2 (env n).inputTwo).1
            (recvReforkMealy (exactClosingRecvForkTwo openRecvTwo close)
              relays.2 (env n).inputTwo relays.1 (env n).inputOne).1
            (close semantic.1 (env n).inputOne semantic.2
              (env n).inputTwo).1
            (close semantic.1 (env n).inputOne semantic.2
              (env n).inputTwo).2
          simp only [recvReforkMealy]
          rw [honeSelect, htwoSelect]
          simpa only [recvReforkMealy] using hnext

omit [Fintype In₁] [Fintype In₂] in
/-- Moore-facing version: the underlying controls stored by the actual
physical global trace select the canonical semantic controls. -/
theorem exactClosingPairedMealyController_globalStateTrace_pairSelects
    (initialOne : Control₁) (initialTwo : Control₂)
    (noRecvOne : Control₁ → In₁ → Control₁ × Out₁)
    (noRecvTwo : Control₂ → In₂ → Control₂ × Out₂)
    (openRecvOne :
      Control₁ → In₁ → Control₂ → In₂ → Control₁ × Out₁)
    (openRecvTwo :
      Control₂ → In₂ → Control₁ → In₁ → Control₂ × Out₂)
    (close : Control₁ → In₁ → Control₂ → In₂ →
      Control₁ × Control₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let controller := exactClosingPairedMealyController initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close
    let state := controller.mooreize.globalMachine.globalStateTrace env n
    let semantic := exactClosingSemanticPairTrace initialOne initialTwo
      noRecvOne noRecvTwo openRecvOne openRecvTwo close env n
    PairSelects state.1.1 state.2.1 semantic.1 semantic.2 := by
  let controller := exactClosingPairedMealyController initialOne initialTwo
    noRecvOne noRecvTwo openRecvOne openRecvTwo close
  have hcontrols := controller.mooreize_globalStateTrace_underlying env n
  have hselects :=
    exactClosingPairedMealyController_semanticControlTrace_pairSelects
      initialOne initialTwo noRecvOne noRecvTwo openRecvOne openRecvTwo close
        env n
  dsimp only at hcontrols hselects ⊢
  rw [controller.mooreize_globalStateTrace_underlying_one env n,
    controller.mooreize_globalStateTrace_underlying_two env n]
  exact hselects

end

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
