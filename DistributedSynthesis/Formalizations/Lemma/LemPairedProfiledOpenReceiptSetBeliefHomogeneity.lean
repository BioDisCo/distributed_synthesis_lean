/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefReadback
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenShapeFreeSetValuedReceiptRecurrence

/-!
# Set-valued receipts imply reachable-belief output homogeneity

This file is the lost-bit-safe bridge between the set-valued receipt
recurrence and `FiniteGlobalRoundMachine.ReachableBeliefsUniform`.

It deliberately does not choose a receipt, a re-anchored evaluation, an
epoch-entry row, an orientation, or a strict leader.  Instead a proof-side
relation may represent one global state by any receipt in the process's
current finite receipt set.  Pairwise behavior uniformity of the whole set
then makes every two represented states output-equivalent.

The representation relation is intentionally abstract.  In the physical
adapter it may retain all compatible dependent member/root evaluations and
all compatible sticky `PairedEntryRow`s.  Thus the theorem remains sound even
when one bit is lost forever: no later-recovery premise is used.
-/

namespace DistributedSynthesis

universe u v w x y oc tc om tm

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- A proof-side set-valued receipt presentation of the two Moore outputs.

`RepresentedOne rounds state receipt` and its mirror may contain arbitrary
erased witnesses.  In particular they need not make `receipt` functional in
`state`, and they may quantify over multiple compatible sticky rows. -/
structure ReceiptSetOutputPresentation
    {Out₁ : Type x} {Out₂ : Type y}
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (OneClass : Type oc) (TwoClass : Type tc)
    (OneMove : Type om) (TwoMove : Type tm) where
  summaryOne : List (EnvironmentRound In₁ In₂) →
    (OneClass → OneMove) × Finset OneClass
  summaryTwo : List (EnvironmentRound In₁ In₂) →
    (TwoClass → TwoMove) × Finset TwoClass
  EquivalentOne : OneMove → OneMove → Prop
  EquivalentTwo : TwoMove → TwoMove → Prop
  RepresentedOne : List (EnvironmentRound In₁ In₂) →
    G.State → OneClass → Prop
  RepresentedTwo : List (EnvironmentRound In₁ In₂) →
    G.State → TwoClass → Prop
  coverOne : ∀ rounds state,
    state ∈ (G.beliefsAfter rounds).1 →
      ∃ receipt ∈ (summaryOne rounds).2,
        RepresentedOne rounds state receipt
  coverTwo : ∀ rounds state,
    state ∈ (G.beliefsAfter rounds).2 →
      ∃ receipt ∈ (summaryTwo rounds).2,
        RepresentedTwo rounds state receipt
  uniformOne : ∀ rounds left,
    left ∈ (summaryOne rounds).2 → ∀ right,
      right ∈ (summaryOne rounds).2 →
        EquivalentOne ((summaryOne rounds).1 left)
          ((summaryOne rounds).1 right)
  uniformTwo : ∀ rounds left,
    left ∈ (summaryTwo rounds).2 → ∀ right,
      right ∈ (summaryTwo rounds).2 →
        EquivalentTwo ((summaryTwo rounds).1 left)
          ((summaryTwo rounds).1 right)
  outputOne_eq : ∀ {rounds left right leftReceipt rightReceipt},
    RepresentedOne rounds left leftReceipt →
      RepresentedOne rounds right rightReceipt →
      EquivalentOne ((summaryOne rounds).1 leftReceipt)
        ((summaryOne rounds).1 rightReceipt) →
      outputOne left = outputOne right
  outputTwo_eq : ∀ {rounds left right leftReceipt rightReceipt},
    RepresentedTwo rounds left leftReceipt →
      RepresentedTwo rounds right rightReceipt →
      EquivalentTwo ((summaryTwo rounds).1 leftReceipt)
        ((summaryTwo rounds).1 rightReceipt) →
      outputTwo left = outputTwo right

namespace ReceiptSetOutputPresentation

variable {Out₁ : Type x} {Out₂ : Type y}
variable (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
variable {OneClass : Type oc} {TwoClass : Type tc}
variable {OneMove : Type om} {TwoMove : Type tm}

/-- Set-valued receipt representation closes the exact dangerous-zone gate.
No functionality or eventual resolution of a receipt is assumed. -/
theorem reachableBeliefsUniform
    (P : G.ReceiptSetOutputPresentation outputOne outputTwo OneClass TwoClass
      OneMove TwoMove) :
    G.ReachableBeliefsUniform outputOne outputTwo := by
  intro rounds
  constructor
  · intro left hleft right hright
    rcases P.coverOne rounds left hleft with
      ⟨leftReceipt, hleftReceipt, hleftRep⟩
    rcases P.coverOne rounds right hright with
      ⟨rightReceipt, hrightReceipt, hrightRep⟩
    exact P.outputOne_eq hleftRep hrightRep
      (P.uniformOne rounds leftReceipt hleftReceipt rightReceipt
        hrightReceipt)
  · intro left hleft right hright
    rcases P.coverTwo rounds left hleft with
      ⟨leftReceipt, hleftReceipt, hleftRep⟩
    rcases P.coverTwo rounds right hright with
      ⟨rightReceipt, hrightReceipt, hrightRep⟩
    exact P.outputTwo_eq hleftRep hrightRep
      (P.uniformTwo rounds leftReceipt hleftReceipt rightReceipt
        hrightReceipt)

end ReceiptSetOutputPresentation

end FiniteGlobalRoundMachine

/-! ## Direct specialization to the profiled set-valued receipt summaries -/

universe i s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev ReceiptClass :=
  ProfiledOpenActiveLaneSideClass A initialCode

private abbrev ReceiptSummary :=
  ProfiledOpenActiveLaneWitnessedReceiptSetSummary A initialCode

private abbrev RightValue :=
  ProfiledOpenFixedRightPinnedValue A initialCode

private abbrev LeftValue :=
  ProfiledOpenFixedLeftPinnedValue A initialCode

/-- The existing profiled behavior-uniformity predicates, together with
coverage and output soundness of an arbitrary proof-side representation,
produce the generic receipt presentation.  The representation may keep every
compatible evaluation and row; neither coordinate is selected here. -/
noncomputable def profiledOpenReceiptSetOutputPresentation
    (G : FiniteGlobalRoundMachine In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (summaryOne summaryTwo :
      List (EnvironmentRound In₁ In₂) → ReceiptSummary A initialCode)
    (EquivalentOne : RightValue A initialCode →
      RightValue A initialCode → Prop)
    (EquivalentTwo : LeftValue A initialCode →
      LeftValue A initialCode → Prop)
    (RepresentedOne : List (EnvironmentRound In₁ In₂) →
      G.State → ReceiptClass A initialCode → Prop)
    (RepresentedTwo : List (EnvironmentRound In₁ In₂) →
      G.State → ReceiptClass A initialCode → Prop)
    (hcoverOne : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).1 →
        ∃ receipt ∈ (summaryOne rounds).2,
          RepresentedOne rounds state receipt)
    (hcoverTwo : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).2 →
        ∃ receipt ∈ (summaryTwo rounds).2,
          RepresentedTwo rounds state receipt)
    (huniformOne : ∀ rounds,
      ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform A initialCode
        EquivalentOne (summaryOne rounds).1 (summaryOne rounds).2)
    (huniformTwo : ∀ rounds,
      ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform A initialCode
        EquivalentTwo (summaryTwo rounds).1 (summaryTwo rounds).2)
    (houtputOne : ∀ {rounds left right leftReceipt rightReceipt},
      RepresentedOne rounds left leftReceipt →
        RepresentedOne rounds right rightReceipt →
        EquivalentOne ((summaryOne rounds).1.1 leftReceipt)
          ((summaryOne rounds).1.1 rightReceipt) →
        outputOne left = outputOne right)
    (houtputTwo : ∀ {rounds left right leftReceipt rightReceipt},
      RepresentedTwo rounds left leftReceipt →
        RepresentedTwo rounds right rightReceipt →
        EquivalentTwo ((summaryTwo rounds).1.2 leftReceipt)
          ((summaryTwo rounds).1.2 rightReceipt) →
        outputTwo left = outputTwo right) :
    G.ReceiptSetOutputPresentation outputOne outputTwo
      (ReceiptClass A initialCode) (ReceiptClass A initialCode)
      (RightValue A initialCode) (LeftValue A initialCode) where
  summaryOne := fun rounds ↦ ((summaryOne rounds).1.1,
    (summaryOne rounds).2)
  summaryTwo := fun rounds ↦ ((summaryTwo rounds).1.2,
    (summaryTwo rounds).2)
  EquivalentOne := EquivalentOne
  EquivalentTwo := EquivalentTwo
  RepresentedOne := RepresentedOne
  RepresentedTwo := RepresentedTwo
  coverOne := hcoverOne
  coverTwo := hcoverTwo
  uniformOne := by
    intro rounds left hleft right hright
    exact huniformOne rounds left hleft right hright
  uniformTwo := by
    intro rounds left hleft right hright
    exact huniformTwo rounds left hleft right hright
  outputOne_eq := houtputOne
  outputTwo_eq := houtputTwo

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- One-arrow specialization of the generic theorem. -/
theorem profiledOpen_reachableBeliefsUniform_of_receiptSetBehaviorUniform
    (G : FiniteGlobalRoundMachine In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (summaryOne summaryTwo :
      List (EnvironmentRound In₁ In₂) → ReceiptSummary A initialCode)
    (EquivalentOne : RightValue A initialCode →
      RightValue A initialCode → Prop)
    (EquivalentTwo : LeftValue A initialCode →
      LeftValue A initialCode → Prop)
    (RepresentedOne : List (EnvironmentRound In₁ In₂) →
      G.State → ReceiptClass A initialCode → Prop)
    (RepresentedTwo : List (EnvironmentRound In₁ In₂) →
      G.State → ReceiptClass A initialCode → Prop)
    (hcoverOne : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).1 →
        ∃ receipt ∈ (summaryOne rounds).2,
          RepresentedOne rounds state receipt)
    (hcoverTwo : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).2 →
        ∃ receipt ∈ (summaryTwo rounds).2,
          RepresentedTwo rounds state receipt)
    (huniformOne : ∀ rounds,
      ProfiledOpenActiveLaneRightReceiptSetBehaviorUniform A initialCode
        EquivalentOne (summaryOne rounds).1 (summaryOne rounds).2)
    (huniformTwo : ∀ rounds,
      ProfiledOpenActiveLaneLeftReceiptSetBehaviorUniform A initialCode
        EquivalentTwo (summaryTwo rounds).1 (summaryTwo rounds).2)
    (houtputOne : ∀ {rounds left right leftReceipt rightReceipt},
      RepresentedOne rounds left leftReceipt →
        RepresentedOne rounds right rightReceipt →
        EquivalentOne ((summaryOne rounds).1.1 leftReceipt)
          ((summaryOne rounds).1.1 rightReceipt) →
        outputOne left = outputOne right)
    (houtputTwo : ∀ {rounds left right leftReceipt rightReceipt},
      RepresentedTwo rounds left leftReceipt →
        RepresentedTwo rounds right rightReceipt →
        EquivalentTwo ((summaryTwo rounds).1.2 leftReceipt)
          ((summaryTwo rounds).1.2 rightReceipt) →
        outputTwo left = outputTwo right) :
    G.ReachableBeliefsUniform outputOne outputTwo := by
  apply FiniteGlobalRoundMachine.ReceiptSetOutputPresentation.reachableBeliefsUniform
  exact profiledOpenReceiptSetOutputPresentation A initialCode G outputOne
    outputTwo summaryOne summaryTwo EquivalentOne EquivalentTwo RepresentedOne
    RepresentedTwo hcoverOne hcoverTwo huniformOne huniformTwo houtputOne
    houtputTwo

end DetParityAutomaton

end DistributedSynthesis
