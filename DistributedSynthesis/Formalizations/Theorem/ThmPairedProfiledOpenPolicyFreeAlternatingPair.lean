/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPolicyFreeThreadStep

/-!
# Two consecutive policy-free block transitions retain one semantic thread

The Bérard finite-memory proof rationalizes labels that are *whole
synchronization-to-synchronization strategy blocks*.  Before that single
rationalization, the label at a semantic node may depend on the complete
semantic history.  What must already be true is that a child label is taken
at the actual child history produced by its parent, rather than at an
unrelated representative of the same finite view class.

This file checks the dangerous alternating pair directly against the current
profiled interfaces.  A right block produces a pointed left realization.  We
use that very realization and its selected root for the following left block.
The resulting two hidden-thread transitions and the two raw-strategy memory
steps compose without any root reselection.

The selected roots are proof-side witnesses only.  Neither move contains a
strict-leader bit, and neither process is asked to know the current
orientation.
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

omit [Inhabited Out₁] [Inhabited Out₂] in
/--
Generic two-block correlation law for the finite block-label interface.

`ProfiledOpenRepresentableMove` is the finite object playing the role of a
Bérard strategy-tree label: it contains the complete rational block table,
not one round's action.  If the second direction starts at the root emitted by
the first label, two live steps reduce to the endpoint emitted by the second
label.  There is no intervening family state at which a root could be chosen
again.
-/
theorem profiledOpenThreadStep_live_pair_of
    (firstInitial secondInitial : ProfiledOpenObservation A)
    (current : ProfiledOpenClassifiedAnchor A)
    (firstLetter secondLetter :
      ProfiledOpenRepresentableMove A × ProfiledOpenObservation A)
    (firstDirection secondDirection : ProfiledOpenClassifiedDirection A)
    (hfirstSource : firstDirection.anchor A = current)
    (hfirstClass :
      (firstLetter.1.successor A firstDirection).2 =
        firstLetter.2.roots A)
    (hsecondSource :
      secondDirection.anchor A =
        (firstLetter.1.successor A firstDirection).1)
    (hsecondClass :
      (secondLetter.1.successor A secondDirection).2 =
        secondLetter.2.roots A) :
    profiledOpenThreadStep A secondInitial
        (profiledOpenThreadStep A firstInitial (.live current) firstLetter
          firstDirection)
        secondLetter secondDirection =
      .live (secondLetter.1.successor A secondDirection).1 := by
  rw [profiledOpenThreadStep_live_of A firstInitial current firstLetter
    firstDirection hfirstSource hfirstClass]
  exact profiledOpenThreadStep_live_of A secondInitial
    (firstLetter.1.successor A firstDirection).1 secondLetter secondDirection
    hsecondSource hsecondClass

omit [Inhabited Out₁] [Inhabited Out₂] in
/--
The concrete right-then-left pair test.

The second table is not chosen from the public child class.  It is read from
`child.realization`, the pointed semantic child returned by the first step.
Consequently the source of the second hidden transition is definitionally
the root emitted by the first one.  The last two conjuncts record the same
fact at the underlying raw-strategy-memory level.
-/
theorem exists_profiledOpenPolicyFreeRightLeftPair
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)}
    {basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis}
    {source : ProfiledOpenRightViewClass A}
    (realization : ProfiledOpenRightRealization A strategy hwin basis source)
    (member : {root // root ∈ source.1})
    (rightRow : PairedEntryRow)
    (rightPast : List (In₂ × In₁)) (rightInput : In₂ × In₁)
    (leftRow : PairedEntryRow)
    (leftPast : List (In₁ × In₂)) (leftInput : In₁ × In₂) :
    let rightOutput := profiledOpenRightRepresentableOutputAt A source
      (realization.coherentTable A).table member
      (omegaOfList (rightPast ++ [rightInput])) rightPast.length
    ∃ rightSemanticPast :
        List ((({root // root ∈ source.1} × In₂) × In₁)),
      ∃ child : ProfiledOpenLeftPointedRealization A strategy hwin basis
          (rightOutput.2 rightRow).2,
        let leftOutput := profiledOpenLeftRepresentableOutputAt A
          (rightOutput.2 rightRow).2
          (child.realization.coherentTable A).table child.selected
          (omegaOfList (leftPast ++ [leftInput])) leftPast.length
        ∃ leftSemanticPast :
            List ((({root // root ∈ (rightOutput.2 rightRow).2.1} × In₁) × In₂)),
          ∃ grandchild : ProfiledOpenRightPointedRealization A strategy hwin
              basis (leftOutput.2 leftRow).2,
            profiledOpenThreadStep A (.right source)
                (.live (.right member.1))
                (realization.representableMove A,
                  .left (rightOutput.2 rightRow).2)
                (.fromOne member.1 rightRow rightPast rightInput) =
              .live (.left child.selected.1) ∧
            profiledOpenThreadStep A
                (.left (rightOutput.2 rightRow).2)
                (.live (.left child.selected.1))
                (child.realization.representableMove A,
                  .right (leftOutput.2 leftRow).2)
                (.fromTwo child.selected.1 leftRow leftPast leftInput) =
              .live (.right grandchild.selected.1) ∧
            PairedStrategyMemory.step (A := A)
                (.processOne (realization.entry member)
                  (realization.minimum member))
                (.fromOne rightRow
                  (rightSemanticPast.map fun old => (old.1.2, old.2))
                  rightInput) =
              .processTwo child.actualEntry child.actualMinimum ∧
            PairedStrategyMemory.step (A := A)
                (.processTwo child.actualEntry child.actualMinimum)
                (.fromTwo leftRow
                  (leftSemanticPast.map fun old => (old.1.2, old.2))
                  leftInput) =
              .processOne grandchild.actualEntry grandchild.actualMinimum := by
  classical
  dsimp only
  obtain ⟨rightSemanticPast, child, hrightThread, hrightMemory⟩ :=
    exists_profiledOpenRightPolicyFreeLiveThreadStep A realization member
      rightRow rightPast rightInput
  let rightOutput := profiledOpenRightRepresentableOutputAt A source
    (realization.coherentTable A).table member
    (omegaOfList (rightPast ++ [rightInput])) rightPast.length
  obtain ⟨leftSemanticPast, grandchild, hleftThread, hleftMemory⟩ :=
    exists_profiledOpenLeftPolicyFreeLiveThreadStep A child.realization
      child.selected leftRow leftPast leftInput
  have hleftMemory' :
      PairedStrategyMemory.step (A := A)
          (.processTwo child.actualEntry child.actualMinimum)
          (.fromTwo leftRow
            (leftSemanticPast.map fun old => (old.1.2, old.2)) leftInput) =
        .processOne grandchild.actualEntry grandchild.actualMinimum := by
    simpa only [child.entry_selected, child.minimum_selected] using hleftMemory
  exact ⟨rightSemanticPast, child, leftSemanticPast, grandchild,
    hrightThread, hleftThread, hrightMemory, hleftMemory'⟩

end

end

end DetParityAutomaton

end DistributedSynthesis
