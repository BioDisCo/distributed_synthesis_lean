/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialBothReceiveShadow
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridSelfPoweredStagedReceivers
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaIndexedKernel
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaRootStaging

/-!
# A fixed-anchor test for consecutive simultaneous receives

The current exceptional receiver may keep advancing as the locally
indistinguishable same-strict contingency.  The ordinary child selected at
the first actual close must nevertheless stay fixed: refreshing that anchor
to the exceptional controller's next target can leave the two recurrent
controls at different policy keys.

This file packages the immutable anchor and performs the decisive
replace-not-accumulate test.  After one mixed exceptional/ordinary round, one
further physical round in any of the three graph shapes produces ordinary
controls indexed by the same mega child.  The construction uses no graph or
leader datum in a local state; the three resolution functions are selected by
the ordinary receive/no-receive dispatcher.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## The immutable exceptional-right anchor -/

/-- The advancing exceptional-right contingency together with the exact
ordinary child emitted at its first actual close.  `current.receiver.pending`
may change; `anchor` deliberately does not. -/
structure ProfiledRawJointHybridAnchoredInitialRightPhase where
  current : ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
    initialBank
  anchor : Option (ProfiledRawJointHybridInitialLeftPending A strategy hwin
    initialBank current.receiver.base.1)

noncomputable instance
    profiledRawJointHybridAnchoredInitialRightPhaseFintype :
    Fintype (ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ current :
      ProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
        initialBank,
    Option (ProfiledRawJointHybridInitialLeftPending A strategy hwin
      initialBank current.receiver.base.1)
  let equiv :
      ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦ ⟨state.current, state.anchor⟩
    invFun := fun state ↦ ⟨state.1, state.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by intro state; rcases state with ⟨current, anchor⟩; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Convert the corrected first-`both` phase into an immutable-anchor phase.
Both local processes call this same function on the same old receiver. -/
noncomputable def startProfiledRawJointHybridAnchoredInitialRightPhase
    (partner : ProfiledRawJointRootLeftReceiverControl A strategy)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) × Option
      (ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
        initialBank) :=
  let next :=
    startProfiledRawJointHybridInitialGuardedRightBothShadow A strategy hwin
      initialBank partner row current
  (next.1, next.2.map fun state ↦
    ⟨⟨state.receiver, state.owner⟩, state.receiver.pending⟩)

/-- Advance only the hypothetical exceptional parent, preserving the first
closed child rather than replacing it by the new pending target. -/
noncomputable def advanceProfiledRawJointHybridAnchoredInitialRightParent
    (state : ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    Out₂ × ProfiledRawJointHybridAnchoredInitialRightPhase A strategy
      hwin initialBank :=
  let next :=
    advanceProfiledRawJointHybridPoweredInitialLeftReceiver A strategy hwin
      initialBank state.current (current.2, current.1)
  (next.1, ⟨next.2, state.anchor⟩)

@[simp] theorem
    advanceProfiledRawJointHybridAnchoredInitialRightParent_anchor
    (state : ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    (advanceProfiledRawJointHybridAnchoredInitialRightParent A strategy hwin
      initialBank state current).2.anchor = state.anchor :=
  rfl

/-! ## The fixed mega child and a matched-left constructor -/

/-- Embed the immutable exceptional-right child in the global mega family. -/
def profiledRawJointHybridAnchoredInitialRightChild
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy)
    (anchor : ProfiledRawJointHybridInitialLeftPending A strategy hwin
      initialBank key) :
    ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank :=
  profiledRawJointHybridMegaChildOfInitial A strategy hwin initialBank
    (.inl ⟨key, anchor.1⟩)

/-- Execute one matched-left round at one exact mega root.  Both controls are
indexed by the same child by construction. -/
noncomputable def profiledRawJointHybridMegaStartMatchedLeft
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (root : ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank
      child)
    (row : PairedEntryRow) (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
          child ×
        ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
          child) :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank child
  let restart := profiledRawJointUnitRestartLeft A strategy source policy bank
    root row
  let receiver := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank restart.2 restart.1 current
  let owner := stepProfiledRawJointUnitLeftPolicyOwner A strategy source policy
    bank restart.1 current.2
  ((receiver.1, owner.1), (receiver.2, owner.2))

/-! ## One mixed round, then unconditional exit -/

/-- Proof-side synchronized state after the first repeated `both`: process
one has entered the fixed ordinary child, process two may still be advancing
the exceptional parent, and both can compute all three finite components.
There is no recursively nested shadow. -/
structure ProfiledRawJointHybridAnchoredInitialRightMixed where
  child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank
  leftReceiver : ProfiledRawJointHybridMegaLeftReceiver A strategy hwin
    initialBank child
  leftOwner : ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
    child
  parent : ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
    initialBank

noncomputable instance
    profiledRawJointHybridAnchoredInitialRightMixedFintype :
    Fintype (ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
      initialBank) := by
  classical
  let Rep := Σ child :
      ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank,
    ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank child ×
      ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank child ×
      ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
        initialBank
  let equiv :
      ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
          initialBank ≃ Rep := {
    toFun := fun state ↦
      ⟨state.child, state.leftReceiver, state.leftOwner, state.parent⟩
    invFun := fun state ↦
      ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
    left_inv := by intro state; cases state; rfl
    right_inv := by
      intro state
      rcases state with ⟨child, receiver, owner, parent⟩
      rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- Enter the unique mixed phase using the immutable first child.  Failure is
only the existing totalization of an absent/unlive staged root. -/
noncomputable def enterProfiledRawJointHybridAnchoredInitialRightMixed
    (state : ProfiledRawJointHybridAnchoredInitialRightPhase A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    Option ((Out₁ × Out₂) ×
      ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
        initialBank) := by
  classical
  cases hanchor : state.anchor with
  | none => exact none
  | some anchor =>
      let child := profiledRawJointHybridAnchoredInitialRightChild A strategy
        hwin initialBank state.current.receiver.base.1 anchor
      cases hroot : profiledRawJointHybridMegaLeftRoot? A strategy hwin
          initialBank child with
      | none => exact none
      | some root =>
          let matched := profiledRawJointHybridMegaStartMatchedLeft A strategy
            hwin initialBank child root state.current.receiver.base.2.1 current
          let parent :=
            advanceProfiledRawJointHybridAnchoredInitialRightParent A strategy
              hwin initialBank state current
          exact some ((matched.1.1, parent.1),
            ⟨child, matched.2.1, matched.2.2, parent.2⟩)

/-- A following strict-left round stays at the fixed child. -/
noncomputable def
    resolveProfiledRawJointHybridAnchoredInitialRightMixedLeft
    (state : ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
          state.child ×
        ProfiledRawJointHybridMegaLeftOwner A strategy hwin initialBank
          state.child) :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank state.child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank state.child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank state.child
  let receiver := continueProfiledRawJointUnitLeftPolicyReceiver A strategy
    source policy bank state.leftReceiver state.leftOwner current
  let owner := stepProfiledRawJointUnitLeftPolicyOwner A strategy source policy
    bank state.leftOwner current.2
  ((receiver.1, owner.1), (receiver.2, owner.2))

/-- A following strict-right round switches both local controls inside the
same fixed child policy. -/
noncomputable def
    resolveProfiledRawJointHybridAnchoredInitialRightMixedRight
    (state : ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (ProfiledRawJointHybridMegaRightOwner A strategy hwin initialBank
          state.child ×
        ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank
          state.child) :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank state.child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank state.child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank state.child
  let owner := profiledRawJointUnitPolicyStartRightOwner A strategy source
    policy bank state.leftReceiver current.1
  let receiver := profiledRawJointUnitPolicyStartRightReceiver A strategy
    source policy bank state.leftReceiver (current.2, current.1)
  ((owner.1, receiver.1), (owner.2, receiver.2))

/-- A following simultaneous round produces the ordinary receiver/receiver
cross, still at one fixed child. -/
noncomputable def
    resolveProfiledRawJointHybridAnchoredInitialRightMixedBoth
    (state : ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
      initialBank)
    (current : In₁ × In₂) :
    (Out₁ × Out₂) ×
      (ProfiledRawJointHybridMegaLeftReceiver A strategy hwin initialBank
          state.child ×
        ProfiledRawJointHybridMegaRightReceiver A strategy hwin initialBank
          state.child) :=
  let source := profiledRawJointHybridMegaChildSource A strategy hwin
    initialBank state.child
  let policy := profiledRawJointHybridMegaChildPolicy A strategy hwin
    initialBank state.child
  let bank := profiledRawJointHybridMegaChildControllerBank A strategy hwin
    initialBank state.child
  let left := continueProfiledRawJointUnitLeftPolicyReceiver A strategy source
    policy bank state.leftReceiver state.leftOwner current
  let right := profiledRawJointUnitPolicyStartRightReceiver A strategy source
    policy bank state.leftReceiver (current.2, current.1)
  ((left.1, right.1), (left.2, right.2))

/-- The endpoint child keys, and hence their finite incidence codes, are
literally identical in every resolution. -/
theorem profiledRawJointHybridAnchoredInitialRightMixed_incidence_same
    (state : ProfiledRawJointHybridAnchoredInitialRightMixed A strategy hwin
      initialBank) :
    profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        state.child =
      profiledRawJointHybridMegaChildIncidenceCode A strategy hwin initialBank
        state.child :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
