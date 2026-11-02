/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedFirstPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose

/-!
# Exact physical children of a root-pinned raw-joint move

A root-pinned policy is exceptional only at its fresh root.  The move
installed there has a literal semantic provenance witness, selected once by
`profiledRawJointRootPinnedSelectedSource`.  This file turns a live singleton
slot of that selected source into the right- or left-block activation needed
by the first recurrent block.

The receiver target is not an arbitrary same-code representative.  It is the
finite subtype element obtained from the concrete physical row, past, and
current input.  Its value is definitionally the exact one-sided raw child of
the installed semantic source.  Hence it can be used immediately as the key
of the fresh ordinary child-policy bank after the exceptional block.

The orientation remains proof-side.  No process is told which lane is live,
which row Nature selected, or who is the strict leader.
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

/-! ## Canonical exact targets -/

/-- The exact finite child produced at one physical right close of the move
actually installed at the guarded root. -/
def profiledRawJointGuardedFirstRightTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package) :=
  profiledRawJointOneSidedLiteralChildCodeOfActual A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package)
    (profiledRawJointUnitRightActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input)

/-- Left-close mirror. -/
def profiledRawJointGuardedFirstLeftTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedLiteralChildCode A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package) :=
  profiledRawJointOneSidedLiteralChildCodeOfActual A strategy
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package)
    (profiledRawJointUnitLeftActualDirection
      (In₁ := In₁) (In₂ := In₂) row past input)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointGuardedFirstRightTarget_val
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
      package row past input).1 =
      let selected := profiledRawJointRootPinnedSelectedSource A strategy
        initial RootPred package
      profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointGuardedFirstLeftTarget_val
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
      package row past input).1 =
      let selected := profiledRawJointRootPinnedSelectedSource A strategy
        initial RootPred package
      profiledRawJointOneSidedNext A (selected.code A) (selected.move A)
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input) :=
  rfl

/-! ## Installed physical activations -/

/-- One installed right lambda at a live slot of the selected guarded-root
source, together with the exact active-slot equation for every physical
close. -/
structure ProfiledRawJointGuardedFirstRightBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A) where
  lambda : ProcOnePairedRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : package.rootMove.rightLambda () = some lambda
  initial_profile : rightInitialFirstProfile lambda = source.2
  forever : PairedRightForeverAccepts A source.1.1 lambda
  target_active_slot : ∀ row past input,
    (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
      package row past input).1.family.left () =
      some (profiledRawRightChildSlot A source lambda row past input)

/-- Process-two/left mirror. -/
structure ProfiledRawJointGuardedFirstLeftBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A) where
  lambda : ProcTwoPairedLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  lambda_selected : package.rootMove.leftLambda () = some lambda
  initial_profile : leftInitialFirstProfile lambda = source.2
  forever : PairedLeftForeverAccepts A source.1.1 lambda
  target_active_slot : ∀ row past input,
    (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
      package row past input).1.family.right () =
      some (profiledRawLeftChildSlot A source lambda row past input)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The root-pinned provenance witness unconditionally supplies the complete
right activation at every live right slot of its selected source. -/
theorem nonempty_profiledRawJointGuardedFirstRightBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawRightSlot A)
    (hsource : (initial.code A).family.right () = some source) :
    Nonempty (ProfiledRawJointGuardedFirstRightBlockActivation A strategy
      initial RootPred package source) := by
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    RootPred package
  have hcode : selected.code A = initial.code A :=
    profiledRawJointRootPinnedSelectedSource_code A strategy initial RootPred
      package
  have hmove : selected.move A = package.rootMove :=
    profiledRawJointRootPinnedSelectedSource_move A strategy initial RootPred
      package
  have hsourceSelected : (selected.code A).family.right () = some source := by
    rw [hcode]
    exact hsource
  have hvalid : (selected.move A).Valid A (selected.code A).family := by
    rw [hcode, hmove]
    exact package.rootMove_realizes.1.1
  rcases hvalid.2.2.2.1 () source hsourceSelected with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .right
      (selected.code A) () = some (.inl source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsourceSelected]
  refine ⟨{
    lambda := lambda
    lambda_selected := ?_
    initial_profile := hprofile
    forever := hforever
    target_active_slot := ?_ }⟩
  · rw [← hmove]
    exact hlambda
  · intro row past input
    have hreflexive := selected.rightPattern_self_of_currentSlot A
      (.inl source) hcurrent row
    have hfunctional := hvalid.2.1 ((), row)
    exact profiledRawJointOneSidedNext_unitRight_leftSlot A
      (selected.code A) (selected.move A) row past input source lambda
      hsourceSelected hlambda hfunctional hreflexive

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left activation mirror. -/
theorem nonempty_profiledRawJointGuardedFirstLeftBlockActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (source : ProfiledRawLeftSlot A)
    (hsource : (initial.code A).family.left () = some source) :
    Nonempty (ProfiledRawJointGuardedFirstLeftBlockActivation A strategy
      initial RootPred package source) := by
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    RootPred package
  have hcode : selected.code A = initial.code A :=
    profiledRawJointRootPinnedSelectedSource_code A strategy initial RootPred
      package
  have hmove : selected.move A = package.rootMove :=
    profiledRawJointRootPinnedSelectedSource_move A strategy initial RootPred
      package
  have hsourceSelected : (selected.code A).family.left () = some source := by
    rw [hcode]
    exact hsource
  have hvalid : (selected.move A).Valid A (selected.code A).family := by
    rw [hcode, hmove]
    exact package.rootMove_realizes.1.1
  rcases hvalid.2.2.2.2.2.1 () source hsourceSelected with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hcurrent : profiledRawJointOneSidedCurrentSlots A .left
      (selected.code A) () = some (.inr source) := by
    simp [profiledRawJointOneSidedCurrentSlots, hsourceSelected]
  refine ⟨{
    lambda := lambda
    lambda_selected := ?_
    initial_profile := hprofile
    forever := hforever
    target_active_slot := ?_ }⟩
  · rw [← hmove]
    exact hlambda
  · intro row past input
    have hreflexive := selected.leftPattern_self_of_currentSlot A
      (.inr source) hcurrent row
    have hfunctional := hvalid.2.2.1 ((), row)
    exact profiledRawJointOneSidedNext_unitLeft_rightSlot A
      (selected.code A) (selected.move A) row past input source lambda
      hsourceSelected hlambda hfunctional hreflexive

/-! ## Direct handoff to the fresh ordinary bank -/

/-- After a concrete exceptional right close, select the fresh ordinary
policy rooted at that exact raw child. -/
noncomputable def profiledRawJointGuardedFirstRightChildPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
        package row past input).1 :=
  profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
    RootPred package
    (profiledRawJointGuardedFirstRightTarget A strategy initial RootPred
      package row past input)

/-- Left-close mirror. -/
noncomputable def profiledRawJointGuardedFirstLeftChildPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := Unit) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
        package row past input).1 :=
  profiledRawJointRootPinnedLiteralChildPolicyBank A strategy hwin initial
    RootPred package
    (profiledRawJointGuardedFirstLeftTarget A strategy initial RootPred
      package row past input)

end

end DetParityAutomaton

end DistributedSynthesis
