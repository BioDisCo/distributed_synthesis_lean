/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedProvenancePolicy
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedRationalPolicy

/-!
# A one-shot raw-joint root guard and its ordinary child-policy bank

The initial seam carries one finite overlap promise which is not determined
by the recurrent Unit incidence code alone.  That promise must constrain the
literal root move once, not every later occurrence of the same finite code.
The generic source-free root guard gives exactly that quantifier order.

The guarded policy is deliberately not used as the recurrent policy.  Its
children carry a `withInitial` continuation of the old code monitor, whereas
the already established recurrent block monitors consume an ordinary
provenance policy freshly rooted at a recurrent code.  For every finite code
which is a literal child of the guarded semantic root, this file therefore
selects one such ordinary policy.  After the exceptional first block chooses
a child, the guard disappears and the corresponding ordinary fixed-policy
bank can be used unchanged.

The selected side and the witness that a code is literal are proof data.  The
runtime index of the child bank is only a finite incidence code; no process is
given an orientation or strict-leader bit.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-! ## The root predicate is checked exactly once -/

/-- Provenance-strengthened finite-code policy with a one-shot predicate on
the move installed at the literal semantic root. -/
noncomputable abbrev ProfiledRawJointOneSidedRootPinnedProvenancePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop) :=
  SourceFreeBeliefFiniteCodeRootPinnedPolicy
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
    (initial.code A)
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    RootPred

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any predicate true of the literal semantic move can be retained through
finite-code rationalization at the fresh root only. -/
theorem nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (hroot : RootPred (initial.move A)) :
    Nonempty
      (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy initial
        RootPred) := by
  let raw := profiledRawJointOneSidedSemanticTree A initial
  let certificate :=
    profiledRawJointOneSidedSemanticTree_provenanceCodeParityCertificate A
      strategy hwin initial
  exact certificate.nonempty_finiteCodeDirectionRootPinnedRationalPolicy
    (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
    (initial.code A)
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (profiledRawJointOneSidedNext A)
    raw RootPred hroot

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- In particular, the complete literal root move can be pinned.  Concrete
initial seams normally use a weaker finite response predicate instead. -/
theorem nonempty_profiledRawJointOneSidedExactRootProvenancePolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    Nonempty
      (ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy initial
        (fun move ↦ move = initial.move A)) :=
  nonempty_profiledRawJointOneSidedRootPinnedProvenancePolicy A strategy hwin
    initial (fun move ↦ move = initial.move A) rfl

/-- The provenance conjunct of the guarded root move supplies one literal
semantic source for the move actually selected by rationalization. -/
noncomputable def profiledRawJointRootPinnedSelectedSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := I) :=
  Classical.choose package.rootMove_realizes.1.2

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The selected semantic source has the guarded root's advertised finite
code. -/
theorem profiledRawJointRootPinnedSelectedSource_code
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package).code A = initial.code A :=
  (Classical.choose_spec package.rootMove_realizes.1.2).1

/-- Its literal semantic move is exactly the move installed by the guarded
rational policy, so its children are the children of the selected root
transition rather than of an unrelated same-code representative. -/
theorem profiledRawJointRootPinnedSelectedSource_move
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package).move A = package.rootMove :=
  (Classical.choose_spec package.rootMove_realizes.1.2).2

/-- On every literal direction of the selected semantic source, the guarded
root transition announces exactly that source's child code.  This is the
equation checked by the exceptional first-block monitor before it enters the
ordinary child-policy bank. -/
theorem profiledRawJointRootPinned_successor_eq_selectedChild
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred)
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    let selected := profiledRawJointRootPinnedSelectedSource A strategy
      initial RootPred package
    let childCode := profiledRawJointOneSidedNext A (selected.code A)
      (selected.move A) actual
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton
            (profiledRawJointOneSidedCodeParityDPA A (initial.code A))
            (initial.code A)
            (ProfiledRawJointOneSidedProvenanceValid A strategy)
            (profiledRawJointOneSidedFiniteCodeNext A)).initial)
        childCode =
      (false,
        (childCode,
          (profiledRawJointOneSidedCodeParityDPA A (initial.code A)).step
            (profiledRawJointOneSidedCodeParityDPA A
              (initial.code A)).initial childCode)) := by
  let selected := profiledRawJointRootPinnedSelectedSource A strategy initial
    RootPred package
  let childCode := profiledRawJointOneSidedNext A (selected.code A)
    (selected.move A) actual
  have hcode : selected.code A = initial.code A :=
    profiledRawJointRootPinnedSelectedSource_code A strategy initial RootPred
      package
  have hmove : selected.move A = package.rootMove :=
    profiledRawJointRootPinnedSelectedSource_move A strategy initial RootPred
      package
  have hfinite :
      profiledRawJointOneSidedFiniteCodeNext A (initial.code A)
          package.rootMove childCode = childCode := by
    dsimp only [childCode]
    rw [hcode, hmove]
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (profiledRawJointOneSidedNext A) (initial.code A) package.rootMove actual
  have hsuccessor := package.rootMove_realizes.2.2 childCode
  have hfinite' :
      sourceFreeBeliefFiniteCodeNext (profiledRawJointOneSidedNext A)
          (initial.code A) package.rootMove childCode = childCode := by
    simpa only [profiledRawJointOneSidedFiniteCodeNext] using hfinite
  simp only [hfinite'] at hsuccessor
  simpa only using hsuccessor

end

/-! ## Finite literal-child codes -/

/-- The finite subtype of incidence codes which occur as a literal semantic
child of `initial` under its installed raw joint move. -/
abbrev ProfiledRawJointOneSidedLiteralChildCode
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :=
  { childCode : ProfiledRawJointIncidenceCode A (I := I) //
    ∃ actual : ProfiledRawJointActualDirection
        (I := I) (In₁ := In₁) (In₂ := In₂),
      profiledRawJointOneSidedNext A (initial.code A) (initial.move A) actual =
        childCode }

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    Fintype (ProfiledRawJointOneSidedLiteralChildCode A strategy initial) := by
  classical
  infer_instance

/-- Package an actual direction by its literal finite child code. -/
def profiledRawJointOneSidedLiteralChildCodeOfActual
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedLiteralChildCode A strategy initial :=
  ⟨profiledRawJointOneSidedNext A (initial.code A) (initial.move A) actual,
    actual, rfl⟩

omit [Fintype I] [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
@[simp] theorem profiledRawJointOneSidedLiteralChildCodeOfActual_val
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointOneSidedLiteralChildCodeOfActual A strategy initial
      actual).1 =
      profiledRawJointOneSidedNext A (initial.code A) (initial.move A) actual :=
  rfl

noncomputable instance
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    Inhabited (ProfiledRawJointOneSidedLiteralChildCode A strategy initial) :=
  let actual := Classical.choice
    (profiledRawJointActualDirectionNonempty
      (I := I) (In₁ := In₁) (In₂ := In₂))
  ⟨profiledRawJointOneSidedLiteralChildCodeOfActual A strategy initial actual⟩

/-- A chosen literal semantic child representing one realizable finite child
code.  Different exact directions with the same code need not be retained. -/
noncomputable def profiledRawJointOneSidedLiteralChildSource
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := I) :=
  initial.step A (Classical.choose child.2)

omit [Inhabited I] [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂]
    [Fintype Out₁] [Fintype Out₂] in
/-- The chosen semantic representative has exactly the advertised child
code. -/
theorem profiledRawJointOneSidedLiteralChildSource_code
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial) :
    (profiledRawJointOneSidedLiteralChildSource A strategy initial child).code
        A = child.1 := by
  let actual := Classical.choose child.2
  have hstep := ProfiledRawJointOneSidedSemanticState.step_code A initial
    actual
  have hcode := Classical.choose_spec child.2
  exact hstep.trans hcode

/-! ## A fresh ordinary policy at every literal child -/

/-- An ordinary provenance policy freshly rooted at a literal child code.
This is the policy type consumed by the recurrent Unit block monitors. -/
noncomputable def profiledRawJointOneSidedLiteralChildPolicy
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1 := by
  let source :=
    profiledRawJointOneSidedLiteralChildSource A strategy initial child
  have hcode : source.code A = child.1 :=
    profiledRawJointOneSidedLiteralChildSource_code A strategy initial child
  rw [← hcode]
  exact Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      source)

/-- The finite bank selected after the exceptional first block.  The bank is
fixed proof-side; a runtime handoff carries only its finite child-code key. -/
abbrev ProfiledRawJointOneSidedLiteralChildPolicyBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :=
  ∀ child : ProfiledRawJointOneSidedLiteralChildCode A strategy initial,
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy child.1

/-- All literal finite children simultaneously receive ordinary fixed
policies.  This is finite choice over child codes, not a policy switch during
the recurrent phase: after one child is selected, its policy remains fixed. -/
noncomputable def profiledRawJointOneSidedLiteralChildPolicyBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I)) :
    ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy initial :=
  fun child ↦
    profiledRawJointOneSidedLiteralChildPolicy A strategy hwin initial child

/-- The ordinary child-policy bank attached to the semantic source of the
move actually installed at a guarded root. -/
noncomputable def profiledRawJointRootPinnedLiteralChildPolicyBank
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (RootPred : ProfiledRawJointLambdaFamilyMove A (I := I) → Prop)
    (package : ProfiledRawJointOneSidedRootPinnedProvenancePolicy A strategy
      initial RootPred) :
    ProfiledRawJointOneSidedLiteralChildPolicyBank A strategy
      (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
        package) :=
  profiledRawJointOneSidedLiteralChildPolicyBank A strategy hwin
    (profiledRawJointRootPinnedSelectedSource A strategy initial RootPred
      package)

/-- Direct actual-direction readback of the bank. -/
noncomputable def profiledRawJointOneSidedLiteralChildPolicyAtActual
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := I))
    (actual : ProfiledRawJointActualDirection
      (I := I) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      (profiledRawJointOneSidedNext A (initial.code A) (initial.move A)
        actual) :=
  profiledRawJointOneSidedLiteralChildPolicyBank A strategy hwin initial
    (profiledRawJointOneSidedLiteralChildCodeOfActual A strategy initial
      actual)

end

end DetParityAutomaton

end DistributedSynthesis
