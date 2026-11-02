/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCrossPreselection
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedRationalPolicy

/-!
# Root-pinned literal cross policy at a guarded common occurrence

The ordinary decorated common-policy rationalization may select, at its
initial finite state, any valid occurrence having the same public code.  That
is sufficient for parity acceptance but not for an unresolved acknowledged
fork: its hidden closed branch must emit exactly the same blind output as the
literal open branch.

This file applies the one-shot root guard before rationalization.  Its unique
fresh root is forced to retain both the guarded move and the two literal-cross
table IDs extracted at the supplied semantic occurrence.  Below the first
input the root bit disappears and the policy is an ordinary finite rational
policy.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossExtra :=
  ProfiledRawJointGuardedCommonLiteralCrossExtra A

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

private abbrev DecoratedMove :=
  ProfiledRawJointGuardedCommonPair A strategy hwin × CrossExtra A

/-- The one-shot root predicate fixes the complete literal decorated move,
not merely its public code. -/
def profiledRawJointGuardedCommonLiteralCrossRootPred
    (initial : CommonPoint A strategy) (move : DecoratedMove A strategy hwin) :
    Prop :=
  move =
    (initial.move A strategy hwin,
      profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
        initial)

/-- Finite root-guarded common policy whose fresh root is the supplied literal
occurrence. -/
noncomputable abbrev
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy
    (initial : CommonPoint A strategy) :=
  SourceFreeBeliefCodeParityRootPinnedPolicy
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      (CrossValid A strategy hwin))
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
    (profiledRawJointGuardedCommonLiteralCrossRootPred A strategy hwin initial)

/-- Root-pinned rationalization exists unconditionally because the physical
input-pair alphabet is finite. -/
theorem
    nonempty_profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy
    (initial : CommonPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy
        hwin initial) := by
  let extra : CommonPoint A strategy → CrossExtra A :=
    profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
  let raw :=
    profiledRawJointGuardedCommonDecoratedSemanticTree A strategy hwin initial
      extra
  let certificate :=
    profiledRawJointGuardedCommonDecoratedSemanticTree_codeParityCertificate A
      strategy hwin initial extra (CrossValid A strategy hwin) (by
        intro point
        exact ⟨point, rfl, rfl, rfl⟩)
  exact certificate.nonempty_rootPinnedRationalPolicy_of_finite
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      (CrossValid A strategy hwin))
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
    raw
    (profiledRawJointGuardedCommonLiteralCrossRootPred A strategy hwin initial)
    rfl

/-- Canonical finite root-pinned package. -/
noncomputable def
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy
    (initial : CommonPoint A strategy) :
    ProfiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A
      strategy hwin initial)

/-- The selected fresh-root move is definitionally constrained to the exact
literal guarded pair and both preselected cross tables. -/
@[simp] theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_rootMove
    (initial : CommonPoint A strategy) :
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial).rootMove =
      (initial.move A strategy hwin,
        profiledRawJointGuardedCommonLiteralCrossExtraOfPoint A strategy hwin
          initial) :=
  (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
    initial).rootMove_realizes.2.1

/-- Every first input leaves the fresh root with the literal move's exact
child code.  This is the entry equation needed before constructing the
endpoint-local bootstrap controls. -/
theorem
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_successor
    (initial : CommonPoint A strategy) (input : In₁ × In₂) :
    let package :=
      profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
        initial
    let D :=
      profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy)
    package.policy.successor
        (true,
          (sourceFreeBeliefCodeParityRunAutomaton D
            (initial.code A strategy)
            (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
              (CrossValid A strategy hwin))
            (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)
            ).initial)
        input =
      (false,
        (initial.move A strategy hwin |>.bothNextCode A strategy hwin input,
          D.step D.initial
            (initial.move A strategy hwin |>.bothNextCode A strategy hwin
              input))) := by
  dsimp only
  have hroot :=
    (profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy A strategy hwin
      initial).rootMove_realizes.2.2 input
  rw [
    profiledRawJointGuardedCommonLiteralCrossRootPinnedPolicy_rootMove A
      strategy hwin initial] at hroot
  simpa [ProfiledRawJointGuardedCommonDecoratedNext,
    sourceFreeBeliefDecoratedNext] using hroot

end

end DetParityAutomaton

end DistributedSynthesis
