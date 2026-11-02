/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridCommonOneRoundReplacement
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitPolicyControllerBank

/-!
# Fresh recurrent policy banks at a common successor

The one-round replacement theorem identifies either strict shadow of a
common receive with one singleton projection of the hypothetical simultaneous
successor.  This file makes the operational consequence finite: at every
reachable common control and input pair, select an ordinary one-sided policy,
its live root macro, and its complete recurrent controller bank for each of
the two singleton projections.

The two choices are proof-side data indexed by finite common controls.  They
are not an orientation or leader signal supplied to either process.  A later
local carrier chooses a projection only after its honest `recv`/`noRecv`
event resolves the common/strict ambiguity.
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

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridCommonPolicyKey A strategy initialCode
  policy}

/-! ## The two exact replacement sources -/

/-- Process-one/right-live replacement at the hypothetical simultaneous
successor.  It represents the locally indistinguishable strict-left child. -/
abbrev ProfiledRawJointHybridCommonRightReplacementSource
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (installed.nextInstalled A input).world.oneSidedState A .right

/-- Process-two/left-live mirror, representing the strict-right child. -/
abbrev ProfiledRawJointHybridCommonLeftReplacementSource
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedSemanticState A strategy (I := Unit) :=
  (installed.nextInstalled A input).world.oneSidedState A .left

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact finite-code identification of the right-live replacement. -/
theorem profiledRawJointHybridCommonRightReplacementSource_code
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridCommonRightReplacementSource A installed input).code
        A =
      profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictLeft input) :=
  installed.oneRound_rightReplacement_code A input

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact finite-code identification of the left-live replacement. -/
theorem profiledRawJointHybridCommonLeftReplacementSource_code
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    (ProfiledRawJointHybridCommonLeftReplacementSource A installed input).code
        A =
      profiledRawJointOneSidedNext A key.incidenceCode installed.rawMove
        (profiledRawJointCommonOneRoundStrictRight input) :=
  installed.oneRound_leftReplacement_code A input

/-! ## Fresh ordinary policies and their live roots -/

/-- Select an ordinary recurrent policy at the right-live replacement. -/
noncomputable def profiledRawJointHybridCommonRightReplacementPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((ProfiledRawJointHybridCommonRightReplacementSource A installed input
        ).code A) :=
  Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      (ProfiledRawJointHybridCommonRightReplacementSource A installed input))

/-- Left-live mirror. -/
noncomputable def profiledRawJointHybridCommonLeftReplacementPolicy
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
      ((ProfiledRawJointHybridCommonLeftReplacementSource A installed input
        ).code A) :=
  Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      (ProfiledRawJointHybridCommonLeftReplacementSource A installed input))

/-- The selected right-live policy starts at its literal singleton slot. -/
noncomputable def profiledRawJointHybridCommonRightReplacementRoot
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointUnitRightPolicyMacro A strategy
      ((ProfiledRawJointHybridCommonRightReplacementSource A installed input
        ).code A)
      (profiledRawJointHybridCommonRightReplacementPolicy A hwin installed
        input) := by
  let source :=
    ProfiledRawJointHybridCommonRightReplacementSource A installed input
  let replacementPolicy :=
    profiledRawJointHybridCommonRightReplacementPolicy A hwin installed input
  have hrootCode : (replacementPolicy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst replacementPolicy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := replacementPolicy.run []
    reachable := ⟨[], rfl⟩
    slot := (installed.nextInstalled A input).world.procOneSlot A
    active_slot := by
      rw [hrootCode]
      rfl }

/-- The selected left-live policy starts at its literal singleton slot. -/
noncomputable def profiledRawJointHybridCommonLeftReplacementRoot
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointUnitLeftPolicyMacro A strategy
      ((ProfiledRawJointHybridCommonLeftReplacementSource A installed input
        ).code A)
      (profiledRawJointHybridCommonLeftReplacementPolicy A hwin installed
        input) := by
  let source :=
    ProfiledRawJointHybridCommonLeftReplacementSource A installed input
  let replacementPolicy :=
    profiledRawJointHybridCommonLeftReplacementPolicy A hwin installed input
  have hrootCode : (replacementPolicy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst replacementPolicy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := replacementPolicy.run []
    reachable := ⟨[], rfl⟩
    slot := (installed.nextInstalled A input).world.procTwoSlot A
    active_slot := by
      rw [hrootCode]
      rfl }

/-! ## Complete recurrent controller banks -/

/-- All recurrent controllers below the right-live replacement policy. -/
noncomputable def profiledRawJointHybridCommonRightReplacementControllerBank
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (ProfiledRawJointHybridCommonRightReplacementSource A installed input)
      (profiledRawJointHybridCommonRightReplacementPolicy A hwin installed
        input) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (ProfiledRawJointHybridCommonRightReplacementSource A installed input)
    (profiledRawJointHybridCommonRightReplacementPolicy A hwin installed input)

/-- All recurrent controllers below the left-live replacement policy. -/
noncomputable def profiledRawJointHybridCommonLeftReplacementControllerBank
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridCommonInstalledMove A strategy
      initialCode policy key)
    (input : In₁ × In₂) :
    ProfiledRawJointUnitPolicyControllerBank A strategy
      (ProfiledRawJointHybridCommonLeftReplacementSource A installed input)
      (profiledRawJointHybridCommonLeftReplacementPolicy A hwin installed
        input) :=
  profiledRawJointUnitPolicyControllerBank A strategy
    (ProfiledRawJointHybridCommonLeftReplacementSource A installed input)
    (profiledRawJointHybridCommonLeftReplacementPolicy A hwin installed input)

end

end DetParityAutomaton

end DistributedSynthesis
