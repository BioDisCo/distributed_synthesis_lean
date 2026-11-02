/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPersistentOneSidedPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose

/-!
# Physical closes inside one persistent hybrid policy

This file connects the persistent-policy invariant to the already verified
raw-joint physical child equations.  At a reachable one-sided hybrid key, a
right or left physical close emits a live opposite-lane slot and follows an
allowed edge of the same hybrid policy.  No independently rationalized child
policy occurs in the statement.
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

/-- Allowed targets in one fixed hybrid finite-code policy. -/
abbrev ProfiledRawJointHybridProvenanceAllowedTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (initialCode : ProfiledRawJointHybridCode A)
    (policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
      initialCode)
    (source target : ProfiledRawJointHybridProvenancePolicyState A strategy
      initialCode) : Prop :=
  SourceFreeBeliefFiniteCodePolicyImage.AllowedTarget
    (profiledRawJointHybridCodeParityDPA A initialCode)
    initialCode
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A)
    policy source target

namespace ProfiledRawJointHybridOneSidedInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointHybridCode A}
variable {policy : ProfiledRawJointHybridProvenanceRationalPolicy A strategy
  initialCode}
variable {key : ProfiledRawJointHybridOneSidedPolicyKey A strategy initialCode
  policy}

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The installed raw move is valid for the exact incidence family stored by
the hybrid key. -/
theorem move_valid
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key) :
    installed.rawMove.Valid A key.incidenceCode.family := by
  have hvalid := installed.source.move_valid_of_winning A hwin
  rw [installed.incidence_eq, installed.move_eq] at hvalid
  exact hvalid

/-- Every physical strict child is an allowed target of the same hybrid
policy. -/
theorem strict_allowedTarget
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
      policy key.state (installed.strictSuccessorKey A actual).state := by
  refine ⟨installed.strictChildCode A actual, ?_⟩
  rfl

/-- A live right slot in the installed semantic source is reflexive at every
physical closing row. -/
theorem rightPattern_self
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source)
    (row : PairedEntryRow) :
    key.incidenceCode.family.rightPattern ((), row) ((), row) = true := by
  have hslot : profiledRawJointOneSidedCurrentSlots A .right
      (installed.source.code A) () = some (.inl source) := by
    simp [installed.incidence_eq, hsource,
      profiledRawJointOneSidedCurrentSlots]
  have hreflexive := installed.source.rightPattern_self_of_currentSlot A
    (.inl source) hslot row
  simpa [installed.incidence_eq] using hreflexive

/-- Left-slot mirror. -/
theorem leftPattern_self
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawLeftSlot A)
    (hsource : key.incidenceCode.family.left () = some source)
    (row : PairedEntryRow) :
    key.incidenceCode.family.leftPattern ((), row) ((), row) = true := by
  have hslot : profiledRawJointOneSidedCurrentSlots A .left
      (installed.source.code A) () = some (.inr source) := by
    simp [installed.incidence_eq, hsource,
      profiledRawJointOneSidedCurrentSlots]
  have hreflexive := installed.source.leftPattern_self_of_currentSlot A
    (.inr source) hslot row
  simpa [installed.incidence_eq] using hreflexive

/-- A concrete right physical close installs its literal left child slot in
the next state of the same hybrid policy. -/
theorem unitRight_physicalClose
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawRightSlot A)
    (hsource : key.incidenceCode.family.right () = some source)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      installed.rawMove.rightLambda () = some lambda ∧
        rightInitialFirstProfile lambda = source.2 ∧
        PairedRightForeverAccepts A source.1.1 lambda ∧
        let actual := profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input
        (installed.strictSuccessorKey A actual).incidenceCode.family.left () =
            some (profiledRawRightChildSlot A source lambda row past input) ∧
          ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
            policy key.state (installed.strictSuccessorKey A actual).state := by
  have hvalid := installed.move_valid A hwin
  rcases hvalid.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hfunctional := hvalid.2.1 ((), row)
  have hreflexive := installed.rightPattern_self A source hsource row
  let actual := profiledRawJointUnitRightActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  have hslot :
      (installed.strictSuccessorKey A actual).incidenceCode.family.left () =
        some (profiledRawRightChildSlot A source lambda row past input) := by
    simpa [actual] using
      profiledRawJointOneSidedNext_unitRight_leftSlot A key.incidenceCode
        installed.rawMove row past input source lambda hsource hlambda
        hfunctional hreflexive
  exact ⟨lambda, hlambda, hprofile, hforever, hslot,
    installed.strict_allowedTarget A actual⟩

/-- Left physical-close mirror. -/
theorem unitLeft_physicalClose
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (installed : ProfiledRawJointHybridOneSidedInstalledMove A strategy
      initialCode policy key)
    (source : ProfiledRawLeftSlot A)
    (hsource : key.incidenceCode.family.left () = some source)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      installed.rawMove.leftLambda () = some lambda ∧
        leftInitialFirstProfile lambda = source.2 ∧
        PairedLeftForeverAccepts A source.1.1 lambda ∧
        let actual := profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) row past input
        (installed.strictSuccessorKey A actual).incidenceCode.family.right () =
            some (profiledRawLeftChildSlot A source lambda row past input) ∧
          ProfiledRawJointHybridProvenanceAllowedTarget A strategy initialCode
            policy key.state (installed.strictSuccessorKey A actual).state := by
  have hvalid := installed.move_valid A hwin
  rcases hvalid.2.2.2.2.2.1 () source hsource with
    ⟨lambda, hlambda, hprofile, hforever⟩
  have hfunctional := hvalid.2.2.1 ((), row)
  have hreflexive := installed.leftPattern_self A source hsource row
  let actual := profiledRawJointUnitLeftActualDirection
    (In₁ := In₁) (In₂ := In₂) row past input
  have hslot :
      (installed.strictSuccessorKey A actual).incidenceCode.family.right () =
        some (profiledRawLeftChildSlot A source lambda row past input) := by
    simpa [actual] using
      profiledRawJointOneSidedNext_unitLeft_rightSlot A key.incidenceCode
        installed.rawMove row past input source lambda hsource hlambda
        hfunctional hreflexive
  exact ⟨lambda, hlambda, hprofile, hforever, hslot,
    installed.strict_allowedTarget A actual⟩

end

end ProfiledRawJointHybridOneSidedInstalledMove

end

end DetParityAutomaton

end DistributedSynthesis
