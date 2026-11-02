/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedInstalledMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitPhysicalPolicyClose

/-!
# Physical closes in the root-pinned persistent hybrid policy

The false/one-sided keys below the exact guarded root support the same
physical close equations as ordinary one-sided policy keys.  Here the target
is packaged directly as another false/one-sided key of the original guarded
policy.  Thus a physical close neither refreshes the policy nor reactivates
the one-shot root bit.
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

noncomputable instance
    profiledRawJointHybridInitialRootPinnedGuardedStateInhabited
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (first : In₁ × In₂) :
    Inhabited
      (ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first) :=
  ⟨(true,
    (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy first
      ).initial)⟩

/-- Allowed targets of the one exact guarded policy table. -/
def ProfiledRawJointHybridInitialRootPinnedAllowedTarget
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (first : In₁ × In₂)
    (source target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first) :
    Prop :=
  ∃ childCode : ProfiledRawJointHybridCode A,
    (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
      ).policy.successor source childCode = target

/-! ## Monitor-facing projections of guarded targets -/

def profiledRawJointHybridInitialRootPinnedRightTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {first : In₁ × In₂}
    (target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first) :
    PairedProfiledTreeState A :=
  match target.2.1 with
  | .oneSided code =>
      match code.family.left () with
      | some slot => .inr (.inr slot)
      | none => .inl PUnit.unit
  | _ => .inl PUnit.unit

def profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {first : In₁ × In₂}
    (target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first) :
    PairedProfiledTreeState A :=
  match target.2.1 with
  | .oneSided code =>
      match code.family.right () with
      | some slot => .inr (.inl slot)
      | none => .inl PUnit.unit
  | _ => .inl PUnit.unit

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    profiledRawJointHybridInitialRootPinnedRightTargetProfiledState_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {first : In₁ × In₂}
    (target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hcode : target.2.1 = .oneSided code)
    (hslot : code.family.left () = some slot) :
    profiledRawJointHybridInitialRootPinnedRightTargetProfiledState A target =
      .inr (.inr slot) := by
  simp [profiledRawJointHybridInitialRootPinnedRightTargetProfiledState,
    hcode, hslot]

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState_eq
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    {first : In₁ × In₂}
    (target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hcode : target.2.1 = .oneSided code)
    (hslot : code.family.right () = some slot) :
    profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState A target =
      .inr (.inl slot) := by
  simp [profiledRawJointHybridInitialRootPinnedLeftTargetProfiledState,
    hcode, hslot]

namespace ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env)}
variable {first : In₁ × In₂}
variable {key : ProfiledRawJointHybridInitialRootPinnedFalseOneSidedKey A
  strategy hwin first}

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The installed raw move is valid for the exact incidence family of the
guarded one-sided key. -/
theorem move_valid
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key) :
    installed.rawMove.Valid A key.incidenceCode.family := by
  have hvalid := installed.source.move_valid_of_winning A hwin
  rw [installed.incidence_eq, installed.move_eq] at hvalid
  exact hvalid

/-- Every strict physical child is an allowed edge of this same guarded
policy. -/
theorem strict_allowedTarget
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin first
      key.state (installed.strictSuccessorKey A actual).state := by
  exact ⟨installed.strictChildCode A actual, rfl⟩

theorem rightPattern_self
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
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

theorem leftPattern_self
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
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

/-- A concrete right physical close installs its literal left child slot at
a false/one-sided successor of the same guarded policy. -/
theorem unitRight_physicalClose
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
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
          ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
            first key.state (installed.strictSuccessorKey A actual).state := by
  have hvalid := installed.move_valid A
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
    (installed :
      ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove A
        strategy hwin first key)
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
          ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
            first key.state (installed.strictSuccessorKey A actual).state := by
  have hvalid := installed.move_valid A
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

end ProfiledRawJointHybridInitialRootPinnedFalseOneSidedInstalledMove

end


end DetParityAutomaton

end DistributedSynthesis
