/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledControllerFamily

/-!
# A recurrent profiled bank under one fixed policy

The older feasible-state bank selected a fresh rational policy whenever the
receiver crossed a block boundary.  That is unsuitable for the end-to-end
construction: all recurrent blocks below a guarded first child must remain
inside the single policy obtained by restricting the original guarded
policy.

This module extracts the policy-parametric core.  Its runtime keys are just
finite live profiled states together with proof-irrelevant reachability.  An
allowed close is staged in the opposite orientation by
`reachable_of_allowed`; no new rational policy, leader bit, or unbounded
direction witness is stored.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- A reachable process-one macro under one fixed profiled policy. -/
abbrev ProfiledPolicyRightMacro :=
  {live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) //
    PairedProfiledRationalPolicy.Reachable A policy (.inr (.inl live))}

/-- Process-two mirror. -/
abbrev ProfiledPolicyLeftMacro :=
  {live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) //
    PairedProfiledRationalPolicy.Reachable A policy (.inr (.inr live))}

noncomputable instance : Fintype (ProfiledPolicyRightMacro A policy) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledPolicyLeftMacro A policy) := by
  classical
  infer_instance

/-- The coherent finite right controller at a fixed-policy macro. -/
noncomputable def profiledPolicyRightController
    (source : ProfiledPolicyRightMacro A policy) :=
  (finiteProfiledPairedPolicyFamily A policy).rightController
    source.1.1.1 source.1.1.2 source.1.2 source.2

/-- Its certificate monitor. -/
noncomputable abbrev profiledPolicyRightMonitor
    (source : ProfiledPolicyRightMacro A policy) :=
  profiledRightBlockMonitor.{u, v, x, y, s, 1} A policy
    source.1.1.1 source.1.1.2 source.1.2

theorem profiledPolicyRightController_wins
    (source : ProfiledPolicyRightMacro A policy) :
    NarrowedAllThreadsWin (profiledPolicyRightMonitor A policy source)
      (profiledPolicyRightController A policy source).labeledTree :=
  (finiteProfiledPairedPolicyFamily A policy).rightWins
    source.1.1.1 source.1.1.2 source.1.2 source.2

/-- Process-two mirror. -/
noncomputable def profiledPolicyLeftController
    (source : ProfiledPolicyLeftMacro A policy) :=
  (finiteProfiledPairedPolicyFamily A policy).leftController
    source.1.1.1 source.1.1.2 source.1.2 source.2

noncomputable abbrev profiledPolicyLeftMonitor
    (source : ProfiledPolicyLeftMacro A policy) :=
  profiledLeftBlockMonitor.{u, v, x, y, s, 1} A policy
    source.1.1.1 source.1.1.2 source.1.2

theorem profiledPolicyLeftController_wins
    (source : ProfiledPolicyLeftMacro A policy) :
    NarrowedAllThreadsWin (profiledPolicyLeftMonitor A policy source)
      (profiledPolicyLeftController A policy source).labeledTree :=
  (finiteProfiledPairedPolicyFamily A policy).leftWins
    source.1.1.1 source.1.1.2 source.1.2 source.2

/-- Stay in the same policy after an allowed right-to-left close. -/
def profiledPolicyStageLeftOfAllowed
    (source : ProfiledPolicyRightMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) (.inr (.inr live))) :
    ProfiledPolicyLeftMacro A policy :=
  ⟨live, PairedProfiledRationalPolicy.reachable_of_allowed A policy
    source.2 hallowed⟩

/-- Left-to-right mirror. -/
def profiledPolicyStageRightOfAllowed
    (source : ProfiledPolicyLeftMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) (.inr (.inl live))) :
    ProfiledPolicyRightMacro A policy :=
  ⟨live, PairedProfiledRationalPolicy.reachable_of_allowed A policy
    source.2 hallowed⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledPolicyStageLeftOfAllowed_live
    (source : ProfiledPolicyRightMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) (.inr (.inr live))) :
    (profiledPolicyStageLeftOfAllowed A policy source live hallowed).1 = live :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledPolicyStageRightOfAllowed_live
    (source : ProfiledPolicyLeftMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) (.inr (.inl live))) :
    (profiledPolicyStageRightOfAllowed A policy source live hallowed).1 = live :=
  rfl

/-! ## Checked certificate inversion -/

/-- A checked right close produces the exact opposite-orientation macro
inside the same fixed policy. -/
def profiledPolicyLeftMacroOfRightCertificate
    (source : ProfiledPolicyRightMacro A policy)
    (target : PairedProfiledTreeState A)
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) target) :
    ProfiledPolicyLeftMacro A policy := by
  cases htarget : target with
  | inl trivial =>
      rw [htarget] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          rw [htarget] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedRightCloseTarget] at herase
      | inr leftLive =>
          exact profiledPolicyStageLeftOfAllowed A policy source leftLive
            (by simpa [htarget] using hallowed)

/-- Left-to-right mirror. -/
def profiledPolicyRightMacroOfLeftCertificate
    (source : ProfiledPolicyLeftMacro A policy)
    (target : PairedProfiledTreeState A)
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A target =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) target) :
    ProfiledPolicyRightMacro A policy := by
  cases htarget : target with
  | inl trivial =>
      rw [htarget] at herase
      cases row <;>
        simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase
  | inr live =>
      cases live with
      | inl rightLive =>
          exact profiledPolicyStageRightOfAllowed A policy source rightLive
            (by simpa [htarget] using hallowed)
      | inr leftLive =>
          rw [htarget] at herase
          cases row <;>
            simp [erasePairedProfiledState, pairedLeftCloseTarget] at herase

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledPolicyLeftMacroOfRightCertificate_live
    (source : ProfiledPolicyRightMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (scan : PairedRightScanState A) (row : PairedEntryRow)
    (letter : PairedRightBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (.inr (.inr live)) =
      pairedRightCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inl source.1)) (.inr (.inr live))) :
    (profiledPolicyLeftMacroOfRightCertificate A policy source
      (.inr (.inr live)) scan row letter herase hallowed).1 = live := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledPolicyRightMacroOfLeftCertificate_live
    (source : ProfiledPolicyLeftMacro A policy)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (scan : PairedLeftScanState A) (row : PairedEntryRow)
    (letter : PairedLeftBlockLetter
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (herase : erasePairedProfiledState A (.inr (.inl live)) =
      pairedLeftCloseTarget A scan row letter)
    (hallowed : PairedProfiledRationalPolicy.Allowed A policy
      (.inr (.inr source.1)) (.inr (.inl live))) :
    (profiledPolicyRightMacroOfLeftCertificate A policy source
      (.inr (.inl live)) scan row letter herase hallowed).1 = live := rfl

end

end DetParityAutomaton

end DistributedSynthesis
