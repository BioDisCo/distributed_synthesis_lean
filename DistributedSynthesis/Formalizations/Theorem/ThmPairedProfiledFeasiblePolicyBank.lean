/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledControllerSoundness

/-!
# Finite bank of feasible profiled paired policies

This is the profiled replacement for `ThmPairedFeasiblePolicyBank`.  A bank
key retains the one-round boundary profile as part of the paired state.  For
each feasible key we choose one rational profiled policy and the coherent
finite controller family constructed from it.
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

/-- A finite profiled paired state whose input-free run language has a
rational accepting run. -/
abbrev FeasibleProfiledPairedState :=
  {state : PairedProfiledTreeState A //
    (pairedProfiledEntryRunAutomaton A state).HasRationalRun}

noncomputable instance : Fintype (FeasibleProfiledPairedState A) := by
  classical
  infer_instance

/-- A rational profiled transition policy selected at one feasible target. -/
noncomputable def feasibleProfiledPolicy
    (target : FeasibleProfiledPairedState A) :
    (pairedProfiledEntryRunAutomaton A target.1).RationalTransitionPolicy :=
  Classical.choice
    (InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (pairedProfiledEntryRunAutomaton A target.1) target.2)

/-- The coherent finite recurrent controllers selected for this bank entry. -/
noncomputable def feasibleProfiledControllerFamily
    (target : FeasibleProfiledPairedState A) :
    FiniteProfiledPairedPolicyFamily A (feasibleProfiledPolicy A target) :=
  finiteProfiledPairedPolicyFamily A (feasibleProfiledPolicy A target)

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- The chosen policy starts at its bank target. -/
theorem feasibleProfiledPolicy_target_reachable
    (target : FeasibleProfiledPairedState A) :
    PairedProfiledRationalPolicy.Reachable A
      (feasibleProfiledPolicy A target) target.1 := by
  refine ⟨[], ?_⟩
  exact (feasibleProfiledPolicy A target).accepts.1.1

/-- Reachable process-one state in one profiled feasible bank entry. -/
abbrev ProfiledBankRightMacro :=
  Σ target : FeasibleProfiledPairedState A,
    {live : (((A.State × A.State) × A.State) ×
        RightInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)) //
      PairedProfiledRationalPolicy.Reachable A
        (feasibleProfiledPolicy A target) (.inr (.inl live))}

/-- Reachable process-two mirror. -/
abbrev ProfiledBankLeftMacro :=
  Σ target : FeasibleProfiledPairedState A,
    {live : (((A.State × A.State) × A.State) ×
        LeftInitialActionProfile
          (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)) //
      PairedProfiledRationalPolicy.Reachable A
        (feasibleProfiledPolicy A target) (.inr (.inr live))}

noncomputable instance : Fintype (ProfiledBankRightMacro A) := by
  classical
  infer_instance

noncomputable instance : Fintype (ProfiledBankLeftMacro A) := by
  classical
  infer_instance

/-- The selected right controller at a concrete profiled bank macro. -/
noncomputable def profiledBankRightController
    (source : ProfiledBankRightMacro A) :=
  (feasibleProfiledControllerFamily A source.1).rightController
    source.2.1.1.1 source.2.1.1.2 source.2.1.2 source.2.2

/-- Its certificate monitor. -/
noncomputable abbrev profiledBankRightMonitor
    (source : ProfiledBankRightMacro A) :=
  profiledRightBlockMonitor.{u, v, x, y, s, 1} A
    (feasibleProfiledPolicy A source.1)
    source.2.1.1.1 source.2.1.1.2 source.2.1.2

theorem profiledBankRightController_wins
    (source : ProfiledBankRightMacro A) :
    NarrowedAllThreadsWin (profiledBankRightMonitor A source)
      (profiledBankRightController A source).labeledTree :=
  (feasibleProfiledControllerFamily A source.1).rightWins
    source.2.1.1.1 source.2.1.1.2 source.2.1.2 source.2.2

/-- Left mirror. -/
noncomputable def profiledBankLeftController
    (source : ProfiledBankLeftMacro A) :=
  (feasibleProfiledControllerFamily A source.1).leftController
    source.2.1.1.1 source.2.1.1.2 source.2.1.2 source.2.2

noncomputable abbrev profiledBankLeftMonitor
    (source : ProfiledBankLeftMacro A) :=
  profiledLeftBlockMonitor.{u, v, x, y, s, 1} A
    (feasibleProfiledPolicy A source.1)
    source.2.1.1.1 source.2.1.1.2 source.2.1.2

theorem profiledBankLeftController_wins
    (source : ProfiledBankLeftMacro A) :
    NarrowedAllThreadsWin (profiledBankLeftMonitor A source)
      (profiledBankLeftController A source).labeledTree :=
  (feasibleProfiledControllerFamily A source.1).leftWins
    source.2.1.1.1 source.2.1.1.2 source.2.1.2 source.2.2

/-- Retype a feasible process-one target as its initial bank macro. -/
def profiledBankRightRoot
    (target : FeasibleProfiledPairedState A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (hshape : target.1 = .inr (.inl live)) :
    ProfiledBankRightMacro A := by
  refine ⟨target, live, ?_⟩
  rw [← hshape]
  exact feasibleProfiledPolicy_target_reachable A target

/-- Process-two mirror. -/
def profiledBankLeftRoot
    (target : FeasibleProfiledPairedState A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (hshape : target.1 = .inr (.inr live)) :
    ProfiledBankLeftMacro A := by
  refine ⟨target, live, ?_⟩
  rw [← hshape]
  exact feasibleProfiledPolicy_target_reachable A target

/-- An allowed right close gives the opposite profiled bank key without any
new feasibility proof: it stays inside the same rational policy. -/
def profiledBankStageLeftOfAllowed
    (source : ProfiledBankRightMacro A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (.inr (.inr live))) :
    ProfiledBankLeftMacro A :=
  ⟨source.1, live,
    PairedProfiledRationalPolicy.reachable_of_allowed A
      (feasibleProfiledPolicy A source.1) source.2.2 hallowed⟩

/-- Left-to-right mirror. -/
def profiledBankStageRightOfAllowed
    (source : ProfiledBankLeftMacro A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (.inr (.inl live))) :
    ProfiledBankRightMacro A :=
  ⟨source.1, live,
    PairedProfiledRationalPolicy.reachable_of_allowed A
      (feasibleProfiledPolicy A source.1) source.2.2 hallowed⟩

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledBankStageLeftOfAllowed_bank
    (source : ProfiledBankRightMacro A)
    (live : (((A.State × A.State) × A.State) ×
      LeftInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inl source.2.1))
        (.inr (.inr live))) :
    (profiledBankStageLeftOfAllowed A source live hallowed).1 = source.1 := rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
@[simp] theorem profiledBankStageRightOfAllowed_bank
    (source : ProfiledBankLeftMacro A)
    (live : (((A.State × A.State) × A.State) ×
      RightInitialActionProfile
        (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)))
    (hallowed : PairedProfiledRationalPolicy.Allowed A
      (feasibleProfiledPolicy A source.1) (.inr (.inr source.2.1))
        (.inr (.inl live))) :
    (profiledBankStageRightOfAllowed A source live hallowed).1 = source.1 := rfl

end

end


end DetParityAutomaton

end DistributedSynthesis
