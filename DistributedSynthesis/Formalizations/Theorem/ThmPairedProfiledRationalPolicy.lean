/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRationalTree

/-!
# Finite transition policies of profiled paired-entry runs

This is the profiled analogue of `ThmPairedEntryRationalPolicy`.  A rational
run supplies a finite successor table.  At a reachable live state its legal
transition yields one block lambda whose initial action profile is the one
stored in the state and whose every close lands in an allowed profiled child.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

namespace PairedProfiledRationalPolicy

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

/-- A profiled state occurs in the rational run. -/
def Reachable (state : PairedProfiledTreeState A) : Prop :=
  ∃ node, policy.run node = state

/-- Finite successor relation induced by the profiled policy. -/
def Allowed (source target : PairedProfiledTreeState A) : Prop :=
  ∃ direction, policy.successor source direction = target

theorem reachable_of_allowed
    {source target : PairedProfiledTreeState A}
    (hsource : Reachable A policy source)
    (hallowed : Allowed A policy source target) :
    Reachable A policy target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hallowed with ⟨direction, hdirection⟩
  refine ⟨node ++ [direction], ?_⟩
  rw [← policy.successor_at node direction, hnode, hdirection]

/-- Arbitrary mixing of allowed profiled edges remains accepting. -/
theorem accepts_of_allowed_path
    (states : Nat → PairedProfiledTreeState A)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n, Allowed A policy (states n) (states (n + 1))) :
    NatSeqMinEvenParity (fun n => pairedProfiledEntryPriority A (states n)) := by
  classical
  choose branch hbranch using hstep
  have hstates : ∀ n, states n = policy.run (branchNode branch n) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [branchNode, ← policy.successor_at (branchNode branch n) (branch n),
          ← ih]
        exact (hbranch n).symm
  have haccepts := policy.accepts.2 branch
  convert haccepts using 1
  funext n
  rw [hstates n]
  rfl

/-- A legal reachable process-one transition exposes its lambda, stored
initial profile, and complete profiled successor table. -/
theorem exists_processOneLambda
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hreachable : Reachable A policy
      (.inr (.inl ((code, minimum), profile)))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedRightForeverAccepts A code lambda ∧
        rightInitialFirstProfile lambda = profile ∧
        ∀ direction,
          policy.successor (.inr (.inl ((code, minimum), profile))) direction =
            match direction with
            | .fromOne row past move =>
                pairedProfiledOneChild A code lambda row past move
            | .fromTwo _ _ _ => .inl PUnit.unit := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  exact hlegal

/-- Process-two mirror. -/
theorem exists_processTwoLambda
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hreachable : Reachable A policy
      (.inr (.inr ((code, minimum), profile)))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedLeftForeverAccepts A code lambda ∧
        leftInitialFirstProfile lambda = profile ∧
        ∀ direction,
          policy.successor (.inr (.inr ((code, minimum), profile))) direction =
            match direction with
            | .fromOne _ _ _ => .inl PUnit.unit
            | .fromTwo row past move =>
                pairedProfiledTwoChild A code lambda row past move := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  exact hlegal

/-- Every close of a process-one lambda is an allowed profiled edge. -/
def ProcessOneCloseSafe
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    Allowed A policy (.inr (.inl ((code, minimum), profile)))
      (pairedProfiledOneChild A code lambda row past move)

/-- Process-two mirror. -/
def ProcessTwoCloseSafe
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    Allowed A policy (.inr (.inr ((code, minimum), profile)))
      (pairedProfiledTwoChild A code lambda row past move)

theorem exists_processOneLambda_closeSafe
    (code : A.State × A.State) (minimum : A.State)
    (profile : RightInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (hreachable : Reachable A policy
      (.inr (.inl ((code, minimum), profile)))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedRightForeverAccepts A code lambda ∧
        rightInitialFirstProfile lambda = profile ∧
        ProcessOneCloseSafe A policy code minimum profile lambda := by
  rcases exists_processOneLambda A policy code minimum profile hreachable with
    ⟨lambda, hforever, hprofile, htransition⟩
  refine ⟨lambda, hforever, hprofile, ?_⟩
  intro row past move
  refine ⟨PairedEntryDirection.fromOne row past move, ?_⟩
  exact htransition (.fromOne row past move)

theorem exists_processTwoLambda_closeSafe
    (code : A.State × A.State) (minimum : A.State)
    (profile : LeftInitialActionProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (hreachable : Reachable A policy
      (.inr (.inr ((code, minimum), profile)))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedLeftForeverAccepts A code lambda ∧
        leftInitialFirstProfile lambda = profile ∧
        ProcessTwoCloseSafe A policy code minimum profile lambda := by
  rcases exists_processTwoLambda A policy code minimum profile hreachable with
    ⟨lambda, hforever, hprofile, htransition⟩
  refine ⟨lambda, hforever, hprofile, ?_⟩
  intro row past move
  refine ⟨PairedEntryDirection.fromTwo row past move, ?_⟩
  exact htransition (.fromTwo row past move)

end PairedProfiledRationalPolicy

end DetParityAutomaton

end DistributedSynthesis
