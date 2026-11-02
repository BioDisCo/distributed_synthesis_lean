/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedEntryRootGlue

/-!
# Transition policies of rational paired-entry runs

This is the first extraction layer after rationalization.  A rational run
induces one successor table indexed only by the finite paired automaton state.
At every reachable live state, legality of that table supplies exactly one
paired lambda: one blind block strategy shared by both pending variants and
one informed fragment for each visible variant.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

namespace PairedRationalPolicy

/-- A finite paired state occurs in the rational run. -/
def Reachable
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (state : PairedEntryTreeState A) : Prop :=
  ∃ node, policy.run node = state

/-- Finite successor relation induced by the rational transition table.  It
forgets which (possibly very long) block direction produced the successor and
retains only the pair of finite states. -/
def Allowed
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (source target : PairedEntryTreeState A) : Prop :=
  ∃ direction, policy.successor source direction = target

/-- Allowed successors of reachable states are reachable. -/
theorem reachable_of_allowed
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    {source target : PairedEntryTreeState A}
    (hsource : Reachable A policy source)
    (hallowed : Allowed A policy source target) :
    Reachable A policy target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hallowed with ⟨direction, hdirection⟩
  refine ⟨node ++ [direction], ?_⟩
  rw [← policy.successor_at node direction, hnode, hdirection]

/-- Crucial finite-image closure: arbitrary mixing of allowed finite-state
edges is still accepting.  Every chosen edge has some original direction;
choosing one witness at each step reconstructs a branch of the accepting
rational run.  Thus later block regularization need preserve only `Allowed`,
not the original possibly nonregular direction-to-successor function. -/
theorem accepts_of_allowed_path
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (states : Nat -> PairedEntryTreeState A)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n, Allowed A policy (states n) (states (n + 1))) :
    NatSeqMinEvenParity (fun n => pairedEntryPriority A (states n)) := by
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

/-- At a reachable process-one state, the rational successor table is
realized by one shared process-one lambda satisfying the infinite-block
condition. -/
theorem exists_processOneLambda
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : Reachable A policy
      (Sum.inr (Sum.inl (code, minimum)))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedRightForeverAccepts A code lambda ∧
        ∀ direction,
          policy.successor (Sum.inr (Sum.inl (code, minimum))) direction =
            match direction with
            | .fromOne row past move =>
                pairedOneChild A code lambda row past move
            | .fromTwo _ _ _ => Sum.inl PUnit.unit := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  exact hlegal

/-- Mirror extraction at a reachable process-two state. -/
theorem exists_processTwoLambda
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : Reachable A policy
      (Sum.inr (Sum.inr (code, minimum)))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedLeftForeverAccepts A code lambda ∧
        ∀ direction,
          policy.successor (Sum.inr (Sum.inr (code, minimum))) direction =
            match direction with
            | .fromOne _ _ _ => Sum.inl PUnit.unit
            | .fromTwo row past move =>
                pairedTwoChild A code lambda row past move := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  exact hlegal

/-- Every possible closing successor of a process-one block stays inside the
finite allowed graph of the rational policy. -/
def ProcessOneCloseSafe
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (lambda : ProcOnePairedRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    Allowed A policy (Sum.inr (Sum.inl (code, minimum)))
      (pairedOneChild A code lambda row past move)

/-- Mirror closing-safety predicate. -/
def ProcessTwoCloseSafe
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (lambda : ProcTwoPairedLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)) : Prop :=
  ∀ row past move,
    Allowed A policy (Sum.inr (Sum.inr (code, minimum)))
      (pairedTwoChild A code lambda row past move)

/-- The lambda extracted from a legal rational transition is simultaneously
T2-winning and closing-safe. -/
theorem exists_processOneLambda_closeSafe
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : Reachable A policy
      (Sum.inr (Sum.inl (code, minimum)))) :
    ∃ lambda : ProcOnePairedRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedRightForeverAccepts A code lambda ∧
        ProcessOneCloseSafe A policy code minimum lambda := by
  rcases exists_processOneLambda A policy code minimum hreachable with
    ⟨lambda, hforever, htransition⟩
  refine ⟨lambda, hforever, ?_⟩
  intro row past move
  refine ⟨PairedEntryDirection.fromOne row past move, ?_⟩
  exact htransition (.fromOne row past move)

/-- Mirror T2-and-safety extraction. -/
theorem exists_processTwoLambda_closeSafe
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (code : A.State × A.State) (minimum : A.State)
    (hreachable : Reachable A policy
      (Sum.inr (Sum.inr (code, minimum)))) :
    ∃ lambda : ProcTwoPairedLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      PairedLeftForeverAccepts A code lambda ∧
        ProcessTwoCloseSafe A policy code minimum lambda := by
  rcases exists_processTwoLambda A policy code minimum hreachable with
    ⟨lambda, hforever, htransition⟩
  refine ⟨lambda, hforever, ?_⟩
  intro row past move
  refine ⟨PairedEntryDirection.fromTwo row past move, ?_⟩
  exact htransition (.fromTwo row past move)

/-- The extracted successor table agrees at every occurrence of a reachable
state; this is the right-congruence needed by the later finite controllers. -/
theorem successor_eq_at_occurrence
    {initialState : PairedEntryTreeState A}
    (policy :
      (pairedEntryRunAutomaton A initialState).RationalTransitionPolicy)
    (node : TreeNode
      (PairedEntryDirection (In₁ := In₁) (In₂ := In₂))) :
    ∀ direction,
      policy.successor (policy.run node) direction =
        policy.run (node ++ [direction]) :=
  policy.successor_at node

end PairedRationalPolicy

end DetParityAutomaton

end DistributedSynthesis
