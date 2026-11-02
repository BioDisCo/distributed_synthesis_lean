/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Finite safety products for input-free parity tree automata

A finite safety component can be carried through the input-free
rationalization without changing the parity objective.  The product below
conjoins the two transition relations and reads priorities only from the
original parity state.  Consequently an accepting product run projects to an
accepting original run, while any accepting original run paired with a legal
safety run is accepting in the product.
-/

namespace DistributedSynthesis

universe u w z

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u} {Safety : Type z}

/-- A tree-indexed run of a safety transition system. -/
def IsSafetyRun
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → Safety) : Prop :=
  run [] = initialSafety ∧
    ∀ node : TreeNode Branch,
      safetyDelta (run node) (fun branch => run (node ++ [branch]))

/-- Conjoin an input-free parity automaton with a finite safety transition
system.  The safety state affects legality but not priority. -/
def safetyProduct
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop) :
    InputFreeRunParityTreeAutomaton.{u, max w z} Branch where
  State := A.State × Safety
  stateFinite := inferInstance
  initial := (A.initial, initialSafety)
  delta state _ children :=
    A.delta state.1 PUnit.unit (fun branch => (children branch).1) ∧
      safetyDelta state.2 (fun branch => (children branch).2)
  priority state := A.priority state.1

/-- Forget the safety coordinate of a product run. -/
def safetyProductProjectRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch → A.State × Safety) :
    TreeNode Branch → A.State :=
  fun node => (run node).1

/-- Pair an automaton run with a safety run. -/
def safetyProductPairRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety) :
    TreeNode Branch → A.State × Safety :=
  fun node => (run node, safetyRun node)

@[simp] theorem safetyProductProjectRun_apply
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch → A.State × Safety)
    (node : TreeNode Branch) :
    safetyProductProjectRun A run node = (run node).1 :=
  rfl

@[simp] theorem safetyProductPairRun_apply
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety)
    (node : TreeNode Branch) :
    safetyProductPairRun A run safetyRun node = (run node, safetyRun node) :=
  rfl

/-- Every accepting product run projects to an accepting run of the original
parity automaton. -/
theorem safetyProduct_project_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → (A.safetyProduct initialSafety safetyDelta).State)
    (hrun : (A.safetyProduct initialSafety safetyDelta).IsAcceptingRun
      uniqueTree run) :
    A.IsAcceptingRun uniqueTree (safetyProductProjectRun A run) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact congrArg Prod.fst hrun.1.1
  · intro node
    exact (hrun.1.2 node).1
  · intro branch
    exact hrun.2 branch

/-- The safety coordinate of every product run is itself a legal safety run.
This companion projection is useful when the finite augmentation must be
recovered after rationalization. -/
theorem safetyProduct_safety_isSafetyRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → (A.safetyProduct initialSafety safetyDelta).State)
    (hrun : (A.safetyProduct initialSafety safetyDelta).IsRun uniqueTree run) :
    IsSafetyRun initialSafety safetyDelta (fun node => (run node).2) := by
  refine ⟨congrArg Prod.snd hrun.1, ?_⟩
  intro node
  exact (hrun.2 node).2

/-- Pairing an accepting automaton run with any compatible safety run gives
an accepting product run. -/
theorem safetyProduct_pair_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hsafety : IsSafetyRun initialSafety safetyDelta safetyRun) :
    (A.safetyProduct initialSafety safetyDelta).IsAcceptingRun uniqueTree
      (safetyProductPairRun A run safetyRun) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact Prod.ext hrun.1.1 hsafety.1
  · intro node
    exact ⟨hrun.1.2 node, hsafety.2 node⟩
  · intro branch
    exact hrun.2 branch

/-! ## One-shot rationalization of a parity/safety product -/

/-- An accepting parity run and a compatible safety run give a nonempty
language for the *single* product automaton.  This is the correct order for
applications in which rationalization must retain a finite locality or
family-table invariant: form the product first, and rationalize only once. -/
theorem safetyProduct_nonemptyLanguage_of_runs
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hsafety : IsSafetyRun initialSafety safetyDelta safetyRun) :
    (A.safetyProduct initialSafety safetyDelta).NonemptyLanguage := by
  exact ⟨safetyProductPairRun A run safetyRun,
    safetyProduct_pair_isAcceptingRun A initialSafety safetyDelta run
      safetyRun hrun hsafety⟩

/-- Apply the named rational-run basis once, after the finite safety
coordinate has been coupled to the accepting parity run.  No policy is
selected separately at a safety state or hidden family member. -/
theorem safetyProduct_hasRationalRun_of_runs
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hsafety : IsSafetyRun initialSafety safetyDelta safetyRun)
    (basis : (A.safetyProduct initialSafety safetyDelta).RationalRunBasis) :
    (A.safetyProduct initialSafety safetyDelta).HasRationalRun := by
  exact basis (safetyProduct_nonemptyLanguage_of_runs A initialSafety
    safetyDelta run safetyRun hrun hsafety)

/-- Executable finite-policy endpoint of the same one-shot construction. -/
theorem nonempty_safetyProduct_rationalPolicy_of_runs
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Safety]
    (initialSafety : Safety)
    (safetyDelta : Safety → (Branch → Safety) → Prop)
    (run : TreeNode Branch → A.State)
    (safetyRun : TreeNode Branch → Safety)
    (hrun : A.IsAcceptingRun uniqueTree run)
    (hsafety : IsSafetyRun initialSafety safetyDelta safetyRun)
    (basis : (A.safetyProduct initialSafety safetyDelta).RationalRunBasis) :
    Nonempty
      ((A.safetyProduct initialSafety safetyDelta).RationalTransitionPolicy) := by
  apply nonempty_rationalTransitionPolicy_of_hasRationalRun
    (A.safetyProduct initialSafety safetyDelta)
  exact safetyProduct_hasRationalRun_of_runs A initialSafety safetyDelta run
    safetyRun hrun hsafety basis

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
