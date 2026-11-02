/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemInputFreeRootForest

/-!
# One rational transition table for a finite family of initial states

Pointwise rationalization is insufficient when several hidden contexts must
use one observation-based action table.  This file gives the correct generic
construction for the case in which all contexts are runs of the same
input-free parity tree automaton, differing only in their initial state.

First enlarge a direction by an irrelevant finite family index.  Below every
node the transition relation requires the complete successor assignment to
ignore that index.  Next glue one accepting run for every initial state below
a fresh guarded root.  One application of finite-direction rationalization to
the complete forest then produces a single rational transition table shared
by the whole family.

The theorem does not prove that model-specific hidden contexts have a common
legal action.  It isolates that as the nonemptiness premise for one common
automaton, and prevents the invalid order `rationalize each context, then try
to identify the selected transitions`.
-/

namespace DistributedSynthesis

universe i u w

namespace InputFreeRunParityTreeAutomaton

variable {Index : Type i} {Branch : Type u}

/-- Add a proof-tree family index to every direction, while requiring the
actual transition to depend only on the underlying direction. -/
def indexInsensitive
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch) :
    InputFreeRunParityTreeAutomaton.{max i u, w} (Index × Branch) where
  State := A.State
  stateFinite := A.stateFinite
  initial := A.initial
  delta state _ children :=
    ∃ next : Branch → A.State,
      A.delta state PUnit.unit next ∧
        ∀ index branch, children (index, branch) = next branch
  priority := A.priority

/-- Erase the irrelevant family index from a finite direction history. -/
def eraseIndexNode (node : TreeNode (Index × Branch)) : TreeNode Branch :=
  node.map Prod.snd

/-- Erase the family index from an infinite direction branch. -/
def eraseIndexBranch (branch : Nat → Index × Branch) : Nat → Branch :=
  fun n ↦ (branch n).2

theorem eraseIndexNode_branchNode
    (branch : Nat → Index × Branch) : ∀ n,
    eraseIndexNode (branchNode branch n) =
      branchNode (eraseIndexBranch branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl]
      unfold eraseIndexNode at ih ⊢
      simp only [List.map_append, List.map_cons, List.map_nil]
      rw [ih]
      rfl

/-- Lift one run by ignoring every family-index coordinate in its branch. -/
def indexInsensitiveRun
    (run : TreeNode Branch → A.State) :
    TreeNode (Index × Branch) → (indexInsensitive (Index := Index) A).State :=
  fun node ↦ run (eraseIndexNode node)

/-- An accepting run remains accepting after the direction alphabet is
enlarged by an index that its transition table is required to ignore. -/
theorem indexInsensitiveRun_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : A.State)
    (run : TreeNode Branch → A.State)
    (hrun : (A.withInitial initial).IsAcceptingRun uniqueTree run) :
    ((indexInsensitive (Index := Index) A).withInitial initial)
      |>.IsAcceptingRun uniqueTree
        (indexInsensitiveRun (Index := Index) run) := by
  constructor
  · constructor
    · exact hrun.1.1
    · intro node
      let next : Branch → A.State :=
        fun branch ↦ run (eraseIndexNode node ++ [branch])
      refine ⟨next, ?_, ?_⟩
      · simpa only [withInitial, uniqueTree] using
          hrun.1.2 (eraseIndexNode node)
      · intro index branch
        change run (eraseIndexNode (node ++ [(index, branch)])) =
          run (eraseIndexNode node ++ [branch])
        simp [eraseIndexNode]
  · intro branch
    have hparity := hrun.2 (eraseIndexBranch branch)
    change NatSeqMinEvenParity (fun n ↦
      A.priority (run (eraseIndexNode (branchNode branch n))))
    simpa only [eraseIndexNode_branchNode] using hparity

/-- At the fresh root, the first family-index coordinate selects the required
initial state.  The accompanying underlying direction is not consumed. -/
def finiteInitialFamilyRootAllowed
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (children : (Index × Branch) → A.State) : Prop :=
  ∀ index branch, children (index, branch) = initial index

/-- One common automaton for a finite family of initial states. -/
def finiteInitialFamily
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State) :
    InputFreeRunParityTreeAutomaton.{max i u, w} (Index × Branch) :=
  (indexInsensitive (Index := Index) A).rootGuarded
    (finiteInitialFamilyRootAllowed (A := A) initial)

/-- A family of runs of the original automaton, one per initial state, forms
one accepting forest of the common family automaton. -/
theorem finiteInitialFamily_nonemptyLanguage
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (runs : ∀ index, TreeNode Branch → A.State)
    (hruns : ∀ index,
      (A.withInitial (initial index)).IsAcceptingRun uniqueTree (runs index)) :
    (finiteInitialFamily A initial).NonemptyLanguage := by
  let lifted := indexInsensitive (Index := Index) A
  let rootAllowed := finiteInitialFamilyRootAllowed (A := A) initial
  let familyInitial : Index × Branch → lifted.State :=
    fun direction ↦ initial direction.1
  let forest : Index × Branch → TreeNode (Index × Branch) → lifted.State :=
    fun direction node ↦
      indexInsensitiveRun (Index := Index) (runs direction.1) node
  refine ⟨rootGuardedForestRun lifted rootAllowed forest, ?_⟩
  apply rootGuardedForest_isAcceptingRun lifted rootAllowed familyInitial
    forest
  · intro direction
    exact hruns direction.1 |>.1.1
  · intro direction
    exact indexInsensitiveRun_isAcceptingRun
      (Index := Index) A (initial direction.1) (runs direction.1)
        (hruns direction.1)
  · intro index branch
    rfl

/-- The finite family is rationalized only after all of its accepting runs
have been glued into one observation-uniform automaton. -/
theorem finiteInitialFamily_hasRationalRun
    [Fintype Index] [Fintype Branch]
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (hfamily : ∀ index,
      (A.withInitial (initial index)).NonemptyLanguage) :
    (finiteInitialFamily A initial).HasRationalRun := by
  classical
  choose runs hruns using hfamily
  exact InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite
    (finiteInitialFamily A initial)
      (finiteInitialFamily_nonemptyLanguage A initial runs hruns)

/-- Type-valued extraction of the one rational transition table obtained for
the complete finite family. -/
theorem nonempty_finiteInitialFamily_rationalTransitionPolicy
    [Fintype Index] [Fintype Branch]
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (hfamily : ∀ index,
      (A.withInitial (initial index)).NonemptyLanguage) :
    Nonempty ((finiteInitialFamily A initial).RationalTransitionPolicy) :=
  nonempty_rationalTransitionPolicy_of_hasRationalRun
    (finiteInitialFamily A initial)
    (finiteInitialFamily_hasRationalRun A initial hfamily)

/-- The extracted table cannot recover the proof-only family index below the
fresh root.  This is the formal observation-uniformity guarantee supplied by
the construction. -/
theorem finiteInitialFamily_policy_successor_index_independent
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (policy : (finiteInitialFamily A initial).RationalTransitionPolicy)
    (node : TreeNode (Index × Branch))
    (hfresh : (policy.run node).1 = false)
    (left right : Index) (branch : Branch) :
    policy.successor (policy.run node) (left, branch) =
      policy.successor (policy.run node) (right, branch) := by
  have hstate : policy.run node = (false, (policy.run node).2) := by
    apply Prod.ext
    · exact hfresh
    · rfl
  have hlegal := policy.legal_at node
  rw [hstate] at hlegal
  change ∃ next : Index × Branch → A.State,
      (∃ underlying : Branch → A.State,
        A.delta (policy.run node).2 PUnit.unit underlying ∧
          ∀ index branch, next (index, branch) = underlying branch) ∧
        policy.successor (false, (policy.run node).2) =
          fun direction ↦ (false, next direction) at hlegal
  rcases hlegal with
    ⟨next, ⟨underlying, _hdelta, hignore⟩, hchildren⟩
  rw [hstate, hchildren]
  apply Prod.ext
  · rfl
  · exact (hignore left branch).trans (hignore right branch).symm

/-- Every state reached strictly below the root satisfies the preceding
index-independence law. -/
theorem finiteInitialFamily_policy_successor_index_independent_belowRoot
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (initial : Index → A.State)
    (policy : (finiteInitialFamily A initial).RationalTransitionPolicy)
    (first : Index × Branch) (node : TreeNode (Index × Branch))
    (left right : Index) (branch : Branch) :
    policy.successor (policy.run ([first] ++ node)) (left, branch) =
      policy.successor (policy.run ([first] ++ node)) (right, branch) := by
  apply finiteInitialFamily_policy_successor_index_independent A initial policy
  exact rootGuardedPolicy_fresh_false
    (indexInsensitive (Index := Index) A)
    (finiteInitialFamilyRootAllowed A initial) policy first node

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
