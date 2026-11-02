/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Order.KonigLemma
import DistributedSynthesis.Library.Automata.Compilers

set_option linter.unusedVariables false

/-!
# Piterman compact-tree transitions

This file contains the compact-tree transition machinery for Piterman's construction from
``From Nondeterministic Büchi and Streett Automata to Deterministic Parity
Automata'' (LMCS 2007, arXiv:0705.2205).

It follows Section 3.2, the NBW-to-DPW construction by compact Safra trees with
dynamic node names. All six stages and their invariants are included. The
language-correctness proof imports this layer through `PitermanAllocation`.
-/

namespace DistributedSynthesis

universe u v

namespace NondetBuchiAutomaton
namespace Piterman

variable {Alphabet : Type u}

/-- Piterman's underlying compact-Safra nodes `V = [2n]`, zero-based.

The paper keeps nodes as entities and lets their dynamic names change during
the transition.  A temporary transition stage may use the second half of this
range before the final compaction step.
-/
abbrev Node (A : NondetBuchiAutomaton.{u, v} Alphabet) : Type :=
  Fin (2 * Fintype.card A.State)

/-- Dynamic names in `[n + 1]`, zero-based.  The last value is the sentinel. -/
abbrev Name (A : NondetBuchiAutomaton.{u, v} Alphabet) : Type :=
  Fin (Fintype.card A.State + 1)

/-- Temporarily assigned names in `[2n]`, zero-based. -/
abbrev TempName (A : NondetBuchiAutomaton.{u, v} Alphabet) : Type :=
  Node A

/-- The root node/name, corresponding to paper name `1` in zero-based form. -/
def root (A : NondetBuchiAutomaton.{u, v} Alphabet) :
    Node A := by
  refine ⟨0, ?_⟩
  have hcard_pos : 0 < Fintype.card A.State :=
    Fintype.card_pos_iff.mpr ⟨A.initial⟩
  omega

/-- Sentinel value `n + 1` from the paper, in zero-based form. -/
def sentinel (A : NondetBuchiAutomaton.{u, v} Alphabet) : Name A :=
  ⟨Fintype.card A.State, Nat.lt_succ_self _⟩

/-- Zero-based dynamic name `1` from the paper. -/
def rootName (A : NondetBuchiAutomaton.{u, v} Alphabet) : Name A :=
  ⟨0, Nat.succ_pos _⟩

/-- Raw compact Safra-tree data for the NBW construction.

The well-formedness predicate below imposes the paper invariants: root,
parenthood by smaller dynamic names, disjoint siblings, and the proper
descendant-label condition.
-/
structure CompactTreeData
    (A : NondetBuchiAutomaton.{u, v} Alphabet) where
  active : Node A -> Bool
  name : Node A -> TempName A
  parent : Node A -> Node A
  label : Node A -> Finset A.State
  e : Name A
  f : Name A

namespace CompactTreeData

variable (A : NondetBuchiAutomaton.{u, v} Alphabet)

noncomputable instance compactTreeDataFintype [DecidableEq A.State] :
    Fintype (CompactTreeData A) := by
  classical
  let Repr :=
    (((((Node A -> Bool) × (Node A -> TempName A)) ×
      (Node A -> Node A)) × (Node A -> Finset A.State)) ×
        Name A) × Name A
  exact Fintype.ofEquiv Repr
    { toFun := fun data =>
        { active := data.1.1.1.1.1
          name := data.1.1.1.1.2
          parent := data.1.1.1.2
          label := data.1.1.2
          e := data.1.2
          f := data.2 }
      invFun := fun tree =>
        (((((tree.active, tree.name), tree.parent), tree.label), tree.e), tree.f)
      left_inv := by
        intro data
        rcases data with ⟨⟨⟨⟨⟨active, name⟩, parent⟩, label⟩, e⟩, f⟩
        rfl
      right_inv := by
        intro tree
        cases tree
        rfl }

/-- Active children of a compact Safra node. -/
def children (tree : CompactTreeData A) (node : Node A) : Finset (Node A) :=
  Finset.univ.filter
    (fun child => tree.active child = true ∧ child ≠ root A ∧ tree.parent child = node)

/-- Union of labels of the active children of a node. -/
def childLabelUnion [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) : Finset A.State :=
  (tree.children A node).biUnion tree.label

theorem childLabelUnion_subset_label [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node, tree.childLabelUnion A node ⊆ tree.label node := by
  intro node state hstate
  rw [childLabelUnion] at hstate
  rw [Finset.mem_biUnion] at hstate
  rcases hstate with ⟨child, hchild, hstateChild⟩
  exact hchildSubset node child hchild hstateChild

theorem exists_private_state_of_childLabelUnion_ssubset [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hproper : tree.childLabelUnion A node ⊂ tree.label node) :
    ∃ state, state ∈ tree.label node ∧
      state ∉ tree.childLabelUnion A node := by
  by_contra hnone
  have hlabel_subset : tree.label node ⊆ tree.childLabelUnion A node := by
    intro state hstate
    by_contra hnot
    exact hnone ⟨state, hstate, hnot⟩
  exact hproper.2 hlabel_subset

theorem not_mem_child_label_of_not_mem_childLabelUnion
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node child : Node A} {state : A.State}
    (hnotUnion : state ∉ tree.childLabelUnion A node)
    (hchild : child ∈ tree.children A node) :
    state ∉ tree.label child := by
  intro hstateChild
  exact hnotUnion (by
    rw [childLabelUnion, Finset.mem_biUnion]
    exact ⟨child, hchild, hstateChild⟩)

noncomputable def privateStateOf [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    (node : Node A)
    (hactive : tree.active node = true) : A.State :=
  Classical.choose
    (exists_private_state_of_childLabelUnion_ssubset A tree
      (hproper node hactive))

theorem privateStateOf_mem_label [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    {node : Node A}
    (hactive : tree.active node = true) :
    tree.privateStateOf A hproper node hactive ∈ tree.label node :=
  (Classical.choose_spec
    (exists_private_state_of_childLabelUnion_ssubset A tree
      (hproper node hactive))).1

theorem privateStateOf_not_mem_childLabelUnion [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    {node : Node A}
    (hactive : tree.active node = true) :
    tree.privateStateOf A hproper node hactive ∉
      tree.childLabelUnion A node :=
  (Classical.choose_spec
    (exists_private_state_of_childLabelUnion_ssubset A tree
      (hproper node hactive))).2

/-- Proper compact-Safra-tree invariant for the raw data. -/
def WellFormed [DecidableEq A.State] (tree : CompactTreeData A) : Prop :=
  tree.active (root A) ∧
    (tree.name (root A)).val = (rootName A).val ∧
    tree.parent (root A) = root A ∧
    (∀ node, tree.active node -> node ≠ root A ->
      tree.active (tree.parent node) ∧
        (tree.name (tree.parent node)).val < (tree.name node).val) ∧
    (∀ node, tree.active node = false -> tree.label node = ∅) ∧
    (∀ node, tree.active node ->
      (tree.name node).val < Fintype.card A.State) ∧
    (∀ left right, tree.active left -> tree.active right ->
      tree.name left = tree.name right -> left = right) ∧
    (∀ k : Nat, k < Fintype.card A.State ->
      (∃ node, tree.active node ∧ (tree.name node).val = k) ->
        ∀ j : Nat, j < k ->
          ∃ node, tree.active node ∧ (tree.name node).val = j) ∧
    (∀ node, tree.active node ->
      tree.childLabelUnion A node ⊂ tree.label node) ∧
    (∀ node child, child ∈ tree.children A node ->
      tree.label child ⊆ tree.label node) ∧
    (∀ node left right,
      left ∈ tree.children A node ->
      right ∈ tree.children A node ->
      left ≠ right ->
        Disjoint (tree.label left) (tree.label right))

/-- The paper's initial compact Safra tree: one root labeled by the NBW initial state. -/
def initial [DecidableEq A.State] : CompactTreeData A where
  active node := decide (node = root A)
  name node := if node = root A then ⟨0, by
      have hcard_pos : 0 < Fintype.card A.State :=
        Fintype.card_pos_iff.mpr ⟨A.initial⟩
      omega⟩ else ⟨Fintype.card A.State, by
      have hcard_pos : 0 < Fintype.card A.State :=
        Fintype.card_pos_iff.mpr ⟨A.initial⟩
      omega⟩
  parent _ := root A
  label node := if node = root A then {A.initial} else ∅
  e := sentinel A
  f := rootName A

theorem initial_active_iff [DecidableEq A.State] {node : Node A} :
    (initial A).active node = true ↔ node = root A := by
  simp [initial]

theorem initial_inactive_label [DecidableEq A.State] {node : Node A}
    (hnode : (initial A).active node = false) :
    (initial A).label node = ∅ := by
  rw [initial]
  have hne : node ≠ root A := by
    intro hroot
    have hactive : (initial A).active node = true := by
      exact (initial_active_iff A).mpr hroot
    simp [hactive] at hnode
  simp [hne]

theorem initial_children_empty [DecidableEq A.State] (node : Node A) :
    (initial A).children A node = ∅ := by
  classical
  ext child
  constructor
  · intro hchild
    rw [children, Finset.mem_filter] at hchild
    have hroot : child = root A := (initial_active_iff A).mp hchild.2.1
    exact (hchild.2.2.1 hroot).elim
  · intro hchild
    simp at hchild

theorem initial_childLabelUnion_empty [DecidableEq A.State] (node : Node A) :
    (initial A).childLabelUnion A node = ∅ := by
  simp [childLabelUnion, initial_children_empty A node]

@[simp]
theorem initial_root_label [DecidableEq A.State] :
    (initial A).label (root A) = {A.initial} := by
  simp [initial]

@[simp]
theorem mem_initial_root_label [DecidableEq A.State] {state : A.State} :
    state ∈ (initial A).label (root A) ↔ state = A.initial := by
  simp

theorem initial_wellFormed [DecidableEq A.State] :
    (initial A).WellFormed A := by
  classical
  have hcard_pos : 0 < Fintype.card A.State :=
    Fintype.card_pos_iff.mpr ⟨A.initial⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [initial]
  · simp [initial, rootName]
  · simp [initial]
  · intro node hactive hnot_root
    have hroot : node = root A := (initial_active_iff A).mp hactive
    exact (hnot_root hroot).elim
  · intro node hactive
    exact initial_inactive_label A hactive
  · intro node hactive
    have hroot : node = root A := (initial_active_iff A).mp hactive
    simp [initial, hroot]
    omega
  · intro left right hleft hright _hname
    have hleft_root : left = root A := (initial_active_iff A).mp hleft
    have hright_root : right = root A := (initial_active_iff A).mp hright
    exact hleft_root.trans hright_root.symm
  · intro k hk hexists j hj
    rcases hexists with ⟨node, hactive, hname⟩
    have hroot : node = root A := (initial_active_iff A).mp hactive
    have hk_zero : k = 0 := by
      simpa [initial, hroot, rootName] using hname.symm
    omega
  · intro node hactive
    have hroot : node = root A := (initial_active_iff A).mp hactive
    rw [initial_childLabelUnion_empty A node]
    rw [initial]
    simp [hroot]
  · intro node child hchild
    rw [initial_children_empty A node] at hchild
    simp at hchild
  · intro node left right hleft _hright _hne
    rw [initial_children_empty A node] at hleft
    simp at hleft

/-- One-step image of a finite state set under the NBW transition relation. -/
noncomputable def stepImage [DecidableEq A.State]
    (letter : Alphabet) (states : Finset A.State) : Finset A.State := by
  classical
  exact
    Finset.univ.filter
      (fun next => ∃ state, state ∈ states ∧ A.step state letter next)

theorem mem_stepImage [DecidableEq A.State]
    {letter : Alphabet} {states : Finset A.State} {next : A.State} :
    next ∈ stepImage A letter states ↔
      ∃ state, state ∈ states ∧ A.step state letter next := by
  simp [stepImage]

/-- Finite-prefix reachability in an NBW after reading `n` letters of `word`. -/
def ReachableAfter
    (start : A.State) (word : OmegaWord Alphabet) :
    Nat -> A.State -> Prop
  | 0, state => state = start
  | n + 1, state =>
      ∃ prev, ReachableAfter start word n prev ∧
        A.step prev (word n) state

/-- A concrete finite NBW prefix witnessing reachability after `n` letters. -/
def ReachablePrefix
    (start : A.State) (word : OmegaWord Alphabet)
    (n : Nat) (target : A.State) : Prop :=
  ∃ path : Nat -> A.State,
    path 0 = start ∧
      path n = target ∧
        ∀ i : Nat, i < n -> A.step (path i) (word i) (path (i + 1))

/-- A concrete NBW run segment over `word[startTime .. startTime+length-1]`. -/
def Segment
    (word : OmegaWord Alphabet) (startTime length : Nat)
    (source target : A.State) : Prop :=
  ∃ path : Nat -> A.State,
    path 0 = source ∧
      path length = target ∧
        ∀ i : Nat, i < length ->
          A.step (path i) (word (startTime + i)) (path (i + 1))

/-- A finite NBW segment that visits the Büchi accepting set. -/
def SegmentVisitsAccepting
    (word : OmegaWord Alphabet) (startTime length : Nat)
    (source target : A.State) : Prop :=
  ∃ path : Nat -> A.State,
    path 0 = source ∧
      path length = target ∧
        (∀ i : Nat, i < length ->
          A.step (path i) (word (startTime + i)) (path (i + 1))) ∧
        ∃ i : Nat, i ≤ length ∧ A.accepting (path i)

/-- A set-to-set finite NBW cover by ordinary run segments. -/
def SegmentCover
    (word : OmegaWord Alphabet) (startTime length : Nat)
    (sources targets : Finset A.State) : Prop :=
  ∀ target, target ∈ targets ->
    ∃ source, source ∈ sources ∧
      Segment A word startTime length source target

/-- A set-to-set finite NBW cover by segments that visit the Büchi set. -/
def SegmentVisitsAcceptingCover
    (word : OmegaWord Alphabet) (startTime length : Nat)
    (sources targets : Finset A.State) : Prop :=
  ∀ target, target ∈ targets ->
    ∃ source, source ∈ sources ∧
      SegmentVisitsAccepting A word startTime length source target

theorem self_le_of_strict_succ_cuts
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    ∀ k : Nat, k ≤ cuts k := by
  intro k
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      have hstep := hstrict k
      omega

theorem cofinal_of_strict_succ_cuts
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    ∀ n : Nat, ∃ k : Nat, n ≤ cuts k := by
  intro n
  exact ⟨n, self_le_of_strict_succ_cuts cuts hstrict n⟩

theorem exists_strict_cuts_of_frequently_at_or_after
    {P : Nat -> Prop}
    (hfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ P k) :
    ∃ cuts : Nat -> Nat,
      (∀ k : Nat, cuts k < cuts (k + 1)) ∧
        ∀ k : Nat, P (cuts k) := by
  classical
  let next : Nat -> Nat := fun n => Classical.choose (hfreq n)
  have hnext_ge : ∀ n : Nat, n ≤ next n := by
    intro n
    exact (Classical.choose_spec (hfreq n)).1
  have hnext_property : ∀ n : Nat, P (next n) := by
    intro n
    exact (Classical.choose_spec (hfreq n)).2
  let cuts : Nat -> Nat :=
    Nat.rec (next 0) (fun _ previous => next (previous + 1))
  refine ⟨cuts, ?_, ?_⟩
  · intro k
    change cuts k < next (cuts k + 1)
    have hge := hnext_ge (cuts k + 1)
    omega
  · intro k
    cases k with
    | zero =>
        change P (next 0)
        exact hnext_property 0
    | succ k =>
        change P (next (cuts k + 1))
        exact hnext_property (cuts k + 1)

theorem exists_strict_cuts_from_zero_of_frequently_at_or_after
    {P : Nat -> Prop}
    (hfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ P k) :
    ∃ cuts : Nat -> Nat,
      cuts 0 = 0 ∧
        (∀ k : Nat, cuts k < cuts (k + 1)) ∧
          ∀ k : Nat, P (cuts (k + 1)) := by
  classical
  let next : Nat -> Nat := fun n => Classical.choose (hfreq n)
  have hnext_ge : ∀ n : Nat, n ≤ next n := by
    intro n
    exact (Classical.choose_spec (hfreq n)).1
  have hnext_property : ∀ n : Nat, P (next n) := by
    intro n
    exact (Classical.choose_spec (hfreq n)).2
  let cuts : Nat -> Nat :=
    Nat.rec 0 (fun _ previous => next (previous + 1))
  refine ⟨cuts, rfl, ?_, ?_⟩
  · intro k
    change cuts k < next (cuts k + 1)
    have hge := hnext_ge (cuts k + 1)
    omega
  · intro k
    change P (next (cuts k + 1))
    exact hnext_property (cuts k + 1)

theorem frequently_left_or_right_of_frequently_or
    {P Q : Nat -> Prop}
    (hfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ (P k ∨ Q k)) :
    (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ P k) ∨
      (∀ n : Nat, ∃ k : Nat, n ≤ k ∧ Q k) := by
  classical
  by_cases hP : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ P k
  · exact Or.inl hP
  · right
    have heventuallyNotP : ∃ n0 : Nat, ∀ k : Nat, n0 ≤ k -> ¬ P k := by
      by_contra hnot
      apply hP
      intro n
      by_contra hn
      apply hnot
      refine ⟨n, ?_⟩
      intro k hk hPk
      exact hn ⟨k, hk, hPk⟩
    rcases heventuallyNotP with ⟨n0, hnotP⟩
    intro n
    rcases hfreq (n + n0) with ⟨k, hk, hcase⟩
    have hnk : n ≤ k := by omega
    have hn0k : n0 ≤ k := by omega
    rcases hcase with hPk | hQk
    · exact False.elim (hnotP k hn0k hPk)
    · exact ⟨k, hnk, hQk⟩

/--
Descent-dichotomy combinator: a per-cut split `P ∨ Q` along a strict cut sequence
yields a strict cut sequence on which one side holds throughout.  Pure cut
bookkeeping (`frequently_left_or_right_of_frequently_or` plus
`exists_strict_cuts_from_zero_of_frequently_at_or_after`); the intended use is to
turn the frontier survives/routed split into a single recurrent branch when
locating the stable green name.
-/
theorem exists_strict_cuts_dichotomy_of_strict_cuts
    {P Q : Nat -> Prop}
    (cuts : Nat -> Nat) (hstrict : ∀ i : Nat, cuts i < cuts (i + 1))
    (hsplit : ∀ i : Nat, P (cuts (i + 1)) ∨ Q (cuts (i + 1))) :
    (∃ c : Nat -> Nat,
        c 0 = 0 ∧ (∀ i : Nat, c i < c (i + 1)) ∧ ∀ i : Nat, P (c (i + 1))) ∨
      (∃ c : Nat -> Nat,
        c 0 = 0 ∧ (∀ i : Nat, c i < c (i + 1)) ∧ ∀ i : Nat, Q (c (i + 1))) := by
  have hPQfreq : ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ (P k ∨ Q k) := by
    intro n
    refine ⟨cuts (n + 1), ?_, hsplit n⟩
    have hle := self_le_of_strict_succ_cuts cuts hstrict (n + 1)
    omega
  rcases frequently_left_or_right_of_frequently_or hPQfreq with hP | hQ
  · exact Or.inl (exists_strict_cuts_from_zero_of_frequently_at_or_after hP)
  · exact Or.inr (exists_strict_cuts_from_zero_of_frequently_at_or_after hQ)

/--
An antitone `ℕ`-valued sequence is eventually constant.  This is the name
stabilization used in the descent (paper proof 4: "`M(v₁)` may decrease finitely
often until it is constant"); the stable value is the infimum of the range.
-/
theorem eventually_constant_of_antitone {g : Nat -> Nat} (hanti : Antitone g) :
    ∃ N a : Nat, ∀ k : Nat, N ≤ k -> g k = a := by
  classical
  have hne : (Set.range g).Nonempty := ⟨g 0, 0, rfl⟩
  obtain ⟨N, hN⟩ := Nat.sInf_mem hne
  refine ⟨N, sInf (Set.range g), fun k hk => ?_⟩
  have hle : g k ≤ g N := hanti hk
  have hge : sInf (Set.range g) ≤ g k := Nat.sInf_le ⟨k, rfl⟩
  rw [hN] at hle
  omega

/--
Bounded-descent termination (paper proof 4: "the number of active nodes is
bounded by `n`, so we can repeat the process only finitely often").  If from any
state satisfying `P` we may either accept or descend to a strictly larger state
still satisfying `P`, and all `P`-states are bounded, then the descent must
terminate in acceptance.  Pure strong induction on the remaining gap `bound - a`;
the construction supplies `P a = "the run settles at a node of constant name a"`,
the descent step, and the bound `Fintype.card A.State`.
-/
theorem bounded_descent_accepts
    {Accept : Prop} {P : Nat -> Prop}
    (bound : Nat)
    (hle : ∀ a : Nat, P a -> a ≤ bound)
    (step : ∀ a : Nat, P a -> Accept ∨ ∃ a' : Nat, a < a' ∧ P a') :
    ∀ a₀ : Nat, P a₀ -> Accept := by
  suffices h : ∀ m a₀ : Nat, bound - a₀ = m -> P a₀ -> Accept from
    fun a₀ hP => h _ a₀ rfl hP
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro a₀ hm hP
    rcases step a₀ hP with hacc | ⟨a', hlt, hP'⟩
    · exact hacc
    · have ha'le : a' ≤ bound := hle a' hP'
      have ha₀le : a₀ ≤ bound := hle a₀ hP
      exact ih (bound - a') (by omega) a' rfl hP'

theorem monotone_of_strict_succ_cuts
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    Monotone cuts := by
  intro i j hij
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hijlt
      · exact le_rfl
      · have hijle : i ≤ j := by omega
        exact Nat.le_trans (ih hijle) (Nat.le_of_lt (hstrict j))

theorem runFrom_accepts_of_accepting_positions_cofinal
    {start : A.State} {word : OmegaWord Alphabet}
    (run : A.RunFrom start word)
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (haccepting : ∀ k : Nat, A.accepting (run.path (cuts k))) :
    run.Accepts := by
  intro n
  rcases hcofinal n with ⟨k, hk⟩
  exact ⟨cuts k, hk, haccepting k⟩

theorem runFrom_accepts_of_accepting_blocks_cofinal
    {start : A.State} {word : OmegaWord Alphabet}
    (run : A.RunFrom start word)
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (hacceptingBlock :
      ∀ k : Nat,
        ∃ i : Nat, cuts k ≤ i ∧ i ≤ cuts (k + 1) ∧
          A.accepting (run.path i)) :
    run.Accepts := by
  intro n
  rcases hcofinal n with ⟨k, hnk⟩
  rcases hacceptingBlock k with ⟨i, hcut, _hiNext, haccepting⟩
  exact ⟨i, Nat.le_trans hnk hcut, haccepting⟩

theorem acceptsFrom_of_path_accepting_positions_cofinal
    {start : A.State} {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = start)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (haccepting : ∀ k : Nat, A.accepting (path (cuts k))) :
    A.AcceptsFrom start word := by
  let run : A.RunFrom start word :=
    { path := path
      initial_state := hstart
      step_valid := hstep }
  exact ⟨run,
    runFrom_accepts_of_accepting_positions_cofinal A run cuts hcofinal
      haccepting⟩

theorem acceptsFrom_of_path_accepting_blocks_cofinal
    {start : A.State} {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = start)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (hacceptingBlock :
      ∀ k : Nat,
        ∃ i : Nat, cuts k ≤ i ∧ i ≤ cuts (k + 1) ∧
          A.accepting (path i)) :
    A.AcceptsFrom start word := by
  let run : A.RunFrom start word :=
    { path := path
      initial_state := hstart
      step_valid := hstep }
  exact ⟨run,
    runFrom_accepts_of_accepting_blocks_cofinal A run cuts hcofinal
      hacceptingBlock⟩

theorem acceptsFrom_of_path_accepting_intervals_strict
    {start : A.State} {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = start)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hacceptingInterval :
      ∀ k : Nat,
        ∃ i : Nat, cuts k ≤ i ∧ i ≤ cuts (k + 1) ∧
          A.accepting (path i)) :
    A.AcceptsFrom start word :=
  acceptsFrom_of_path_accepting_blocks_cofinal A path hstart hstep cuts
    (cofinal_of_strict_succ_cuts cuts hstrict) hacceptingInterval

theorem accepts_of_path_accepting_positions_cofinal
    {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = A.initial)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (haccepting : ∀ k : Nat, A.accepting (path (cuts k))) :
    A.Accepts word :=
  acceptsFrom_of_path_accepting_positions_cofinal A path hstart hstep cuts
    hcofinal haccepting

theorem accepts_of_path_accepting_blocks_cofinal
    {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = A.initial)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hcofinal : ∀ n : Nat, ∃ k : Nat, n ≤ cuts k)
    (hacceptingBlock :
      ∀ k : Nat,
        ∃ i : Nat, cuts k ≤ i ∧ i ≤ cuts (k + 1) ∧
          A.accepting (path i)) :
    A.Accepts word :=
  acceptsFrom_of_path_accepting_blocks_cofinal A path hstart hstep cuts
    hcofinal hacceptingBlock

theorem accepts_of_path_accepting_intervals_strict
    {word : OmegaWord Alphabet}
    (path : Nat -> A.State)
    (hstart : path 0 = A.initial)
    (hstep : ∀ n : Nat, A.step (path n) (word n) (path (n + 1)))
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hacceptingInterval :
      ∀ k : Nat,
        ∃ i : Nat, cuts k ≤ i ∧ i ≤ cuts (k + 1) ∧
          A.accepting (path i)) :
    A.Accepts word :=
  acceptsFrom_of_path_accepting_intervals_strict A path hstart hstep cuts
    hstrict hacceptingInterval

theorem exists_runFrom_of_arbitrarily_long_prefixes
    {start : A.State} {word : OmegaWord Alphabet}
    (hprefix :
      ∀ n : Nat,
        ∃ pref : Fin (n + 1) -> A.State,
          pref 0 = start ∧
            ∀ (i : Nat) (hi : i < n),
              A.step
                (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
                (word i)
                (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) :
    ∃ run : A.RunFrom start word, True := by
  classical
  let Prefix : Nat -> Type v := fun n =>
    { pref : Fin (n + 1) -> A.State //
      pref 0 = start ∧
        ∀ (i : Nat) (hi : i < n),
          A.step
            (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
            (word i)
            (pref ⟨i + 1, Nat.succ_lt_succ hi⟩) }
  have hnonempty : ∀ n : Nat, Nonempty (Prefix n) := by
    intro n
    rcases hprefix n with ⟨pref, hstart, hvalid⟩
    exact ⟨⟨pref, hstart, hvalid⟩⟩
  letI : ∀ n : Nat, Nonempty (Prefix n) := hnonempty
  haveI : Finite (Prefix 0) := inferInstance
  let proj : {i j : Nat} -> i ≤ j -> Prefix j -> Prefix i :=
    fun {i j} hij pref =>
      ⟨fun idx => pref.1 (Fin.castLE (Nat.succ_le_succ hij) idx), by
        constructor
        · have hzero :
            Fin.castLE (Nat.succ_le_succ hij) (0 : Fin (i + 1)) =
              (0 : Fin (j + 1)) := by
              ext
              simp
          simpa [hzero] using pref.2.1
        · intro n hn
          have hnj : n < j := Nat.lt_of_lt_of_le hn hij
          have hstep := pref.2.2 n hnj
          simpa using hstep⟩
  have hproj_refl :
      ∀ ⦃i : Nat⦄ (pref : Prefix i), proj (le_refl i) pref = pref := by
    intro i pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hproj_trans :
      ∀ ⦃i j k : Nat⦄ (hij : i ≤ j) (hjk : j ≤ k)
        (pref : Prefix k),
        proj hij (proj hjk pref) = proj (Nat.le_trans hij hjk) pref := by
    intro i j k hij hjk pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hfin :
      ∀ (i : Nat) (pref : Prefix i),
        {next : Prefix (i + 1) | proj (Nat.le_add_right i 1) next = pref}.Finite := by
    intro i pref
    exact Set.toFinite _
  rcases exists_seq_forall_proj_of_forall_finite
      (α := Prefix) proj hproj_refl hproj_trans hfin with
    ⟨prefixes, hprefixes⟩
  refine ⟨?_, trivial⟩
  refine
    { path := fun n => (prefixes n).1 ⟨n, Nat.lt_succ_self n⟩
      initial_state := ?_
      step_valid := ?_ }
  · simpa using (prefixes 0).2.1
  · intro n
    have hvalid := (prefixes (n + 1)).2.2 n (Nat.lt_succ_self n)
    have hproj :
        proj (Nat.le_succ n) (prefixes (n + 1)) = prefixes n :=
      hprefixes (Nat.le_succ n)
    have hsource :
        (prefixes n).1 ⟨n, Nat.lt_succ_self n⟩ =
            (prefixes (n + 1)).1
            ⟨n, Nat.lt_trans (Nat.lt_succ_self n) (Nat.lt_succ_self (n + 1))⟩ := by
      have hval := congrArg Subtype.val hproj
      have happ := congrFun hval ⟨n, Nat.lt_succ_self n⟩
      simpa [proj] using happ.symm
    simpa [hsource] using hvalid

theorem acceptsFrom_of_arbitrarily_long_prefixes_with_accepting_cut_intervals
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ pref : Fin (cuts m + 1) -> A.State,
          pref 0 = start ∧
            (∀ (i : Nat) (hi : i < cuts m),
              A.step
                (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
                (word i)
                (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) ∧
            (∀ (k : Nat) (hk : k < m),
              ∃ hit : Nat,
                ∃ hhitLeft : cuts k ≤ hit,
                ∃ hhitRight : hit ≤ cuts (k + 1),
                  A.accepting
                    (pref
                      ⟨hit,
                        Nat.lt_succ_of_le
                          (Nat.le_trans hhitRight
                            (monotone_of_strict_succ_cuts cuts hstrict
                              (by omega : k + 1 ≤ m)))⟩))) :
    A.AcceptsFrom start word := by
  classical
  have hmono : Monotone cuts :=
    monotone_of_strict_succ_cuts cuts hstrict
  let Prefix : Nat -> Type v := fun m =>
    { pref : Fin (cuts m + 1) -> A.State //
      pref 0 = start ∧
        (∀ (i : Nat) (hi : i < cuts m),
          A.step
            (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
            (word i)
            (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) ∧
        (∀ (k : Nat) (hk : k < m),
          ∃ hit : Nat,
            ∃ hhitLeft : cuts k ≤ hit,
            ∃ hhitRight : hit ≤ cuts (k + 1),
              A.accepting
                (pref
                  ⟨hit,
                    Nat.lt_succ_of_le
                      (Nat.le_trans hhitRight
                        (hmono (by omega : k + 1 ≤ m)))⟩)) }
  have hnonempty : ∀ m : Nat, Nonempty (Prefix m) := by
    intro m
    rcases hprefix m with ⟨pref, hstart, hvalid, haccepting⟩
    exact ⟨⟨pref, hstart, hvalid, haccepting⟩⟩
  letI : ∀ m : Nat, Nonempty (Prefix m) := hnonempty
  haveI : Finite (Prefix 0) := inferInstance
  let proj : {i j : Nat} -> i ≤ j -> Prefix j -> Prefix i :=
    fun {i j} hij pref =>
      ⟨fun idx => pref.1 (Fin.castLE (Nat.succ_le_succ (hmono hij)) idx), by
        constructor
        · have hzero :
            Fin.castLE (Nat.succ_le_succ (hmono hij)) (0 : Fin (cuts i + 1)) =
              (0 : Fin (cuts j + 1)) := by
              ext
              simp
          simpa [hzero] using pref.2.1
        · constructor
          · intro n hn
            have hnj : n < cuts j :=
              Nat.lt_of_lt_of_le hn (hmono hij)
            have hstep := pref.2.2.1 n hnj
            simpa using hstep
          · intro k hk
            have hkj : k < j := Nat.lt_of_lt_of_le hk hij
            rcases pref.2.2.2 k hkj with
              ⟨hit, hhitLeft, hhitRight, haccepting⟩
            refine ⟨hit, hhitLeft, hhitRight, ?_⟩
            simpa using haccepting⟩
  have hproj_refl :
      ∀ ⦃i : Nat⦄ (pref : Prefix i), proj (le_refl i) pref = pref := by
    intro i pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hproj_trans :
      ∀ ⦃i j k : Nat⦄ (hij : i ≤ j) (hjk : j ≤ k)
        (pref : Prefix k),
        proj hij (proj hjk pref) = proj (Nat.le_trans hij hjk) pref := by
    intro i j k hij hjk pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hfin :
      ∀ (i : Nat) (pref : Prefix i),
        {next : Prefix (i + 1) | proj (Nat.le_add_right i 1) next = pref}.Finite := by
    intro i pref
    exact Set.toFinite _
  rcases exists_seq_forall_proj_of_forall_finite
      (α := Prefix) proj hproj_refl hproj_trans hfin with
    ⟨prefixes, hprefixes⟩
  let path : Nat -> A.State :=
    fun n => (prefixes n).1
      ⟨n,
        Nat.lt_succ_of_le
          (self_le_of_strict_succ_cuts cuts hstrict n)⟩
  have hstartPath : path 0 = start := by
    simpa [path] using (prefixes 0).2.1
  have hstepPath :
      ∀ n : Nat, A.step (path n) (word n) (path (n + 1)) := by
    intro n
    have hnCut : n < cuts (n + 1) := by
      exact Nat.lt_of_le_of_lt
        (self_le_of_strict_succ_cuts cuts hstrict n) (hstrict n)
    have hvalid := (prefixes (n + 1)).2.2.1 n hnCut
    have hproj :
        proj (Nat.le_succ n) (prefixes (n + 1)) = prefixes n :=
      hprefixes (Nat.le_succ n)
    have hsource :
        path n =
          (prefixes (n + 1)).1
            ⟨n, Nat.lt_succ_of_lt hnCut⟩ := by
      have hval := congrArg Subtype.val hproj
      have happ := congrFun hval
        ⟨n,
          Nat.lt_succ_of_le
            (self_le_of_strict_succ_cuts cuts hstrict n)⟩
      simpa [path, proj] using happ.symm
    have htarget :
        path (n + 1) =
          (prefixes (n + 1)).1
            ⟨n + 1, Nat.succ_lt_succ hnCut⟩ := by
      simp [path]
    simpa [hsource, htarget] using hvalid
  apply acceptsFrom_of_path_accepting_intervals_strict A path hstartPath
    hstepPath cuts hstrict
  intro k
  have hkBig : k < cuts (k + 1) := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans (Nat.le_refl k)
        (self_le_of_strict_succ_cuts cuts hstrict k))
      (hstrict k)
  rcases (prefixes (cuts (k + 1))).2.2.2 k hkBig with
    ⟨hit, hhitLeft, hhitRight, haccepting⟩
  refine ⟨hit, hhitLeft, hhitRight, ?_⟩
  have hhit_le_self : hit ≤ cuts hit :=
    self_le_of_strict_succ_cuts cuts hstrict hit
  have hlevel : hit ≤ cuts (k + 1) := hhitRight
  have hpath_hit :
      path hit =
        (prefixes (cuts (k + 1))).1
          ⟨hit,
            Nat.lt_succ_of_le
              (Nat.le_trans hhitRight
                (hmono
                  (self_le_of_strict_succ_cuts cuts hstrict (k + 1))))⟩ := by
    have hproj_hit :
        proj hlevel (prefixes (cuts (k + 1))) = prefixes hit :=
      hprefixes hlevel
    have hval := congrArg Subtype.val hproj_hit
    have happ := congrFun hval
      ⟨hit, Nat.lt_succ_of_le hhit_le_self⟩
    simpa [path, proj] using happ.symm
  rw [hpath_hit]
  exact haccepting

theorem acceptsFrom_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ path : Nat -> A.State,
          path 0 = start ∧
            (∀ (i : Nat), i < cuts m ->
              A.step (path i) (word i) (path (i + 1))) ∧
            (∀ (k : Nat), k < m ->
              ∃ hit : Nat,
                cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                  A.accepting (path hit))) :
    A.AcceptsFrom start word := by
  apply acceptsFrom_of_arbitrarily_long_prefixes_with_accepting_cut_intervals
    A cuts hstrict
  intro m
  rcases hprefix m with ⟨path, hstart, hvalid, haccepting⟩
  refine ⟨fun idx : Fin (cuts m + 1) => path idx.val, ?_, ?_, ?_⟩
  · simpa using hstart
  · intro i hi
    simpa using hvalid i hi
  · intro k hk
    rcases haccepting k hk with
      ⟨hit, hhitLeft, hhitRight, hacceptingHit⟩
    refine ⟨hit, hhitLeft, hhitRight, ?_⟩
    simpa using hacceptingHit

theorem accepts_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ path : Nat -> A.State,
          path 0 = A.initial ∧
            (∀ (i : Nat), i < cuts m ->
              A.step (path i) (word i) (path (i + 1))) ∧
            (∀ (k : Nat), k < m ->
              ∃ hit : Nat,
                cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                  A.accepting (path hit))) :
    A.Accepts word :=
  acceptsFrom_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    A cuts hstrict hprefix

theorem acceptsFrom_of_arbitrarily_long_reachablePrefixes_with_accepting_cut_intervals
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ target : A.State,
          ReachablePrefix A start word (cuts m) target ∧
            ∃ path : Nat -> A.State,
              path 0 = start ∧
                path (cuts m) = target ∧
                (∀ (i : Nat), i < cuts m ->
                  A.step (path i) (word i) (path (i + 1))) ∧
                (∀ (k : Nat), k < m ->
                  ∃ hit : Nat,
                    cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                      A.accepting (path hit))) :
    A.AcceptsFrom start word := by
  apply acceptsFrom_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    A cuts hstrict
  intro m
  rcases hprefix m with
    ⟨_target, _hreachable, path, hstart, _htarget, hvalid, haccepting⟩
  exact ⟨path, hstart, hvalid, haccepting⟩

theorem accepts_of_arbitrarily_long_reachablePrefixes_with_accepting_cut_intervals
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ target : A.State,
          ReachablePrefix A A.initial word (cuts m) target ∧
            ∃ path : Nat -> A.State,
              path 0 = A.initial ∧
                path (cuts m) = target ∧
                (∀ (i : Nat), i < cuts m ->
                  A.step (path i) (word i) (path (i + 1))) ∧
                (∀ (k : Nat), k < m ->
                  ∃ hit : Nat,
                    cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                      A.accepting (path hit))) :
    A.Accepts word :=
  acceptsFrom_of_arbitrarily_long_reachablePrefixes_with_accepting_cut_intervals
    A cuts hstrict hprefix

theorem segmentVisitsAccepting_chain_to_path_prefix
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hzero : cuts 0 = 0)
    (chain : Nat -> A.State)
    (hstart : chain 0 = start) :
    ∀ m : Nat,
      (∀ k : Nat, k < m ->
        SegmentVisitsAccepting A word (cuts k) (cuts (k + 1) - cuts k)
          (chain k) (chain (k + 1))) ->
      ∃ path : Nat -> A.State,
        path 0 = start ∧
          path (cuts m) = chain m ∧
          (∀ i : Nat, i < cuts m ->
            A.step (path i) (word i) (path (i + 1))) ∧
          (∀ k : Nat, k < m ->
            ∃ hit : Nat,
              cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                A.accepting (path hit)) := by
  intro m
  induction m with
  | zero =>
      intro _hsegments
      refine ⟨fun _ => start, rfl, ?_, ?_, ?_⟩
      · simpa [hzero] using hstart.symm
      · intro i hi
        omega
      · intro k hk
        omega
  | succ m ih =>
      intro hsegments
      have hsegmentsPrefix :
          ∀ k : Nat, k < m ->
            SegmentVisitsAccepting A word (cuts k)
              (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
        intro k hk
        exact hsegments k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rcases ih hsegmentsPrefix with
        ⟨prefixPath, hprefixStart, hprefixTarget, hprefixValid,
          hprefixHits⟩
      rcases hsegments m (Nat.lt_succ_self m) with
        ⟨blockPath, hblockStart, hblockTarget, hblockValid,
          blockHit, hblockHitLe, hblockAccepting⟩
      let path : Nat -> A.State :=
        fun i =>
          if i ≤ cuts m then prefixPath i else blockPath (i - cuts m)
      refine ⟨path, ?_, ?_, ?_, ?_⟩
      · have hle0 : 0 ≤ cuts m := Nat.zero_le _
        simp [path, hle0, hprefixStart]
      · have hnot : ¬ cuts (m + 1) ≤ cuts m := by
          have hstrict_m := hstrict m
          omega
        simp [path, hnot, hblockTarget]
      · intro i hi
        by_cases hlt : i < cuts m
        · have hi_le : i ≤ cuts m := Nat.le_of_lt hlt
          have hisucc_le : i + 1 ≤ cuts m := Nat.succ_le_of_lt hlt
          simpa [path, hi_le, hisucc_le] using hprefixValid i hlt
        · have hge : cuts m ≤ i := by omega
          by_cases hle : i ≤ cuts m
          · have hieq : i = cuts m := by omega
            subst i
            have hleft : cuts m ≤ cuts m := le_rfl
            have hright : ¬ cuts m + 1 ≤ cuts m := by omega
            have hsub : cuts m + 1 - cuts m = 1 := by omega
            have hblockStep :
                A.step (chain m) (word (cuts m)) (blockPath 1) := by
              have hlen_pos : 0 < cuts (m + 1) - cuts m := by omega
              simpa [hblockStart] using hblockValid 0 hlen_pos
            simpa [path, hleft, hright, hsub, hprefixTarget] using
              hblockStep
          · have hi_not : ¬ i ≤ cuts m := hle
            have hisucc_not : ¬ i + 1 ≤ cuts m := by omega
            have hidx_lt : i - cuts m < cuts (m + 1) - cuts m := by
              omega
            have hsucc_sub :
                i + 1 - cuts m = i - cuts m + 1 := by omega
            have hword : cuts m + (i - cuts m) = i := by omega
            simpa [path, hi_not, hisucc_not, hsucc_sub, hword] using
              hblockValid (i - cuts m) hidx_lt
      · intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkm | hkm
        · rcases hprefixHits k hkm with
            ⟨hit, hhitLeft, hhitRight, haccepting⟩
          refine ⟨hit, hhitLeft, hhitRight, ?_⟩
          have hmono := monotone_of_strict_succ_cuts cuts hstrict
          have hhit_le_m : hit ≤ cuts m := by
            exact Nat.le_trans hhitRight (hmono (by omega))
          simp [path, hhit_le_m, haccepting]
        · subst k
          refine ⟨cuts m + blockHit, ?_, ?_, ?_⟩
          · omega
          · have hstrict_m := hstrict m
            omega
          · by_cases hhit0 : blockHit = 0
            · subst blockHit
              have hblockAcceptingStart : A.accepting (chain m) := by
                simpa [hblockStart] using hblockAccepting
              simp [path, hprefixTarget, hblockAcceptingStart]
            · have hnot : ¬ cuts m + blockHit ≤ cuts m := by omega
              have hsub : cuts m + blockHit - cuts m = blockHit := by omega
              simpa [path, hnot, hsub] using hblockAccepting

theorem reachablePrefix_segmentVisitsAccepting_chain_to_path_prefix
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (chain : Nat -> A.State)
    (hfrontier : ReachablePrefix A start word (cuts 0) (chain 0)) :
    ∀ m : Nat,
      (∀ k : Nat, k < m ->
        SegmentVisitsAccepting A word (cuts k) (cuts (k + 1) - cuts k)
          (chain k) (chain (k + 1))) ->
      ∃ path : Nat -> A.State,
        path 0 = start ∧
          path (cuts m) = chain m ∧
          (∀ i : Nat, i < cuts m ->
            A.step (path i) (word i) (path (i + 1))) ∧
          (∀ k : Nat, k < m ->
            ∃ hit : Nat,
              cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                A.accepting (path hit)) := by
  intro m
  induction m with
  | zero =>
      intro _hsegments
      rcases hfrontier with ⟨path, hstart, htarget, hvalid⟩
      exact ⟨path, hstart, htarget, hvalid, by intro k hk; omega⟩
  | succ m ih =>
      intro hsegments
      have hsegmentsPrefix :
          ∀ k : Nat, k < m ->
            SegmentVisitsAccepting A word (cuts k)
              (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
        intro k hk
        exact hsegments k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rcases ih hsegmentsPrefix with
        ⟨prefixPath, hprefixStart, hprefixTarget, hprefixValid,
          hprefixHits⟩
      rcases hsegments m (Nat.lt_succ_self m) with
        ⟨blockPath, hblockStart, hblockTarget, hblockValid,
          blockHit, hblockHitLe, hblockAccepting⟩
      let path : Nat -> A.State :=
        fun i =>
          if i ≤ cuts m then prefixPath i else blockPath (i - cuts m)
      refine ⟨path, ?_, ?_, ?_, ?_⟩
      · have hle0 : 0 ≤ cuts m := Nat.zero_le _
        simp [path, hle0, hprefixStart]
      · have hnot : ¬ cuts (m + 1) ≤ cuts m := by
          have hstrict_m := hstrict m
          omega
        simp [path, hnot, hblockTarget]
      · intro i hi
        by_cases hlt : i < cuts m
        · have hi_le : i ≤ cuts m := Nat.le_of_lt hlt
          have hisucc_le : i + 1 ≤ cuts m := Nat.succ_le_of_lt hlt
          simpa [path, hi_le, hisucc_le] using hprefixValid i hlt
        · have hge : cuts m ≤ i := by omega
          by_cases hle : i ≤ cuts m
          · have hieq : i = cuts m := by omega
            subst i
            have hleft : cuts m ≤ cuts m := le_rfl
            have hright : ¬ cuts m + 1 ≤ cuts m := by omega
            have hsub : cuts m + 1 - cuts m = 1 := by omega
            have hblockStep :
                A.step (chain m) (word (cuts m)) (blockPath 1) := by
              have hlen_pos : 0 < cuts (m + 1) - cuts m := by omega
              simpa [hblockStart] using hblockValid 0 hlen_pos
            simpa [path, hleft, hright, hsub, hprefixTarget] using
              hblockStep
          · have hi_not : ¬ i ≤ cuts m := hle
            have hisucc_not : ¬ i + 1 ≤ cuts m := by omega
            have hidx_lt : i - cuts m < cuts (m + 1) - cuts m := by
              omega
            have hsucc_sub :
                i + 1 - cuts m = i - cuts m + 1 := by omega
            have hword : cuts m + (i - cuts m) = i := by omega
            simpa [path, hi_not, hisucc_not, hsucc_sub, hword] using
              hblockValid (i - cuts m) hidx_lt
      · intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkm | hkm
        · rcases hprefixHits k hkm with
            ⟨hit, hhitLeft, hhitRight, haccepting⟩
          refine ⟨hit, hhitLeft, hhitRight, ?_⟩
          have hmono := monotone_of_strict_succ_cuts cuts hstrict
          have hhit_le_m : hit ≤ cuts m := by
            exact Nat.le_trans hhitRight (hmono (by omega))
          simp [path, hhit_le_m, haccepting]
        · subst k
          refine ⟨cuts m + blockHit, ?_, ?_, ?_⟩
          · omega
          · have hstrict_m := hstrict m
            omega
          · by_cases hhit0 : blockHit = 0
            · subst blockHit
              have hblockAcceptingStart : A.accepting (chain m) := by
                simpa [hblockStart] using hblockAccepting
              simp [path, hprefixTarget, hblockAcceptingStart]
            · have hnot : ¬ cuts m + blockHit ≤ cuts m := by omega
              have hsub : cuts m + blockHit - cuts m = blockHit := by omega
              simpa [path, hnot, hsub] using hblockAccepting

theorem acceptsFrom_of_arbitrarily_long_segment_chains_with_accepting_cut_intervals
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hzero : cuts 0 = 0)
    (hchains :
      ∀ m : Nat,
        ∃ chain : Nat -> A.State,
          chain 0 = start ∧
            ∀ k : Nat, k < m ->
              SegmentVisitsAccepting A word (cuts k)
                (cuts (k + 1) - cuts k) (chain k) (chain (k + 1))) :
    A.AcceptsFrom start word := by
  apply acceptsFrom_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    A cuts hstrict
  intro m
  rcases hchains m with ⟨chain, hstart, hsegments⟩
  rcases segmentVisitsAccepting_chain_to_path_prefix A cuts hstrict hzero
      chain hstart m hsegments with
    ⟨path, hpathStart, _htarget, hvalid, hhits⟩
  exact ⟨path, hpathStart, hvalid, hhits⟩

theorem accepts_of_arbitrarily_long_segment_chains_with_accepting_cut_intervals
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hzero : cuts 0 = 0)
    (hchains :
      ∀ m : Nat,
        ∃ chain : Nat -> A.State,
          chain 0 = A.initial ∧
            ∀ k : Nat, k < m ->
              SegmentVisitsAccepting A word (cuts k)
                (cuts (k + 1) - cuts k) (chain k) (chain (k + 1))) :
    A.Accepts word :=
  acceptsFrom_of_arbitrarily_long_segment_chains_with_accepting_cut_intervals
    A cuts hstrict hzero hchains

theorem segmentVisitsAcceptingCover_chain_to_segment_chain_to_target
    [DecidableEq A.State]
    (word : OmegaWord Alphabet)
    {start : A.State}
    (cuts : Nat -> Nat)
    (sets : Nat -> Finset A.State)
    (hstartSet : sets 0 = {start}) :
    ∀ m : Nat,
      ∀ target : A.State,
        target ∈ sets m ->
          (∀ k : Nat, k < m ->
            SegmentVisitsAcceptingCover A word (cuts k)
              (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) ->
            ∃ chain : Nat -> A.State,
              chain 0 = start ∧
                chain m = target ∧
                  ∀ k : Nat, k < m ->
                    SegmentVisitsAccepting A word (cuts k)
                      (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
  intro m
  induction m with
  | zero =>
      intro target htarget _hcover
      have htargetStart : target = start := by
        rw [hstartSet] at htarget
        simpa using htarget
      subst target
      exact ⟨fun _ => start, rfl, rfl, by intro k hk; omega⟩
  | succ m ih =>
      intro target htarget hcover
      rcases hcover m (Nat.lt_succ_self m) target htarget with
        ⟨source, hsource, hsegment⟩
      have hcoverPrefix :
          ∀ k : Nat, k < m ->
            SegmentVisitsAcceptingCover A word (cuts k)
              (cuts (k + 1) - cuts k) (sets k) (sets (k + 1)) := by
        intro k hk
        exact hcover k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rcases ih source hsource hcoverPrefix with
        ⟨prefixPath, hprefixStart, hprefixTarget, hprefixSegments⟩
      let chain : Nat -> A.State :=
        fun i => if i = m + 1 then target else prefixPath i
      refine ⟨chain, ?_, ?_, ?_⟩
      · have hne : 0 ≠ m + 1 := by omega
        simp [chain, hprefixStart]
      · simp [chain]
      · intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkm | hkm
        · have hk_ne : k ≠ m + 1 := by omega
          have hksucc_ne : k + 1 ≠ m + 1 := by omega
          have hk_ne_m : k ≠ m := by omega
          simpa [chain, hk_ne, hksucc_ne, hk_ne_m] using
            hprefixSegments k hkm
        · subst k
          have hm_ne : m ≠ m + 1 := by omega
          simpa [chain, hm_ne, hprefixTarget] using hsegment

theorem segmentVisitsAcceptingCover_chain_to_segment_chain_from_singleton
    [DecidableEq A.State]
    (word : OmegaWord Alphabet)
    {start : A.State}
    (cuts : Nat -> Nat)
    (sets : Nat -> Finset A.State)
    (hstartSet : sets 0 = {start})
    (m : Nat)
    (hnonempty : (sets m).Nonempty)
    (hcover :
      ∀ k : Nat, k < m ->
        SegmentVisitsAcceptingCover A word (cuts k)
          (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) :
    ∃ chain : Nat -> A.State,
      chain 0 = start ∧
        ∀ k : Nat, k < m ->
          SegmentVisitsAccepting A word (cuts k)
            (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
  rcases hnonempty with ⟨target, htarget⟩
  rcases segmentVisitsAcceptingCover_chain_to_segment_chain_to_target
      A word cuts sets hstartSet m target htarget hcover with
    ⟨chain, hstart, _htarget, hsegments⟩
  exact ⟨chain, hstart, hsegments⟩

theorem segmentVisitsAcceptingCover_chain_to_segment_chain_to_target_from_frontier
    (word : OmegaWord Alphabet)
    (cuts : Nat -> Nat)
    (sets : Nat -> Finset A.State) :
    ∀ m : Nat,
      ∀ target : A.State,
        target ∈ sets m ->
          (∀ k : Nat, k < m ->
            SegmentVisitsAcceptingCover A word (cuts k)
              (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) ->
            ∃ source : A.State,
              source ∈ sets 0 ∧
                ∃ chain : Nat -> A.State,
                  chain 0 = source ∧
                    chain m = target ∧
                      ∀ k : Nat, k < m ->
                        SegmentVisitsAccepting A word (cuts k)
                          (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
  intro m
  induction m with
  | zero =>
      intro target htarget _hcover
      exact ⟨target, htarget, fun _ => target, rfl, rfl,
        by intro k hk; omega⟩
  | succ m ih =>
      intro target htarget hcover
      rcases hcover m (Nat.lt_succ_self m) target htarget with
        ⟨middle, hmiddle, hsegment⟩
      have hcoverPrefix :
          ∀ k : Nat, k < m ->
            SegmentVisitsAcceptingCover A word (cuts k)
              (cuts (k + 1) - cuts k) (sets k) (sets (k + 1)) := by
        intro k hk
        exact hcover k (Nat.lt_trans hk (Nat.lt_succ_self m))
      rcases ih middle hmiddle hcoverPrefix with
        ⟨source, hsource, prefixPath, hprefixStart, hprefixTarget,
          hprefixSegments⟩
      let chain : Nat -> A.State :=
        fun i => if i = m + 1 then target else prefixPath i
      refine ⟨source, hsource, chain, ?_, ?_, ?_⟩
      · simp [chain, hprefixStart]
      · simp [chain]
      · intro k hk
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hkm | hkm
        · have hk_ne : k ≠ m + 1 := by omega
          have hksucc_ne : k + 1 ≠ m + 1 := by omega
          have hk_ne_m : k ≠ m := by omega
          simpa [chain, hk_ne, hksucc_ne, hk_ne_m] using
            hprefixSegments k hkm
        · subst k
          have hm_ne : m ≠ m + 1 := by omega
          simpa [chain, hm_ne, hprefixTarget] using hsegment

theorem segmentVisitsAcceptingCover_chain_to_segment_chain_from_frontier
    (word : OmegaWord Alphabet)
    (cuts : Nat -> Nat)
    (sets : Nat -> Finset A.State)
    (m : Nat)
    (hnonempty : (sets m).Nonempty)
    (hcover :
      ∀ k : Nat, k < m ->
        SegmentVisitsAcceptingCover A word (cuts k)
          (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) :
    ∃ source : A.State,
      source ∈ sets 0 ∧
        ∃ chain : Nat -> A.State,
          chain 0 = source ∧
            ∀ k : Nat, k < m ->
              SegmentVisitsAccepting A word (cuts k)
                (cuts (k + 1) - cuts k) (chain k) (chain (k + 1)) := by
  rcases hnonempty with ⟨target, htarget⟩
  rcases segmentVisitsAcceptingCover_chain_to_segment_chain_to_target_from_frontier
      A word cuts sets m target htarget hcover with
    ⟨source, hsource, chain, hchainStart, _hchainTarget, hsegments⟩
  exact ⟨source, hsource, chain, hchainStart, hsegments⟩

theorem acceptsFrom_of_arbitrarily_long_segment_cover_chains_from_singleton
    [DecidableEq A.State]
    {start : A.State} {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hzero : cuts 0 = 0)
    (sets : Nat -> Finset A.State)
    (hstartSet : sets 0 = {start})
    (hnonempty : ∀ m : Nat, (sets m).Nonempty)
    (hcover :
      ∀ k : Nat,
        SegmentVisitsAcceptingCover A word (cuts k)
          (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) :
    A.AcceptsFrom start word := by
  apply acceptsFrom_of_arbitrarily_long_segment_chains_with_accepting_cut_intervals
    A cuts hstrict hzero
  intro m
  rcases segmentVisitsAcceptingCover_chain_to_segment_chain_from_singleton
      A word cuts sets hstartSet m (hnonempty m)
      (fun k _hk => hcover k) with
    ⟨chain, hchainStart, hsegments⟩
  exact ⟨chain, hchainStart, hsegments⟩

theorem accepts_of_arbitrarily_long_segment_cover_chains_from_singleton
    [DecidableEq A.State]
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hzero : cuts 0 = 0)
    (sets : Nat -> Finset A.State)
    (hstartSet : sets 0 = {A.initial})
    (hnonempty : ∀ m : Nat, (sets m).Nonempty)
    (hcover :
      ∀ k : Nat,
        SegmentVisitsAcceptingCover A word (cuts k)
          (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) :
    A.Accepts word :=
  acceptsFrom_of_arbitrarily_long_segment_cover_chains_from_singleton
    A cuts hstrict hzero sets hstartSet hnonempty hcover

theorem accepts_of_arbitrarily_long_segment_cover_chains_from_reachable_frontier
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (sets : Nat -> Finset A.State)
    (hfrontierReachable :
      ∀ source, source ∈ sets 0 ->
        ReachablePrefix A A.initial word (cuts 0) source)
    (hnonempty : ∀ m : Nat, (sets m).Nonempty)
    (hcover :
      ∀ k : Nat,
        SegmentVisitsAcceptingCover A word (cuts k)
          (cuts (k + 1) - cuts k) (sets k) (sets (k + 1))) :
    A.Accepts word := by
  apply accepts_of_arbitrarily_long_path_prefixes_with_accepting_cut_intervals
    A cuts hstrict
  intro m
  rcases segmentVisitsAcceptingCover_chain_to_segment_chain_from_frontier
      A word cuts sets m (hnonempty m) (fun k _hk => hcover k) with
    ⟨source, hsource, chain, hchainStart, hsegments⟩
  have hfrontier :
      ReachablePrefix A A.initial word (cuts 0) (chain 0) := by
    rw [hchainStart]
    exact hfrontierReachable source hsource
  rcases reachablePrefix_segmentVisitsAccepting_chain_to_path_prefix
      A cuts hstrict chain hfrontier m hsegments with
    ⟨path, hpathStart, _htarget, hvalid, hhits⟩
  exact ⟨path, hpathStart, hvalid, hhits⟩

def shiftedEventFrontierCuts (cuts : Nat -> Nat) : Nat -> Nat :=
  fun k => cuts (k + 1) + 1

theorem shiftedEventFrontierCuts_strict
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    ∀ k : Nat,
      shiftedEventFrontierCuts cuts k <
        shiftedEventFrontierCuts cuts (k + 1) := by
  intro k
  simp [shiftedEventFrontierCuts]
  exact hstrict (k + 1)

theorem accepts_of_arbitrarily_long_segment_cover_chains_from_shifted_event_frontiers
    {word : OmegaWord Alphabet}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (sets : Nat -> Finset A.State)
    (hfrontierReachable :
      ∀ source, source ∈ sets 0 ->
        ReachablePrefix A A.initial word (cuts 1 + 1) source)
    (hnonempty : ∀ m : Nat, (sets m).Nonempty)
    (hcover :
      ∀ k : Nat,
        SegmentVisitsAcceptingCover A word (cuts (k + 1) + 1)
          ((cuts (k + 2) + 1) - (cuts (k + 1) + 1))
          (sets k) (sets (k + 1))) :
    A.Accepts word := by
  let shiftedCuts := shiftedEventFrontierCuts cuts
  have hshiftedStrict :
      ∀ k : Nat, shiftedCuts k < shiftedCuts (k + 1) := by
    intro k
    exact shiftedEventFrontierCuts_strict cuts hstrict k
  apply accepts_of_arbitrarily_long_segment_cover_chains_from_reachable_frontier
    A shiftedCuts hshiftedStrict sets
  · intro source hsource
    simpa [shiftedCuts, shiftedEventFrontierCuts] using
      hfrontierReachable source hsource
  · exact hnonempty
  · intro k
    simpa [shiftedCuts, shiftedEventFrontierCuts] using hcover k

theorem reachableAfter_zero
    (start : A.State) (word : OmegaWord Alphabet) {state : A.State} :
    ReachableAfter A start word 0 state ↔ state = start := by
  rfl

theorem reachableAfter_succ
    (start : A.State) (word : OmegaWord Alphabet)
    {n : Nat} {state : A.State} :
    ReachableAfter A start word (n + 1) state ↔
      ∃ prev, ReachableAfter A start word n prev ∧
        A.step prev (word n) state := by
  rfl

theorem reachableAfter_to_prefix
    (start : A.State) (word : OmegaWord Alphabet) :
    ∀ {n : Nat} {target : A.State},
      ReachableAfter A start word n target ->
        ReachablePrefix A start word n target := by
  intro n
  induction n with
  | zero =>
      intro target htarget
      refine ⟨fun _ => start, rfl, ?_, ?_⟩
      · simp [htarget.symm]
      · intro i hi
        omega
  | succ n ih =>
      intro target htarget
      rcases htarget with ⟨prev, hprevReach, hstep⟩
      rcases ih hprevReach with ⟨path, hstart, htargetPrev, hvalid⟩
      refine ⟨fun i => if i = n + 1 then target else path i, ?_, ?_, ?_⟩
      · have hne : 0 ≠ n + 1 := by omega
        simp [hstart]
      · simp
      · intro i hi
        have hle : i ≤ n := Nat.le_of_lt_succ hi
        rcases Nat.lt_or_eq_of_le hle with hlt | heq
        · have hi_ne : i ≠ n + 1 := by omega
          have hi_ne_n : i ≠ n := by omega
          simp [hi_ne, hi_ne_n]
          exact hvalid i hlt
        · subst i
          have hn_ne : n ≠ n + 1 := by omega
          simp [htargetPrev, hstep]

theorem exists_runFrom_of_arbitrarily_long_reachablePrefixes
    {start : A.State} {word : OmegaWord Alphabet}
    (hprefix :
      ∀ n : Nat, ∃ target : A.State,
        ReachablePrefix A start word n target) :
    ∃ run : A.RunFrom start word, True := by
  apply exists_runFrom_of_arbitrarily_long_prefixes A
  intro n
  rcases hprefix n with ⟨target, path, hstart, _htarget, hvalid⟩
  refine ⟨fun idx : Fin (n + 1) => path idx.val, ?_, ?_⟩
  · simpa using hstart
  · intro i hi
    simpa using hvalid i hi

theorem reachablePrefix_to_segment
    (start : A.State) (word : OmegaWord Alphabet)
    {n : Nat} {target : A.State}
    (hprefix : ReachablePrefix A start word n target) :
    Segment A word 0 n start target := by
  rcases hprefix with ⟨path, hstart, htarget, hstep⟩
  exact ⟨path, hstart, htarget, by
    intro i hi
    simpa using hstep i hi⟩

theorem reachablePrefix_split_last
    (start : A.State) (word : OmegaWord Alphabet)
    {n : Nat} {target : A.State}
    (hprefix : ReachablePrefix A start word n target) (hpos : 0 < n) :
    ∃ source : A.State,
      ReachablePrefix A start word (n - 1) source ∧
        Segment A word (n - 1) 1 source target := by
  rcases hprefix with ⟨path, hstart, htarget, hvalid⟩
  let source := path (n - 1)
  have hidx : n - 1 + 1 = n := by omega
  have hstep : A.step source (word (n - 1)) target := by
    have hlt : n - 1 < n := by omega
    simpa [source, hidx, htarget] using hvalid (n - 1) hlt
  have hprefixSource :
      ReachablePrefix A start word (n - 1) source :=
    ⟨path, hstart, by simp [source], fun i hi => hvalid i (by omega)⟩
  have hsegment : Segment A word (n - 1) 1 source target := by
    let path' : Nat -> A.State := fun i => if i = 0 then source else target
    refine ⟨path', by simp [path'], by simp [path'], ?_⟩
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [path'] using hstep
  exact ⟨source, hprefixSource, hsegment⟩

theorem reachablePrefix_split_last_accepting
    (start : A.State) (word : OmegaWord Alphabet)
    {n : Nat} {target : A.State}
    (hprefix : ReachablePrefix A start word n target)
    (haccepting : A.accepting target) (hpos : 0 < n) :
    ∃ source : A.State,
      ReachablePrefix A start word (n - 1) source ∧
        SegmentVisitsAccepting A word (n - 1) 1 source target := by
  rcases reachablePrefix_split_last A start word hprefix hpos with
    ⟨source, hsourceReach, hsegment⟩
  rcases hsegment with ⟨path, hsource, htarget, hvalid⟩
  exact ⟨source, hsourceReach,
    ⟨path, hsource, htarget, hvalid, 1, le_rfl,
      by simpa [htarget] using haccepting⟩⟩

theorem segment_zero
    (word : OmegaWord Alphabet) (startTime : Nat) (state : A.State) :
    Segment A word startTime 0 state state := by
  exact ⟨fun _ => state, rfl, rfl, by intro i hi; omega⟩

theorem segment_of_step
    (word : OmegaWord Alphabet) {startTime : Nat} {source target : A.State}
    (hstep : A.step source (word startTime) target) :
    Segment A word startTime 1 source target := by
  let path : Nat -> A.State := fun i => if i = 0 then source else target
  refine ⟨path, by simp [path], by simp [path], ?_⟩
  intro i hi
  have hi0 : i = 0 := by omega
  subst i
  simpa [path] using hstep

/--
The concrete accepting run supplies an ordinary segment between any two
positions written as `startTime` and `startTime + length`.
-/
theorem runFrom_segment
    {start : A.State} {word : OmegaWord Alphabet}
    (run : A.RunFrom start word) (startTime length : Nat) :
    Segment A word startTime length (run.path startTime)
      (run.path (startTime + length)) := by
  let path : Nat -> A.State := fun i => run.path (startTime + i)
  refine ⟨path, rfl, ?_, ?_⟩
  · rfl
  · intro i hi
    have hidx : startTime + (i + 1) = startTime + i + 1 := by omega
    change
      A.step (run.path (startTime + i)) (word (startTime + i))
        (run.path (startTime + (i + 1)))
    rw [hidx]
    exact run.step_valid (startTime + i)

theorem segment_append_step
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source middle target : A.State}
    (hsegment : Segment A word startTime length source middle)
    (hstep : A.step middle (word (startTime + length)) target) :
    Segment A word startTime (length + 1) source target := by
  rcases hsegment with ⟨path, hsource, hmiddle, hvalid⟩
  let path' : Nat -> A.State :=
    fun i => if i ≤ length then path i else target
  refine ⟨path', ?_, ?_, ?_⟩
  · have hzero : 0 ≤ length := Nat.zero_le _
    simp [path', hzero, hsource]
  · have hnot : ¬ length + 1 ≤ length := by omega
    simp [path', hnot]
  · intro i hi
    by_cases hlt : i < length
    · have hi_le : i ≤ length := Nat.le_of_lt hlt
      have hisucc_le : i + 1 ≤ length := Nat.succ_le_of_lt hlt
      have hword : startTime + i = startTime + i := rfl
      simpa [path', hi_le, hisucc_le, hword] using hvalid i hlt
    · have hi_eq : i = length := by omega
      subst i
      have hle : length ≤ length := le_rfl
      have hnot_succ : ¬ length + 1 ≤ length := by omega
      simpa [path', hle, hnot_succ, hmiddle] using hstep

theorem segment_prepend_step
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source middle target : A.State}
    (hstep : A.step source (word startTime) middle)
    (hsegment : Segment A word (startTime + 1) length middle target) :
    Segment A word startTime (length + 1) source target := by
  rcases hsegment with ⟨path, hmiddle, htarget, hvalid⟩
  let path' : Nat -> A.State :=
    fun i => if i = 0 then source else path (i - 1)
  refine ⟨path', ?_, ?_, ?_⟩
  · simp [path']
  · have hne : length + 1 ≠ 0 := by omega
    have hsub : length + 1 - 1 = length := by omega
    simp [path', hsub, htarget]
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hsucc_ne : 1 ≠ 0 := by omega
      simpa [path', hsucc_ne, hmiddle] using hstep
    · have hpos : 0 < i := Nat.pos_of_ne_zero hi0
      have hlt : i - 1 < length := by omega
      have hsucc_ne : i + 1 ≠ 0 := by omega
      have hsucc_sub : i + 1 - 1 = i := by omega
      have hpred_succ : i - 1 + 1 = i := by omega
      have hword : startTime + i = (startTime + 1) + (i - 1) := by omega
      simpa [path', hi0, hsucc_ne, hsucc_sub, hword, hpred_succ] using
        hvalid (i - 1) hlt

theorem segment_append
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {source middle target : A.State}
    (hleft : Segment A word startTime leftLength source middle)
    (hright :
      Segment A word (startTime + leftLength) rightLength middle target) :
    Segment A word startTime (leftLength + rightLength) source target := by
  rcases hleft with ⟨leftPath, hleftSource, hleftMiddle, hleftValid⟩
  rcases hright with ⟨rightPath, hrightMiddle, hrightTarget, hrightValid⟩
  let path : Nat -> A.State :=
    fun i => if i ≤ leftLength then leftPath i else rightPath (i - leftLength)
  refine ⟨path, ?_, ?_, ?_⟩
  · have hzero : 0 ≤ leftLength := Nat.zero_le _
    simp [path, hzero, hleftSource]
  · by_cases hrightZero : rightLength = 0
    · subst rightLength
      have hle : leftLength + 0 ≤ leftLength := by omega
      have hmiddleTarget : middle = target := by
        rw [← hrightMiddle, hrightTarget]
      simp [path, hleftMiddle, hmiddleTarget]
    · have hnot : ¬ leftLength + rightLength ≤ leftLength := by omega
      have hsub : leftLength + rightLength - leftLength = rightLength := by omega
      simp [path, hnot, hsub, hrightTarget]
  · intro i hi
    by_cases hlt : i < leftLength
    · have hi_le : i ≤ leftLength := Nat.le_of_lt hlt
      have hisucc_le : i + 1 ≤ leftLength := Nat.succ_le_of_lt hlt
      simpa [path, hi_le, hisucc_le] using hleftValid i hlt
    · have hleft_le_i : leftLength ≤ i := by omega
      by_cases heq : i = leftLength
      · subst i
        have hle : leftLength ≤ leftLength := le_rfl
        by_cases hrightZero : rightLength = 0
        · subst rightLength
          omega
        · have hnot_succ : ¬ leftLength + 1 ≤ leftLength := by omega
          have hsucc_sub : leftLength + 1 - leftLength = 1 := by omega
          have hrightStep :
              A.step middle (word (startTime + leftLength)) (rightPath 1) := by
            simpa [hrightMiddle] using hrightValid 0 (by omega)
          simpa [path, hle, hnot_succ, hsucc_sub, hleftMiddle] using
            hrightStep
      · have hgt : leftLength < i := by omega
        have hi_not : ¬ i ≤ leftLength := by omega
        have hisucc_not : ¬ i + 1 ≤ leftLength := by omega
        have hidx_lt : i - leftLength < rightLength := by omega
        have hsucc_sub : i + 1 - leftLength = i - leftLength + 1 := by omega
        have hword :
            startTime + i =
              startTime + leftLength + (i - leftLength) := by omega
        simpa [path, hi_not, hisucc_not, hsucc_sub, hword] using
          hrightValid (i - leftLength) hidx_lt

theorem segmentVisitsAccepting_of_segment_accepting_target
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source target : A.State}
    (hsegment : Segment A word startTime length source target)
    (haccepting : A.accepting target) :
    SegmentVisitsAccepting A word startTime length source target := by
  rcases hsegment with ⟨path, hsource, htarget, hstep⟩
  exact ⟨path, hsource, htarget, hstep, length, le_rfl,
    by simpa [htarget] using haccepting⟩

theorem segmentVisitsAccepting_of_segment_accepting_source
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source target : A.State}
    (hsegment : Segment A word startTime length source target)
    (haccepting : A.accepting source) :
    SegmentVisitsAccepting A word startTime length source target := by
  rcases hsegment with ⟨path, hsource, htarget, hstep⟩
  exact ⟨path, hsource, htarget, hstep, 0, Nat.zero_le _,
    by simpa [hsource] using haccepting⟩

/--
Run interval form with an accepting source.  This packages the common situation
where a selected accepting occurrence is used as the first accepting visit of a
longer interval.
-/
theorem runFrom_segmentVisitsAccepting_of_accepting_source
    {start : A.State} {word : OmegaWord Alphabet}
    (run : A.RunFrom start word) {startTime length : Nat}
    (haccepting : A.accepting (run.path startTime)) :
    SegmentVisitsAccepting A word startTime length (run.path startTime)
      (run.path (startTime + length)) :=
  segmentVisitsAccepting_of_segment_accepting_source A word
    (runFrom_segment A run startTime length) haccepting

theorem segmentVisitsAccepting_of_step_accepting_target
    (word : OmegaWord Alphabet) {startTime : Nat} {source target : A.State}
    (hstep : A.step source (word startTime) target)
    (haccepting : A.accepting target) :
    SegmentVisitsAccepting A word startTime 1 source target :=
  segmentVisitsAccepting_of_segment_accepting_target A word
    (segment_of_step A word hstep) haccepting

theorem segmentVisitsAccepting_append_step
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source middle target : A.State}
    (hsegment :
      SegmentVisitsAccepting A word startTime length source middle)
    (hstep : A.step middle (word (startTime + length)) target) :
    SegmentVisitsAccepting A word startTime (length + 1) source target := by
  rcases hsegment with
    ⟨path, hsource, hmiddle, hvalid, hit, hitle, haccepting⟩
  let path' : Nat -> A.State :=
    fun i => if i ≤ length then path i else target
  refine ⟨path', ?_, ?_, ?_, hit, ?_, ?_⟩
  · have hzero : 0 ≤ length := Nat.zero_le _
    simp [path', hzero, hsource]
  · have hnot : ¬ length + 1 ≤ length := by omega
    simp [path', hnot]
  · intro i hi
    by_cases hlt : i < length
    · have hi_le : i ≤ length := Nat.le_of_lt hlt
      have hisucc_le : i + 1 ≤ length := Nat.succ_le_of_lt hlt
      simpa [path', hi_le, hisucc_le] using hvalid i hlt
    · have hi_eq : i = length := by omega
      subst i
      have hle : length ≤ length := le_rfl
      have hnot_succ : ¬ length + 1 ≤ length := by omega
      simpa [path', hle, hnot_succ, hmiddle] using hstep
  · omega
  · have hhit_le : hit ≤ length := hitle
    simp [path', hhit_le, haccepting]

theorem segmentVisitsAccepting_prepend_step
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source middle target : A.State}
    (hstep : A.step source (word startTime) middle)
    (hsegment :
      SegmentVisitsAccepting A word (startTime + 1) length middle target) :
    SegmentVisitsAccepting A word startTime (length + 1) source target := by
  rcases hsegment with
    ⟨path, hmiddle, htarget, hvalid, hit, hitle, haccepting⟩
  let path' : Nat -> A.State :=
    fun i => if i = 0 then source else path (i - 1)
  refine ⟨path', ?_, ?_, ?_, hit + 1, ?_, ?_⟩
  · simp [path']
  · have hsub : length + 1 - 1 = length := by omega
    simp [path', hsub, htarget]
  · intro i hi
    by_cases hi0 : i = 0
    · subst i
      have hsucc_ne : 1 ≠ 0 := by omega
      simpa [path', hsucc_ne, hmiddle] using hstep
    · have hlt : i - 1 < length := by omega
      have hsucc_ne : i + 1 ≠ 0 := by omega
      have hsucc_sub : i + 1 - 1 = i := by omega
      have hpred_succ : i - 1 + 1 = i := by omega
      have hword : startTime + i = (startTime + 1) + (i - 1) := by omega
      simpa [path', hi0, hsucc_ne, hsucc_sub, hword, hpred_succ] using
        hvalid (i - 1) hlt
  · omega
  · have hhit_ne : hit + 1 ≠ 0 := by omega
    have hhit_sub : hit + 1 - 1 = hit := by omega
    simpa [path', hhit_ne, hhit_sub] using haccepting

theorem segmentVisitsAccepting_append_left
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {source middle target : A.State}
    (hleft :
      SegmentVisitsAccepting A word startTime leftLength source middle)
    (hright :
      Segment A word (startTime + leftLength) rightLength middle target) :
    SegmentVisitsAccepting A word startTime (leftLength + rightLength)
      source target := by
  rcases hleft with
    ⟨leftPath, hleftSource, hleftMiddle, hleftValid, hit, hitle,
      haccepting⟩
  rcases hright with ⟨rightPath, hrightMiddle, hrightTarget, hrightValid⟩
  let path : Nat -> A.State :=
    fun i => if i ≤ leftLength then leftPath i else rightPath (i - leftLength)
  refine ⟨path, ?_, ?_, ?_, hit, ?_, ?_⟩
  · have hzero : 0 ≤ leftLength := Nat.zero_le _
    simp [path, hzero, hleftSource]
  · by_cases hrightZero : rightLength = 0
    · subst rightLength
      have hmiddleTarget : middle = target := by
        rw [← hrightMiddle, hrightTarget]
      simp [path, hleftMiddle, hmiddleTarget]
    · have hnot : ¬ leftLength + rightLength ≤ leftLength := by omega
      have hsub : leftLength + rightLength - leftLength = rightLength := by omega
      simp [path, hnot, hsub, hrightTarget]
  · intro i hi
    by_cases hlt : i < leftLength
    · have hi_le : i ≤ leftLength := Nat.le_of_lt hlt
      have hisucc_le : i + 1 ≤ leftLength := Nat.succ_le_of_lt hlt
      simpa [path, hi_le, hisucc_le] using hleftValid i hlt
    · by_cases heq : i = leftLength
      · subst i
        have hle : leftLength ≤ leftLength := le_rfl
        by_cases hrightZero : rightLength = 0
        · subst rightLength
          omega
        · have hnot_succ : ¬ leftLength + 1 ≤ leftLength := by omega
          have hsucc_sub : leftLength + 1 - leftLength = 1 := by omega
          have hrightStep :
              A.step middle (word (startTime + leftLength)) (rightPath 1) := by
            simpa [hrightMiddle] using hrightValid 0 (by omega)
          simpa [path, hle, hnot_succ, hsucc_sub, hleftMiddle] using
            hrightStep
      · have hi_not : ¬ i ≤ leftLength := by omega
        have hisucc_not : ¬ i + 1 ≤ leftLength := by omega
        have hidx_lt : i - leftLength < rightLength := by omega
        have hsucc_sub : i + 1 - leftLength = i - leftLength + 1 := by omega
        have hword :
            startTime + i =
              startTime + leftLength + (i - leftLength) := by omega
        simpa [path, hi_not, hisucc_not, hsucc_sub, hword] using
          hrightValid (i - leftLength) hidx_lt
  · omega
  · have hhit_le : hit ≤ leftLength := hitle
    simp [path, hhit_le, haccepting]

theorem segmentVisitsAccepting_append_right
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {source middle target : A.State}
    (hleft : Segment A word startTime leftLength source middle)
    (hright :
      SegmentVisitsAccepting A word (startTime + leftLength) rightLength
        middle target) :
    SegmentVisitsAccepting A word startTime (leftLength + rightLength)
      source target := by
  rcases hleft with ⟨leftPath, hleftSource, hleftMiddle, hleftValid⟩
  rcases hright with
    ⟨rightPath, hrightMiddle, hrightTarget, hrightValid, hit, hitle,
      haccepting⟩
  let path : Nat -> A.State :=
    fun i => if i ≤ leftLength then leftPath i else rightPath (i - leftLength)
  refine ⟨path, ?_, ?_, ?_, leftLength + hit, ?_, ?_⟩
  · have hzero : 0 ≤ leftLength := Nat.zero_le _
    simp [path, hzero, hleftSource]
  · by_cases hrightZero : rightLength = 0
    · subst rightLength
      have hmiddleTarget : middle = target := by
        rw [← hrightMiddle, hrightTarget]
      simp [path, hleftMiddle, hmiddleTarget]
    · have hnot : ¬ leftLength + rightLength ≤ leftLength := by omega
      have hsub : leftLength + rightLength - leftLength = rightLength := by omega
      simp [path, hnot, hsub, hrightTarget]
  · intro i hi
    by_cases hlt : i < leftLength
    · have hi_le : i ≤ leftLength := Nat.le_of_lt hlt
      have hisucc_le : i + 1 ≤ leftLength := Nat.succ_le_of_lt hlt
      simpa [path, hi_le, hisucc_le] using hleftValid i hlt
    · by_cases heq : i = leftLength
      · subst i
        have hle : leftLength ≤ leftLength := le_rfl
        by_cases hrightZero : rightLength = 0
        · subst rightLength
          omega
        · have hnot_succ : ¬ leftLength + 1 ≤ leftLength := by omega
          have hsucc_sub : leftLength + 1 - leftLength = 1 := by omega
          have hrightStep :
              A.step middle (word (startTime + leftLength)) (rightPath 1) := by
            simpa [hrightMiddle] using hrightValid 0 (by omega)
          simpa [path, hle, hnot_succ, hsucc_sub, hleftMiddle] using
            hrightStep
      · have hi_not : ¬ i ≤ leftLength := by omega
        have hisucc_not : ¬ i + 1 ≤ leftLength := by omega
        have hidx_lt : i - leftLength < rightLength := by omega
        have hsucc_sub : i + 1 - leftLength = i - leftLength + 1 := by omega
        have hword :
            startTime + i =
              startTime + leftLength + (i - leftLength) := by omega
        simpa [path, hi_not, hisucc_not, hsucc_sub, hword] using
          hrightValid (i - leftLength) hidx_lt
  · omega
  · by_cases hhitZero : hit = 0
    · subst hit
      have hle : leftLength + 0 ≤ leftLength := by omega
      have hmiddleAccepting : A.accepting middle := by
        simpa [hrightMiddle] using haccepting
      simp [path, hleftMiddle, hmiddleAccepting]
    · have hnot : ¬ leftLength + hit ≤ leftLength := by omega
      have hsub : leftLength + hit - leftLength = hit := by omega
      simpa [path, hnot, hsub] using haccepting

theorem segmentCover_of_pointwise
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources targets : Finset A.State}
    (hcover :
      ∀ target, target ∈ targets ->
        ∃ source, source ∈ sources ∧
          Segment A word startTime length source target) :
    SegmentCover A word startTime length sources targets :=
  hcover

theorem segmentCover_singleton
    [DecidableEq A.State]
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source target : A.State}
    (hsegment : Segment A word startTime length source target) :
    SegmentCover A word startTime length {source} {target} := by
  intro target' htarget'
  have htargetEq : target' = target := by
    simpa using htarget'
  subst target'
  exact ⟨source, by simp, hsegment⟩

theorem segmentCover_append
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      SegmentCover A word startTime leftLength sources middles)
    (hright :
      SegmentCover A word (startTime + leftLength) rightLength
        middles targets) :
    SegmentCover A word startTime (leftLength + rightLength)
      sources targets := by
  intro target htarget
  rcases hright target htarget with ⟨middle, hmiddle, hsegmentRight⟩
  rcases hleft middle hmiddle with ⟨source, hsource, hsegmentLeft⟩
  exact ⟨source, hsource,
    segment_append A word hsegmentLeft hsegmentRight⟩

theorem segmentCover_mono_targets
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources targets₁ targets₂ : Finset A.State}
    (hcover : SegmentCover A word startTime length sources targets₁)
    (hsubset : targets₂ ⊆ targets₁) :
    SegmentCover A word startTime length sources targets₂ := by
  intro target htarget
  exact hcover target (hsubset htarget)

theorem segmentCover_mono_sources
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources₁ sources₂ targets : Finset A.State}
    (hcover : SegmentCover A word startTime length sources₁ targets)
    (hsubset : sources₁ ⊆ sources₂) :
    SegmentCover A word startTime length sources₂ targets := by
  intro target htarget
  rcases hcover target htarget with ⟨source, hsource, hsegment⟩
  exact ⟨source, hsubset hsource, hsegment⟩

theorem segmentCover_mono
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources₁ sources₂ targets₁ targets₂ : Finset A.State}
    (hcover : SegmentCover A word startTime length sources₁ targets₁)
    (hsourceSubset : sources₁ ⊆ sources₂)
    (htargetSubset : targets₂ ⊆ targets₁) :
    SegmentCover A word startTime length sources₂ targets₂ :=
  segmentCover_mono_targets A word
    (segmentCover_mono_sources A word hcover hsourceSubset)
    htargetSubset

theorem segmentVisitsAcceptingCover_append_segmentCover_right
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      SegmentVisitsAcceptingCover A word startTime leftLength sources middles)
    (hright :
      SegmentCover A word (startTime + leftLength) rightLength
        middles targets) :
    SegmentVisitsAcceptingCover A word startTime (leftLength + rightLength)
      sources targets := by
  intro target htarget
  rcases hright target htarget with ⟨middle, hmiddle, hsegmentRight⟩
  rcases hleft middle hmiddle with
    ⟨source, hsource, hsegmentLeft⟩
  exact ⟨source, hsource,
    segmentVisitsAccepting_append_left A word hsegmentLeft hsegmentRight⟩

theorem segmentVisitsAcceptingCover_append_segmentCover_left
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      SegmentCover A word startTime leftLength sources middles)
    (hright :
      SegmentVisitsAcceptingCover A word (startTime + leftLength)
        rightLength middles targets) :
    SegmentVisitsAcceptingCover A word startTime (leftLength + rightLength)
      sources targets := by
  intro target htarget
  rcases hright target htarget with
    ⟨middle, hmiddle, hsegmentRight⟩
  rcases hleft middle hmiddle with ⟨source, hsource, hsegmentLeft⟩
  exact ⟨source, hsource,
    segmentVisitsAccepting_append_right A word hsegmentLeft hsegmentRight⟩

theorem segmentVisitsAcceptingCover_of_segmentCover_acceptingHead_segmentCover
    (word : OmegaWord Alphabet) {startTime prefixLength tailLength : Nat}
    {sources middles heads targets : Finset A.State}
    (hprefix :
      SegmentCover A word startTime prefixLength sources middles)
    (hhead :
      SegmentVisitsAcceptingCover A word (startTime + prefixLength) 1
        middles heads)
    (htail :
      SegmentCover A word (startTime + prefixLength + 1) tailLength
        heads targets) :
    SegmentVisitsAcceptingCover A word startTime
      (prefixLength + 1 + tailLength) sources targets := by
  have hprefixHead :
      SegmentVisitsAcceptingCover A word startTime (prefixLength + 1)
        sources heads := by
    simpa using
      segmentVisitsAcceptingCover_append_segmentCover_left A word
        hprefix hhead
  have hcombined :
      SegmentVisitsAcceptingCover A word startTime
        ((prefixLength + 1) + tailLength) sources targets :=
    segmentVisitsAcceptingCover_append_segmentCover_right A word
      hprefixHead htail
  simpa [Nat.add_assoc] using hcombined

theorem segmentVisitsAcceptingCover_of_pointwise
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources targets : Finset A.State}
    (hcover :
      ∀ target, target ∈ targets ->
        ∃ source, source ∈ sources ∧
          SegmentVisitsAccepting A word startTime length source target) :
    SegmentVisitsAcceptingCover A word startTime length sources targets :=
  hcover

theorem segmentVisitsAcceptingCover_singleton
    [DecidableEq A.State]
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source target : A.State}
    (hsegment :
      SegmentVisitsAccepting A word startTime length source target) :
    SegmentVisitsAcceptingCover A word startTime length {source} {target} := by
  intro target' htarget'
  have htargetEq : target' = target := by
    simpa using htarget'
  subst target'
  exact ⟨source, by simp, hsegment⟩

theorem segmentVisitsAcceptingCover_append_right
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      SegmentVisitsAcceptingCover A word startTime leftLength sources middles)
    (hright :
      ∀ target, target ∈ targets ->
        ∃ middle, middle ∈ middles ∧
          Segment A word (startTime + leftLength) rightLength middle target) :
    SegmentVisitsAcceptingCover A word startTime (leftLength + rightLength)
      sources targets := by
  intro target htarget
  rcases hright target htarget with ⟨middle, hmiddle, hsegmentRight⟩
  rcases hleft middle hmiddle with
    ⟨source, hsource, hsegmentLeft⟩
  exact ⟨source, hsource,
    segmentVisitsAccepting_append_left A word hsegmentLeft hsegmentRight⟩

theorem segmentVisitsAcceptingCover_append_left
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      ∀ middle, middle ∈ middles ->
        ∃ source, source ∈ sources ∧
          Segment A word startTime leftLength source middle)
    (hright :
      SegmentVisitsAcceptingCover A word (startTime + leftLength)
        rightLength middles targets) :
    SegmentVisitsAcceptingCover A word startTime (leftLength + rightLength)
      sources targets := by
  intro target htarget
  rcases hright target htarget with
    ⟨middle, hmiddle, hsegmentRight⟩
  rcases hleft middle hmiddle with ⟨source, hsource, hsegmentLeft⟩
  exact ⟨source, hsource,
    segmentVisitsAccepting_append_right A word hsegmentLeft hsegmentRight⟩

theorem segmentVisitsAcceptingCover_append
    (word : OmegaWord Alphabet) {startTime leftLength rightLength : Nat}
    {sources middles targets : Finset A.State}
    (hleft :
      SegmentVisitsAcceptingCover A word startTime leftLength sources middles)
    (hright :
      SegmentVisitsAcceptingCover A word (startTime + leftLength)
        rightLength middles targets) :
    SegmentVisitsAcceptingCover A word startTime (leftLength + rightLength)
      sources targets := by
  apply segmentVisitsAcceptingCover_append_right A word hleft
  intro target htarget
  rcases hright target htarget with ⟨middle, hmiddle, hsegmentRight⟩
  rcases hsegmentRight with
    ⟨path, hsource, htarget, hvalid, _hit, _hitle, _haccepting⟩
  exact ⟨middle, hmiddle, ⟨path, hsource, htarget, hvalid⟩⟩

theorem segmentVisitsAcceptingCover_mono_targets
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources targets₁ targets₂ : Finset A.State}
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources targets₁)
    (hsubset : targets₂ ⊆ targets₁) :
    SegmentVisitsAcceptingCover A word startTime length sources targets₂ := by
  intro target htarget
  exact hcover target (hsubset htarget)

theorem segmentVisitsAcceptingCover_mono_sources
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources₁ sources₂ targets : Finset A.State}
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources₁ targets)
    (hsubset : sources₁ ⊆ sources₂) :
    SegmentVisitsAcceptingCover A word startTime length sources₂ targets := by
  intro target htarget
  rcases hcover target htarget with ⟨source, hsource, hsegment⟩
  exact ⟨source, hsubset hsource, hsegment⟩

theorem segmentVisitsAcceptingCover_mono
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources₁ sources₂ targets₁ targets₂ : Finset A.State}
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources₁ targets₁)
    (hsourceSubset : sources₁ ⊆ sources₂)
    (htargetSubset : targets₂ ⊆ targets₁) :
    SegmentVisitsAcceptingCover A word startTime length sources₂ targets₂ :=
  segmentVisitsAcceptingCover_mono_targets A word
    (segmentVisitsAcceptingCover_mono_sources A word hcover hsourceSubset)
    htargetSubset

theorem segmentVisitsAccepting_to_segment
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {source target : A.State}
    (hsegment : SegmentVisitsAccepting A word startTime length source target) :
    Segment A word startTime length source target := by
  rcases hsegment with ⟨path, hsource, htarget, hstep, _haccepting⟩
  exact ⟨path, hsource, htarget, hstep⟩

theorem segmentCover_of_segmentVisitsAcceptingCover
    (word : OmegaWord Alphabet) {startTime length : Nat}
    {sources targets : Finset A.State}
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources targets) :
    SegmentCover A word startTime length sources targets := by
  intro target htarget
  rcases hcover target htarget with ⟨source, hsource, hsegment⟩
  exact ⟨source, hsource,
    segmentVisitsAccepting_to_segment A word hsegment⟩

theorem reachableAfter_of_segment
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {source target : A.State}
    (hreach : ReachableAfter A start word startTime source)
    (hsegment : Segment A word startTime length source target) :
    ReachableAfter A start word (startTime + length) target := by
  revert startTime source target
  induction length with
  | zero =>
      intro startTime source target hreach hsegment
      rcases hsegment with ⟨path, hsource, htarget, _hvalid⟩
      have htargetSource : target = source := by
        rw [← htarget, hsource]
      simpa [htargetSource] using hreach
  | succ length ih =>
      intro startTime source target hreach hsegment
      rcases hsegment with ⟨path, hsource, htarget, hvalid⟩
      let middle := path length
      have hprefix : Segment A word startTime length source middle := by
        exact ⟨path, hsource, rfl, by
          intro i hi
          exact hvalid i (Nat.lt_trans hi (Nat.lt_succ_self length))⟩
      have hreachMiddle :
          ReachableAfter A start word (startTime + length) middle :=
        ih hreach hprefix
      have hstep : A.step middle (word (startTime + length)) target := by
        have hlast := hvalid length (Nat.lt_succ_self length)
        simpa [middle, htarget] using hlast
      change ReachableAfter A start word ((startTime + length) + 1) target
      exact ⟨middle, hreachMiddle, hstep⟩

theorem reachableAfter_of_segmentVisitsAccepting
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {source target : A.State}
    (hreach : ReachableAfter A start word startTime source)
    (hsegment :
      SegmentVisitsAccepting A word startTime length source target) :
    ReachableAfter A start word (startTime + length) target :=
  reachableAfter_of_segment A start word hreach
    (segmentVisitsAccepting_to_segment A word hsegment)

theorem reachablePrefix_of_segment
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {source target : A.State}
    (hreach : ReachableAfter A start word startTime source)
    (hsegment : Segment A word startTime length source target) :
    ReachablePrefix A start word (startTime + length) target :=
  reachableAfter_to_prefix A start word
    (reachableAfter_of_segment A start word hreach hsegment)

theorem reachablePrefix_of_segmentVisitsAccepting
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {source target : A.State}
    (hreach : ReachableAfter A start word startTime source)
    (hsegment :
      SegmentVisitsAccepting A word startTime length source target) :
    ReachablePrefix A start word (startTime + length) target :=
  reachableAfter_to_prefix A start word
    (reachableAfter_of_segmentVisitsAccepting A start word hreach hsegment)

theorem reachableAfter_of_segmentVisitsAcceptingCover
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {sources targets : Finset A.State}
    (hsourceReach :
      ∀ source, source ∈ sources ->
        ReachableAfter A start word startTime source)
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources targets)
    {target : A.State}
    (htarget : target ∈ targets) :
    ∃ source,
      source ∈ sources ∧
        ReachableAfter A start word startTime source ∧
          SegmentVisitsAccepting A word startTime length source target ∧
            ReachableAfter A start word (startTime + length) target := by
  rcases hcover target htarget with ⟨source, hsource, hsegment⟩
  have hreachSource := hsourceReach source hsource
  exact ⟨source, hsource, hreachSource, hsegment,
    reachableAfter_of_segmentVisitsAccepting A start word hreachSource
      hsegment⟩

theorem reachablePrefix_of_segmentVisitsAcceptingCover
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {sources targets : Finset A.State}
    (hsourceReach :
      ∀ source, source ∈ sources ->
        ReachableAfter A start word startTime source)
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources targets)
    {target : A.State}
    (htarget : target ∈ targets) :
    ∃ source,
      source ∈ sources ∧
        ReachableAfter A start word startTime source ∧
          SegmentVisitsAccepting A word startTime length source target ∧
            ReachablePrefix A start word (startTime + length) target := by
  rcases reachableAfter_of_segmentVisitsAcceptingCover A start word
      hsourceReach hcover htarget with
    ⟨source, hsource, hreachSource, hsegment, hreachTarget⟩
  exact ⟨source, hsource, hreachSource, hsegment,
    reachableAfter_to_prefix A start word hreachTarget⟩

theorem exists_reachableAfter_of_segmentVisitsAcceptingCover_nonempty
    (start : A.State) (word : OmegaWord Alphabet)
    {startTime length : Nat} {sources targets : Finset A.State}
    (hsourceReach :
      ∀ source, source ∈ sources ->
        ReachableAfter A start word startTime source)
    (hcover :
      SegmentVisitsAcceptingCover A word startTime length sources targets)
    (htargets : targets.Nonempty) :
    ∃ source target,
      source ∈ sources ∧ target ∈ targets ∧
        ReachableAfter A start word startTime source ∧
          SegmentVisitsAccepting A word startTime length source target ∧
            ReachableAfter A start word (startTime + length) target := by
  rcases htargets with ⟨target, htarget⟩
  rcases reachableAfter_of_segmentVisitsAcceptingCover A start word
      hsourceReach hcover htarget with
    ⟨source, hsource, hreachSource, hsegment, hreachTarget⟩
  exact ⟨source, target, hsource, htarget, hreachSource, hsegment,
    hreachTarget⟩

theorem reachablePrefix_to_segmentVisitsAccepting_of_accepting_target
    (start : A.State) (word : OmegaWord Alphabet)
    {n : Nat} {target : A.State}
    (hprefix : ReachablePrefix A start word n target)
    (haccepting : A.accepting target) :
    SegmentVisitsAccepting A word 0 n start target :=
  segmentVisitsAccepting_of_segment_accepting_target A word
    (reachablePrefix_to_segment A start word hprefix) haccepting

/-- Piterman Section 3.2, transition stage (1): replace each label by successors. -/
noncomputable def stage1 [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) : CompactTreeData A where
  active := tree.active
  name := tree.name
  parent := tree.parent
  label node := stepImage A letter (tree.label node)
  e := sentinel A
  f := sentinel A

theorem mem_stage1_label [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    {node : Node A} {next : A.State} :
    next ∈ (stage1 A tree letter).label node ↔
      ∃ state, state ∈ tree.label node ∧ A.step state letter next := by
  exact mem_stepImage A

theorem stage1_label_segment
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat} {node : Node A} {next : A.State}
    (hnext : next ∈ (tree.stage1 A (word startTime)).label node) :
    ∃ state, state ∈ tree.label node ∧
      Segment A word startTime 1 state next := by
  rcases (mem_stage1_label A tree (word startTime)).mp hnext with
    ⟨state, hstate, hstep⟩
  exact ⟨state, hstate, segment_of_step A word hstep⟩

theorem stage1_active [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) (node : Node A) :
    (tree.stage1 A letter).active node = tree.active node := rfl

theorem stage1_name [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) (node : Node A) :
    (tree.stage1 A letter).name node = tree.name node := rfl

theorem stage1_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) (node : Node A) :
    (tree.stage1 A letter).parent node = tree.parent node := rfl

theorem stage1_children [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) (node : Node A) :
    (tree.stage1 A letter).children A node = tree.children A node := by
  simp [children, stage1]

theorem stage1_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State) :
    ∀ node, (tree.stage1 A letter).active node = true ->
      ((tree.stage1 A letter).name node).val < Fintype.card A.State := by
  intro node hactive
  exact hbound node (by simpa [stage1] using hactive)

theorem stage1_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage1 A letter).active left = true ->
      (tree.stage1 A letter).active right = true ->
      (tree.stage1 A letter).name left = (tree.stage1 A letter).name right ->
        left = right := by
  intro left right hleft hright hname
  exact hinjective left right
    (by simpa [stage1] using hleft)
    (by simpa [stage1] using hright)
    (by simpa [stage1] using hname)

theorem stage1_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage1 A letter).active node = false ->
      (tree.stage1 A letter).label node = ∅ := by
  intro node hactive
  have htree_inactive : tree.active node = false := by
    simpa [stage1] using hactive
  ext next
  constructor
  · intro hnext
    rw [mem_stage1_label A tree letter] at hnext
    rcases hnext with ⟨state, hstate, _hstep⟩
    rw [hinactiveLabel node htree_inactive] at hstate
    simp at hstate
  · intro hnext
    simp at hnext

theorem stage1_preserves_parent_active_and_name_lt [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val) :
    ∀ node,
      (tree.stage1 A letter).active node = true ->
      node ≠ root A ->
        (tree.stage1 A letter).active ((tree.stage1 A letter).parent node) = true ∧
          ((tree.stage1 A letter).name ((tree.stage1 A letter).parent node)).val <
            ((tree.stage1 A letter).name node).val := by
  intro node hactive hnot_root
  simpa [stage1] using
    hparentInvariant node (by simpa [stage1] using hactive) hnot_root

theorem stage1_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage1 A letter).children A node ->
      (tree.stage1 A letter).label child ⊆ (tree.stage1 A letter).label node := by
  intro node child hchild next hnext
  rw [mem_stage1_label A tree letter] at hnext
  rcases hnext with ⟨state, hstate, hstep⟩
  rw [stage1_children A tree letter node] at hchild
  rw [mem_stage1_label A tree letter]
  exact ⟨state, hchildSubset node child hchild hstate, hstep⟩

/-- The finite set of active nodes of a compact Safra tree. -/
def activeNodes (tree : CompactTreeData A) : Finset (Node A) :=
  Finset.univ.filter (fun node => tree.active node = true)

theorem mem_activeNodes (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.activeNodes A ↔ tree.active node = true := by
  simp [activeNodes]

theorem stage1_activeNodes [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) :
    (tree.stage1 A letter).activeNodes A = tree.activeNodes A := by
  simp [activeNodes, stage1]

theorem activeNodes_card_le_of_privateState_injective [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    (hinjective :
      ∀ left right
        (hleft : tree.active left = true)
        (hright : tree.active right = true),
        tree.privateStateOf A hproper left hleft =
          tree.privateStateOf A hproper right hright ->
            left = right) :
    (tree.activeNodes A).card ≤ Fintype.card A.State := by
  classical
  let toPrivate :
      { node // node ∈ tree.activeNodes A } -> A.State :=
    fun node =>
      tree.privateStateOf A hproper node.1
        ((mem_activeNodes A tree).mp node.2)
  have htoPrivate_injective : Function.Injective toPrivate := by
    intro left right hprivate
    apply Subtype.ext
    exact hinjective left.1 right.1
      ((mem_activeNodes A tree).mp left.2)
      ((mem_activeNodes A tree).mp right.2)
      hprivate
  have hcard :=
    Fintype.card_le_of_injective toPrivate htoPrivate_injective
  simpa [Fintype.card_coe] using hcard

/-- The accepting part of a node label, `S' ∩ α` in Piterman stage (2). -/
noncomputable def acceptingPart [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) : Finset A.State := by
  classical
  exact tree.label node |>.filter A.accepting

theorem mem_acceptingPart [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} {state : A.State} :
    state ∈ tree.acceptingPart A node ↔
      state ∈ tree.label node ∧ A.accepting state := by
  classical
  simp [acceptingPart]

/-- Nodes that trigger Piterman transition stage (2). -/
noncomputable def stage2Triggers [DecidableEq A.State]
    (tree : CompactTreeData A) : Finset (Node A) := by
  classical
  exact
    tree.activeNodes A |>.filter
      (fun node => (tree.acceptingPart A node).Nonempty)

theorem mem_stage2Triggers [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.stage2Triggers A ↔
      tree.active node = true ∧ (tree.acceptingPart A node).Nonempty := by
  classical
  simp [stage2Triggers, activeNodes]

theorem exists_accepting_label_of_stage2Trigger [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hnode : node ∈ tree.stage2Triggers A) :
    ∃ state, state ∈ tree.label node ∧ A.accepting state := by
  obtain ⟨_hactive, hnonempty⟩ := (mem_stage2Triggers A tree).mp hnode
  rcases hnonempty with ⟨state, hstate⟩
  exact ⟨state, (mem_acceptingPart A tree).mp hstate⟩

theorem mem_stage2Triggers_of_accepting_label [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A} {state : A.State}
    (hactive : tree.active node = true)
    (hstate : state ∈ tree.label node)
    (haccepting : A.accepting state) :
    node ∈ tree.stage2Triggers A := by
  rw [mem_stage2Triggers A tree]
  exact ⟨hactive, ⟨state,
    (mem_acceptingPart A tree).mpr ⟨hstate, haccepting⟩⟩⟩

/-- Inactive nodes available for temporary stage-2 allocation. -/
def inactiveNodes (tree : CompactTreeData A) : Finset (Node A) :=
  Finset.univ \ tree.activeNodes A

theorem mem_inactiveNodes (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.inactiveNodes A ↔ tree.active node = false := by
  rw [inactiveNodes, Finset.mem_sdiff, mem_activeNodes]
  cases tree.active node <;> simp

/-- Temporary high-name slot `n + i`, corresponding to paper names above all old names. -/
def highTempName (idx : Fin (Fintype.card A.State)) : TempName A := by
  refine ⟨Fintype.card A.State + idx.val, ?_⟩
  have hidx := idx.isLt
  have hcard_pos : 0 < Fintype.card A.State :=
    Fintype.card_pos_iff.mpr ⟨A.initial⟩
  omega

theorem highTempName_val_ge (idx : Fin (Fintype.card A.State)) :
    Fintype.card A.State ≤ (highTempName A idx).val := by
  simp [highTempName]

theorem highTempName_injective :
    Function.Injective (highTempName A) := by
  intro left right h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa [highTempName] using hval

theorem stage2Triggers_subset_activeNodes [DecidableEq A.State]
    (tree : CompactTreeData A) :
    tree.stage2Triggers A ⊆ tree.activeNodes A := by
  intro node hnode
  exact (mem_activeNodes A tree).mpr ((mem_stage2Triggers A tree).mp hnode).1

theorem stage2Triggers_card_le_activeNodes [DecidableEq A.State]
    (tree : CompactTreeData A) :
    (tree.stage2Triggers A).card ≤ (tree.activeNodes A).card :=
  Finset.card_le_card (stage2Triggers_subset_activeNodes A tree)

theorem activeNodes_card_le_of_name_bound_injective [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.activeNodes A).card ≤ Fintype.card A.State := by
  classical
  let toBoundedName : { node // node ∈ tree.activeNodes A } ->
      Fin (Fintype.card A.State) :=
    fun node => ⟨(tree.name node.1).val,
      hbound node.1 ((mem_activeNodes A tree).mp node.2)⟩
  have htoBoundedName_injective : Function.Injective toBoundedName := by
    intro left right heq
    apply Subtype.ext
    apply hinjective
    · exact (mem_activeNodes A tree).mp left.2
    · exact (mem_activeNodes A tree).mp right.2
    · have hval : (tree.name left.1).val = (tree.name right.1).val := by
        simpa [toBoundedName] using congrArg Fin.val heq
      exact Fin.ext hval
  have hcard :=
    Fintype.card_le_of_injective toBoundedName htoBoundedName_injective
  simpa [Fintype.card_coe] using hcard

theorem inactiveNodes_card [DecidableEq A.State]
    (tree : CompactTreeData A) :
    (tree.inactiveNodes A).card =
      2 * Fintype.card A.State - (tree.activeNodes A).card := by
  classical
  rw [inactiveNodes, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  simp [Node]

theorem stage2Triggers_card_le_inactiveNodes_of_active_card_le
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hactive_card : (tree.activeNodes A).card ≤ Fintype.card A.State) :
    (tree.stage2Triggers A).card ≤ (tree.inactiveNodes A).card := by
  classical
  have htrigger_active := stage2Triggers_card_le_activeNodes A tree
  have htrigger_card : (tree.stage2Triggers A).card ≤ Fintype.card A.State :=
    htrigger_active.trans hactive_card
  have hinactive := inactiveNodes_card A tree
  have hnode_pool : (tree.activeNodes A).card ≤ 2 * Fintype.card A.State := by
    omega
  omega

theorem active_name_lt_activeNodes_card_of_consecutive
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ node, tree.active node = true ->
      (tree.name node).val < (tree.activeNodes A).card := by
  classical
  intro node hnode_active
  let names : Finset Nat :=
    (tree.activeNodes A).image (fun node => (tree.name node).val)
  have hcard_names :
      names.card = (tree.activeNodes A).card := by
    exact Finset.card_image_of_injOn (s := tree.activeNodes A)
      (f := fun node => (tree.name node).val)
      (by
        intro left hleft right hright hname
        apply hinjective left right
        · exact (mem_activeNodes A tree).mp hleft
        · exact (mem_activeNodes A tree).mp hright
        · exact Fin.ext hname)
  have hnames_range :
      Finset.range ((tree.name node).val + 1) ⊆ names := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj_le : j ≤ (tree.name node).val := by omega
    by_cases heq : j = (tree.name node).val
    · change j ∈ (tree.activeNodes A).image (fun node => (tree.name node).val)
      rw [Finset.mem_image]
      exact ⟨node, (mem_activeNodes A tree).mpr hnode_active, heq.symm⟩
    · have hj_lt : j < (tree.name node).val := by omega
      have hnode_exists :
          ∃ old, tree.active old ∧ (tree.name old).val = (tree.name node).val :=
        ⟨node, hnode_active, rfl⟩
      obtain ⟨old, hold_active, hold_name⟩ :=
        hconsecutive (tree.name node).val (hbound node hnode_active)
          hnode_exists j hj_lt
      have hold_mem : old ∈ tree.activeNodes A :=
        (mem_activeNodes A tree).mpr hold_active
      change j ∈ (tree.activeNodes A).image (fun node => (tree.name node).val)
      rw [Finset.mem_image]
      exact ⟨old, hold_mem, hold_name⟩
  have hcard_range_le : (Finset.range ((tree.name node).val + 1)).card ≤ names.card :=
    Finset.card_le_card hnames_range
  simp only [Finset.card_range] at hcard_range_le
  rw [hcard_names] at hcard_range_le
  omega

theorem exists_active_name_eq_of_lt_activeNodes_card_of_consecutive
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ j : Nat, j < (tree.activeNodes A).card ->
      ∃ node, tree.active node = true ∧ (tree.name node).val = j := by
  classical
  intro j hj
  let names : Finset Nat :=
    (tree.activeNodes A).image (fun node => (tree.name node).val)
  have hcard_names :
      names.card = (tree.activeNodes A).card := by
    exact Finset.card_image_of_injOn (s := tree.activeNodes A)
      (f := fun node => (tree.name node).val)
      (by
        intro left hleft right hright hname
        apply hinjective left right
        · exact (mem_activeNodes A tree).mp hleft
        · exact (mem_activeNodes A tree).mp hright
        · exact Fin.ext hname)
  have hnames_subset :
      names ⊆ Finset.range (tree.activeNodes A).card := by
    intro value hvalue
    rw [Finset.mem_range]
    change value ∈ (tree.activeNodes A).image
      (fun node => (tree.name node).val) at hvalue
    rw [Finset.mem_image] at hvalue
    rcases hvalue with ⟨node, hnode, hvalue⟩
    rw [← hvalue]
    exact active_name_lt_activeNodes_card_of_consecutive A tree
      hbound hinjective hconsecutive node
      ((mem_activeNodes A tree).mp hnode)
  by_contra hmissing
  have hj_range : j ∈ Finset.range (tree.activeNodes A).card := by
    rw [Finset.mem_range]
    exact hj
  have hnames_subset_erase :
      names ⊆ (Finset.range (tree.activeNodes A).card).erase j := by
    intro value hvalue
    rw [Finset.mem_erase]
    constructor
    · intro hvalue_eq
      change value ∈ (tree.activeNodes A).image
        (fun node => (tree.name node).val) at hvalue
      rw [Finset.mem_image] at hvalue
      rcases hvalue with ⟨node, hnode, hname⟩
      exact hmissing ⟨node, (mem_activeNodes A tree).mp hnode, hname.trans hvalue_eq⟩
    · exact hnames_subset hvalue
  have hcard_le :
      names.card ≤ ((Finset.range (tree.activeNodes A).card).erase j).card :=
    Finset.card_le_card hnames_subset_erase
  have herase_card :
      ((Finset.range (tree.activeNodes A).card).erase j).card =
        (tree.activeNodes A).card - 1 :=
    by simpa using Finset.card_erase_of_mem hj_range
  rw [herase_card, hcard_names] at hcard_le
  omega

theorem exists_active_name_eq_of_lt_activeNodes_card_of_bounded_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hnameLtCard :
      ∀ node, tree.active node = true ->
        (tree.name node).val < (tree.activeNodes A).card) :
    ∀ j : Nat, j < (tree.activeNodes A).card ->
      ∃ node, tree.active node = true ∧ (tree.name node).val = j := by
  classical
  intro j hj
  let names : Finset Nat :=
    (tree.activeNodes A).image (fun node => (tree.name node).val)
  have hcard_names :
      names.card = (tree.activeNodes A).card := by
    exact Finset.card_image_of_injOn (s := tree.activeNodes A)
      (f := fun node => (tree.name node).val)
      (by
        intro left hleft right hright hname
        apply hinjective left right
        · exact (mem_activeNodes A tree).mp hleft
        · exact (mem_activeNodes A tree).mp hright
        · exact Fin.ext hname)
  have hnames_subset :
      names ⊆ Finset.range (tree.activeNodes A).card := by
    intro value hvalue
    rw [Finset.mem_range]
    change value ∈ (tree.activeNodes A).image
      (fun node => (tree.name node).val) at hvalue
    rw [Finset.mem_image] at hvalue
    rcases hvalue with ⟨node, hnode, hvalue⟩
    rw [← hvalue]
    exact hnameLtCard node ((mem_activeNodes A tree).mp hnode)
  by_contra hmissing
  have hj_range : j ∈ Finset.range (tree.activeNodes A).card := by
    rw [Finset.mem_range]
    exact hj
  have hnames_subset_erase :
      names ⊆ (Finset.range (tree.activeNodes A).card).erase j := by
    intro value hvalue
    rw [Finset.mem_erase]
    constructor
    · intro hvalue_eq
      change value ∈ (tree.activeNodes A).image
        (fun node => (tree.name node).val) at hvalue
      rw [Finset.mem_image] at hvalue
      rcases hvalue with ⟨node, hnode, hname⟩
      exact hmissing ⟨node, (mem_activeNodes A tree).mp hnode,
        hname.trans hvalue_eq⟩
    · exact hnames_subset hvalue
  have hcard_le :
      names.card ≤ ((Finset.range (tree.activeNodes A).card).erase j).card :=
    Finset.card_le_card hnames_subset_erase
  have herase_card :
      ((Finset.range (tree.activeNodes A).card).erase j).card =
        (tree.activeNodes A).card - 1 :=
    by simpa using Finset.card_erase_of_mem hj_range
  rw [herase_card, hcard_names] at hcard_le
  omega

/--
Local fresh-node allocation data for Piterman transition stage (2).

The paper says to create one fresh son for each active node whose label
intersects the Buchi accepting set.  This record isolates the finite allocation
part.  A later lemma should construct it from `WellFormed`, using the fact that
there are at most `n` active nodes and the temporary node pool has size `2n`.
-/
structure Stage2Plan [DecidableEq A.State] (tree : CompactTreeData A) where
  freshChild : Node A -> Node A
  freshName : Node A -> TempName A
  fresh_inactive :
    ∀ node, node ∈ tree.stage2Triggers A ->
      tree.active (freshChild node) = false
  fresh_injective :
    ∀ left right,
      left ∈ tree.stage2Triggers A ->
      right ∈ tree.stage2Triggers A ->
      freshChild left = freshChild right ->
        left = right
  fresh_name_gt_used :
    ∀ node old,
      node ∈ tree.stage2Triggers A ->
      old ∈ tree.activeNodes A ->
        (tree.name old).val < (freshName node).val
  fresh_name_ge_active_card :
    ∀ node,
      node ∈ tree.stage2Triggers A ->
        (tree.activeNodes A).card ≤ (freshName node).val
  fresh_name_lt_active_plus_triggers :
    ∀ node,
      node ∈ tree.stage2Triggers A ->
        (freshName node).val <
          (tree.activeNodes A).card + (tree.stage2Triggers A).card
  fresh_name_covers_interval :
    ∀ idx : Nat, idx < (tree.stage2Triggers A).card ->
      ∃ node, node ∈ tree.stage2Triggers A ∧
        (freshName node).val = (tree.activeNodes A).card + idx
  fresh_name_injective :
    ∀ left right,
      left ∈ tree.stage2Triggers A ->
      right ∈ tree.stage2Triggers A ->
      freshName left = freshName right ->
        left = right

theorem exists_stage2Plan_of_active_name_bound_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    Nonempty (Stage2Plan A tree) := by
  classical
  let Trigger := { node : Node A // node ∈ tree.stage2Triggers A }
  have hactive_card :
      (tree.activeNodes A).card ≤ Fintype.card A.State :=
    activeNodes_card_le_of_name_bound_injective A tree hbound hinjective
  have htriggers_inactive :
      (tree.stage2Triggers A).card ≤ (tree.inactiveNodes A).card :=
    stage2Triggers_card_le_inactiveNodes_of_active_card_le A tree hactive_card
  have htriggers_inactive_fintype :
      Fintype.card Trigger ≤ (tree.inactiveNodes A).card := by
    simpa [Trigger, Fintype.card_coe] using htriggers_inactive
  obtain ⟨freshChildEmb, hfreshChild_range⟩ :
      ∃ f : Trigger ↪ Node A, Set.range f ⊆ tree.inactiveNodes A :=
    Function.Embedding.exists_of_card_le_finset htriggers_inactive_fintype
  have htriggers_names :
      (tree.stage2Triggers A).card ≤ Fintype.card A.State :=
    (stage2Triggers_card_le_activeNodes A tree).trans hactive_card
  have htriggers_names_fintype :
      Fintype.card Trigger ≤ Fintype.card (Fin (Fintype.card A.State)) := by
    simpa [Trigger, Fintype.card_coe]
      using htriggers_names
  let freshNameIndex : Trigger ≃ Fin (Fintype.card Trigger) :=
    Fintype.equivFin Trigger
  let freshChild : Node A -> Node A :=
    fun node =>
      if hnode : node ∈ tree.stage2Triggers A then
        freshChildEmb ⟨node, hnode⟩
      else
        root A
  let freshName : Node A -> TempName A :=
    fun node =>
      if hnode : node ∈ tree.stage2Triggers A then
        let idx := freshNameIndex ⟨node, hnode⟩
        ⟨(tree.activeNodes A).card + idx.val, by
          have hidx : idx.val < (tree.stage2Triggers A).card := by
            simpa [Trigger, Fintype.card_coe] using idx.isLt
          have htrigger_active := stage2Triggers_card_le_activeNodes A tree
          omega⟩
      else
        root A
  refine ⟨{
    freshChild := freshChild
    freshName := freshName
    fresh_inactive := ?_
    fresh_injective := ?_
    fresh_name_gt_used := ?_
    fresh_name_ge_active_card := ?_
    fresh_name_lt_active_plus_triggers := ?_
    fresh_name_covers_interval := ?_
    fresh_name_injective := ?_
  }⟩
  · intro node hnode
    have hmem : freshChild node ∈ tree.inactiveNodes A := by
      have hrange : freshChild node ∈ Set.range freshChildEmb := by
        refine ⟨⟨node, hnode⟩, ?_⟩
        simp [freshChild, hnode]
      exact hfreshChild_range hrange
    exact (mem_inactiveNodes A tree).mp hmem
  · intro left right hleft hright hchild
    have hsub :
        (⟨left, hleft⟩ : Trigger) = ⟨right, hright⟩ := by
      apply freshChildEmb.injective
      simpa [freshChild, hleft, hright] using hchild
    exact congrArg Subtype.val hsub
  · intro node old hnode hold
    have hold_active : tree.active old = true :=
      (mem_activeNodes A tree).mp hold
    have hold_lt_active_card :
        (tree.name old).val < (tree.activeNodes A).card :=
      active_name_lt_activeNodes_card_of_consecutive A tree
        hbound hinjective hconsecutive old hold_active
    have hfresh_ge :
        (tree.activeNodes A).card ≤ (freshName node).val := by
      simp [freshName, hnode]
    omega
  · intro node hnode
    simp [freshName, hnode]
  · intro node hnode
    have hidx :
        (freshNameIndex ⟨node, hnode⟩).val <
          (tree.stage2Triggers A).card := by
      simpa [Trigger, Fintype.card_coe]
        using (freshNameIndex ⟨node, hnode⟩).isLt
    simp [freshName, hnode]
    omega
  · intro idx hidx
    let finIdx : Fin (Fintype.card Trigger) := ⟨idx, by
      simpa [Trigger, Fintype.card_coe] using hidx⟩
    obtain ⟨trigger, htrigger⟩ := freshNameIndex.surjective finIdx
    refine ⟨trigger.1, trigger.2, ?_⟩
    have hval := congrArg Fin.val htrigger
    simp [freshName, trigger.2, finIdx] at hval ⊢
    omega
  · intro left right hleft hright hname
    have hsub :
        (⟨left, hleft⟩ : Trigger) = ⟨right, hright⟩ := by
      apply freshNameIndex.injective
      apply Fin.ext
      have hval := congrArg Fin.val hname
      simpa [freshName, hleft, hright] using hval
    exact congrArg Subtype.val hsub

theorem exists_stage2Plan_of_wellFormed
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (htree : tree.WellFormed A) :
    Nonempty (Stage2Plan A tree) := by
  rcases htree with
    ⟨_, _, _, _, _, hbound, hinjective, hconsecutive, _, _, _⟩
  exact
    exists_stage2Plan_of_active_name_bound_injective A tree
      (by
        intro node hnode
        exact hbound node hnode)
      (by
        intro left right hleft hright hname
        exact hinjective left right hleft hright hname)
      (by
        intro k hk hexists j hj
        exact hconsecutive k hk hexists j hj)

namespace Stage2Plan

variable [DecidableEq A.State]

/-- The stage-2 parent that owns a newly allocated child, if any. -/
noncomputable def ownerOf
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree) (node : Node A) : Option (Node A) := by
  classical
  by_cases h : ∃ parent,
      parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node
  · exact some (Classical.choose h)
  · exact none

theorem ownerOf_eq_some_of_freshChild
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    plan.ownerOf A (plan.freshChild parent) = some parent := by
  classical
  have hExists : ∃ owner : Node A,
      owner ∈ tree.stage2Triggers A ∧ plan.freshChild owner = plan.freshChild parent :=
    ⟨parent, hparent, rfl⟩
  unfold ownerOf
  simp only [dif_pos hExists]
  apply congrArg some
  exact
    plan.fresh_injective
      (Classical.choose hExists)
      parent
      (Classical.choose_spec hExists).1
      hparent
      (Classical.choose_spec hExists).2

theorem ownerOf_eq_some_spec
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree)
    {node parent : Node A}
    (howner : plan.ownerOf A node = some parent) :
    parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node := by
  classical
  unfold ownerOf at howner
  by_cases h : ∃ owner,
      owner ∈ tree.stage2Triggers A ∧ plan.freshChild owner = node
  · simp only [dif_pos h] at howner
    have hchoose : Classical.choose h = parent := Option.some.inj howner
    simpa [hchoose] using (Classical.choose_spec h)
  · simp [dif_neg h] at howner

theorem ownerOf_freshChild_isSome
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (plan.ownerOf A (plan.freshChild parent)).isSome = true := by
  rw [ownerOf_eq_some_of_freshChild A plan hparent]
  rfl

theorem ownerOf_eq_none_iff
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree)
    {node : Node A} :
    plan.ownerOf A node = none ↔
      ∀ parent, parent ∈ tree.stage2Triggers A ->
        plan.freshChild parent ≠ node := by
  classical
  unfold ownerOf
  by_cases h : ∃ parent,
      parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node
  · rcases h with ⟨parent, hparent, hchild⟩
    have hExists : ∃ owner : Node A,
        owner ∈ tree.stage2Triggers A ∧ plan.freshChild owner = node :=
      ⟨parent, hparent, hchild⟩
    have hnotall :
        ¬ (∀ parent, parent ∈ tree.stage2Triggers A ->
          plan.freshChild parent ≠ node) := by
      intro hall
      exact hall parent hparent hchild
    simp [dif_pos hExists, hnotall]
  · simp only [dif_neg h, true_iff]
    intro parent hparent hchild
    exact h ⟨parent, hparent, hchild⟩

theorem ownerOf_eq_none_of_active
    {tree : CompactTreeData A}
    (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    plan.ownerOf A node = none := by
  rw [ownerOf_eq_none_iff A plan]
  intro parent hparent hchild
  have hinactive := plan.fresh_inactive parent hparent
  rw [hchild] at hinactive
  simp [hactive] at hinactive

end Stage2Plan

/--
Piterman Section 3.2, transition stage (2): for every active node whose label
intersects the Buchi accepting set, create a fresh child labeled by that
intersection and named above all old names.
-/
noncomputable def stage2 [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree) :
    CompactTreeData A where
  active node :=
    if (plan.ownerOf A node).isSome then true else tree.active node
  name node :=
    match plan.ownerOf A node with
    | some parent => plan.freshName parent
    | none => tree.name node
  parent node :=
    match plan.ownerOf A node with
    | some parent => parent
    | none => tree.parent node
  label node :=
    match plan.ownerOf A node with
    | some parent => tree.acceptingPart A parent
    | none => tree.label node
  e := sentinel A
  f := sentinel A

theorem stage2_freshChild_active [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.stage2 A plan).active (plan.freshChild parent) = true := by
  simp [stage2, Stage2Plan.ownerOf_freshChild_isSome A plan hparent]

theorem stage2_freshChild_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.stage2 A plan).parent (plan.freshChild parent) = parent := by
  simp [stage2, Stage2Plan.ownerOf_eq_some_of_freshChild A plan hparent]

theorem stage2_freshChild_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.stage2 A plan).name (plan.freshChild parent) =
      plan.freshName parent := by
  simp [stage2, Stage2Plan.ownerOf_eq_some_of_freshChild A plan hparent]

theorem stage2_freshChild_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.stage2 A plan).label (plan.freshChild parent) =
      tree.acceptingPart A parent := by
  simp [stage2, Stage2Plan.ownerOf_eq_some_of_freshChild A plan hparent]

theorem stage2_freshChild_label_nonempty [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    ((tree.stage2 A plan).label (plan.freshChild parent)).Nonempty := by
  rw [stage2_freshChild_label A tree plan hparent]
  exact (mem_stage2Triggers A tree).mp hparent |>.2

theorem mem_stage2_freshChild_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State} :
    state ∈ (tree.stage2 A plan).label (plan.freshChild parent) ↔
      state ∈ tree.label parent ∧ A.accepting state := by
  rw [stage2_freshChild_label A tree plan hparent]
  exact mem_acceptingPart A tree

theorem stage2_freshChild_label_accepting [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ (tree.stage2 A plan).label (plan.freshChild parent)) :
    A.accepting state :=
  (mem_stage2_freshChild_label A tree plan hparent).mp hstate |>.2

theorem stage2_freshChild_label_mem_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ (tree.stage2 A plan).label (plan.freshChild parent)) :
    state ∈ tree.label parent :=
  (mem_stage2_freshChild_label A tree plan hparent).mp hstate |>.1

theorem stage2_old_active [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (howner : plan.ownerOf A node = none) :
    (tree.stage2 A plan).active node = tree.active node := by
  simp [stage2, howner]

theorem stage2_old_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (howner : plan.ownerOf A node = none) :
    (tree.stage2 A plan).name node = tree.name node := by
  simp [stage2, howner]

theorem stage2_old_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (howner : plan.ownerOf A node = none) :
    (tree.stage2 A plan).parent node = tree.parent node := by
  simp [stage2, howner]

theorem stage2_old_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (howner : plan.ownerOf A node = none) :
    (tree.stage2 A plan).label node = tree.label node := by
  simp [stage2, howner]

theorem stage2_active_old_owner_none [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    plan.ownerOf A node = none :=
  Stage2Plan.ownerOf_eq_none_of_active A plan hactive

theorem stage2_preserves_active_node_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    (tree.stage2 A plan).name node = tree.name node := by
  exact stage2_old_name A tree plan
    (stage2_active_old_owner_none A tree plan hactive)

theorem stage2_preserves_active_node_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    (tree.stage2 A plan).parent node = tree.parent node := by
  exact stage2_old_parent A tree plan
    (stage2_active_old_owner_none A tree plan hactive)

theorem stage2_preserves_active_node_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    (tree.stage2 A plan).label node = tree.label node := by
  exact stage2_old_label A tree plan
    (stage2_active_old_owner_none A tree plan hactive)

theorem stage2_preserves_active_node_active [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : tree.active node = true) :
    (tree.stage2 A plan).active node = true := by
  rw [stage2_old_active A tree plan
    (stage2_active_old_owner_none A tree plan hactive)]
  exact hactive

theorem stage2_root_active [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot : tree.active (root A) = true) :
    (tree.stage2 A plan).active (root A) = true :=
  stage2_preserves_active_node_active A tree plan hroot

theorem stage2_root_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot : tree.active (root A) = true) :
    (tree.stage2 A plan).name (root A) = tree.name (root A) :=
  stage2_preserves_active_node_name A tree plan hroot

theorem stage2_root_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot : tree.active (root A) = true) :
    (tree.stage2 A plan).parent (root A) = tree.parent (root A) :=
  stage2_preserves_active_node_parent A tree plan hroot

theorem stage2_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage2 A plan).active node = false ->
      (tree.stage2 A plan).label node = ∅ := by
  intro node hactive
  cases howner : plan.ownerOf A node with
  | none =>
      have htree_inactive : tree.active node = false := by
        rw [stage2_old_active A tree plan howner] at hactive
        exact hactive
      rw [stage2_old_label A tree plan howner]
      exact hinactiveLabel node htree_inactive
  | some parent =>
      have hstage_active : (tree.stage2 A plan).active node = true := by
        simp [stage2, howner]
      simp [hstage_active] at hactive

theorem stage2_freshChild_not_active_old [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent old : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (hold : old ∈ tree.activeNodes A) :
    plan.freshChild parent ≠ old := by
  intro h
  have hfresh_inactive := plan.fresh_inactive parent hparent
  have hold_active := (mem_activeNodes A tree).mp hold
  rw [h] at hfresh_inactive
  simp [hold_active] at hfresh_inactive

theorem stage2_freshChild_ne_root [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot_active : tree.active (root A) = true)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    plan.freshChild parent ≠ root A := by
  exact stage2_freshChild_not_active_old A tree plan hparent
    ((mem_activeNodes A tree).mpr hroot_active)

theorem stage2_fresh_name_gt_active_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent old : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (hold : tree.active old = true) :
    (tree.name old).val < (plan.freshName parent).val := by
  exact plan.fresh_name_gt_used parent old hparent
    ((mem_activeNodes A tree).mpr hold)

theorem stage2_fresh_name_ge_active_card [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.activeNodes A).card ≤ (plan.freshName parent).val :=
  plan.fresh_name_ge_active_card parent hparent

theorem stage2_fresh_name_lt_active_plus_triggers [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (plan.freshName parent).val <
      (tree.activeNodes A).card + (tree.stage2Triggers A).card :=
  plan.fresh_name_lt_active_plus_triggers parent hparent

theorem stage2_fresh_name_covers_interval [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {idx : Nat}
    (hidx : idx < (tree.stage2Triggers A).card) :
    ∃ parent, parent ∈ tree.stage2Triggers A ∧
      (plan.freshName parent).val = (tree.activeNodes A).card + idx :=
  plan.fresh_name_covers_interval idx hidx

theorem stage2_fresh_name_gt_root_name [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot_active : tree.active (root A) = true)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    (tree.name (root A)).val < (plan.freshName parent).val := by
  exact stage2_fresh_name_gt_active_name A tree plan hparent hroot_active

theorem stage2_freshName_injective_on_triggers [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {left right : Node A}
    (hleft : left ∈ tree.stage2Triggers A)
    (hright : right ∈ tree.stage2Triggers A)
    (hname : plan.freshName left = plan.freshName right) :
    left = right :=
  plan.fresh_name_injective left right hleft hright hname

theorem stage2_active_cases [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : (tree.stage2 A plan).active node = true) :
    tree.active node = true ∨
      ∃ parent, parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node := by
  classical
  by_cases howner : ∃ parent,
      parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node
  · exact Or.inr howner
  · have hnone : plan.ownerOf A node = none := by
      rw [Stage2Plan.ownerOf_eq_none_iff A plan]
      intro parent hparent hchild
      exact howner ⟨parent, hparent, hchild⟩
    left
    simpa [stage2, hnone] using hactive

theorem stage2_fresh_active_cases [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A}
    (hactive : (tree.stage2 A plan).active node = true)
    (hnot_old : tree.active node ≠ true) :
    ∃ parent, parent ∈ tree.stage2Triggers A ∧ plan.freshChild parent = node := by
  rcases stage2_active_cases A tree plan hactive with hold | hfresh
  · exact (hnot_old hold).elim
  · exact hfresh

theorem stage2_active_label_mem_source_label [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A} {state : A.State}
    (hactive : (tree.stage2 A plan).active node = true)
    (hstate : state ∈ (tree.stage2 A plan).label node) :
    ∃ source, tree.active source = true ∧ state ∈ tree.label source := by
  rcases stage2_active_cases A tree plan hactive with hold | hfresh
  · refine ⟨node, hold, ?_⟩
    rwa [stage2_preserves_active_node_label A tree plan hold] at hstate
  · rcases hfresh with ⟨parent, hparent, hfresh⟩
    subst hfresh
    have hparent_active : tree.active parent = true :=
      (mem_stage2Triggers A tree).mp hparent |>.1
    refine ⟨parent, hparent_active, ?_⟩
    exact stage2_freshChild_label_mem_parent A tree plan hparent hstate

theorem stage2_active_label_mem_source_label_name_le
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node : Node A} {state : A.State}
    (hactive : (tree.stage2 A plan).active node = true)
    (hstate : state ∈ (tree.stage2 A plan).label node) :
    ∃ source,
      tree.active source = true ∧
        state ∈ tree.label source ∧
        (tree.name source).val ≤ ((tree.stage2 A plan).name node).val := by
  rcases stage2_active_cases A tree plan hactive with hold | hfresh
  · refine ⟨node, hold, ?_, ?_⟩
    · rwa [stage2_preserves_active_node_label A tree plan hold] at hstate
    · rw [stage2_preserves_active_node_name A tree plan hold]
  · rcases hfresh with ⟨parent, hparent, hfresh⟩
    subst hfresh
    have hparent_active : tree.active parent = true :=
      (mem_stage2Triggers A tree).mp hparent |>.1
    refine ⟨parent, hparent_active, ?_, ?_⟩
    · exact stage2_freshChild_label_mem_parent A tree plan hparent hstate
    · rw [stage2_freshChild_name A tree plan hparent]
      exact Nat.le_of_lt
        (stage2_fresh_name_gt_active_name A tree plan hparent
          hparent_active)

theorem stage1_stage2_active_label_segment_from_source
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat}
    (plan : Stage2Plan A (tree.stage1 A (word startTime)))
    {node : Node A} {state : A.State}
    (hactive :
      ((tree.stage1 A (word startTime)).stage2 A plan).active node = true)
    (hstate :
      state ∈ ((tree.stage1 A (word startTime)).stage2 A plan).label node) :
    ∃ sourceNode sourceState,
      tree.active sourceNode = true ∧
        sourceState ∈ tree.label sourceNode ∧
          Segment A word startTime 1 sourceState state := by
  rcases stage2_active_label_mem_source_label A
      (tree.stage1 A (word startTime)) plan hactive hstate with
    ⟨sourceNode, hsourceActiveStage1, hstateStage1⟩
  rcases stage1_label_segment A tree word hstateStage1 with
    ⟨sourceState, hsourceState, hsegment⟩
  exact ⟨sourceNode, sourceState,
    by simpa [stage1] using hsourceActiveStage1, hsourceState, hsegment⟩

theorem stage1_stage2_active_label_segment_from_source_name_le
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat}
    (plan : Stage2Plan A (tree.stage1 A (word startTime)))
    {node : Node A} {state : A.State}
    (hactive :
      ((tree.stage1 A (word startTime)).stage2 A plan).active node = true)
    (hstate :
      state ∈ ((tree.stage1 A (word startTime)).stage2 A plan).label node) :
    ∃ sourceNode sourceState,
      tree.active sourceNode = true ∧
        sourceState ∈ tree.label sourceNode ∧
          Segment A word startTime 1 sourceState state ∧
            (tree.name sourceNode).val ≤
              (((tree.stage1 A (word startTime)).stage2 A plan).name node).val := by
  rcases stage2_active_label_mem_source_label_name_le A
      (tree.stage1 A (word startTime)) plan hactive hstate with
    ⟨sourceNode, hsourceActiveStage1, hstateStage1, hnameLe⟩
  rcases stage1_label_segment A tree word hstateStage1 with
    ⟨sourceState, hsourceState, hsegment⟩
  refine ⟨sourceNode, sourceState,
    by simpa [stage1] using hsourceActiveStage1, hsourceState, hsegment,
    ?_⟩
  simpa [stage1] using hnameLe

theorem stage2_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage2 A plan).active left = true ->
      (tree.stage2 A plan).active right = true ->
      (tree.stage2 A plan).name left = (tree.stage2 A plan).name right ->
        left = right := by
  intro left right hleft_active hright_active hname
  rcases stage2_active_cases A tree plan hleft_active with hleft_old | hleft_fresh
  · rcases stage2_active_cases A tree plan hright_active with hright_old | hright_fresh
    · apply hinjective left right hleft_old hright_old
      rw [stage2_preserves_active_node_name A tree plan hleft_old] at hname
      rw [stage2_preserves_active_node_name A tree plan hright_old] at hname
      exact hname
    · rcases hright_fresh with ⟨rightParent, hrightParent, hright_eq⟩
      rw [stage2_preserves_active_node_name A tree plan hleft_old] at hname
      rw [← hright_eq] at hname
      rw [stage2_freshChild_name A tree plan hrightParent] at hname
      have hlt := stage2_fresh_name_gt_active_name A tree plan hrightParent hleft_old
      have hval := congrArg Fin.val hname
      omega
  · rcases hleft_fresh with ⟨leftParent, hleftParent, hleft_eq⟩
    rcases stage2_active_cases A tree plan hright_active with hright_old | hright_fresh
    · rw [← hleft_eq] at hname
      rw [stage2_freshChild_name A tree plan hleftParent] at hname
      rw [stage2_preserves_active_node_name A tree plan hright_old] at hname
      have hlt := stage2_fresh_name_gt_active_name A tree plan hleftParent hright_old
      have hval := congrArg Fin.val hname
      omega
    · rcases hright_fresh with ⟨rightParent, hrightParent, hright_eq⟩
      rw [← hleft_eq] at hname
      rw [← hright_eq] at hname
      rw [stage2_freshChild_name A tree plan hleftParent] at hname
      rw [stage2_freshChild_name A tree plan hrightParent] at hname
      have hparents :
          leftParent = rightParent :=
        stage2_freshName_injective_on_triggers A tree plan
          hleftParent hrightParent hname
      calc
        left = plan.freshChild leftParent := hleft_eq.symm
        _ = plan.freshChild rightParent := by rw [hparents]
        _ = right := hright_eq

theorem stage2_active_name_lt_active_plus_triggers
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ node, (tree.stage2 A plan).active node = true ->
      ((tree.stage2 A plan).name node).val <
        (tree.activeNodes A).card + (tree.stage2Triggers A).card := by
  intro node hactive
  rcases stage2_active_cases A tree plan hactive with hold | hfresh
  · rw [stage2_preserves_active_node_name A tree plan hold]
    have hlt :=
      active_name_lt_activeNodes_card_of_consecutive A tree
        hbound hinjective hconsecutive node hold
    omega
  · rcases hfresh with ⟨parent, hparent, hnode⟩
    rw [← hnode]
    rw [stage2_freshChild_name A tree plan hparent]
    exact stage2_fresh_name_lt_active_plus_triggers A tree plan hparent

theorem stage2_exists_active_name_eq_of_lt_active_plus_triggers
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ j : Nat, j < (tree.activeNodes A).card + (tree.stage2Triggers A).card ->
      ∃ node, (tree.stage2 A plan).active node = true ∧
        ((tree.stage2 A plan).name node).val = j := by
  intro j hj
  by_cases hold : j < (tree.activeNodes A).card
  · obtain ⟨node, hactive, hname⟩ :=
      exists_active_name_eq_of_lt_activeNodes_card_of_consecutive A tree
        hbound hinjective hconsecutive j hold
    refine ⟨node, stage2_preserves_active_node_active A tree plan hactive, ?_⟩
    rw [stage2_preserves_active_node_name A tree plan hactive]
    exact hname
  · have hidx : j - (tree.activeNodes A).card <
        (tree.stage2Triggers A).card := by
      omega
    obtain ⟨parent, hparent, hname⟩ :=
      stage2_fresh_name_covers_interval A tree plan hidx
    refine ⟨plan.freshChild parent,
      stage2_freshChild_active A tree plan hparent, ?_⟩
    rw [stage2_freshChild_name A tree plan hparent]
    have hge : (tree.activeNodes A).card ≤ j := by omega
    omega

theorem stage2_preserves_parent_active_and_name_lt [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val) :
    ∀ node,
      (tree.stage2 A plan).active node = true ->
      node ≠ root A ->
        (tree.stage2 A plan).active ((tree.stage2 A plan).parent node) = true ∧
          ((tree.stage2 A plan).name ((tree.stage2 A plan).parent node)).val <
            ((tree.stage2 A plan).name node).val := by
  intro node hactive hnot_root
  rcases stage2_active_cases A tree plan hactive with hold | hfresh
  · have hold_parent := hparentInvariant node hold hnot_root
    constructor
    · rw [stage2_preserves_active_node_parent A tree plan hold]
      exact stage2_preserves_active_node_active A tree plan hold_parent.1
    · rw [stage2_preserves_active_node_parent A tree plan hold]
      rw [stage2_preserves_active_node_name A tree plan hold]
      rw [stage2_preserves_active_node_name A tree plan hold_parent.1]
      exact hold_parent.2
  · rcases hfresh with ⟨parent, hparent, hnode⟩
    have hparent_active : tree.active parent = true :=
      ((mem_stage2Triggers A tree).mp hparent).1
    constructor
    · rw [← hnode]
      rw [stage2_freshChild_parent A tree plan hparent]
      exact stage2_preserves_active_node_active A tree plan hparent_active
    · rw [← hnode]
      rw [stage2_freshChild_parent A tree plan hparent]
      rw [stage2_freshChild_name A tree plan hparent]
      rw [stage2_preserves_active_node_name A tree plan hparent_active]
      exact stage2_fresh_name_gt_active_name A tree plan hparent hparent_active

theorem stage2_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage2 A plan).children A node ->
      (tree.stage2 A plan).label child ⊆ (tree.stage2 A plan).label node := by
  intro node child hchild state hstate
  rw [children, Finset.mem_filter] at hchild
  have hchild_active : (tree.stage2 A plan).active child = true := hchild.2.1
  have hchild_not_root : child ≠ root A := hchild.2.2.1
  have hstage_parent : (tree.stage2 A plan).parent child = node := hchild.2.2.2
  cases howner : plan.ownerOf A child with
  | some parent =>
      have hspec := Stage2Plan.ownerOf_eq_some_spec A plan howner
      have hparent_trigger : parent ∈ tree.stage2Triggers A := hspec.1
      have hfresh : plan.freshChild parent = child := hspec.2
      have hparent_eq_node : parent = node := by
        have hstage_parent' :
            (tree.stage2 A plan).parent child = parent := by
          simp [stage2, howner]
        exact hstage_parent'.symm.trans hstage_parent
      have hnode_active : tree.active node = true := by
        rw [← hparent_eq_node]
        exact ((mem_stage2Triggers A tree).mp hparent_trigger).1
      have hlabel_child :
          (tree.stage2 A plan).label child = tree.acceptingPart A parent := by
        rw [← hfresh]
        exact stage2_freshChild_label A tree plan hparent_trigger
      rw [hlabel_child] at hstate
      have hstate_old : state ∈ tree.label parent :=
        (mem_acceptingPart A tree).mp hstate |>.1
      rw [stage2_preserves_active_node_label A tree plan hnode_active]
      simpa [hparent_eq_node] using hstate_old
  | none =>
      have htree_child_active : tree.active child = true := by
        rw [stage2_old_active A tree plan howner] at hchild_active
        exact hchild_active
      have htree_parent_active :=
        (hparentInvariant child htree_child_active hchild_not_root).1
      have htree_parent : tree.parent child = node := by
        rw [stage2_old_parent A tree plan howner] at hstage_parent
        exact hstage_parent
      have hnode_active : tree.active node = true := by
        rw [← htree_parent]
        exact htree_parent_active
      have hold_child : child ∈ tree.children A node := by
        rw [children, Finset.mem_filter]
        exact ⟨Finset.mem_univ child,
          htree_child_active, hchild_not_root, htree_parent⟩
      have hsubset := hchildSubset node child hold_child
      rw [stage2_old_label A tree plan howner] at hstate
      have howner_node : plan.ownerOf A node = none :=
        stage2_active_old_owner_none A tree plan hnode_active
      rw [stage2_old_label A tree plan howner_node]
      exact hsubset hstate

theorem stage2_freshChild_mem_children [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hroot_active : tree.active (root A) = true)
    {parent : Node A}
    (hparent : parent ∈ tree.stage2Triggers A) :
    plan.freshChild parent ∈ (tree.stage2 A plan).children A parent := by
  rw [children, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    stage2_freshChild_active A tree plan hparent,
    stage2_freshChild_ne_root A tree plan hroot_active hparent,
    stage2_freshChild_parent A tree plan hparent⟩

theorem stage2_preserves_old_child_mem [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {node child : Node A}
    (hchild : child ∈ tree.children A node) :
    child ∈ (tree.stage2 A plan).children A node := by
  rw [children, Finset.mem_filter] at hchild
  have hchild_active : tree.active child = true := hchild.2.1
  have hchild_not_root : child ≠ root A := hchild.2.2.1
  have hchild_parent : tree.parent child = node := hchild.2.2.2
  rw [children, Finset.mem_filter]
  exact ⟨Finset.mem_univ _,
    stage2_preserves_active_node_active A tree plan hchild_active,
    hchild_not_root,
    by
      rw [stage2_preserves_active_node_parent A tree plan hchild_active]
      exact hchild_parent⟩

/-- `ancestor` lies on the parent chain from `node`, including `node` itself. -/
def IsAncestorOrSelf (tree : CompactTreeData A)
    (ancestor node : Node A) : Prop :=
  ∃ steps : Nat, (tree.parent^[steps]) node = ancestor

theorem isAncestorOrSelf_refl (tree : CompactTreeData A) (node : Node A) :
    tree.IsAncestorOrSelf A node node := by
  exact ⟨0, rfl⟩

theorem isAncestorOrSelf_of_child [DecidableEq A.State]
    (tree : CompactTreeData A)
    {ancestor node child : Node A}
    (hancestor : tree.IsAncestorOrSelf A ancestor node)
    (hchild : child ∈ tree.children A node) :
    tree.IsAncestorOrSelf A ancestor child := by
  rcases hancestor with ⟨steps, hsteps⟩
  rw [children, Finset.mem_filter] at hchild
  refine ⟨steps + 1, ?_⟩
  rw [Function.iterate_succ_apply]
  rw [hchild.2.2.2]
  exact hsteps

theorem isAncestorOrSelf_trans
    (tree : CompactTreeData A)
    {ancestor middle node : Node A}
    (hleft : tree.IsAncestorOrSelf A ancestor middle)
    (hright : tree.IsAncestorOrSelf A middle node) :
    tree.IsAncestorOrSelf A ancestor node := by
  rcases hleft with ⟨leftSteps, hleftSteps⟩
  rcases hright with ⟨rightSteps, hrightSteps⟩
  refine ⟨leftSteps + rightSteps, ?_⟩
  rw [Function.iterate_add_apply]
  rw [hrightSteps, hleftSteps]

theorem isAncestorOrSelf_from_root_eq_root
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    {ancestor : Node A}
    (hancestor : tree.IsAncestorOrSelf A ancestor (root A)) :
    ancestor = root A := by
  rcases hancestor with ⟨steps, hsteps⟩
  have hfixed : ∀ n : Nat, (tree.parent^[n]) (root A) = root A := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [Function.iterate_succ_apply]
        rw [hrootParent]
        exact ih
  have hiter : (tree.parent^[steps]) (root A) = root A := hfixed steps
  exact hsteps.symm.trans hiter

theorem active_mem_children_parent
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hactive : tree.active node = true)
    (hnotRoot : node ≠ root A) :
    node ∈ tree.children A (tree.parent node) := by
  rw [children, Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hactive, hnotRoot, rfl⟩

theorem child_ne_parent_of_parent_active_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {parent child : Node A}
    (hchild : child ∈ tree.children A parent) :
    parent ≠ child := by
  rw [children, Finset.mem_filter] at hchild
  intro hsame
  rcases hchild with ⟨_huniv, hactive, hnotRoot, hparentEq⟩
  rcases hparentInvariant child hactive hnotRoot with ⟨_hparentActive, hlt⟩
  subst parent
  rw [hparentEq] at hlt
  exact Nat.lt_irrefl _ hlt

theorem isAncestorOrSelf_parent_of_ne
    (tree : CompactTreeData A)
    {ancestor node : Node A}
    (hancestor : tree.IsAncestorOrSelf A ancestor node)
    (hne : ancestor ≠ node) :
    tree.IsAncestorOrSelf A ancestor (tree.parent node) := by
  rcases hancestor with ⟨steps, hsteps⟩
  cases steps with
  | zero =>
      simp at hsteps
      exact False.elim (hne hsteps.symm)
  | succ steps =>
      refine ⟨steps, ?_⟩
      rw [Function.iterate_succ_apply] at hsteps
      exact hsteps

theorem active_parent_iter
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hactive : tree.active node = true) :
    ∀ steps : Nat, tree.active ((tree.parent^[steps]) node) = true := by
  intro steps
  induction steps with
  | zero => exact hactive
  | succ steps ih =>
      rw [Function.iterate_succ_apply']
      by_cases hroot : (tree.parent^[steps]) node = root A
      · rw [hroot, hrootParent]
        simpa [hroot] using ih
      · exact (hparentInvariant ((tree.parent^[steps]) node) ih hroot).1

theorem exists_parent_iter_eq_root
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hactive : tree.active node = true) :
    ∃ steps : Nat, (tree.parent^[steps]) node = root A := by
  let P : Nat -> Prop := fun k =>
    ∀ node : Node A,
      tree.active node = true ->
      (tree.name node).val = k ->
        ∃ steps : Nat, (tree.parent^[steps]) node = root A
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro node hnodeActive hname
        by_cases hroot : node = root A
        · exact ⟨0, hroot⟩
        · have hparent := hparentInvariant node hnodeActive hroot
          obtain ⟨steps, hsteps⟩ :=
            ih (tree.name (tree.parent node)).val
              (by omega)
              (tree.parent node) hparent.1 rfl
          refine ⟨steps + 1, ?_⟩
          rw [Function.iterate_succ_apply]
          exact hsteps
  exact hmain (tree.name node).val node hactive rfl

theorem root_isAncestorOrSelf
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hactive : tree.active node = true) :
    tree.IsAncestorOrSelf A (root A) node :=
  exists_parent_iter_eq_root A tree hparentInvariant hactive

theorem label_subset_parent_iter
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {node : Node A}
    (hactive : tree.active node = true) :
    ∀ steps : Nat, tree.label node ⊆
      tree.label ((tree.parent^[steps]) node) := by
  intro steps
  induction steps with
  | zero =>
      intro state hstate
      exact hstate
  | succ steps ih =>
      intro state hstate
      rw [Function.iterate_succ_apply']
      have hstate_current : state ∈ tree.label ((tree.parent^[steps]) node) :=
        ih hstate
      by_cases hroot : (tree.parent^[steps]) node = root A
      · rw [hroot, hrootParent]
        simpa [hroot] using hstate_current
      · have hcurrent_active :
            tree.active ((tree.parent^[steps]) node) = true :=
          active_parent_iter A tree hrootParent hparentInvariant hactive steps
        have hchild :
            (tree.parent^[steps]) node ∈
              tree.children A (tree.parent ((tree.parent^[steps]) node)) := by
          rw [children, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hcurrent_active, hroot, rfl⟩
        exact hchildSubset (tree.parent ((tree.parent^[steps]) node))
          ((tree.parent^[steps]) node) hchild hstate_current

theorem label_subset_of_isAncestorOrSelf
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {ancestor node : Node A}
    (hactive : tree.active node = true)
    (hancestor : tree.IsAncestorOrSelf A ancestor node) :
    tree.label node ⊆ tree.label ancestor := by
  rcases hancestor with ⟨steps, hsteps⟩
  rw [← hsteps]
  exact label_subset_parent_iter A tree hrootParent hparentInvariant
    hchildSubset hactive steps

theorem exists_descendant_label_frontier
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    {node : Node A} {state : A.State}
    (hactive : tree.active node = true)
    (hstate : state ∈ tree.label node) :
    ∃ frontier,
      tree.active frontier = true ∧
        tree.IsAncestorOrSelf A node frontier ∧
          state ∈ tree.label frontier ∧
            state ∉ tree.childLabelUnion A frontier := by
  classical
  let measure : Node A -> Nat := fun node =>
    Fintype.card A.State - (tree.name node).val
  have hmain :
      ∀ m : Nat, ∀ node : Node A,
        measure node = m ->
          tree.active node = true ->
            state ∈ tree.label node ->
              ∃ frontier,
                tree.active frontier = true ∧
                  tree.IsAncestorOrSelf A node frontier ∧
                    state ∈ tree.label frontier ∧
                      state ∉ tree.childLabelUnion A frontier := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro node hmeasure hactive hstate
        by_cases hchildUnion : state ∈ tree.childLabelUnion A node
        · rw [childLabelUnion, Finset.mem_biUnion] at hchildUnion
          rcases hchildUnion with ⟨child, hchild, hstateChild⟩
          have hchildSpec := hchild
          rw [children, Finset.mem_filter] at hchildSpec
          have hchildActive : tree.active child = true := hchildSpec.2.1
          have hchildNotRoot : child ≠ root A := hchildSpec.2.2.1
          have hparentEq : tree.parent child = node := hchildSpec.2.2.2
          have hnameLt :
              (tree.name node).val < (tree.name child).val := by
            rcases hparentInvariant child hchildActive hchildNotRoot with
              ⟨_hparentActive, hlt⟩
            simpa [hparentEq] using hlt
          have hmeasureChildLt : measure child < m := by
            have hchildBound := hbound child hchildActive
            dsimp [measure] at hmeasure ⊢
            omega
          rcases ih (measure child) hmeasureChildLt child rfl
              hchildActive hstateChild with
            ⟨frontier, hfrontierActive, hchildAncestor, hfrontierState,
              hfrontierPrivate⟩
          refine ⟨frontier, hfrontierActive, ?_, hfrontierState,
            hfrontierPrivate⟩
          exact isAncestorOrSelf_trans A tree
            (isAncestorOrSelf_of_child A tree
              (isAncestorOrSelf_refl A tree node) hchild)
            hchildAncestor
        · exact ⟨node, hactive, isAncestorOrSelf_refl A tree node, hstate,
            hchildUnion⟩
  exact hmain (measure node) node rfl hactive hstate

theorem name_lt_of_isAncestorOrSelf_ne
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {ancestor node : Node A}
    (hactive : tree.active node = true)
    (hancestor : tree.IsAncestorOrSelf A ancestor node)
    (hne : ancestor ≠ node) :
    (tree.name ancestor).val < (tree.name node).val := by
  let P : Nat -> Prop := fun k =>
    ∀ node : Node A,
      tree.active node = true ->
      (tree.name node).val = k ->
      ∀ ancestor : Node A,
        tree.IsAncestorOrSelf A ancestor node ->
        ancestor ≠ node ->
          (tree.name ancestor).val < (tree.name node).val
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro node hnodeActive hname ancestor hancestor hne
        have hnodeNotRoot : node ≠ root A := by
          intro hnodeRoot
          have hancestorRoot : ancestor = root A := by
            subst node
            exact isAncestorOrSelf_from_root_eq_root A tree hrootParent
              hancestor
          exact hne (by simpa [hnodeRoot] using hancestorRoot)
        have hparent := hparentInvariant node hnodeActive hnodeNotRoot
        have hancestorParent :
            tree.IsAncestorOrSelf A ancestor (tree.parent node) :=
          isAncestorOrSelf_parent_of_ne A tree hancestor hne
        by_cases hparentEq : ancestor = tree.parent node
        · rw [hparentEq]
          exact hparent.2
        · have hltParent :
              (tree.name ancestor).val < (tree.name (tree.parent node)).val :=
            ih (tree.name (tree.parent node)).val
              (by
                rw [← hname]
                exact hparent.2)
              (tree.parent node) hparent.1 rfl ancestor hancestorParent
              hparentEq
          omega
  exact hmain (tree.name node).val node hactive rfl ancestor hancestor hne

theorem name_le_of_isAncestorOrSelf
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {ancestor node : Node A}
    (hactive : tree.active node = true)
    (hancestor : tree.IsAncestorOrSelf A ancestor node) :
    (tree.name ancestor).val ≤ (tree.name node).val := by
  by_cases hsame : ancestor = node
  · subst ancestor
    exact le_rfl
  · exact Nat.le_of_lt
      (name_lt_of_isAncestorOrSelf_ne A tree hrootParent hparentInvariant
        hactive hancestor hsame)

theorem exists_child_of_isAncestorOrSelf_ne
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {ancestor node : Node A}
    (hnodeActive : tree.active node = true)
    (hancestor : tree.IsAncestorOrSelf A ancestor node)
    (hne : ancestor ≠ node) :
    ∃ child, child ∈ tree.children A ancestor ∧
      tree.IsAncestorOrSelf A child node := by
  let P : Nat -> Prop := fun k =>
    ∀ node : Node A,
      tree.active node = true ->
      (tree.name node).val = k ->
      ∀ ancestor : Node A,
        tree.IsAncestorOrSelf A ancestor node ->
        ancestor ≠ node ->
          ∃ child, child ∈ tree.children A ancestor ∧
            tree.IsAncestorOrSelf A child node
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro node hactive hname ancestor hancestor hne
        have hnodeNotRoot : node ≠ root A := by
          intro hroot
          subst hroot
          have hancestor_root :
              ancestor = root A :=
            isAncestorOrSelf_from_root_eq_root A tree hrootParent hancestor
          exact hne hancestor_root
        by_cases hparent_eq : ancestor = tree.parent node
        · refine ⟨node, ?_, isAncestorOrSelf_refl A tree node⟩
          rw [hparent_eq]
          exact active_mem_children_parent A tree hactive hnodeNotRoot
        · have hparent := hparentInvariant node hactive hnodeNotRoot
          have hancestor_parent :
              tree.IsAncestorOrSelf A ancestor (tree.parent node) :=
            isAncestorOrSelf_parent_of_ne A tree hancestor hne
          obtain ⟨child, hchild, hchildAncestor⟩ :=
            ih (tree.name (tree.parent node)).val
              (by omega)
              (tree.parent node) hparent.1 rfl ancestor
              hancestor_parent hparent_eq
          refine ⟨child, hchild, ?_⟩
          exact isAncestorOrSelf_of_child A tree hchildAncestor
            (active_mem_children_parent A tree hactive hnodeNotRoot)
  exact hmain (tree.name node).val node hnodeActive rfl ancestor hancestor hne

/--
Ancestor split for an immediate child: if `child` is a child of `parent`, then
any ancestor-or-self of `child` is either `child` itself or an ancestor-or-self of
`parent`.  This is the structural split used when iterating stage-(3) blockers
through children of a settled node.
-/
theorem isAncestorOrSelf_child_cases
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    {parent child ancestor : Node A}
    (hchild : child ∈ tree.children A parent)
    (hancestor : tree.IsAncestorOrSelf A ancestor child) :
    ancestor = child ∨ tree.IsAncestorOrSelf A ancestor parent := by
  by_cases hsame : ancestor = child
  · exact Or.inl hsame
  · right
    have hparentAncestor :=
      isAncestorOrSelf_parent_of_ne A tree hancestor hsame
    rw [children, Finset.mem_filter] at hchild
    rwa [hchild.2.2.2] at hparentAncestor

theorem exists_branching_children_of_incomparable
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {left right : Node A}
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hnotComparable :
      ¬ (tree.IsAncestorOrSelf A left right ∨
        tree.IsAncestorOrSelf A right left)) :
    ∃ ancestor leftChild rightChild,
      leftChild ∈ tree.children A ancestor ∧
        rightChild ∈ tree.children A ancestor ∧
        leftChild ≠ rightChild ∧
        tree.IsAncestorOrSelf A leftChild left ∧
        tree.IsAncestorOrSelf A rightChild right := by
  let P : Nat -> Prop := fun k =>
    ∀ left right : Node A,
      tree.active left = true ->
      tree.active right = true ->
      (tree.name left).val + (tree.name right).val = k ->
      ¬ (tree.IsAncestorOrSelf A left right ∨
        tree.IsAncestorOrSelf A right left) ->
        ∃ ancestor leftChild rightChild,
          leftChild ∈ tree.children A ancestor ∧
            rightChild ∈ tree.children A ancestor ∧
            leftChild ≠ rightChild ∧
            tree.IsAncestorOrSelf A leftChild left ∧
            tree.IsAncestorOrSelf A rightChild right
  have hmain : ∀ k, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro left right hleftActive hrightActive hsum hnotComparable
        have hleftNotRoot : left ≠ root A := by
          intro hroot
          subst hroot
          exact hnotComparable (Or.inl
            (root_isAncestorOrSelf A tree hparentInvariant hrightActive))
        have hrightNotRoot : right ≠ root A := by
          intro hroot
          subst hroot
          exact hnotComparable (Or.inr
            (root_isAncestorOrSelf A tree hparentInvariant hleftActive))
        have hleftParent := hparentInvariant left hleftActive hleftNotRoot
        have hrightParent := hparentInvariant right hrightActive hrightNotRoot
        have hleftChild :
            left ∈ tree.children A (tree.parent left) :=
          active_mem_children_parent A tree hleftActive hleftNotRoot
        have hrightChild :
            right ∈ tree.children A (tree.parent right) :=
          active_mem_children_parent A tree hrightActive hrightNotRoot
        by_cases hsameParent : tree.parent left = tree.parent right
        · refine ⟨tree.parent left, left, right, hleftChild, ?_, ?_,
            isAncestorOrSelf_refl A tree left,
            isAncestorOrSelf_refl A tree right⟩
          · simpa [hsameParent.symm] using hrightChild
          · intro heq
            have hcomp : tree.IsAncestorOrSelf A left right := by
              subst heq
              exact isAncestorOrSelf_refl A tree left
            exact hnotComparable (Or.inl hcomp)
        · by_cases hparentComparable :
            tree.IsAncestorOrSelf A (tree.parent left) (tree.parent right) ∨
              tree.IsAncestorOrSelf A (tree.parent right) (tree.parent left)
          · rcases hparentComparable with hleftParentAncestor | hrightParentAncestor
            · obtain ⟨rightChild, hrightChildOfLeftParent, hrightBranch⟩ :=
                exists_child_of_isAncestorOrSelf_ne A tree hrootParent
                  hparentInvariant hrightParent.1 hleftParentAncestor
                  (by
                    intro h
                    exact hsameParent h)
              refine ⟨tree.parent left, left, rightChild, hleftChild,
                hrightChildOfLeftParent, ?_,
                isAncestorOrSelf_refl A tree left, ?_⟩
              · intro hchild_eq
                subst hchild_eq
                exact hnotComparable (Or.inl
                  (isAncestorOrSelf_of_child A tree hrightBranch hrightChild))
              · exact isAncestorOrSelf_of_child A tree hrightBranch hrightChild
            · obtain ⟨leftChild, hleftChildOfRightParent, hleftBranch⟩ :=
                exists_child_of_isAncestorOrSelf_ne A tree hrootParent
                  hparentInvariant hleftParent.1 hrightParentAncestor
                  (fun h => hsameParent h.symm)
              refine ⟨tree.parent right, leftChild, right,
                hleftChildOfRightParent, hrightChild, ?_, ?_,
                isAncestorOrSelf_refl A tree right⟩
              · intro hchild_eq
                subst hchild_eq
                exact hnotComparable (Or.inr
                  (isAncestorOrSelf_of_child A tree hleftBranch hleftChild))
              · exact isAncestorOrSelf_of_child A tree hleftBranch hleftChild
          · obtain ⟨ancestor, leftChild, rightChild,
                hleftChildOfAncestor, hrightChildOfAncestor, hchildNe,
                hleftBranchToParent, hrightBranchToParent⟩ :=
              ih ((tree.name (tree.parent left)).val +
                  (tree.name (tree.parent right)).val)
                (by omega)
                (tree.parent left) (tree.parent right)
                hleftParent.1 hrightParent.1 rfl hparentComparable
            refine ⟨ancestor, leftChild, rightChild,
              hleftChildOfAncestor, hrightChildOfAncestor, hchildNe, ?_, ?_⟩
            · exact isAncestorOrSelf_of_child A tree hleftBranchToParent hleftChild
            · exact isAncestorOrSelf_of_child A tree hrightBranchToParent hrightChild
  exact hmain ((tree.name left).val + (tree.name right).val)
    left right hleftActive hrightActive rfl hnotComparable

/--
Two active nodes sharing a label state are comparable.  Incomparable nodes branch
at a common ancestor into two distinct children, each carrying the shared state by
label monotonicity; sibling-label disjointness then forbids the state from lying
in both.  This is the tree-chain property: the active nodes whose label contains a
fixed state form a chain from the root.
-/
theorem comparable_of_mem_label_of_mem_label
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    {left right : Node A} {state : A.State}
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hleft : state ∈ tree.label left)
    (hright : state ∈ tree.label right) :
    tree.IsAncestorOrSelf A left right ∨ tree.IsAncestorOrSelf A right left := by
  by_contra hnotComparable
  obtain ⟨ancestor, leftChild, rightChild, hleftChildOfAncestor,
      hrightChildOfAncestor, hchildNe, hleftBranch, hrightBranch⟩ :=
    exists_branching_children_of_incomparable A tree hrootParent
      hparentInvariant hleftActive hrightActive hnotComparable
  have hstateLeftChild : state ∈ tree.label leftChild :=
    label_subset_of_isAncestorOrSelf A tree hrootParent hparentInvariant
      hchildSubset hleftActive hleftBranch hleft
  have hstateRightChild : state ∈ tree.label rightChild :=
    label_subset_of_isAncestorOrSelf A tree hrootParent hparentInvariant
      hchildSubset hrightActive hrightBranch hright
  have hdisjoint :=
    hsiblingDisjoint ancestor leftChild rightChild hleftChildOfAncestor
      hrightChildOfAncestor hchildNe
  exact (Finset.disjoint_left.mp hdisjoint hstateLeftChild) hstateRightChild

/--
Chain property with the direction pinned by names: of two active nodes sharing a
label state, the one with the strictly smaller name is the ancestor.  Combines
`comparable_of_mem_label_of_mem_label` with the depth-monotone naming
(`name_lt_of_isAncestorOrSelf_ne`).
-/
theorem isAncestorOrSelf_of_mem_label_of_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    {u w : Node A} {state : A.State}
    (huActive : tree.active u = true)
    (hwActive : tree.active w = true)
    (hu : state ∈ tree.label u)
    (hw : state ∈ tree.label w)
    (hname : (tree.name u).val < (tree.name w).val) :
    tree.IsAncestorOrSelf A u w := by
  rcases
      comparable_of_mem_label_of_mem_label A tree hrootParent hparentInvariant
        hchildSubset hsiblingDisjoint huActive hwActive hu hw with
    huw | hwu
  · exact huw
  · exfalso
    by_cases heq : w = u
    · rw [heq] at hname
      exact absurd hname (lt_irrefl _)
    · have hlt :=
        name_lt_of_isAncestorOrSelf_ne A tree hrootParent hparentInvariant
          huActive hwu heq
      omega

theorem private_state_not_mem_descendant_through_child
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {node child descendant : Node A} {state : A.State}
    (hprivate : state ∉ tree.childLabelUnion A node)
    (hchild : child ∈ tree.children A node)
    (hdescActive : tree.active descendant = true)
    (hdescendant : tree.IsAncestorOrSelf A child descendant) :
    state ∉ tree.label descendant := by
  intro hstate
  have hdesc_subset_child :
      tree.label descendant ⊆ tree.label child :=
    label_subset_of_isAncestorOrSelf A tree hrootParent hparentInvariant
      hchildSubset hdescActive hdescendant
  exact not_mem_child_label_of_not_mem_childLabelUnion A tree
    hprivate hchild (hdesc_subset_child hstate)

theorem private_states_ne_of_descendant_through_child
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {node child descendant : Node A}
    {nodePrivate descendantPrivate : A.State}
    (hnodePrivate : nodePrivate ∉ tree.childLabelUnion A node)
    (hchild : child ∈ tree.children A node)
    (hdescActive : tree.active descendant = true)
    (hdescendant : tree.IsAncestorOrSelf A child descendant)
    (hdescendantPrivateMem : descendantPrivate ∈ tree.label descendant) :
    nodePrivate ≠ descendantPrivate := by
  intro heq
  exact private_state_not_mem_descendant_through_child A tree hrootParent
    hparentInvariant hchildSubset hnodePrivate hchild hdescActive hdescendant
    (by simpa [heq] using hdescendantPrivateMem)

theorem private_states_ne_of_proper_ancestor
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {ancestor descendant : Node A}
    {ancestorPrivate descendantPrivate : A.State}
    (hancestorPrivate : ancestorPrivate ∉ tree.childLabelUnion A ancestor)
    (hdescActive : tree.active descendant = true)
    (hancestor : tree.IsAncestorOrSelf A ancestor descendant)
    (hne : ancestor ≠ descendant)
    (hdescendantPrivateMem : descendantPrivate ∈ tree.label descendant) :
    ancestorPrivate ≠ descendantPrivate := by
  obtain ⟨child, hchild, hchildAncestor⟩ :=
    exists_child_of_isAncestorOrSelf_ne A tree hrootParent hparentInvariant
      hdescActive hancestor hne
  exact private_states_ne_of_descendant_through_child A tree hrootParent
    hparentInvariant hchildSubset hancestorPrivate hchild hdescActive
    hchildAncestor hdescendantPrivateMem

theorem private_states_ne_of_comparable
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {left right : Node A}
    {leftPrivate rightPrivate : A.State}
    (hleftPrivate : leftPrivate ∉ tree.childLabelUnion A left)
    (hrightPrivate : rightPrivate ∉ tree.childLabelUnion A right)
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hleftPrivateMem : leftPrivate ∈ tree.label left)
    (hrightPrivateMem : rightPrivate ∈ tree.label right)
    (hcomparable :
      tree.IsAncestorOrSelf A left right ∨
        tree.IsAncestorOrSelf A right left)
    (hne : left ≠ right) :
    leftPrivate ≠ rightPrivate := by
  rcases hcomparable with hleftAncestor | hrightAncestor
  · exact private_states_ne_of_proper_ancestor A tree hrootParent
      hparentInvariant hchildSubset hleftPrivate hrightActive hleftAncestor
      hne hrightPrivateMem
  · intro heq
    exact private_states_ne_of_proper_ancestor A tree hrootParent
      hparentInvariant hchildSubset hrightPrivate hleftActive hrightAncestor
      (fun h => hne h.symm) hleftPrivateMem heq.symm

theorem privateStateOf_ne_of_comparable
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    {left right : Node A}
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hcomparable :
      tree.IsAncestorOrSelf A left right ∨
        tree.IsAncestorOrSelf A right left)
    (hne : left ≠ right) :
    tree.privateStateOf A hproper left hleftActive ≠
      tree.privateStateOf A hproper right hrightActive := by
  exact private_states_ne_of_comparable A tree hrootParent hparentInvariant
    hchildSubset
    (privateStateOf_not_mem_childLabelUnion A tree hproper hleftActive)
    (privateStateOf_not_mem_childLabelUnion A tree hproper hrightActive)
    hleftActive hrightActive
    (privateStateOf_mem_label A tree hproper hleftActive)
    (privateStateOf_mem_label A tree hproper hrightActive)
    hcomparable hne

theorem private_states_ne_of_siblings
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    {parent left right : Node A}
    {leftPrivate rightPrivate : A.State}
    (hleft : left ∈ tree.children A parent)
    (hright : right ∈ tree.children A parent)
    (hne : left ≠ right)
    (hleftPrivateMem : leftPrivate ∈ tree.label left)
    (hrightPrivateMem : rightPrivate ∈ tree.label right) :
    leftPrivate ≠ rightPrivate := by
  intro heq
  have hdisjoint := hsiblingDisjoint parent left right hleft hright hne
  exact Finset.disjoint_left.mp hdisjoint hleftPrivateMem
    (by simpa [heq] using hrightPrivateMem)

theorem private_states_ne_of_branching_children
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    {ancestor leftChild rightChild left right : Node A}
    {leftPrivate rightPrivate : A.State}
    (hleftChild : leftChild ∈ tree.children A ancestor)
    (hrightChild : rightChild ∈ tree.children A ancestor)
    (hchildNe : leftChild ≠ rightChild)
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hleftBranch : tree.IsAncestorOrSelf A leftChild left)
    (hrightBranch : tree.IsAncestorOrSelf A rightChild right)
    (hleftPrivateMem : leftPrivate ∈ tree.label left)
    (hrightPrivateMem : rightPrivate ∈ tree.label right) :
    leftPrivate ≠ rightPrivate := by
  have hleftMemChild : leftPrivate ∈ tree.label leftChild :=
    label_subset_of_isAncestorOrSelf A tree hrootParent hparentInvariant
      hchildSubset hleftActive hleftBranch hleftPrivateMem
  have hrightMemChild : rightPrivate ∈ tree.label rightChild :=
    label_subset_of_isAncestorOrSelf A tree hrootParent hparentInvariant
      hchildSubset hrightActive hrightBranch hrightPrivateMem
  exact private_states_ne_of_siblings A tree hsiblingDisjoint hleftChild
    hrightChild hchildNe hleftMemChild hrightMemChild

theorem privateStateOf_ne_of_branching_children
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    {ancestor leftChild rightChild left right : Node A}
    (hleftChild : leftChild ∈ tree.children A ancestor)
    (hrightChild : rightChild ∈ tree.children A ancestor)
    (hchildNe : leftChild ≠ rightChild)
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hleftBranch : tree.IsAncestorOrSelf A leftChild left)
    (hrightBranch : tree.IsAncestorOrSelf A rightChild right) :
    tree.privateStateOf A hproper left hleftActive ≠
      tree.privateStateOf A hproper right hrightActive := by
  exact private_states_ne_of_branching_children A tree hrootParent
    hparentInvariant hchildSubset hsiblingDisjoint hleftChild hrightChild
    hchildNe hleftActive hrightActive hleftBranch hrightBranch
    (privateStateOf_mem_label A tree hproper hleftActive)
    (privateStateOf_mem_label A tree hproper hrightActive)

theorem privateStateOf_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node) :
    ∀ left right
      (hleft : tree.active left = true)
      (hright : tree.active right = true),
      tree.privateStateOf A hproper left hleft =
        tree.privateStateOf A hproper right hright ->
          left = right := by
  intro left right hleft hright hprivateEq
  by_cases hnodeEq : left = right
  · exact hnodeEq
  · by_cases hcomparable :
      tree.IsAncestorOrSelf A left right ∨
        tree.IsAncestorOrSelf A right left
    · exact False.elim
        ((privateStateOf_ne_of_comparable A tree hrootParent hparentInvariant
          hchildSubset hproper hleft hright hcomparable hnodeEq) hprivateEq)
    · obtain ⟨ancestor, leftChild, rightChild,
          hleftChild, hrightChild, hchildNe, hleftBranch, hrightBranch⟩ :=
        exists_branching_children_of_incomparable A tree hrootParent
          hparentInvariant hleft hright hcomparable
      exact False.elim
        ((privateStateOf_ne_of_branching_children A tree hrootParent
          hparentInvariant hchildSubset hsiblingDisjoint hproper
          hleftChild hrightChild hchildNe hleft hright hleftBranch
          hrightBranch) hprivateEq)

theorem activeNodes_card_le_of_tree_structure
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    (tree.activeNodes A).card ≤ Fintype.card A.State := by
  exact activeNodes_card_le_of_privateState_injective A tree hproper
    (privateStateOf_injective A tree hrootParent hparentInvariant
      hchildSubset hsiblingDisjoint hproper)

theorem private_states_ne_of_same_parent
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right))
    {left right : Node A}
    {leftPrivate rightPrivate : A.State}
    (hleftActive : tree.active left = true)
    (hrightActive : tree.active right = true)
    (hleftNotRoot : left ≠ root A)
    (hrightNotRoot : right ≠ root A)
    (hparent : tree.parent left = tree.parent right)
    (hne : left ≠ right)
    (hleftPrivateMem : leftPrivate ∈ tree.label left)
    (hrightPrivateMem : rightPrivate ∈ tree.label right) :
    leftPrivate ≠ rightPrivate := by
  have hleftChild :
      left ∈ tree.children A (tree.parent left) :=
    active_mem_children_parent A tree hleftActive hleftNotRoot
  have hrightChild :
      right ∈ tree.children A (tree.parent left) := by
    rw [hparent]
    exact active_mem_children_parent A tree hrightActive hrightNotRoot
  exact private_states_ne_of_siblings A tree hsiblingDisjoint hleftChild
    hrightChild hne hleftPrivateMem hrightPrivateMem

/-- Piterman stage (3)'s older-sibling relation, with smaller dynamic name older. -/
def OlderSibling (tree : CompactTreeData A)
    (older younger : Node A) : Prop :=
  tree.active older = true ∧
    tree.active younger = true ∧
    tree.parent older ≠ older ∧
    older ≠ younger ∧
    tree.parent older = tree.parent younger ∧
    (tree.name older).val < (tree.name younger).val

theorem olderSibling_older_active
    (tree : CompactTreeData A)
    {older younger : Node A}
    (holder : tree.OlderSibling A older younger) :
    tree.active older = true :=
  holder.1

theorem olderSibling_younger_active
    (tree : CompactTreeData A)
    {older younger : Node A}
    (holder : tree.OlderSibling A older younger) :
    tree.active younger = true :=
  holder.2.1

theorem not_olderSibling_of_self_parent
    (tree : CompactTreeData A)
    {older younger : Node A}
    (hself : tree.parent older = older) :
    ¬ tree.OlderSibling A older younger := by
  intro holder
  exact holder.2.2.1 hself

theorem olderSibling_name_lt
    (tree : CompactTreeData A)
    {older younger : Node A}
    (holder : tree.OlderSibling A older younger) :
    (tree.name older).val < (tree.name younger).val :=
  holder.2.2.2.2.2

theorem stage2_old_child_olderSibling_freshChild [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {parent oldChild : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (holdChild : oldChild ∈ tree.children A parent) :
    (tree.stage2 A plan).OlderSibling A oldChild (plan.freshChild parent) := by
  rw [children, Finset.mem_filter] at holdChild
  have hold_active : tree.active oldChild = true := holdChild.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact stage2_preserves_active_node_active A tree plan hold_active
  · exact stage2_freshChild_active A tree plan hparent
  · have hparentNeOld : parent ≠ oldChild :=
      child_ne_parent_of_parent_active_name_lt A tree hparentInvariant
        (by
          rw [children, Finset.mem_filter]
          exact holdChild)
    intro hself
    rw [stage2_preserves_active_node_parent A tree plan hold_active] at hself
    rw [holdChild.2.2.2] at hself
    exact hparentNeOld hself
  · exact (stage2_freshChild_not_active_old A tree plan hparent
      ((mem_activeNodes A tree).mpr hold_active)).symm
  · rw [stage2_preserves_active_node_parent A tree plan hold_active]
    rw [stage2_freshChild_parent A tree plan hparent]
    exact holdChild.2.2.2
  · rw [stage2_preserves_active_node_name A tree plan hold_active]
    rw [stage2_freshChild_name A tree plan hparent]
    exact stage2_fresh_name_gt_active_name A tree plan hparent hold_active

theorem stage2_old_child_of_stage2_child_not_fresh
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent child : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (hchild : child ∈ (tree.stage2 A plan).children A parent)
    (hnotFresh : child ≠ plan.freshChild parent) :
    child ∈ tree.children A parent := by
  rw [children, Finset.mem_filter] at hchild
  have hstageActive : (tree.stage2 A plan).active child = true := hchild.2.1
  have hstageNotRoot : child ≠ root A := hchild.2.2.1
  have hstageParent : (tree.stage2 A plan).parent child = parent := hchild.2.2.2
  rcases stage2_active_cases A tree plan hstageActive with hold | hfresh
  · rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hold, hstageNotRoot, by
      have hparentOld :=
        stage2_preserves_active_node_parent A tree plan hold
      rw [hparentOld] at hstageParent
      exact hstageParent⟩
  · rcases hfresh with ⟨owner, howner, hchildEq⟩
    have hownerEq : owner = parent := by
      have hstageParentFresh :
          (tree.stage2 A plan).parent child = owner := by
        rw [← hchildEq]
        exact stage2_freshChild_parent A tree plan howner
      exact hstageParentFresh.symm.trans hstageParent
    subst owner
    exact False.elim (hnotFresh hchildEq.symm)

theorem stage2_old_child_of_stage2_child_nontrigger
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent child : Node A}
    (hparentNot : parent ∉ tree.stage2Triggers A)
    (hchild : child ∈ (tree.stage2 A plan).children A parent) :
    child ∈ tree.children A parent := by
  rw [children, Finset.mem_filter] at hchild
  have hstageActive : (tree.stage2 A plan).active child = true := hchild.2.1
  have hstageNotRoot : child ≠ root A := hchild.2.2.1
  have hstageParent : (tree.stage2 A plan).parent child = parent :=
    hchild.2.2.2
  rcases stage2_active_cases A tree plan hstageActive with hold | hfresh
  · rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hold, hstageNotRoot, by
      have hparentOld :=
        stage2_preserves_active_node_parent A tree plan hold
      rw [hparentOld] at hstageParent
      exact hstageParent⟩
  · rcases hfresh with ⟨owner, howner, hchildEq⟩
    have hownerEq : owner = parent := by
      have hstageParentFresh :
          (tree.stage2 A plan).parent child = owner := by
        rw [← hchildEq]
        exact stage2_freshChild_parent A tree plan howner
      exact hstageParentFresh.symm.trans hstageParent
    subst owner
    exact False.elim (hparentNot howner)

theorem stage2_isAncestorOrSelf_freshChild_cases
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent ancestor : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (hancestor :
      (tree.stage2 A plan).IsAncestorOrSelf A ancestor
        (plan.freshChild parent)) :
    ancestor = plan.freshChild parent ∨
      (tree.stage2 A plan).IsAncestorOrSelf A ancestor parent := by
  by_cases hsame : ancestor = plan.freshChild parent
  · exact Or.inl hsame
  · have hparentAncestor :
        (tree.stage2 A plan).IsAncestorOrSelf A ancestor
          ((tree.stage2 A plan).parent (plan.freshChild parent)) :=
      isAncestorOrSelf_parent_of_ne A (tree.stage2 A plan) hancestor hsame
    rw [stage2_freshChild_parent A tree plan hparent] at hparentAncestor
    exact Or.inr hparentAncestor

/--
A state is blocked at `node` if some ancestor-or-self has an older sibling
whose label already contains the state.  Stage (3) removes exactly these states
from that node and all descendants.
-/
def BlockedByOlderSibling [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) (state : A.State) : Prop :=
  ∃ ancestor older : Node A,
    tree.IsAncestorOrSelf A ancestor node ∧
      tree.OlderSibling A older ancestor ∧
      state ∈ tree.label older

/--
Blocker split for an immediate child: if a state in a child is removed by stage
(3), then either the blocker is an older sibling that is itself another child of
the same parent, or the blocker has name strictly below the parent.  This is the
finite sibling-descent primitive for iterating blocked child branches.
-/
theorem blocked_child_same_parent_or_lower_name
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {parent child : Node A} {state : A.State}
    (hchild : child ∈ tree.children A parent)
    (hblocked : tree.BlockedByOlderSibling A child state) :
    (∃ older,
        older ∈ tree.children A parent ∧
          state ∈ tree.label older ∧
          (tree.name older).val < (tree.name child).val) ∨
      (∃ lower,
        tree.active lower = true ∧
          state ∈ tree.label lower ∧
          (tree.name lower).val < (tree.name parent).val) := by
  rcases hblocked with ⟨ancestor, older, hancestor, holder, hstate⟩
  rcases isAncestorOrSelf_child_cases A tree hchild hancestor with
    hsame | hancestorParent
  · subst ancestor
    rw [children, Finset.mem_filter] at hchild
    obtain ⟨_, _hchildActive, _hchildNotRoot, hchildParent⟩ := hchild
    have holderParent : tree.parent older = parent := by
      have hp := holder.2.2.2.2.1
      rw [hchildParent] at hp
      exact hp
    have holderNotRoot : older ≠ root A := by
      intro hroot
      subst older
      exact holder.2.2.1 hrootParent
    have holderChild : older ∈ tree.children A parent := by
      rw [children, Finset.mem_filter]
      exact ⟨Finset.mem_univ older, holder.1, holderNotRoot, holderParent⟩
    exact Or.inl
      ⟨older, holderChild, hstate, olderSibling_name_lt A tree holder⟩
  · rw [children, Finset.mem_filter] at hchild
    obtain ⟨_, hchildActive, hchildNotRoot, hchildParent⟩ := hchild
    have hparentActive : tree.active parent = true := by
      have hp := (hparentInvariant child hchildActive hchildNotRoot).1
      rwa [hchildParent] at hp
    have hancestorLeParent :
        (tree.name ancestor).val ≤ (tree.name parent).val :=
      name_le_of_isAncestorOrSelf A tree hrootParent hparentInvariant
        hparentActive hancestorParent
    have holderLtAncestor : (tree.name older).val < (tree.name ancestor).val :=
      olderSibling_name_lt A tree holder
    exact Or.inr ⟨older, holder.1, hstate, by omega⟩

/--
Piterman Section 3.2, transition stage (3): remove duplicate states from every
younger sibling and all descendants of that younger sibling.
-/
noncomputable def stage3 [DecidableEq A.State]
    (tree : CompactTreeData A) : CompactTreeData A where
  active := tree.active
  name := tree.name
  parent := tree.parent
  label node := by
    classical
    exact
      (tree.label node).filter
        (fun state => ¬ tree.BlockedByOlderSibling A node state)
  e := sentinel A
  f := sentinel A

theorem mem_stage3_label [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} {state : A.State} :
    state ∈ (tree.stage3 A).label node ↔
      state ∈ tree.label node ∧
        ¬ tree.BlockedByOlderSibling A node state := by
  classical
  simp [stage3]

theorem not_blockedByOlderSibling_root
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hrootName : (tree.name (root A)).val = (rootName A).val)
    {state : A.State} :
    ¬ tree.BlockedByOlderSibling A (root A) state := by
  intro hblocked
  rcases hblocked with ⟨ancestor, older, hancestor, holder, _hstate⟩
  have hancestorRoot : ancestor = root A :=
    isAncestorOrSelf_from_root_eq_root A tree hrootParent hancestor
  subst ancestor
  have hlt := olderSibling_name_lt A tree holder
  have hrootVal : (tree.name (root A)).val = 0 := by
    simpa [rootName] using hrootName
  omega

theorem stage3_root_label
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hrootName : (tree.name (root A)).val = (rootName A).val) :
    (tree.stage3 A).label (root A) = tree.label (root A) := by
  ext state
  rw [mem_stage3_label A tree]
  constructor
  · intro hstate
    exact hstate.1
  · intro hstate
    exact ⟨hstate,
      not_blockedByOlderSibling_root A tree hrootParent hrootName⟩

theorem stage3_active [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage3 A).active node = tree.active node := rfl

theorem stage3_name [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage3 A).name node = tree.name node := rfl

theorem stage3_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage3 A).parent node = tree.parent node := rfl

theorem stage3_children [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage3 A).children A node = tree.children A node := by
  simp [children, stage3]

theorem stage3_activeNodes [DecidableEq A.State]
    (tree : CompactTreeData A) :
    (tree.stage3 A).activeNodes A = tree.activeNodes A := by
  simp [activeNodes, stage3]

theorem stage2_stage3_old_child_of_stage3_child_not_fresh
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent child : Node A}
    (hparent : parent ∈ tree.stage2Triggers A)
    (hchild :
      child ∈ ((tree.stage2 A plan).stage3 A).children A parent)
    (hnotFresh : child ≠ plan.freshChild parent) :
    child ∈ tree.children A parent := by
  exact stage2_old_child_of_stage2_child_not_fresh A tree plan hparent
    (by simpa [stage3_children A (tree.stage2 A plan) parent] using hchild)
    hnotFresh

theorem stage2_stage3_old_child_of_stage3_child_nontrigger
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent child : Node A}
    (hparentNot : parent ∉ tree.stage2Triggers A)
    (hchild :
      child ∈ ((tree.stage2 A plan).stage3 A).children A parent) :
    child ∈ tree.children A parent := by
  exact stage2_old_child_of_stage2_child_nontrigger A tree plan hparentNot
    (by simpa [stage3_children A (tree.stage2 A plan) parent] using hchild)

theorem stage3_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage3 A).label node ⊆ tree.label node := by
  intro state hstate
  exact (mem_stage3_label A tree).mp hstate |>.1

theorem stage1_stage2_stage3_active_label_segment_from_source
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat}
    (plan : Stage2Plan A (tree.stage1 A (word startTime)))
    {node : Node A} {state : A.State}
    (hactive :
      (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).active
        node = true)
    (hstate :
      state ∈
        (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).label
          node) :
    ∃ sourceNode sourceState,
      tree.active sourceNode = true ∧
        sourceState ∈ tree.label sourceNode ∧
          Segment A word startTime 1 sourceState state := by
  let t2 := (tree.stage1 A (word startTime)).stage2 A plan
  have hactive_t2 : t2.active node = true := by
    simpa [t2, stage3] using hactive
  have hstate_t2 : state ∈ t2.label node :=
    stage3_label_subset A t2 node (by simpa [t2] using hstate)
  exact stage1_stage2_active_label_segment_from_source A tree word plan
    hactive_t2 hstate_t2

theorem stage3_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage3 A).active node = false ->
      (tree.stage3 A).label node = ∅ := by
  intro node hactive
  ext state
  constructor
  · intro hstate
    have hold : state ∈ tree.label node :=
      stage3_label_subset A tree node hstate
    have htree_inactive : tree.active node = false := by
      simpa [stage3] using hactive
    rw [hinactiveLabel node htree_inactive] at hold
    simp at hold
  · intro hstate
    simp at hstate

theorem stage3_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State) :
    ∀ node, (tree.stage3 A).active node = true ->
      ((tree.stage3 A).name node).val < Fintype.card A.State := by
  intro node hactive
  exact hbound node (by simpa [stage3] using hactive)

theorem stage3_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage3 A).active left = true ->
      (tree.stage3 A).active right = true ->
      (tree.stage3 A).name left = (tree.stage3 A).name right ->
        left = right := by
  intro left right hleft hright hname
  exact hinjective left right
    (by simpa [stage3] using hleft)
    (by simpa [stage3] using hright)
    (by simpa [stage3] using hname)

theorem stage3_preserves_parent_active_and_name_lt [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val) :
    ∀ node,
      (tree.stage3 A).active node = true ->
      node ≠ root A ->
        (tree.stage3 A).active ((tree.stage3 A).parent node) = true ∧
          ((tree.stage3 A).name ((tree.stage3 A).parent node)).val <
            ((tree.stage3 A).name node).val := by
  intro node hactive hnot_root
  have hold := hparentInvariant node (by simpa [stage3] using hactive) hnot_root
  simpa [stage3] using hold

theorem stage3_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage3 A).children A node ->
      (tree.stage3 A).label child ⊆ (tree.stage3 A).label node := by
  intro node child hchild state hstate
  rw [stage3_children A tree node] at hchild
  have hstateOldChild : state ∈ tree.label child :=
    (mem_stage3_label A tree).mp hstate |>.1
  have hstateNotBlockedChild :
      ¬ tree.BlockedByOlderSibling A child state :=
    (mem_stage3_label A tree).mp hstate |>.2
  rw [mem_stage3_label A tree]
  constructor
  · exact hchildSubset node child hchild hstateOldChild
  · intro hblockedNode
    rcases hblockedNode with ⟨ancestor, older, hancestor, holder, hstateOlder⟩
    exact hstateNotBlockedChild
      ⟨ancestor, older,
        isAncestorOrSelf_of_child A tree hancestor hchild,
        holder,
        hstateOlder⟩

theorem not_mem_stage3_label_of_olderSibling_blocker [DecidableEq A.State]
    (tree : CompactTreeData A)
    {ancestor older node : Node A} {state : A.State}
    (hancestor : tree.IsAncestorOrSelf A ancestor node)
    (holder : tree.OlderSibling A older ancestor)
    (hstate : state ∈ tree.label older) :
    state ∉ (tree.stage3 A).label node := by
  intro hmem
  exact ((mem_stage3_label A tree).mp hmem).2
    ⟨ancestor, older, hancestor, holder, hstate⟩

theorem stage3_blocked_of_mem_label_not_mem [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A} {state : A.State}
    (hstate : state ∈ tree.label node)
    (hnot : state ∉ (tree.stage3 A).label node) :
    tree.BlockedByOlderSibling A node state := by
  by_contra hblocked
  exact hnot ((mem_stage3_label A tree).mpr ⟨hstate, hblocked⟩)

theorem not_mem_stage3_freshChild_label_of_old_child_state
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {parent oldChild : Node A} {state : A.State}
    (hparent : parent ∈ tree.stage2Triggers A)
    (holdChild : oldChild ∈ tree.children A parent)
    (hstate : state ∈ (tree.stage2 A plan).label oldChild) :
    state ∉ ((tree.stage2 A plan).stage3 A).label (plan.freshChild parent) := by
  have holder :
      (tree.stage2 A plan).OlderSibling A oldChild (plan.freshChild parent) :=
    stage2_old_child_olderSibling_freshChild A tree plan hparentInvariant
      hparent holdChild
  exact not_mem_stage3_label_of_olderSibling_blocker A (tree.stage2 A plan)
    (isAncestorOrSelf_refl A (tree.stage2 A plan) (plan.freshChild parent))
    holder hstate

theorem stage2_stage3_removed_freshChild_blocked_by_older
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ (tree.stage2 A plan).label (plan.freshChild parent))
    (hnot :
      state ∉ ((tree.stage2 A plan).stage3 A).label
        (plan.freshChild parent)) :
    ∃ ancestor older,
      (tree.stage2 A plan).IsAncestorOrSelf A ancestor
        (plan.freshChild parent) ∧
        (tree.stage2 A plan).OlderSibling A older ancestor ∧
        state ∈ (tree.stage2 A plan).label older ∧
        A.accepting state := by
  have hblocked :
      (tree.stage2 A plan).BlockedByOlderSibling A
        (plan.freshChild parent) state :=
    stage3_blocked_of_mem_label_not_mem A (tree.stage2 A plan)
      hstate hnot
  rcases hblocked with ⟨ancestor, older, hancestor, holder, holderState⟩
  exact ⟨ancestor, older, hancestor, holder, holderState,
    stage2_freshChild_label_accepting A tree plan hparent hstate⟩

/--
Root fresh-child routing after the corrected sibling definition: if the root's
fresh accepting child is removed by stage (3), then the blocker is a genuine
active child of the root in the stage-(2) tree.  The old spurious possibility
`older = root` is excluded by `OlderSibling`'s `parent older ≠ older` conjunct.
-/
theorem stage2_stage3_removed_root_freshChild_blocked_by_root_child
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hrootActive : tree.active (root A) = true)
    (hrootName : (tree.name (root A)).val = (rootName A).val)
    (hrootParent : tree.parent (root A) = root A)
    (htrigger : root A ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ (tree.stage2 A plan).label (plan.freshChild (root A)))
    (hnot :
      state ∉ ((tree.stage2 A plan).stage3 A).label
        (plan.freshChild (root A))) :
    ∃ older,
      older ∈ (tree.stage2 A plan).children A (root A) ∧
        (tree.stage2 A plan).OlderSibling A older
          (plan.freshChild (root A)) ∧
        state ∈ (tree.stage2 A plan).label older ∧
        A.accepting state := by
  let t2 := tree.stage2 A plan
  rcases stage2_stage3_removed_freshChild_blocked_by_older
      A tree plan htrigger hstate hnot with
    ⟨ancestor, older, hancestor, holder, holderState, haccepting⟩
  have ht2RootParent : t2.parent (root A) = root A := by
    exact (stage2_root_parent A tree plan hrootActive).trans hrootParent
  have ht2RootName : (t2.name (root A)).val = (rootName A).val := by
    rw [show t2.name (root A) = tree.name (root A) from
      stage2_root_name A tree plan hrootActive]
    exact hrootName
  have hancestorFresh : ancestor = plan.freshChild (root A) := by
    rcases stage2_isAncestorOrSelf_freshChild_cases A tree plan htrigger
        hancestor with hsame | habove
    · exact hsame
    · have hancestorRoot : ancestor = root A :=
        isAncestorOrSelf_from_root_eq_root A t2 ht2RootParent habove
      subst ancestor
      have hlt := olderSibling_name_lt A t2 holder
      have hrootZero : (t2.name (root A)).val = 0 := by
        simpa [rootName] using ht2RootName
      omega
  have holderFresh :
      t2.OlderSibling A older (plan.freshChild (root A)) := by
    simpa [t2, hancestorFresh] using holder
  have hparentOlder : t2.parent older = root A := by
    have hsameParent :
        t2.parent older = t2.parent (plan.freshChild (root A)) :=
      holderFresh.2.2.2.2.1
    rw [stage2_freshChild_parent A tree plan htrigger] at hsameParent
    exact hsameParent
  have hnotRoot : older ≠ root A := by
    intro hroot
    have hself : t2.parent older = older := by
      simpa [hroot] using ht2RootParent
    exact holderFresh.2.2.1 hself
  have hchild : older ∈ t2.children A (root A) := by
    rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ older, holderFresh.1, hnotRoot, hparentOlder⟩
  exact ⟨older, by simpa [t2] using hchild,
    by simpa [t2] using holderFresh,
    by simpa [t2] using holderState, haccepting⟩

theorem stage3_sibling_labels_disjoint_of_name_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ node left right,
      left ∈ tree.children A node ->
      right ∈ tree.children A node ->
      left ≠ right ->
        Disjoint ((tree.stage3 A).label left) ((tree.stage3 A).label right) := by
  intro node left right hleftChild hrightChild hne
  rw [Finset.disjoint_left]
  intro state hleftState hrightState
  rw [children, Finset.mem_filter] at hleftChild hrightChild
  have hleftActive : tree.active left = true := hleftChild.2.1
  have hrightActive : tree.active right = true := hrightChild.2.1
  have hleftParent : tree.parent left = node := hleftChild.2.2.2
  have hrightParent : tree.parent right = node := hrightChild.2.2.2
  have hleftParentNe : tree.parent left ≠ left := by
    rw [hleftParent]
    exact child_ne_parent_of_parent_active_name_lt A tree hparentInvariant
      (by
        rw [children, Finset.mem_filter]
        exact hleftChild)
  have hrightParentNe : tree.parent right ≠ right := by
    rw [hrightParent]
    exact child_ne_parent_of_parent_active_name_lt A tree hparentInvariant
      (by
        rw [children, Finset.mem_filter]
        exact hrightChild)
  have hleftLabel : state ∈ tree.label left :=
    (mem_stage3_label A tree).mp hleftState |>.1
  have hrightLabel : state ∈ tree.label right :=
    (mem_stage3_label A tree).mp hrightState |>.1
  have hname_ne : tree.name left ≠ tree.name right := by
    intro hname
    exact hne (hinjective left right hleftActive hrightActive hname)
  have hval_ne : (tree.name left).val ≠ (tree.name right).val := by
    intro hval
    exact hname_ne (Fin.ext hval)
  by_cases hlt : (tree.name left).val < (tree.name right).val
  · have holder : tree.OlderSibling A left right := by
      refine ⟨hleftActive, hrightActive, hleftParentNe, hne, ?_, hlt⟩
      rw [hleftParent, hrightParent]
    have hblocked : tree.BlockedByOlderSibling A right state :=
      ⟨right, left, isAncestorOrSelf_refl A tree right, holder, hleftLabel⟩
    exact ((mem_stage3_label A tree).mp hrightState).2 hblocked
  · have hgt : (tree.name right).val < (tree.name left).val := by
      omega
    have holder : tree.OlderSibling A right left := by
      refine ⟨hrightActive, hleftActive, hrightParentNe, ?_, ?_, hgt⟩
      · exact hne.symm
      · rw [hleftParent, hrightParent]
    have hblocked : tree.BlockedByOlderSibling A left state :=
      ⟨left, right, isAncestorOrSelf_refl A tree left, holder, hrightLabel⟩
    exact ((mem_stage3_label A tree).mp hleftState).2 hblocked

theorem stage2_stage3_sibling_labels_disjoint
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ node left right,
      left ∈ (tree.stage2 A plan).children A node ->
      right ∈ (tree.stage2 A plan).children A node ->
      left ≠ right ->
        Disjoint (((tree.stage2 A plan).stage3 A).label left)
          (((tree.stage2 A plan).stage3 A).label right) := by
  exact
    stage3_sibling_labels_disjoint_of_name_injective A (tree.stage2 A plan)
      (stage2_preserves_parent_active_and_name_lt A tree plan hparentInvariant)
      (stage2_preserves_name_injective A tree plan hinjective)

theorem stage2_stage3_preserves_inactive_label
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, ((tree.stage2 A plan).stage3 A).active node = false ->
      ((tree.stage2 A plan).stage3 A).label node = ∅ := by
  exact
    stage3_preserves_inactive_label A (tree.stage2 A plan)
      (stage2_preserves_inactive_label A tree plan hinactiveLabel)

theorem stage2_stage3_preserves_name_bound
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State) :
    ∀ node, ((tree.stage2 A plan).stage3 A).active node = true ->
      (((tree.stage2 A plan).stage3 A).name node).val < 2 * Fintype.card A.State := by
  intro node hactive
  have hstage2_active : (tree.stage2 A plan).active node = true := by
    simpa [stage3] using hactive
  rcases stage2_active_cases A tree plan hstage2_active with hold | hfresh
  · rw [stage3_name, stage2_preserves_active_node_name A tree plan hold]
    have hlt := hbound node hold
    omega
  · rcases hfresh with ⟨parent, hparent, hnode⟩
    rw [← hnode]
    rw [stage3_name, stage2_freshChild_name A tree plan hparent]
    exact (plan.freshName parent).isLt

theorem stage2_stage3_preserves_name_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      ((tree.stage2 A plan).stage3 A).active left = true ->
      ((tree.stage2 A plan).stage3 A).active right = true ->
      ((tree.stage2 A plan).stage3 A).name left =
        ((tree.stage2 A plan).stage3 A).name right ->
        left = right := by
  exact
    stage3_preserves_name_injective A (tree.stage2 A plan)
      (stage2_preserves_name_injective A tree plan hinjective)

theorem stage2_stage3_active_name_lt_active_plus_triggers
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ node, ((tree.stage2 A plan).stage3 A).active node = true ->
      (((tree.stage2 A plan).stage3 A).name node).val <
        (tree.activeNodes A).card + (tree.stage2Triggers A).card := by
  intro node hactive
  exact stage2_active_name_lt_active_plus_triggers A tree plan
    hbound hinjective hconsecutive node
    (by simpa [stage3] using hactive)

theorem stage2_stage3_exists_active_name_eq_of_lt_active_plus_triggers
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j) :
    ∀ j : Nat, j < (tree.activeNodes A).card + (tree.stage2Triggers A).card ->
      ∃ node, ((tree.stage2 A plan).stage3 A).active node = true ∧
        (((tree.stage2 A plan).stage3 A).name node).val = j := by
  intro j hj
  obtain ⟨node, hactive, hname⟩ :=
    stage2_exists_active_name_eq_of_lt_active_plus_triggers A tree plan
      hbound hinjective hconsecutive j hj
  exact ⟨node, by simpa [stage3] using hactive, by simpa [stage3] using hname⟩

theorem stage2_stage3_preserves_parent_active_and_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val) :
    ∀ node,
      ((tree.stage2 A plan).stage3 A).active node = true ->
      node ≠ root A ->
        ((tree.stage2 A plan).stage3 A).active
            (((tree.stage2 A plan).stage3 A).parent node) = true ∧
          (((tree.stage2 A plan).stage3 A).name
              (((tree.stage2 A plan).stage3 A).parent node)).val <
            (((tree.stage2 A plan).stage3 A).name node).val := by
  exact
    stage3_preserves_parent_active_and_name_lt A (tree.stage2 A plan)
      (stage2_preserves_parent_active_and_name_lt A tree plan hparentInvariant)

theorem stage2_stage3_preserves_child_label_subset
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ ((tree.stage2 A plan).stage3 A).children A node ->
      ((tree.stage2 A plan).stage3 A).label child ⊆
        ((tree.stage2 A plan).stage3 A).label node := by
  exact
    stage3_preserves_child_label_subset A (tree.stage2 A plan)
      (stage2_preserves_child_label_subset A tree plan
        hparentInvariant hchildSubset)

/--
Packaged post-stage-(3) invariants for one transition.  From a WellFormed source
tree (the relevant fields), the intermediate tree `t3 = ((tree.stage1).stage2).stage3`
satisfies the four structural invariants needed by the chain/comparability lemmas:
root self-parenthood, the depth-monotone parent invariant, child-label inclusion,
and sibling-label disjointness.  This bundles the standard stage (1)/(2)/(3)
preservation lemmas so downstream geometry can be stated directly on `t3`.
-/
theorem stage1_stage2_stage3_invariants
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : Stage2Plan A (tree.stage1 A letter))
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hinjective :
      ∀ left right, tree.active left = true -> tree.active right = true ->
        tree.name left = tree.name right -> left = right) :
    (((tree.stage1 A letter).stage2 A plan).stage3 A).parent (root A) = root A ∧
      (∀ node,
        (((tree.stage1 A letter).stage2 A plan).stage3 A).active node = true ->
        node ≠ root A ->
          (((tree.stage1 A letter).stage2 A plan).stage3 A).active
              ((((tree.stage1 A letter).stage2 A plan).stage3 A).parent node) =
            true ∧
            ((((tree.stage1 A letter).stage2 A plan).stage3 A).name
                ((((tree.stage1 A letter).stage2 A plan).stage3 A).parent node)).val <
              ((((tree.stage1 A letter).stage2 A plan).stage3 A).name node).val) ∧
      (∀ node child,
        child ∈ (((tree.stage1 A letter).stage2 A plan).stage3 A).children A node ->
          (((tree.stage1 A letter).stage2 A plan).stage3 A).label child ⊆
            (((tree.stage1 A letter).stage2 A plan).stage3 A).label node) ∧
      (∀ node left right,
        left ∈ (((tree.stage1 A letter).stage2 A plan).stage3 A).children A node ->
        right ∈ (((tree.stage1 A letter).stage2 A plan).stage3 A).children A node ->
        left ≠ right ->
          Disjoint ((((tree.stage1 A letter).stage2 A plan).stage3 A).label left)
            ((((tree.stage1 A letter).stage2 A plan).stage3 A).label right)) := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan
  let t3 := t2.stage3 A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter hparentInvariant)
  have ht1_childSubset :
      ∀ node child, child ∈ t1.children A node ->
        t1.label child ⊆ t1.label node := by
    simpa [t1] using
      (stage1_preserves_child_label_subset A tree letter hchildSubset)
  have ht1_injective :
      ∀ left right, t1.active left = true -> t1.active right = true ->
        t1.name left = t1.name right -> left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht3_parent :
      ∀ node, t3.active node = true -> node ≠ root A ->
        t3.active (t3.parent node) = true ∧
          (t3.name (t3.parent node)).val < (t3.name node).val := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_parent_active_and_name_lt A t1 plan ht1_parent)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1 plan ht1_parent
        ht1_childSubset)
  have ht3_sibling :
      ∀ node left right,
        left ∈ t3.children A node ->
        right ∈ t3.children A node ->
        left ≠ right ->
          Disjoint (t3.label left) (t3.label right) := by
    simpa [t2, t3] using
      (stage2_stage3_sibling_labels_disjoint A t1 plan ht1_parent ht1_injective)
  have ht3_rootParent : t3.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan ht1_rootActive
    have ht2_rootParent : t2.parent (root A) = root A := by
      rw [hparent]; simpa [t1] using hrootParent
    simpa [t3] using ht2_rootParent
  exact ⟨ht3_rootParent, ht3_parent, ht3_childSubset, ht3_sibling⟩

theorem stage2_stage3_freshChild_label_accepting [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ ((tree.stage2 A plan).stage3 A).label
        (plan.freshChild parent)) :
    A.accepting state := by
  exact stage2_freshChild_label_accepting A tree plan hparent
    (stage3_label_subset A (tree.stage2 A plan)
      (plan.freshChild parent) hstate)

theorem stage2_stage3_freshChild_label_mem_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A)
    {state : A.State}
    (hstate :
      state ∈ ((tree.stage2 A plan).stage3 A).label
        (plan.freshChild parent)) :
    state ∈ tree.label parent := by
  exact stage2_freshChild_label_mem_parent A tree plan hparent
    (stage3_label_subset A (tree.stage2 A plan)
      (plan.freshChild parent) hstate)

theorem stage2_stage3_freshChild_mem_children [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hrootActive : tree.active (root A) = true)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A) :
    plan.freshChild parent ∈
      ((tree.stage2 A plan).stage3 A).children A parent := by
  simpa [stage3_children A (tree.stage2 A plan) parent] using
    (stage2_freshChild_mem_children A tree plan hrootActive hparent)

theorem stage2_stage3_freshChild_label_subset_childLabelUnion
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hrootActive : tree.active (root A) = true)
    {parent : Node A} (hparent : parent ∈ tree.stage2Triggers A) :
    ((tree.stage2 A plan).stage3 A).label (plan.freshChild parent) ⊆
      ((tree.stage2 A plan).stage3 A).childLabelUnion A parent := by
  intro state hstate
  rw [childLabelUnion, Finset.mem_biUnion]
  exact ⟨plan.freshChild parent,
    stage2_stage3_freshChild_mem_children A tree plan hrootActive hparent,
    hstate⟩

/-- Piterman stage (4)'s green nodes: their label is exactly covered by children. -/
def greenNodes [DecidableEq A.State]
    (tree : CompactTreeData A) : Finset (Node A) :=
  (tree.activeNodes A).filter
    (fun node => tree.label node = tree.childLabelUnion A node)

theorem mem_greenNodes [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.greenNodes A ↔
      tree.active node = true ∧
        tree.label node = tree.childLabelUnion A node := by
  simp [greenNodes, activeNodes]

/--
Breakpoint measure: the number of *uncovered* (private) states of a node, i.e.
states in its label not contributed by any child.  This is the Safra/Piterman
progress measure for the green-event recurrence: a node greens exactly when its
measure reaches `0`.
-/
def uncoveredCount [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) : Nat :=
  (tree.label node \ tree.childLabelUnion A node).card

/--
A node greens precisely when its breakpoint measure is `0`.  Requires the
standard `childLabelUnion ⊆ label` invariant so that emptiness of the difference
gives equality, not merely containment.
-/
theorem green_iff_uncoveredCount_zero [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hactive : tree.active node = true)
    (hsub : tree.childLabelUnion A node ⊆ tree.label node) :
    node ∈ tree.greenNodes A ↔ tree.uncoveredCount A node = 0 := by
  rw [mem_greenNodes A tree, uncoveredCount, Finset.card_eq_zero,
    Finset.sdiff_eq_empty_iff_subset]
  constructor
  · rintro ⟨_, heq⟩
    rw [heq]
  · intro hle
    exact ⟨hactive, Finset.Subset.antisymm hle hsub⟩

/--
The breakpoint measure is antitone in coverage: with a node's label unchanged,
growing its children's coverage cannot increase its uncovered count.  Pure
`Finset` monotonicity, the workhorse for the green-event progress argument across
stages and steps.
-/
theorem uncoveredCount_le_of_label_eq_of_childLabelUnion_subset
    [DecidableEq A.State]
    (tree₁ tree₂ : CompactTreeData A) (node : Node A)
    (hlabel : tree₁.label node = tree₂.label node)
    (hcover : tree₁.childLabelUnion A node ⊆ tree₂.childLabelUnion A node) :
    tree₂.uncoveredCount A node ≤ tree₁.uncoveredCount A node := by
  unfold uncoveredCount
  rw [hlabel]
  exact Finset.card_le_card
    (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hcover)

/--
Strict decrease of the breakpoint measure: covering a previously uncovered state
strictly drops the uncovered count.  This is the per-step progress that drives the
measure to `0` (a green event).
-/
theorem uncoveredCount_lt_of_label_eq_of_newly_covered
    [DecidableEq A.State]
    (tree₁ tree₂ : CompactTreeData A) (node : Node A)
    (hlabel : tree₁.label node = tree₂.label node)
    (hcover : tree₁.childLabelUnion A node ⊆ tree₂.childLabelUnion A node)
    {state : A.State}
    (hmem : state ∈ tree₁.label node)
    (hold : state ∉ tree₁.childLabelUnion A node)
    (hnew : state ∈ tree₂.childLabelUnion A node) :
    tree₂.uncoveredCount A node < tree₁.uncoveredCount A node := by
  unfold uncoveredCount
  rw [hlabel]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset
    (Finset.sdiff_subset_sdiff (Finset.Subset.refl _) hcover)]
  refine ⟨state, ?_, ?_⟩
  · simp only [Finset.mem_sdiff]
    exact ⟨by rw [← hlabel]; exact hmem, hold⟩
  · simp only [Finset.mem_sdiff, not_and, not_not]
    intro _
    exact hnew

/--
Positive breakpoint measure exposes an actually uncovered state: a state in the
node label that is not yet covered by any child.
-/
theorem exists_uncovered_state_of_uncoveredCount_pos
    [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A)
    (hpos : 0 < tree.uncoveredCount A node) :
    ∃ state : A.State,
      state ∈ tree.label node ∧ state ∉ tree.childLabelUnion A node := by
  have hcard :
      0 < (tree.label node \ tree.childLabelUnion A node).card := by
    simpa [uncoveredCount] using hpos
  rcases Finset.card_pos.mp hcard with ⟨state, hmem⟩
  rw [Finset.mem_sdiff] at hmem
  exact ⟨state, hmem.1, hmem.2⟩

theorem green_label_mem_childLabelUnion [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hgreen : node ∈ tree.greenNodes A)
    {state : A.State}
    (hstate : state ∈ tree.label node) :
    state ∈ tree.childLabelUnion A node := by
  have hgreen_eq :
      tree.label node = tree.childLabelUnion A node :=
    (mem_greenNodes A tree).mp hgreen |>.2
  simpa [hgreen_eq] using hstate

theorem stage1_stage2_stage3_green_label_segment_from_source
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat}
    (plan : Stage2Plan A (tree.stage1 A (word startTime)))
    {green : Node A} {state : A.State}
    (hgreen :
      green ∈
        (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).greenNodes A)
    (hstate :
      state ∈
        (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).label
          green) :
    ∃ sourceNode sourceState,
      tree.active sourceNode = true ∧
        sourceState ∈ tree.label sourceNode ∧
          Segment A word startTime 1 sourceState state := by
  have hactive :
      (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).active
        green = true :=
    (mem_greenNodes A
      (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A)).mp
        hgreen |>.1
  exact stage1_stage2_stage3_active_label_segment_from_source A tree word plan
    hactive hstate

theorem exists_child_state_of_green_label_nonempty [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hgreen : node ∈ tree.greenNodes A)
    (hnonempty : tree.label node ≠ ∅) :
    ∃ child state,
      child ∈ tree.children A node ∧
        state ∈ tree.label child ∧
        state ∈ tree.label node := by
  classical
  have hlabelNonempty : (tree.label node).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hnonempty
  rcases hlabelNonempty with ⟨state, hstateLabel⟩
  have hstateUnion :
      state ∈ tree.childLabelUnion A node :=
    green_label_mem_childLabelUnion A tree hgreen hstateLabel
  rw [childLabelUnion, Finset.mem_biUnion] at hstateUnion
  rcases hstateUnion with ⟨child, hchild, hstateChild⟩
  exact ⟨child, state, hchild, hstateChild, hstateLabel⟩

theorem stage2_stage3_green_freshChild_label_subset_parent
    [DecidableEq A.State]
    (tree : CompactTreeData A) (plan : Stage2Plan A tree)
    (hrootActive : tree.active (root A) = true)
    {parent : Node A}
    (htrigger : parent ∈ tree.stage2Triggers A)
    (hgreen :
      parent ∈ ((tree.stage2 A plan).stage3 A).greenNodes A) :
    ((tree.stage2 A plan).stage3 A).label (plan.freshChild parent) ⊆
      ((tree.stage2 A plan).stage3 A).label parent := by
  intro state hstate
  have hchildUnion :
      state ∈ ((tree.stage2 A plan).stage3 A).childLabelUnion A parent :=
    stage2_stage3_freshChild_label_subset_childLabelUnion A tree plan
      hrootActive htrigger hstate
  have hgreen_eq :
      ((tree.stage2 A plan).stage3 A).label parent =
        ((tree.stage2 A plan).stage3 A).childLabelUnion A parent :=
    (mem_greenNodes A ((tree.stage2 A plan).stage3 A)).mp hgreen |>.2
  rw [hgreen_eq]
  exact hchildUnion

theorem stage1_stage2_stage3_green_trigger_accepting_segment_from_source_or_routes
    [DecidableEq A.State]
    (tree : CompactTreeData A) (word : OmegaWord Alphabet)
    {startTime : Nat}
    (plan : Stage2Plan A (tree.stage1 A (word startTime)))
    (hrootActive :
      (tree.stage1 A (word startTime)).active (root A) = true)
    {green : Node A}
    (htrigger : green ∈ (tree.stage1 A (word startTime)).stage2Triggers A)
    (hgreen :
      green ∈
        (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).greenNodes A) :
    ∃ acceptingState sourceNode sourceState,
      A.accepting acceptingState ∧
        tree.active sourceNode = true ∧
          sourceState ∈ tree.label sourceNode ∧
            SegmentVisitsAccepting A word startTime 1 sourceState acceptingState ∧
            (acceptingState ∈
                (((tree.stage1 A (word startTime)).stage2 A plan).stage3 A).label
                  green ∨
              ∃ ancestor older,
                ((tree.stage1 A (word startTime)).stage2 A plan).IsAncestorOrSelf A
                  ancestor (plan.freshChild green) ∧
                ((tree.stage1 A (word startTime)).stage2 A plan).OlderSibling A
                  older ancestor ∧
                acceptingState ∈
                  ((tree.stage1 A (word startTime)).stage2 A plan).label older) := by
  let t1 := tree.stage1 A (word startTime)
  let t2 := t1.stage2 A plan
  let t3 := t2.stage3 A
  rcases exists_accepting_label_of_stage2Trigger A t1
      (by simpa [t1] using htrigger) with
    ⟨acceptingState, hstateParent, haccepting⟩
  have hstateFresh_t2 :
      acceptingState ∈ t2.label (plan.freshChild green) := by
    simp only [t2]
    rw [stage2_freshChild_label A t1 plan (by simpa [t1] using htrigger)]
    rw [mem_acceptingPart A t1]
    exact ⟨hstateParent, haccepting⟩
  by_cases hsurvives : acceptingState ∈ t3.label (plan.freshChild green)
  · have hstateGreen :
        acceptingState ∈ t3.label green := by
      have hsubset :
          t3.label (plan.freshChild green) ⊆ t3.label green := by
        simpa [t1, t2, t3] using
          (stage2_stage3_green_freshChild_label_subset_parent A t1 plan
            (by simpa [t1] using hrootActive)
            (by simpa [t1] using htrigger)
            (by simpa [t1, t2, t3] using hgreen))
      exact hsubset (by simpa [t3] using hsurvives)
    rcases stage1_stage2_stage3_green_label_segment_from_source
        A tree word plan
        (by simpa [t1, t2, t3] using hgreen)
        (by simpa [t1, t2, t3] using hstateGreen) with
      ⟨sourceNode, sourceState, hsourceActive, hsourceState, hsegment⟩
    exact ⟨acceptingState, sourceNode, sourceState, haccepting,
      hsourceActive, hsourceState,
      segmentVisitsAccepting_of_segment_accepting_target A word hsegment
        haccepting,
      Or.inl (by simpa [t1, t2, t3] using hstateGreen)⟩
  · rcases stage2_stage3_removed_freshChild_blocked_by_older A t1 plan
      (by simpa [t1] using htrigger)
      (by simpa [t1, t2] using hstateFresh_t2)
      (by simpa [t1, t2, t3] using hsurvives) with
      ⟨ancestor, older, hancestor, holder, holderState, haccepting'⟩
    rcases stage1_stage2_active_label_segment_from_source A tree word plan
        holder.1 holderState with
      ⟨sourceNode, sourceState, hsourceActive, hsourceState, hsegment⟩
    exact ⟨acceptingState, sourceNode, sourceState, haccepting',
      hsourceActive, hsourceState,
      segmentVisitsAccepting_of_segment_accepting_target A word hsegment
        haccepting',
      Or.inr ⟨ancestor, older,
        by simpa [t1, t2] using hancestor,
        by simpa [t1, t2] using holder,
        by simpa [t1, t2] using holderState⟩⟩

/-- `node` is a proper descendant of `ancestor` by a positive-length parent path. -/
def IsProperDescendantOf (tree : CompactTreeData A)
    (ancestor node : Node A) : Prop :=
  ∃ steps : Nat, 0 < steps ∧ (tree.parent^[steps]) node = ancestor

theorem isProperDescendantOf_child [DecidableEq A.State]
    (tree : CompactTreeData A)
    {ancestor node child : Node A}
    (hproper : tree.IsProperDescendantOf A ancestor node)
    (hchild : child ∈ tree.children A node) :
    tree.IsProperDescendantOf A ancestor child := by
  rcases hproper with ⟨steps, hpos, hsteps⟩
  rw [children, Finset.mem_filter] at hchild
  refine ⟨steps + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply]
  rw [hchild.2.2.2]
  exact hsteps

/-- Nodes removed at Piterman stage (4): proper descendants of green nodes. -/
def RemovedByGreen [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) : Prop :=
  tree.active node = true ∧
    ∃ green : Node A,
      green ∈ tree.greenNodes A ∧
        ∃ child : Node A,
          child ∈ tree.children A green ∧ tree.IsAncestorOrSelf A child node

theorem removedByGreen_exists_green_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hremoved : tree.RemovedByGreen A node) :
    ∃ green, green ∈ tree.greenNodes A ∧
      (tree.name green).val < (tree.name node).val := by
  rcases hremoved with
    ⟨hnodeActive, green, hgreen, child, hchild, hchildAncestor⟩
  rw [children, Finset.mem_filter] at hchild
  have hchildActive : tree.active child = true := hchild.2.1
  have hchildNotRoot : child ≠ root A := hchild.2.2.1
  have hparentChild : tree.parent child = green := hchild.2.2.2
  have hgreenNameLtChild :
      (tree.name green).val < (tree.name child).val := by
    have hparent := hparentInvariant child hchildActive hchildNotRoot
    simpa [hparentChild] using hparent.2
  by_cases hchildNode : child = node
  · subst child
    exact ⟨green, hgreen, hgreenNameLtChild⟩
  · have hchildNameLtNode :
        (tree.name child).val < (tree.name node).val :=
      name_lt_of_isAncestorOrSelf_ne A tree hrootParent hparentInvariant
        hnodeActive hchildAncestor hchildNode
    exact ⟨green, hgreen, by omega⟩

theorem not_removedByGreen_of_no_smaller_green
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hnoSmallerGreen :
      ∀ green, green ∈ tree.greenNodes A ->
        (tree.name node).val ≤ (tree.name green).val) :
    ¬ tree.RemovedByGreen A node := by
  intro hremoved
  rcases removedByGreen_exists_green_name_lt A tree hrootParent
      hparentInvariant hremoved with
    ⟨green, hgreen, hlt⟩
  have hle := hnoSmallerGreen green hgreen
  omega

/-- Minimum bounded name among a finite node set, or the sentinel if none exists. -/
noncomputable def minBoundedNameOf [DecidableEq A.State]
    (tree : CompactTreeData A) (nodes : Finset (Node A)) : Name A := by
  classical
  let bounded : Finset Nat :=
    nodes.filter (fun node => (tree.name node).val < Fintype.card A.State)
      |>.image (fun node => (tree.name node).val)
  by_cases hbounded : bounded.Nonempty
  · refine ⟨bounded.min' hbounded, ?_⟩
    have hmem : bounded.min' hbounded ∈ bounded := Finset.min'_mem bounded hbounded
    rcases Finset.mem_image.mp hmem with ⟨node, hnode, hname⟩
    have hlt : (tree.name node).val < Fintype.card A.State :=
      (Finset.mem_filter.mp hnode).2
    omega
  · exact sentinel A

theorem exists_node_name_eq_minBoundedNameOf_of_bounded_nonempty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (nodes : Finset (Node A))
    (hboundedExists :
      ∃ node, node ∈ nodes ∧
        (tree.name node).val < Fintype.card A.State) :
    ∃ node, node ∈ nodes ∧
      (tree.name node).val = (tree.minBoundedNameOf A nodes).val := by
  classical
  let bounded : Finset Nat :=
    (nodes.filter (fun node => (tree.name node).val < Fintype.card A.State)).image
      (fun node => (tree.name node).val)
  have hboundedNonempty : bounded.Nonempty := by
    rcases hboundedExists with ⟨node, hnode, hlt⟩
    refine ⟨(tree.name node).val, ?_⟩
    rw [Finset.mem_image]
    exact ⟨node, by simp [hnode, hlt], rfl⟩
  have hmem : bounded.min' hboundedNonempty ∈ bounded :=
    Finset.min'_mem bounded hboundedNonempty
  rcases Finset.mem_image.mp hmem with ⟨node, hnode, hname⟩
  have hnode_mem : node ∈ nodes := (Finset.mem_filter.mp hnode).1
  refine ⟨node, hnode_mem, ?_⟩
  unfold minBoundedNameOf
  simp only
  change (tree.name node).val =
    (if h : bounded.Nonempty then
      (⟨bounded.min' h, by
        have hmem' : bounded.min' h ∈ bounded := Finset.min'_mem bounded h
        rcases Finset.mem_image.mp hmem' with ⟨node', hnode', hname'⟩
        have hlt : (tree.name node').val < Fintype.card A.State :=
          (Finset.mem_filter.mp hnode').2
        omega⟩ : Name A)
    else sentinel A).val
  rw [dif_pos hboundedNonempty]
  exact hname

theorem exists_node_name_eq_minBoundedNameOf_of_min_lt_card
    [DecidableEq A.State]
    (tree : CompactTreeData A) (nodes : Finset (Node A))
    (hmin :
      (tree.minBoundedNameOf A nodes).val < Fintype.card A.State) :
    ∃ node, node ∈ nodes ∧
      (tree.name node).val = (tree.minBoundedNameOf A nodes).val := by
  classical
  let bounded : Finset Nat :=
    (nodes.filter (fun node => (tree.name node).val < Fintype.card A.State)).image
      (fun node => (tree.name node).val)
  by_cases hboundedNonempty : bounded.Nonempty
  · have hmem : bounded.min' hboundedNonempty ∈ bounded :=
      Finset.min'_mem bounded hboundedNonempty
    rcases Finset.mem_image.mp hmem with ⟨node, hnode, hname⟩
    have hnode_mem : node ∈ nodes := (Finset.mem_filter.mp hnode).1
    refine ⟨node, hnode_mem, ?_⟩
    unfold minBoundedNameOf
    simp only
    change (tree.name node).val =
      (if h : bounded.Nonempty then
        (⟨bounded.min' h, by
          have hmem' : bounded.min' h ∈ bounded := Finset.min'_mem bounded h
          rcases Finset.mem_image.mp hmem' with ⟨node', hnode', _hname'⟩
          have hlt : (tree.name node').val < Fintype.card A.State :=
            (Finset.mem_filter.mp hnode').2
          omega⟩ : Name A)
      else sentinel A).val
    rw [dif_pos hboundedNonempty]
    exact hname
  · have hsentinel :
        (tree.minBoundedNameOf A nodes).val = Fintype.card A.State := by
      unfold minBoundedNameOf
      simp only
      change
        (if h : bounded.Nonempty then
          (⟨bounded.min' h, by
            have hmem' : bounded.min' h ∈ bounded := Finset.min'_mem bounded h
            rcases Finset.mem_image.mp hmem' with ⟨node', hnode', _hname'⟩
            have hlt : (tree.name node').val < Fintype.card A.State :=
              (Finset.mem_filter.mp hnode').2
            omega⟩ : Name A)
        else sentinel A).val = Fintype.card A.State
      rw [dif_neg hboundedNonempty]
      rfl
    omega

theorem minBoundedNameOf_le_of_mem
    [DecidableEq A.State]
    (tree : CompactTreeData A) (nodes : Finset (Node A))
    {node : Node A}
    (hnode : node ∈ nodes)
    (hbound : (tree.name node).val < Fintype.card A.State) :
    (tree.minBoundedNameOf A nodes).val ≤ (tree.name node).val := by
  classical
  let bounded : Finset Nat :=
    (nodes.filter (fun node => (tree.name node).val < Fintype.card A.State)).image
      (fun node => (tree.name node).val)
  have hname_mem : (tree.name node).val ∈ bounded := by
    rw [Finset.mem_image]
    exact ⟨node, by simp [hnode, hbound], rfl⟩
  have hboundedNonempty : bounded.Nonempty :=
    ⟨(tree.name node).val, hname_mem⟩
  unfold minBoundedNameOf
  simp only
  change
    (if h : bounded.Nonempty then
      (⟨bounded.min' h, by
        have hmem' : bounded.min' h ∈ bounded := Finset.min'_mem bounded h
        rcases Finset.mem_image.mp hmem' with ⟨node', hnode', _hname'⟩
        have hlt : (tree.name node').val < Fintype.card A.State :=
          (Finset.mem_filter.mp hnode').2
        omega⟩ : Name A)
    else sentinel A).val ≤ (tree.name node).val
  rw [dif_pos hboundedNonempty]
  exact bounded.min'_le _ hname_mem

/--
The minimum bounded name of a set avoiding name `0` is positive: either it is the
sentinel (`= card ≥ 1`), or it is realized by a member, whose name is nonzero.
The intended use is `0 < e`: the same-name-delete field is the minimum name among
removed/empty nodes, and the only name-`0` node is the never-removed root.
-/
theorem minBoundedNameOf_pos_of_forall_ne_zero
    [DecidableEq A.State]
    (tree : CompactTreeData A) (nodes : Finset (Node A))
    (hne : ∀ node ∈ nodes, (tree.name node).val ≠ 0) :
    0 < (tree.minBoundedNameOf A nodes).val := by
  have hcard : 0 < Fintype.card A.State := Fintype.card_pos_iff.mpr ⟨A.initial⟩
  by_cases hlt : (tree.minBoundedNameOf A nodes).val < Fintype.card A.State
  · obtain ⟨node, hnode, hname⟩ :=
      exists_node_name_eq_minBoundedNameOf_of_min_lt_card A tree nodes hlt
    rw [← hname]
    exact Nat.pos_of_ne_zero (hne node hnode)
  · omega

theorem not_removedByGreen_of_name_le_green_minBoundedName
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hle :
      (tree.name node).val ≤
        (tree.minBoundedNameOf A (tree.greenNodes A)).val) :
    ¬ tree.RemovedByGreen A node := by
  intro hremoved
  rcases removedByGreen_exists_green_name_lt A tree hrootParent
      hparentInvariant hremoved with
    ⟨green, hgreen, hgreenLtNode⟩
  have hgreenBound : (tree.name green).val < Fintype.card A.State :=
    hgreenLtNode.trans hnodeBound
  have hminLeGreen :
      (tree.minBoundedNameOf A (tree.greenNodes A)).val ≤
        (tree.name green).val :=
    minBoundedNameOf_le_of_mem A tree (tree.greenNodes A) hgreen
      hgreenBound
  omega

theorem exists_green_name_eq_minBoundedNameOf
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hgreenNonempty : (tree.greenNodes A).Nonempty) :
    ∃ green, green ∈ tree.greenNodes A ∧
      (tree.name green).val =
        (tree.minBoundedNameOf A (tree.greenNodes A)).val := by
  rcases hgreenNonempty with ⟨green, hgreen⟩
  have hgreenActive : tree.active green = true :=
    (mem_greenNodes A tree).mp hgreen |>.1
  exact exists_node_name_eq_minBoundedNameOf_of_bounded_nonempty
    A tree (tree.greenNodes A)
    ⟨green, hgreen, hbound green hgreenActive⟩

/--
Piterman Section 3.2, transition stage (4): green nodes delete all their
descendants and set `f` to the minimum green name.
-/
noncomputable def stage4 [DecidableEq A.State]
    (tree : CompactTreeData A) : CompactTreeData A where
  active node := by
    classical
    exact if tree.RemovedByGreen A node then false else tree.active node
  name := tree.name
  parent := tree.parent
  label node := by
    classical
    exact if tree.RemovedByGreen A node then ∅ else tree.label node
  e := sentinel A
  f := tree.minBoundedNameOf A (tree.greenNodes A)

theorem stage4_removed_inactive [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hremoved : tree.RemovedByGreen A node) :
    (tree.stage4 A).active node = false := by
  simp [stage4, hremoved]

theorem stage4_removed_label [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hremoved : tree.RemovedByGreen A node) :
    (tree.stage4 A).label node = ∅ := by
  simp [stage4, hremoved]

theorem stage4_keeps_unremoved_active [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hnot : ¬ tree.RemovedByGreen A node) :
    (tree.stage4 A).active node = tree.active node := by
  simp [stage4, hnot]

theorem stage4_name [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage4 A).name node = tree.name node := rfl

theorem stage4_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage4 A).parent node = tree.parent node := rfl

theorem stage4_keeps_unremoved_label [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hnot : ¬ tree.RemovedByGreen A node) :
    (tree.stage4 A).label node = tree.label node := by
  simp [stage4, hnot]

theorem stage4_f_val [DecidableEq A.State]
    (tree : CompactTreeData A) :
    ((tree.stage4 A).f).val =
      (tree.minBoundedNameOf A (tree.greenNodes A)).val := by
  rfl

theorem stage4_not_removedByGreen_of_name_le_f
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hle : (tree.name node).val ≤ ((tree.stage4 A).f).val) :
    ¬ tree.RemovedByGreen A node := by
  exact not_removedByGreen_of_name_le_green_minBoundedName A tree
    hrootParent hparentInvariant hnodeBound
    (by simpa [stage4_f_val A tree] using hle)

theorem stage4_keeps_active_of_name_le_f
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A}
    (hnodeActive : tree.active node = true)
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hle : (tree.name node).val ≤ ((tree.stage4 A).f).val) :
    (tree.stage4 A).active node = true := by
  rw [stage4_keeps_unremoved_active A tree
    (stage4_not_removedByGreen_of_name_le_f A tree hrootParent
      hparentInvariant hnodeBound hle)]
  exact hnodeActive

theorem exists_green_name_eq_stage4_f
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hgreenNonempty : (tree.greenNodes A).Nonempty) :
    ∃ green, green ∈ tree.greenNodes A ∧
      (tree.name green).val = ((tree.stage4 A).f).val := by
  simpa [stage4_f_val A tree] using
    exists_green_name_eq_minBoundedNameOf A tree hbound hgreenNonempty

theorem stage4_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (node : Node A) :
    (tree.stage4 A).label node ⊆ tree.label node := by
  classical
  intro state hstate
  by_cases hremoved : tree.RemovedByGreen A node
  · rw [stage4_removed_label A tree hremoved] at hstate
    simp at hstate
  · rw [stage4_keeps_unremoved_label A tree hremoved] at hstate
    exact hstate

theorem stage4_active_cases [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hactive : (tree.stage4 A).active node = true) :
    tree.active node = true ∧ ¬ tree.RemovedByGreen A node := by
  classical
  by_cases hremoved : tree.RemovedByGreen A node
  · have hinactive := stage4_removed_inactive A tree hremoved
    rw [hinactive] at hactive
    simp at hactive
  · have hkeep := stage4_keeps_unremoved_active A tree hremoved
    rw [hkeep] at hactive
    exact ⟨hactive, hremoved⟩

theorem stage4_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage4 A).active node = false ->
      (tree.stage4 A).label node = ∅ := by
  intro node hactive
  classical
  by_cases hremoved : tree.RemovedByGreen A node
  · exact stage4_removed_label A tree hremoved
  · rw [stage4_keeps_unremoved_label A tree hremoved]
    rw [stage4_keeps_unremoved_active A tree hremoved] at hactive
    exact hinactiveLabel node hactive

theorem stage4_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < 2 * Fintype.card A.State) :
    ∀ node, (tree.stage4 A).active node = true ->
      ((tree.stage4 A).name node).val < 2 * Fintype.card A.State := by
  intro node hactive
  exact hbound node (stage4_active_cases A tree hactive).1

theorem stage4_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage4 A).active left = true ->
      (tree.stage4 A).active right = true ->
      (tree.stage4 A).name left = (tree.stage4 A).name right ->
        left = right := by
  intro left right hleft hright hname
  exact hinjective left right
    (stage4_active_cases A tree hleft).1
    (stage4_active_cases A tree hright).1
    (by simpa [stage4] using hname)

theorem stage4_child_old_child [DecidableEq A.State]
    (tree : CompactTreeData A) {node child : Node A}
    (hchild : child ∈ (tree.stage4 A).children A node) :
    child ∈ tree.children A node ∧ ¬ tree.RemovedByGreen A child := by
  rw [children, Finset.mem_filter] at hchild
  have hcases := stage4_active_cases A tree hchild.2.1
  have hparent : tree.parent child = node := by
    simpa [stage4] using hchild.2.2.2
  constructor
  · rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcases.1, hchild.2.2.1, hparent⟩
  · exact hcases.2

theorem stage4_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, ¬ tree.RemovedByGreen A node ->
      child ∈ (tree.stage4 A).children A node ->
      (tree.stage4 A).label child ⊆ (tree.stage4 A).label node := by
  intro node child hnode_not_removed hchild state hstate
  have hchild_old := stage4_child_old_child A tree hchild
  have hchild_not_removed := hchild_old.2
  rw [stage4_keeps_unremoved_label A tree hchild_not_removed] at hstate
  rw [stage4_keeps_unremoved_label A tree hnode_not_removed]
  exact hchildSubset node child hchild_old.1 hstate

theorem stage4_preserves_sibling_disjoint [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    ∀ node left right,
      left ∈ (tree.stage4 A).children A node ->
      right ∈ (tree.stage4 A).children A node ->
      left ≠ right ->
        Disjoint ((tree.stage4 A).label left) ((tree.stage4 A).label right) := by
  intro node left right hleft hright hne
  have hleft_old := stage4_child_old_child A tree hleft
  have hright_old := stage4_child_old_child A tree hright
  rw [stage4_keeps_unremoved_label A tree hleft_old.2]
  rw [stage4_keeps_unremoved_label A tree hright_old.2]
  exact hsiblingDisjoint node left right hleft_old.1 hright_old.1 hne

/-- The finite set of nodes deleted by stage (4). -/
noncomputable def greenRemovedNodes [DecidableEq A.State]
    (tree : CompactTreeData A) : Finset (Node A) := by
  classical
  exact Finset.univ.filter (fun node => tree.RemovedByGreen A node)

theorem mem_greenRemovedNodes [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.greenRemovedNodes A ↔ tree.RemovedByGreen A node := by
  classical
  simp [greenRemovedNodes]

theorem removedByGreen_active [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hremoved : tree.RemovedByGreen A node) :
    tree.active node = true :=
  hremoved.1

theorem root_not_removedByGreen [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A) :
    ¬ tree.RemovedByGreen A (root A) := by
  intro hremoved
  rcases hremoved with ⟨_hactive, green, _hgreen, child, hchild, hancestor⟩
  have hchild_root : child = root A :=
    isAncestorOrSelf_from_root_eq_root A tree hrootParent hancestor
  rw [children, Finset.mem_filter] at hchild
  exact hchild.2.2.1 hchild_root

theorem greenRemovedNodes_active [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A}
    (hnode : node ∈ tree.greenRemovedNodes A) :
    tree.active node = true :=
  removedByGreen_active A tree ((mem_greenRemovedNodes A tree).mp hnode)

theorem greenRemovedNodes_child_closed_after_stage4 [DecidableEq A.State]
    (tree : CompactTreeData A) :
    ∀ node child, child ∈ (tree.stage4 A).children A node ->
      node ∈ tree.greenRemovedNodes A -> child ∈ tree.greenRemovedNodes A := by
  intro node child hchild hnode
  have hchild_old := stage4_child_old_child A tree hchild
  have hremoved_node : tree.RemovedByGreen A node :=
    (mem_greenRemovedNodes A tree).mp hnode
  rcases hremoved_node with ⟨_hnodeActive, green, hgreen, hproper⟩
  have hchild_active : tree.active child = true := by
    have hchild_mem := hchild_old.1
    rw [children, Finset.mem_filter] at hchild_mem
    exact hchild_mem.2.1
  rcases hproper with ⟨greenChild, hgreenChild, hancestor⟩
  exact (mem_greenRemovedNodes A tree).mpr
    ⟨hchild_active,
      green, hgreen, greenChild, hgreenChild,
        isAncestorOrSelf_of_child A tree hancestor hchild_old.1⟩

theorem stage4_no_child_of_green [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node child : Node A}
    (hgreen : node ∈ tree.greenNodes A) :
    child ∉ (tree.stage4 A).children A node := by
  intro hchild
  have hchild_old := stage4_child_old_child A tree hchild
  have hchild_active : tree.active child = true := by
    rw [children, Finset.mem_filter] at hchild_old
    exact hchild_old.1.2.1
  have hremoved : tree.RemovedByGreen A child :=
    ⟨hchild_active, node, hgreen, child, hchild_old.1,
      isAncestorOrSelf_refl A tree child⟩
  exact hchild_old.2 hremoved

theorem stage4_preserves_child_label_subset_of_green_closed
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage4 A).children A node ->
      (tree.stage4 A).label child ⊆ (tree.stage4 A).label node := by
  intro node child hchild
  have hchild_old := stage4_child_old_child A tree hchild
  have hnode_not_removed : ¬ tree.RemovedByGreen A node := by
    intro hnode_removed
    have hchild_removed_mem : child ∈ tree.greenRemovedNodes A :=
      greenRemovedNodes_child_closed_after_stage4 A tree
        node child hchild ((mem_greenRemovedNodes A tree).mpr hnode_removed)
    exact hchild_old.2 ((mem_greenRemovedNodes A tree).mp hchild_removed_mem)
  exact stage4_preserves_child_label_subset A tree hchildSubset
    node child hnode_not_removed hchild

/-- Active nodes with empty labels, removed by Piterman stage (5). -/
def emptyActiveNodes [DecidableEq A.State]
    (tree : CompactTreeData A) : Finset (Node A) :=
  (tree.activeNodes A).filter (fun node => tree.label node = ∅)

theorem mem_emptyActiveNodes [DecidableEq A.State]
    (tree : CompactTreeData A) {node : Node A} :
    node ∈ tree.emptyActiveNodes A ↔
      tree.active node = true ∧ tree.label node = ∅ := by
  simp [emptyActiveNodes, activeNodes]

def RemovedByStage5 [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (node : Node A) : Prop :=
  node ∈ previouslyRemoved ∨ node ∈ tree.emptyActiveNodes A

/--
Piterman Section 3.2, transition stage (5): remove empty-label nodes and set
`e` to the minimum name removed in this transition, including earlier stages.
-/
noncomputable def stage5 [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A)) :
    CompactTreeData A where
  active node := by
    classical
    exact if tree.RemovedByStage5 A previouslyRemoved node then false else tree.active node
  name := tree.name
  parent := tree.parent
  label node := by
    classical
    exact if tree.RemovedByStage5 A previouslyRemoved node then ∅ else tree.label node
  e := tree.minBoundedNameOf A (previouslyRemoved ∪ tree.emptyActiveNodes A)
  f := tree.f

theorem stage5_removed_inactive [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hremoved : tree.RemovedByStage5 A previouslyRemoved node) :
    (tree.stage5 A previouslyRemoved).active node = false := by
  simp [stage5, hremoved]

theorem stage5_removed_label [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hremoved : tree.RemovedByStage5 A previouslyRemoved node) :
    (tree.stage5 A previouslyRemoved).label node = ∅ := by
  simp [stage5, hremoved]

theorem stage5_keeps_unremoved_active [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hnot : ¬ tree.RemovedByStage5 A previouslyRemoved node) :
    (tree.stage5 A previouslyRemoved).active node = tree.active node := by
  simp [stage5, hnot]

theorem stage5_name [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (node : Node A) :
    (tree.stage5 A previouslyRemoved).name node = tree.name node := rfl

theorem stage5_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (node : Node A) :
    (tree.stage5 A previouslyRemoved).parent node = tree.parent node := rfl

theorem stage5_keeps_unremoved_label [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hnot : ¬ tree.RemovedByStage5 A previouslyRemoved node) :
    (tree.stage5 A previouslyRemoved).label node = tree.label node := by
  simp [stage5, hnot]

theorem stage5_f_val [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A)) :
    ((tree.stage5 A previouslyRemoved).f).val = tree.f.val := by
  rfl

theorem stage5_e_val [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A)) :
    ((tree.stage5 A previouslyRemoved).e).val =
      (tree.minBoundedNameOf A
        (previouslyRemoved ∪ tree.emptyActiveNodes A)).val := by
  rfl

theorem stage5_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (node : Node A) :
    (tree.stage5 A previouslyRemoved).label node ⊆ tree.label node := by
  classical
  intro state hstate
  by_cases hremoved : tree.RemovedByStage5 A previouslyRemoved node
  · rw [stage5_removed_label A tree previouslyRemoved hremoved] at hstate
    simp at hstate
  · rw [stage5_keeps_unremoved_label A tree previouslyRemoved hremoved] at hstate
    exact hstate

theorem stage5_active_cases [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hactive : (tree.stage5 A previouslyRemoved).active node = true) :
    tree.active node = true ∧
      ¬ tree.RemovedByStage5 A previouslyRemoved node := by
  classical
  by_cases hremoved : tree.RemovedByStage5 A previouslyRemoved node
  · have hinactive := stage5_removed_inactive A tree previouslyRemoved hremoved
    rw [hinactive] at hactive
    simp at hactive
  · have hkeep := stage5_keeps_unremoved_active A tree previouslyRemoved hremoved
    rw [hkeep] at hactive
    exact ⟨hactive, hremoved⟩

theorem stage5_empty_active_removed [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hnode : node ∈ tree.emptyActiveNodes A) :
    (tree.stage5 A previouslyRemoved).active node = false := by
  exact stage5_removed_inactive A tree previouslyRemoved (Or.inr hnode)

theorem stage5_active_label_nonempty [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hactive : (tree.stage5 A previouslyRemoved).active node = true) :
    (tree.stage5 A previouslyRemoved).label node ≠ ∅ := by
  intro hlabel
  have hcases := stage5_active_cases A tree previouslyRemoved hactive
  have hnot_removed := hcases.2
  have hold_label : tree.label node = ∅ := by
    rw [← stage5_keeps_unremoved_label A tree previouslyRemoved hnot_removed]
    exact hlabel
  have hempty : node ∈ tree.emptyActiveNodes A := by
    rw [mem_emptyActiveNodes A tree]
    exact ⟨hcases.1, hold_label⟩
  exact hnot_removed (Or.inr hempty)

theorem stage5_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage5 A previouslyRemoved).active node = false ->
      (tree.stage5 A previouslyRemoved).label node = ∅ := by
  intro node hactive
  classical
  by_cases hremoved : tree.RemovedByStage5 A previouslyRemoved node
  · exact stage5_removed_label A tree previouslyRemoved hremoved
  · rw [stage5_keeps_unremoved_label A tree previouslyRemoved hremoved]
    rw [stage5_keeps_unremoved_active A tree previouslyRemoved hremoved] at hactive
    exact hinactiveLabel node hactive

theorem stage5_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < 2 * Fintype.card A.State) :
    ∀ node, (tree.stage5 A previouslyRemoved).active node = true ->
      ((tree.stage5 A previouslyRemoved).name node).val <
        2 * Fintype.card A.State := by
  intro node hactive
  exact hbound node (stage5_active_cases A tree previouslyRemoved hactive).1

theorem stage5_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage5 A previouslyRemoved).active left = true ->
      (tree.stage5 A previouslyRemoved).active right = true ->
      (tree.stage5 A previouslyRemoved).name left =
        (tree.stage5 A previouslyRemoved).name right ->
        left = right := by
  intro left right hleft hright hname
  exact hinjective left right
    (stage5_active_cases A tree previouslyRemoved hleft).1
    (stage5_active_cases A tree previouslyRemoved hright).1
    (by simpa [stage5] using hname)

theorem stage5_child_old_child [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node child : Node A}
    (hchild : child ∈ (tree.stage5 A previouslyRemoved).children A node) :
    child ∈ tree.children A node ∧
      ¬ tree.RemovedByStage5 A previouslyRemoved child := by
  rw [children, Finset.mem_filter] at hchild
  have hcases := stage5_active_cases A tree previouslyRemoved hchild.2.1
  have hparent : tree.parent child = node := by
    simpa [stage5] using hchild.2.2.2
  constructor
  · rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcases.1, hchild.2.2.1, hparent⟩
  · exact hcases.2

theorem stage4_stage5_no_child_of_green [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node child : Node A}
    (hgreen : node ∈ tree.greenNodes A) :
    child ∉ ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).children A node := by
  intro hchild
  have hchild4 :=
    (stage5_child_old_child A (tree.stage4 A) (tree.greenRemovedNodes A) hchild).1
  exact stage4_no_child_of_green A tree hgreen hchild4

theorem stage5_child_removed_of_parent_removed [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hpreviousChildClosed :
      ∀ node child, child ∈ tree.children A node ->
        node ∈ previouslyRemoved -> child ∈ previouslyRemoved)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    {node child : Node A}
    (hchild : child ∈ tree.children A node)
    (hremoved : tree.RemovedByStage5 A previouslyRemoved node) :
    tree.RemovedByStage5 A previouslyRemoved child := by
  rcases hremoved with hprevious | hempty
  · exact Or.inl (hpreviousChildClosed node child hchild hprevious)
  · rw [mem_emptyActiveNodes A tree] at hempty
    have hchild_old : child ∈ tree.children A node := hchild
    rw [children, Finset.mem_filter] at hchild
    have hchild_active : tree.active child = true := hchild.2.1
    have hsubset : tree.label child ⊆ tree.label node :=
      hchildSubset node child hchild_old
    have hchild_empty : tree.label child = ∅ := by
      ext state
      constructor
      · intro hstate
        have hstate_node : state ∈ tree.label node := hsubset hstate
        rw [hempty.2] at hstate_node
        simp at hstate_node
      · intro hstate
        simp at hstate
    exact Or.inr ((mem_emptyActiveNodes A tree).mpr
      ⟨hchild_active, hchild_empty⟩)

theorem stage5_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, ¬ tree.RemovedByStage5 A previouslyRemoved node ->
      child ∈ (tree.stage5 A previouslyRemoved).children A node ->
      (tree.stage5 A previouslyRemoved).label child ⊆
        (tree.stage5 A previouslyRemoved).label node := by
  intro node child hnode_not_removed hchild state hstate
  have hchild_old := stage5_child_old_child A tree previouslyRemoved hchild
  have hchild_not_removed := hchild_old.2
  rw [stage5_keeps_unremoved_label A tree previouslyRemoved hchild_not_removed] at hstate
  rw [stage5_keeps_unremoved_label A tree previouslyRemoved hnode_not_removed]
  exact hchildSubset node child hchild_old.1 hstate

theorem stage5_preserves_child_label_subset_of_child_closed_removed
    [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hpreviousChildClosed :
      ∀ node child, child ∈ tree.children A node ->
        node ∈ previouslyRemoved -> child ∈ previouslyRemoved)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage5 A previouslyRemoved).children A node ->
      (tree.stage5 A previouslyRemoved).label child ⊆
        (tree.stage5 A previouslyRemoved).label node := by
  intro node child hchild state hstate
  have hchild_old := stage5_child_old_child A tree previouslyRemoved hchild
  have hnode_not_removed :
      ¬ tree.RemovedByStage5 A previouslyRemoved node := by
    intro hnode_removed
    exact hchild_old.2
      (stage5_child_removed_of_parent_removed A tree previouslyRemoved
        hpreviousChildClosed hchildSubset hchild_old.1 hnode_removed)
  exact stage5_preserves_child_label_subset A tree previouslyRemoved hchildSubset
    node child hnode_not_removed hchild hstate

theorem stage5_preserves_parent_active_and_name_lt_of_child_closed_removed
    [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hpreviousChildClosed :
      ∀ node child, child ∈ tree.children A node ->
        node ∈ previouslyRemoved -> child ∈ previouslyRemoved) :
    ∀ node,
      (tree.stage5 A previouslyRemoved).active node = true ->
      node ≠ root A ->
        (tree.stage5 A previouslyRemoved).active
            ((tree.stage5 A previouslyRemoved).parent node) = true ∧
          ((tree.stage5 A previouslyRemoved).name
              ((tree.stage5 A previouslyRemoved).parent node)).val <
            ((tree.stage5 A previouslyRemoved).name node).val := by
  intro node hactive hnot_root
  have hcases := stage5_active_cases A tree previouslyRemoved hactive
  have hold_parent := hparentInvariant node hcases.1 hnot_root
  have hold_child : node ∈ tree.children A (tree.parent node) := by
    rw [children, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hcases.1, hnot_root, rfl⟩
  have hparent_not_removed :
      ¬ tree.RemovedByStage5 A previouslyRemoved (tree.parent node) := by
    intro hparent_removed
    exact hcases.2
      (stage5_child_removed_of_parent_removed A tree previouslyRemoved
        hpreviousChildClosed hchildSubset hold_child hparent_removed)
  constructor
  · rw [stage5_parent A tree previouslyRemoved node]
    rw [stage5_keeps_unremoved_active A tree previouslyRemoved hparent_not_removed]
    exact hold_parent.1
  · simp [stage5]
    exact hold_parent.2

theorem stage5_preserves_sibling_disjoint [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    ∀ node left right,
      left ∈ (tree.stage5 A previouslyRemoved).children A node ->
      right ∈ (tree.stage5 A previouslyRemoved).children A node ->
      left ≠ right ->
        Disjoint ((tree.stage5 A previouslyRemoved).label left)
          ((tree.stage5 A previouslyRemoved).label right) := by
  intro node left right hleft hright hne
  have hleft_old := stage5_child_old_child A tree previouslyRemoved hleft
  have hright_old := stage5_child_old_child A tree previouslyRemoved hright
  rw [stage5_keeps_unremoved_label A tree previouslyRemoved hleft_old.2]
  rw [stage5_keeps_unremoved_label A tree previouslyRemoved hright_old.2]
  exact hsiblingDisjoint node left right hleft_old.1 hright_old.1 hne

theorem stage4_stage5_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      ((tree.stage4 A).stage5 A previouslyRemoved).active left = true ->
      ((tree.stage4 A).stage5 A previouslyRemoved).active right = true ->
      ((tree.stage4 A).stage5 A previouslyRemoved).name left =
        ((tree.stage4 A).stage5 A previouslyRemoved).name right ->
        left = right := by
  exact stage5_preserves_name_injective A (tree.stage4 A) previouslyRemoved
    (stage4_preserves_name_injective A tree hinjective)

theorem stage4_stage5_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, ((tree.stage4 A).stage5 A previouslyRemoved).active node = false ->
      ((tree.stage4 A).stage5 A previouslyRemoved).label node = ∅ := by
  exact stage5_preserves_inactive_label A (tree.stage4 A) previouslyRemoved
    (stage4_preserves_inactive_label A tree hinactiveLabel)

theorem stage4_stage5_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < 2 * Fintype.card A.State) :
    ∀ node, ((tree.stage4 A).stage5 A previouslyRemoved).active node = true ->
      (((tree.stage4 A).stage5 A previouslyRemoved).name node).val <
        2 * Fintype.card A.State := by
  exact stage5_preserves_name_bound A (tree.stage4 A) previouslyRemoved
    (stage4_preserves_name_bound A tree hbound)

theorem stage4_stage5_preserves_sibling_disjoint [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    ∀ node left right,
      left ∈ ((tree.stage4 A).stage5 A previouslyRemoved).children A node ->
      right ∈ ((tree.stage4 A).stage5 A previouslyRemoved).children A node ->
      left ≠ right ->
        Disjoint (((tree.stage4 A).stage5 A previouslyRemoved).label left)
          (((tree.stage4 A).stage5 A previouslyRemoved).label right) := by
  exact stage5_preserves_sibling_disjoint A (tree.stage4 A) previouslyRemoved
    (stage4_preserves_sibling_disjoint A tree hsiblingDisjoint)

theorem stage4_stage5_preserves_child_label_subset
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child,
      child ∈ ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).children A node ->
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).label child ⊆
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).label node := by
  exact
    stage5_preserves_child_label_subset_of_child_closed_removed A
      (tree.stage4 A) (tree.greenRemovedNodes A)
      (greenRemovedNodes_child_closed_after_stage4 A tree)
      (stage4_preserves_child_label_subset_of_green_closed A tree hchildSubset)

theorem stage4_stage5_active_label_nonempty [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A)) :
    ∀ node, ((tree.stage4 A).stage5 A previouslyRemoved).active node = true ->
      ((tree.stage4 A).stage5 A previouslyRemoved).label node ≠ ∅ := by
  intro node hactive
  exact stage5_active_label_nonempty A (tree.stage4 A) previouslyRemoved hactive

theorem stage4_stage5_preserves_childLabelUnion_ssubset
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node,
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active node = true ->
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).childLabelUnion A node ⊂
          ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).label node := by
  intro node hactive
  let t5 := (tree.stage4 A).stage5 A (tree.greenRemovedNodes A)
  have hsubset :
      t5.childLabelUnion A node ⊆ t5.label node := by
    exact childLabelUnion_subset_label A t5
      (stage4_stage5_preserves_child_label_subset A tree hchildSubset) node
  refine ⟨hsubset, ?_⟩
  intro hreverse
  have hnonempty : t5.label node ≠ ∅ := by
    exact stage4_stage5_active_label_nonempty A tree
      (tree.greenRemovedNodes A) node hactive
  by_cases hgreen : node ∈ tree.greenNodes A
  · have hunion_empty : t5.childLabelUnion A node = ∅ := by
      ext state
      constructor
      · intro hstate
        rw [childLabelUnion] at hstate
        rw [Finset.mem_biUnion] at hstate
        rcases hstate with ⟨child, hchild, _hstateChild⟩
        exact False.elim
          (stage4_stage5_no_child_of_green A tree hgreen hchild)
      · intro hstate
        simp at hstate
    have hlabel_empty : t5.label node = ∅ := by
      ext state
      constructor
      · intro hstate
        have hstateUnion : state ∈ t5.childLabelUnion A node := hreverse hstate
        rw [hunion_empty] at hstateUnion
        simp at hstateUnion
      · intro hstate
        simp at hstate
    exact hnonempty hlabel_empty
  · have hstage4_active : (tree.stage4 A).active node = true :=
      (stage5_active_cases A (tree.stage4 A) (tree.greenRemovedNodes A)
        (by simpa [t5] using hactive)).1
    have hstage5_not_removed :
        ¬ (tree.stage4 A).RemovedByStage5 A (tree.greenRemovedNodes A) node :=
      (stage5_active_cases A (tree.stage4 A) (tree.greenRemovedNodes A)
        (by simpa [t5] using hactive)).2
    have hstage4_cases := stage4_active_cases A tree hstage4_active
    have htree_active : tree.active node = true := hstage4_cases.1
    have hstage4_not_removed : ¬ tree.RemovedByGreen A node := hstage4_cases.2
    have hlabel_t5_tree : t5.label node = tree.label node := by
      calc
        t5.label node = (tree.stage4 A).label node := by
          simpa [t5] using
            stage5_keeps_unremoved_label A (tree.stage4 A)
              (tree.greenRemovedNodes A) hstage5_not_removed
        _ = tree.label node := stage4_keeps_unremoved_label A tree hstage4_not_removed
    have htree_label_subset_union :
        tree.label node ⊆ tree.childLabelUnion A node := by
      intro state hstate
      have hstateT5 : state ∈ t5.label node := by
        simpa [hlabel_t5_tree] using hstate
      have hstateUnion : state ∈ t5.childLabelUnion A node := hreverse hstateT5
      rw [childLabelUnion] at hstateUnion
      rw [Finset.mem_biUnion] at hstateUnion
      rcases hstateUnion with ⟨child, hchildT5, hstateChildT5⟩
      have hchildStage5 :=
        stage5_child_old_child A (tree.stage4 A) (tree.greenRemovedNodes A)
          (by simpa [t5] using hchildT5)
      have hchild4 : child ∈ (tree.stage4 A).children A node := hchildStage5.1
      have hchild5_not_removed : ¬ (tree.stage4 A).RemovedByStage5 A
          (tree.greenRemovedNodes A) child := hchildStage5.2
      have hchildOld := stage4_child_old_child A tree hchild4
      have hchild4_not_removed : ¬ tree.RemovedByGreen A child := hchildOld.2
      have hchildLabel_t5_tree : t5.label child = tree.label child := by
        calc
          t5.label child = (tree.stage4 A).label child := by
            simpa [t5] using
              stage5_keeps_unremoved_label A (tree.stage4 A)
                (tree.greenRemovedNodes A) hchild5_not_removed
          _ = tree.label child :=
              stage4_keeps_unremoved_label A tree hchild4_not_removed
      rw [childLabelUnion]
      rw [Finset.mem_biUnion]
      exact ⟨child, hchildOld.1, by
        simpa [hchildLabel_t5_tree] using hstateChildT5⟩
    have htree_union_subset_label :
        tree.childLabelUnion A node ⊆ tree.label node :=
      childLabelUnion_subset_label A tree hchildSubset node
    have hgreen' : node ∈ tree.greenNodes A := by
      rw [mem_greenNodes A tree]
      exact ⟨htree_active,
        Finset.Subset.antisymm htree_label_subset_union
          htree_union_subset_label⟩
    exact hgreen hgreen'

theorem stage4_stage5_removed_active [DecidableEq A.State]
    (tree : CompactTreeData A) :
    ∀ node,
      node ∈ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A ->
        tree.active node = true := by
  intro node hnode
  rw [Finset.mem_union] at hnode
  rcases hnode with hgreen | hempty
  · exact greenRemovedNodes_active A tree hgreen
  · have hstage4_active : (tree.stage4 A).active node = true :=
      (mem_emptyActiveNodes A (tree.stage4 A)).mp hempty |>.1
    exact (stage4_active_cases A tree hstage4_active).1

theorem stage4_stage5_active_not_removed [DecidableEq A.State]
    (tree : CompactTreeData A) :
    ∀ node,
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active node = true ->
        node ∉ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A := by
  intro node hactive hremoved
  have hcases :=
    stage5_active_cases A (tree.stage4 A) (tree.greenRemovedNodes A) hactive
  rw [Finset.mem_union] at hremoved
  exact hcases.2 hremoved

theorem stage4_stage5_name_injective_on_removed_or_active
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (left ∈ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A ∨
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active left = true) ->
      (right ∈ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A ∨
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active right = true) ->
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name left =
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name right ->
        left = right := by
  intro left right hleft hright hname
  have hleft_active : tree.active left = true := by
    rcases hleft with hremoved | hactive
    · exact stage4_stage5_removed_active A tree left hremoved
    · have hstage4_active :
        (tree.stage4 A).active left = true :=
          (stage5_active_cases A (tree.stage4 A)
            (tree.greenRemovedNodes A) hactive).1
      exact (stage4_active_cases A tree hstage4_active).1
  have hright_active : tree.active right = true := by
    rcases hright with hremoved | hactive
    · exact stage4_stage5_removed_active A tree right hremoved
    · have hstage4_active :
        (tree.stage4 A).active right = true :=
          (stage5_active_cases A (tree.stage4 A)
            (tree.greenRemovedNodes A) hactive).1
      exact (stage4_active_cases A tree hstage4_active).1
  apply hinjective left right hleft_active hright_active
  simpa [stage5, stage4] using hname

theorem stage4_stage5_active_of_not_removed
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    {node : Node A}
    (hactive : tree.active node = true)
    (hnotRemoved :
      node ∉ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A) :
    ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active node = true := by
  have hnotGreen : ¬ tree.RemovedByGreen A node := by
    intro hremoved
    exact hnotRemoved (Finset.mem_union_left _
      ((mem_greenRemovedNodes A tree).mpr hremoved))
  have hstage4_active : (tree.stage4 A).active node = true := by
    rw [stage4_keeps_unremoved_active A tree hnotGreen]
    exact hactive
  have hnotStage5 :
      ¬ (tree.stage4 A).RemovedByStage5 A (tree.greenRemovedNodes A) node := by
    intro hremoved
    rcases hremoved with hgreen | hempty
    · exact hnotRemoved (Finset.mem_union_left _ hgreen)
    · exact hnotRemoved (Finset.mem_union_right _ hempty)
  rw [stage5_keeps_unremoved_active A (tree.stage4 A)
    (tree.greenRemovedNodes A) hnotStage5]
  exact hstage4_active

theorem stage4_stage5_packed_lower_name_coverage
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hcover :
      ∀ node, tree.active node = true ->
        ∀ j : Nat, j < (tree.name node).val ->
          ∃ old, tree.active old = true ∧ (tree.name old).val = j) :
    ∀ node,
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active node = true ->
        ∀ j : Nat,
          j < (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name node).val ->
            ∃ old,
              (old ∈ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A ∨
                ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active old = true) ∧
              (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name old).val = j := by
  intro node hactive j hj
  have hstage4_active : (tree.stage4 A).active node = true :=
    (stage5_active_cases A (tree.stage4 A) (tree.greenRemovedNodes A) hactive).1
  have htree_active : tree.active node = true :=
    (stage4_active_cases A tree hstage4_active).1
  have hj_tree : j < (tree.name node).val := by
    simpa [stage5_name, stage4_name] using hj
  obtain ⟨old, hold_active, hold_name⟩ := hcover node htree_active j hj_tree
  by_cases hremoved :
      old ∈ tree.greenRemovedNodes A ∪ (tree.stage4 A).emptyActiveNodes A
  · refine ⟨old, ⟨Or.inl hremoved, ?_⟩⟩
    simpa [stage5_name, stage4_name] using hold_name
  · have hold_stage5_active :
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active old = true :=
      stage4_stage5_active_of_not_removed A tree hold_active hremoved
    refine ⟨old, ⟨Or.inr hold_stage5_active, ?_⟩⟩
    simpa [stage5_name, stage4_name] using hold_name

theorem stage4_stage5_preserves_parent_active_and_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node,
      ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active node = true ->
      node ≠ root A ->
        ((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).active
            (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).parent node) = true ∧
          (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name
              (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).parent node)).val <
            (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).name node).val := by
  exact
    stage5_preserves_parent_active_and_name_lt_of_child_closed_removed A
      (tree.stage4 A) (tree.greenRemovedNodes A)
      (by
        intro node hactive hnot_root
        have hcases := stage4_active_cases A tree hactive
        have hold := hparentInvariant node hcases.1 hnot_root
        have hparent_not_removed : ¬ tree.RemovedByGreen A (tree.parent node) := by
          intro hparent_removed
          rcases hparent_removed with
            ⟨_hparentActive, green, hgreen, greenChild, hgreenChild, hancestor⟩
          exact hcases.2
            ⟨hcases.1,
              green, hgreen, greenChild, hgreenChild,
              isAncestorOrSelf_of_child A tree hancestor
                (by
                  rw [children, Finset.mem_filter]
                  exact ⟨Finset.mem_univ _, hcases.1, hnot_root, rfl⟩)⟩
        constructor
        · rw [stage4_parent A tree node]
          rw [stage4_keeps_unremoved_active A tree hparent_not_removed]
          exact hold.1
        · simp [stage4]
          exact hold.2)
      (by
        exact stage4_preserves_child_label_subset_of_green_closed A tree hchildSubset)
      (greenRemovedNodes_child_closed_after_stage4 A tree)

theorem stage4_stage5_activeNodes_card_le_state_card
    [DecidableEq A.State]
    (tree : CompactTreeData A)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node)
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    (((tree.stage4 A).stage5 A (tree.greenRemovedNodes A)).activeNodes A).card ≤
      Fintype.card A.State := by
  let t5 := (tree.stage4 A).stage5 A (tree.greenRemovedNodes A)
  have ht5_rootParent : t5.parent (root A) = root A := by
    simpa [t5, stage5_parent, stage4_parent] using hrootParent
  have ht5_parent :
      ∀ node, t5.active node = true -> node ≠ root A ->
        t5.active (t5.parent node) = true ∧
          (t5.name (t5.parent node)).val < (t5.name node).val := by
    simpa [t5] using
      (stage4_stage5_preserves_parent_active_and_name_lt A tree
        hparentInvariant hchildSubset)
  have ht5_proper :
      ∀ node, t5.active node = true ->
        t5.childLabelUnion A node ⊂ t5.label node := by
    simpa [t5] using
      (stage4_stage5_preserves_childLabelUnion_ssubset A tree hchildSubset)
  have ht5_childSubset :
      ∀ node child, child ∈ t5.children A node ->
        t5.label child ⊆ t5.label node := by
    simpa [t5] using
      (stage4_stage5_preserves_child_label_subset A tree hchildSubset)
  have ht5_sibling :
      ∀ node left right,
        left ∈ t5.children A node ->
        right ∈ t5.children A node ->
        left ≠ right ->
          Disjoint (t5.label left) (t5.label right) := by
    simpa [t5] using
      (stage4_stage5_preserves_sibling_disjoint A tree
        (tree.greenRemovedNodes A) hsiblingDisjoint)
  simpa [t5] using
    (activeNodes_card_le_of_tree_structure A t5 ht5_rootParent
      ht5_parent ht5_proper ht5_childSubset ht5_sibling)

/-- Nodes removed with smaller pre-compaction names than `node`. -/
def removedBeforeName (tree : CompactTreeData A)
    (removed : Finset (Node A)) (node : Node A) : Finset (Node A) :=
  removed.filter (fun old => (tree.name old).val < (tree.name node).val)

theorem mem_removedBeforeName (tree : CompactTreeData A)
    (removed : Finset (Node A)) {old node : Node A} :
    old ∈ tree.removedBeforeName A removed node ↔
      old ∈ removed ∧ (tree.name old).val < (tree.name node).val := by
  simp [removedBeforeName]

theorem removedBeforeName_subset_removed
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    tree.removedBeforeName A removed node ⊆ removed := by
  intro old hold
  exact (mem_removedBeforeName A tree removed).mp hold |>.1

theorem removedBeforeName_name_lt
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {old node : Node A}
    (hold : old ∈ tree.removedBeforeName A removed node) :
    (tree.name old).val < (tree.name node).val :=
  (mem_removedBeforeName A tree removed).mp hold |>.2

theorem not_mem_removedBeforeName_of_name_le
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {old node : Node A}
    (hname : (tree.name node).val ≤ (tree.name old).val) :
    old ∉ tree.removedBeforeName A removed node := by
  intro hold
  have hlt := removedBeforeName_name_lt A tree removed hold
  omega

theorem removedBeforeName_eq_empty_of_forall_removed_name_ge
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hge :
      ∀ old, old ∈ removed ->
        (tree.name node).val ≤ (tree.name old).val) :
    tree.removedBeforeName A removed node = ∅ := by
  classical
  ext old
  constructor
  · intro hold
    have hspec := (mem_removedBeforeName A tree removed).mp hold
    have hgeOld := hge old hspec.1
    omega
  · intro hold
    simp at hold

theorem removedBeforeName_eq_empty_of_minBoundedNameOf_ge
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hmin :
      (tree.name node).val ≤ (tree.minBoundedNameOf A removed).val) :
    tree.removedBeforeName A removed node = ∅ := by
  classical
  apply removedBeforeName_eq_empty_of_forall_removed_name_ge A tree removed
  intro old hold
  by_contra hnot
  have hltOld : (tree.name old).val < (tree.name node).val := by omega
  have holdBound : (tree.name old).val < Fintype.card A.State :=
    hltOld.trans hnodeBound
  have hminLeOld :
      (tree.minBoundedNameOf A removed).val ≤ (tree.name old).val :=
    minBoundedNameOf_le_of_mem A tree removed hold holdBound
  omega

theorem removedBeforeName_mono_removed
    (tree : CompactTreeData A) {removed₁ removed₂ : Finset (Node A)}
    (node : Node A)
    (hsubset : removed₁ ⊆ removed₂) :
    tree.removedBeforeName A removed₁ node ⊆
      tree.removedBeforeName A removed₂ node := by
  intro old hold
  rw [mem_removedBeforeName A tree removed₂]
  have hspec := (mem_removedBeforeName A tree removed₁).mp hold
  exact ⟨hsubset hspec.1, hspec.2⟩

theorem removedBeforeName_subset_of_name_le
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val ≤ (tree.name right).val) :
    tree.removedBeforeName A removed left ⊆
      tree.removedBeforeName A removed right := by
  intro old hold
  rw [mem_removedBeforeName A tree removed]
  have hspec := (mem_removedBeforeName A tree removed).mp hold
  exact ⟨hspec.1, by omega⟩

theorem self_not_mem_removedBeforeName
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    node ∉ tree.removedBeforeName A removed node := by
  exact not_mem_removedBeforeName_of_name_le A tree removed (le_rfl)

theorem mem_removedBeforeName_of_removed_and_name_lt
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hleft : left ∈ removed)
    (hname : (tree.name left).val < (tree.name right).val) :
    left ∈ tree.removedBeforeName A removed right := by
  rw [mem_removedBeforeName A tree removed]
  exact ⟨hleft, hname⟩

theorem removedBeforeName_ssubset_of_removed_and_name_lt
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hleft : left ∈ removed)
    (hname : (tree.name left).val < (tree.name right).val) :
    tree.removedBeforeName A removed left ⊂
      tree.removedBeforeName A removed right := by
  refine ⟨removedBeforeName_subset_of_name_le A tree removed (by omega), ?_⟩
  intro hsubset
  have hleft_before_right :
      left ∈ tree.removedBeforeName A removed right :=
    mem_removedBeforeName_of_removed_and_name_lt A tree removed hleft hname
  have hleft_before_left :
      left ∈ tree.removedBeforeName A removed left :=
    hsubset hleft_before_right
  exact self_not_mem_removedBeforeName A tree removed left hleft_before_left

theorem removedBeforeName_card_lt_of_removed_and_name_lt
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hleft : left ∈ removed)
    (hname : (tree.name left).val < (tree.name right).val) :
    (tree.removedBeforeName A removed left).card <
      (tree.removedBeforeName A removed right).card :=
  Finset.card_lt_card
    (removedBeforeName_ssubset_of_removed_and_name_lt A tree removed hleft hname)

/-- Removed nodes with names in the half-open interval
`[tree.name left, tree.name right)`. -/
def removedBetweenNames (tree : CompactTreeData A)
    (removed : Finset (Node A)) (left right : Node A) : Finset (Node A) :=
  tree.removedBeforeName A removed right \ tree.removedBeforeName A removed left

theorem mem_removedBetweenNames_of_name_le
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {old left right : Node A} :
    old ∈ tree.removedBetweenNames A removed left right ↔
      old ∈ removed ∧
        (tree.name left).val ≤ (tree.name old).val ∧
        (tree.name old).val < (tree.name right).val := by
  rw [removedBetweenNames, Finset.mem_sdiff]
  constructor
  · intro hold
    have hright := (mem_removedBeforeName A tree removed).mp hold.1
    have hnot_left := hold.2
    refine ⟨hright.1, ?_, hright.2⟩
    by_contra hlt_not
    have hlt : (tree.name old).val < (tree.name left).val := by omega
    exact hnot_left ((mem_removedBeforeName A tree removed).mpr ⟨hright.1, hlt⟩)
  · intro hold
    constructor
    · exact (mem_removedBeforeName A tree removed).mpr
        ⟨hold.1, hold.2.2⟩
    · intro hleft
      have hlt := (mem_removedBeforeName A tree removed).mp hleft |>.2
      omega

theorem removedBetweenNames_card_add_removedBeforeName_card_eq
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val ≤ (tree.name right).val) :
    (tree.removedBetweenNames A removed left right).card +
        (tree.removedBeforeName A removed left).card =
      (tree.removedBeforeName A removed right).card := by
  have hsubset :
      tree.removedBeforeName A removed left ⊆
        tree.removedBeforeName A removed right :=
    removedBeforeName_subset_of_name_le A tree removed hname
  simpa [removedBetweenNames, Nat.add_comm]
    using Finset.card_sdiff_add_card_eq_card hsubset

theorem removedBetweenNames_card_lt_gap_of_left_not_removed
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val < (tree.name right).val)
    (hleftActive : tree.active left = true)
    (hleftNotRemoved : left ∉ removed)
    (hremovedActive :
      ∀ old, old ∈ removed -> tree.active old = true)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.removedBetweenNames A removed left right).card <
      (tree.name right).val - (tree.name left).val := by
  classical
  let between := tree.removedBetweenNames A removed left right
  let values : Finset Nat :=
    between.image (fun old => (tree.name old).val)
  have hvalues_card : values.card = between.card := by
    exact Finset.card_image_of_injOn (s := between)
      (f := fun old => (tree.name old).val)
      (by
        intro old hold old' hold' hval
        apply hinjective old old'
        · have hold_between :=
            (mem_removedBetweenNames_of_name_le A tree removed).mp hold
          exact hremovedActive old hold_between.1
        · have hold'_between :=
            (mem_removedBetweenNames_of_name_le A tree removed).mp hold'
          exact hremovedActive old' hold'_between.1
        · exact Fin.ext hval)
  have hvalues_subset :
      values ⊆
        (Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1)) := by
    intro value hvalue
    change value ∈ between.image (fun old => (tree.name old).val) at hvalue
    rw [Finset.mem_image] at hvalue
    rcases hvalue with ⟨old, hold, hvalue⟩
    have hold_between :=
      (mem_removedBetweenNames_of_name_le A tree removed).mp hold
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_range]
      omega
    · intro hsmall
      rw [Finset.mem_range] at hsmall
      have hname_eq : tree.name old = tree.name left := by
        apply Fin.ext
        omega
      have hold_active : tree.active old = true :=
        hremovedActive old hold_between.1
      have hold_eq_left : old = left :=
        hinjective old left hold_active hleftActive hname_eq
      exact hleftNotRemoved (by simpa [hold_eq_left] using hold_between.1)
  have hrange_subset :
      Finset.range ((tree.name left).val + 1) ⊆
        Finset.range (tree.name right).val := by
    intro value hvalue
    rw [Finset.mem_range] at hvalue ⊢
    omega
  have htarget_card :
      ((Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1))).card =
        (tree.name right).val - ((tree.name left).val + 1) := by
    simpa using Finset.card_sdiff_of_subset hrange_subset
  have hvalues_le :
      values.card ≤
        ((Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1))).card :=
    Finset.card_le_card hvalues_subset
  rw [htarget_card] at hvalues_le
  rw [hvalues_card] at hvalues_le
  change between.card < (tree.name right).val - (tree.name left).val
  omega

theorem removedBetweenNames_card_lt_gap_of_left_not_removed_name_injective
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val < (tree.name right).val)
    (hleftNotRemoved : left ∉ removed)
    (hinjective :
      ∀ x y,
        (x ∈ removed ∨ x = left) ->
        (y ∈ removed ∨ y = left) ->
        tree.name x = tree.name y ->
          x = y) :
    (tree.removedBetweenNames A removed left right).card <
      (tree.name right).val - (tree.name left).val := by
  classical
  let between := tree.removedBetweenNames A removed left right
  let values : Finset Nat :=
    between.image (fun old => (tree.name old).val)
  have hvalues_card : values.card = between.card := by
    exact Finset.card_image_of_injOn (s := between)
      (f := fun old => (tree.name old).val)
      (by
        intro old hold old' hold' hval
        apply hinjective old old'
        · exact Or.inl ((mem_removedBetweenNames_of_name_le A tree removed).mp hold).1
        · exact Or.inl ((mem_removedBetweenNames_of_name_le A tree removed).mp hold').1
        · exact Fin.ext hval)
  have hvalues_subset :
      values ⊆
        (Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1)) := by
    intro value hvalue
    change value ∈ between.image (fun old => (tree.name old).val) at hvalue
    rw [Finset.mem_image] at hvalue
    rcases hvalue with ⟨old, hold, hvalue⟩
    have hold_between :=
      (mem_removedBetweenNames_of_name_le A tree removed).mp hold
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_range]
      omega
    · intro hsmall
      rw [Finset.mem_range] at hsmall
      have hname_eq : tree.name old = tree.name left := by
        apply Fin.ext
        omega
      have hold_eq_left : old = left :=
        hinjective old left (Or.inl hold_between.1) (Or.inr rfl) hname_eq
      exact hleftNotRemoved (by simpa [hold_eq_left] using hold_between.1)
  have hrange_subset :
      Finset.range ((tree.name left).val + 1) ⊆
        Finset.range (tree.name right).val := by
    intro value hvalue
    rw [Finset.mem_range] at hvalue ⊢
    omega
  have htarget_card :
      ((Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1))).card =
        (tree.name right).val - ((tree.name left).val + 1) := by
    simpa using Finset.card_sdiff_of_subset hrange_subset
  have hvalues_le :
      values.card ≤
        ((Finset.range (tree.name right).val) \
          (Finset.range ((tree.name left).val + 1))).card :=
    Finset.card_le_card hvalues_subset
  rw [htarget_card] at hvalues_le
  rw [hvalues_card] at hvalues_le
  change between.card < (tree.name right).val - (tree.name left).val
  omega

theorem removedBeforeName_card_le_name_of_name_injective
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hinjective :
      ∀ left right,
        left ∈ tree.removedBeforeName A removed node ->
        right ∈ tree.removedBeforeName A removed node ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.removedBeforeName A removed node).card ≤ (tree.name node).val := by
  classical
  let toSmallerName :
      { old // old ∈ tree.removedBeforeName A removed node } ->
        Fin (tree.name node).val :=
    fun old => ⟨(tree.name old.1).val,
      removedBeforeName_name_lt A tree removed old.2⟩
  have htoSmallerName_injective : Function.Injective toSmallerName := by
    intro left right heq
    apply Subtype.ext
    apply hinjective left.1 right.1 left.2 right.2
    have hval : (tree.name left.1).val = (tree.name right.1).val := by
      simpa [toSmallerName] using congrArg Fin.val heq
    exact Fin.ext hval
  have hcard :=
    Fintype.card_le_of_injective toSmallerName htoSmallerName_injective
  simpa [Fintype.card_coe] using hcard

theorem removedBeforeName_card_le_name_of_removed_active
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hremovedActive :
      ∀ old, old ∈ removed -> tree.active old = true)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.removedBeforeName A removed node).card ≤ (tree.name node).val := by
  exact removedBeforeName_card_le_name_of_name_injective A tree removed
    (by
      intro left right hleft hright hname
      apply hinjective left right
      · exact hremovedActive left
          ((mem_removedBeforeName A tree removed).mp hleft).1
      · exact hremovedActive right
          ((mem_removedBeforeName A tree removed).mp hright).1
      · exact hname)

theorem removedBeforeName_card_le_name_of_removed_name_injective
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hinjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.removedBeforeName A removed node).card ≤ (tree.name node).val := by
  exact removedBeforeName_card_le_name_of_name_injective A tree removed
    (by
      intro left right hleft hright hname
      apply hinjective left right
      · exact ((mem_removedBeforeName A tree removed).mp hleft).1
      · exact ((mem_removedBeforeName A tree removed).mp hright).1
      · exact hname)

/-- Active survivor nodes whose old names are at most `node`'s old name. -/
def activeBeforeOrAtName (tree : CompactTreeData A)
    (node : Node A) : Finset (Node A) :=
  (tree.activeNodes A).filter
    (fun kept => (tree.name kept).val ≤ (tree.name node).val)

theorem mem_activeBeforeOrAtName (tree : CompactTreeData A)
    {kept node : Node A} :
    kept ∈ tree.activeBeforeOrAtName A node ↔
      tree.active kept = true ∧
        (tree.name kept).val ≤ (tree.name node).val := by
  simp [activeBeforeOrAtName, activeNodes]

theorem self_mem_activeBeforeOrAtName (tree : CompactTreeData A)
    {node : Node A}
    (hactive : tree.active node = true) :
    node ∈ tree.activeBeforeOrAtName A node := by
  rw [mem_activeBeforeOrAtName]
  exact ⟨hactive, le_rfl⟩

theorem activeBeforeOrAtName_subset_activeNodes
    (tree : CompactTreeData A) (node : Node A) :
    tree.activeBeforeOrAtName A node ⊆ tree.activeNodes A := by
  intro kept hkept
  exact (mem_activeNodes A tree).mpr
    ((mem_activeBeforeOrAtName A tree).mp hkept).1

theorem activeBeforeOrAtName_card_le_activeNodes
    (tree : CompactTreeData A) (node : Node A) :
    (tree.activeBeforeOrAtName A node).card ≤ (tree.activeNodes A).card :=
  Finset.card_le_card (activeBeforeOrAtName_subset_activeNodes A tree node)

theorem disjoint_removedBeforeName_activeBeforeOrAtName
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (node : Node A) :
    Disjoint (tree.removedBeforeName A removed node)
      (tree.activeBeforeOrAtName A node) := by
  rw [Finset.disjoint_left]
  intro old hold hactivePrefix
  have hold_removed : old ∈ removed :=
    (mem_removedBeforeName A tree removed).mp hold |>.1
  have hold_active : tree.active old = true :=
    (mem_activeBeforeOrAtName A tree).mp hactivePrefix |>.1
  exact hactiveNotRemoved old hold_active hold_removed

theorem removedBeforeName_card_add_activeBeforeOrAtName_card_eq_union
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (node : Node A) :
    (tree.removedBeforeName A removed node).card +
        (tree.activeBeforeOrAtName A node).card =
      (tree.removedBeforeName A removed node ∪
        tree.activeBeforeOrAtName A node).card := by
  exact (Finset.card_union_of_disjoint
    (disjoint_removedBeforeName_activeBeforeOrAtName A tree removed
      hactiveNotRemoved node)).symm

theorem range_name_succ_subset_image_removedBefore_union_activeBefore
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hnodeActive : tree.active node = true)
    (hcoverLower :
      ∀ j : Nat, j < (tree.name node).val ->
        ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
          (tree.name old).val = j) :
    Finset.range ((tree.name node).val + 1) ⊆
      (tree.removedBeforeName A removed node ∪
        tree.activeBeforeOrAtName A node).image
          (fun old => (tree.name old).val) := by
  intro j hj
  rw [Finset.mem_range] at hj
  rw [Finset.mem_image]
  by_cases hj_eq : j = (tree.name node).val
  · refine ⟨node, ?_, hj_eq.symm⟩
    rw [Finset.mem_union]
    exact Or.inr (self_mem_activeBeforeOrAtName A tree hnodeActive)
  · have hj_lt : j < (tree.name node).val := by omega
    obtain ⟨old, hold, hname⟩ := hcoverLower j hj_lt
    refine ⟨old, ?_, hname⟩
    rw [Finset.mem_union]
    rcases hold with hold_removed | hold_active
    · exact Or.inl ((mem_removedBeforeName A tree removed).mpr
        ⟨hold_removed, by omega⟩)
    · exact Or.inr ((mem_activeBeforeOrAtName A tree).mpr
        ⟨hold_active, by omega⟩)

theorem name_succ_le_removedBefore_union_activeBefore_card
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hnodeActive : tree.active node = true)
    (hcoverLower :
      ∀ j : Nat, j < (tree.name node).val ->
        ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
          (tree.name old).val = j) :
    (tree.name node).val + 1 ≤
      (tree.removedBeforeName A removed node ∪
        tree.activeBeforeOrAtName A node).card := by
  have hsubset :=
    range_name_succ_subset_image_removedBefore_union_activeBefore
      A tree removed hnodeActive hcoverLower
  have hcard_range :
      (Finset.range ((tree.name node).val + 1)).card ≤
        ((tree.removedBeforeName A removed node ∪
          tree.activeBeforeOrAtName A node).image
            (fun old => (tree.name old).val)).card :=
    Finset.card_le_card hsubset
  have himage_le :
      ((tree.removedBeforeName A removed node ∪
        tree.activeBeforeOrAtName A node).image
          (fun old => (tree.name old).val)).card ≤
        (tree.removedBeforeName A removed node ∪
          tree.activeBeforeOrAtName A node).card :=
    Finset.card_image_le
  simpa [Finset.card_range] using hcard_range.trans himage_le

/-- Piterman stage (6)'s compacted name `M(v) - rem(v)`. -/
def compactedName (tree : CompactTreeData A)
    (removed : Finset (Node A)) (node : Node A) : TempName A :=
  ⟨(tree.name node).val - (tree.removedBeforeName A removed node).card, by
    have hlt := (tree.name node).isLt
    omega⟩

theorem compactedName_le_oldName (tree : CompactTreeData A)
    (removed : Finset (Node A)) (node : Node A) :
    (tree.compactedName A removed node).val ≤ (tree.name node).val := by
  simp [compactedName]

theorem compactedName_val_add_removedBeforeName_card_eq_oldName
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hcard :
      (tree.removedBeforeName A removed node).card ≤ (tree.name node).val) :
    (tree.compactedName A removed node).val +
        (tree.removedBeforeName A removed node).card =
      (tree.name node).val := by
  rw [compactedName]
  exact Nat.sub_add_cancel hcard

theorem compactedName_lt_activeBeforeOrAtName_card
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hnodeActive : tree.active node = true)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hremovedNameInjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hcoverLower :
      ∀ j : Nat, j < (tree.name node).val ->
        ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
          (tree.name old).val = j) :
    (tree.compactedName A removed node).val <
      (tree.activeBeforeOrAtName A node).card := by
  have hcompact_eq :
      (tree.compactedName A removed node).val +
          (tree.removedBeforeName A removed node).card =
        (tree.name node).val :=
    compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
      (node := node)
      (removedBeforeName_card_le_name_of_removed_name_injective A tree removed
        hremovedNameInjective)
  have hunion_lower :
      (tree.name node).val + 1 ≤
        (tree.removedBeforeName A removed node ∪
          tree.activeBeforeOrAtName A node).card :=
    name_succ_le_removedBefore_union_activeBefore_card A tree removed
      hnodeActive hcoverLower
  have hunion_eq :
      (tree.removedBeforeName A removed node).card +
          (tree.activeBeforeOrAtName A node).card =
        (tree.removedBeforeName A removed node ∪
          tree.activeBeforeOrAtName A node).card :=
    removedBeforeName_card_add_activeBeforeOrAtName_card_eq_union
      A tree removed hactiveNotRemoved node
  omega

theorem compactedName_lt_activeNodes_card
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hnodeActive : tree.active node = true)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hremovedNameInjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hcoverLower :
      ∀ j : Nat, j < (tree.name node).val ->
        ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
          (tree.name old).val = j) :
    (tree.compactedName A removed node).val <
      (tree.activeNodes A).card := by
  exact (compactedName_lt_activeBeforeOrAtName_card A tree removed
    hnodeActive hactiveNotRemoved hremovedNameInjective hcoverLower).trans_le
      (activeBeforeOrAtName_card_le_activeNodes A tree node)

theorem compactedName_val_add_removedBeforeName_card_eq_oldName_of_removed_active
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hremovedActive :
      ∀ old, old ∈ removed -> tree.active old = true)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.compactedName A removed node).val +
        (tree.removedBeforeName A removed node).card =
      (tree.name node).val := by
  exact compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
    (removedBeforeName_card_le_name_of_removed_active A tree removed
      hremovedActive hinjective)

theorem compactedName_lt_of_removedBetweenNames_card_lt_gap
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val < (tree.name right).val)
    (hleftCard :
      (tree.removedBeforeName A removed left).card ≤ (tree.name left).val)
    (hrightCard :
      (tree.removedBeforeName A removed right).card ≤ (tree.name right).val)
    (hbetween :
      (tree.removedBetweenNames A removed left right).card <
        (tree.name right).val - (tree.name left).val) :
    (tree.compactedName A removed left).val <
      (tree.compactedName A removed right).val := by
  have hleft_eq :=
    compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
      (node := left) hleftCard
  have hright_eq :=
    compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
      (node := right) hrightCard
  have hbetween_eq :=
    removedBetweenNames_card_add_removedBeforeName_card_eq A tree removed
      (left := left) (right := right) (by omega)
  omega

theorem compactedName_lt_of_name_lt_left_not_removed
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val < (tree.name right).val)
    (hleftActive : tree.active left = true)
    (hleftNotRemoved : left ∉ removed)
    (hremovedActive :
      ∀ old, old ∈ removed -> tree.active old = true)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    (tree.compactedName A removed left).val <
      (tree.compactedName A removed right).val := by
  exact compactedName_lt_of_removedBetweenNames_card_lt_gap A tree removed
    hname
    (removedBeforeName_card_le_name_of_removed_active A tree removed
      hremovedActive hinjective)
    (removedBeforeName_card_le_name_of_removed_active A tree removed
      hremovedActive hinjective)
    (removedBetweenNames_card_lt_gap_of_left_not_removed A tree removed
      hname hleftActive hleftNotRemoved hremovedActive hinjective)

theorem compactedName_lt_of_name_lt_left_not_removed_name_injective
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {left right : Node A}
    (hname : (tree.name left).val < (tree.name right).val)
    (hleftNotRemoved : left ∉ removed)
    (hinjective :
      ∀ x y,
        (x ∈ removed ∨ x = left) ->
        (y ∈ removed ∨ y = left) ->
        tree.name x = tree.name y ->
          x = y) :
    (tree.compactedName A removed left).val <
      (tree.compactedName A removed right).val := by
  exact compactedName_lt_of_removedBetweenNames_card_lt_gap A tree removed
    hname
    (removedBeforeName_card_le_name_of_removed_name_injective A tree removed
      (by
        intro x y hx hy hxy
        exact hinjective x y (Or.inl hx) (Or.inl hy) hxy))
    (removedBeforeName_card_le_name_of_removed_name_injective A tree removed
      (by
        intro x y hx hy hxy
        exact hinjective x y (Or.inl hx) (Or.inl hy) hxy))
    (removedBetweenNames_card_lt_gap_of_left_not_removed_name_injective
      A tree removed hname hleftNotRemoved hinjective)

theorem removedBeforeName_eq_empty_of_name_zero
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hname : (tree.name node).val = 0) :
    tree.removedBeforeName A removed node = ∅ := by
  ext old
  constructor
  · intro hold
    have hlt := (mem_removedBeforeName A tree removed).mp hold |>.2
    omega
  · intro hold
    simp at hold

theorem compactedName_val_eq_zero_of_name_zero
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hname : (tree.name node).val = 0) :
    (tree.compactedName A removed node).val = 0 := by
  rw [compactedName]
  simp [removedBeforeName_eq_empty_of_name_zero A tree removed hname, hname]

/--
If stage (6) has no removed node with smaller pre-compaction name, then
Piterman's compaction does not change this node's numeric name.  This is the
local arithmetic fact used in Claim 4.2 when all lower-name events are absent.
-/
theorem compactedName_val_eq_oldName_of_removedBeforeName_eq_empty
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hremovedBefore :
      tree.removedBeforeName A removed node = ∅) :
    (tree.compactedName A removed node).val = (tree.name node).val := by
  rw [compactedName]
  simp [hremovedBefore]

/--
Piterman Section 3.2, transition stage (6): renumber remaining nonempty nodes
by subtracting the number of removed smaller names.
-/
noncomputable def stage6 [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A)) :
    CompactTreeData A where
  active := tree.active
  name node := by
    classical
    exact if tree.label node = ∅ then tree.name node else tree.compactedName A removed node
  parent := tree.parent
  label := tree.label
  e := tree.e
  f := tree.f

theorem stage6_nonempty_name [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅) :
    (tree.stage6 A removed).name node = tree.compactedName A removed node := by
  simp [stage6, hlabel]

theorem stage6_nonempty_name_val_eq_oldName_of_removedBeforeName_eq_empty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hremovedBefore :
      tree.removedBeforeName A removed node = ∅) :
    ((tree.stage6 A removed).name node).val = (tree.name node).val := by
  rw [stage6_nonempty_name A tree removed hlabel]
  exact compactedName_val_eq_oldName_of_removedBeforeName_eq_empty A tree
    removed hremovedBefore

theorem stage6_nonempty_name_val_eq_oldName_of_forall_removed_name_ge
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hge :
      ∀ old, old ∈ removed ->
        (tree.name node).val ≤ (tree.name old).val) :
    ((tree.stage6 A removed).name node).val = (tree.name node).val :=
  stage6_nonempty_name_val_eq_oldName_of_removedBeforeName_eq_empty
    A tree removed hlabel
    (removedBeforeName_eq_empty_of_forall_removed_name_ge A tree removed hge)

theorem stage6_nonempty_name_val_eq_oldName_of_minBoundedNameOf_ge
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hmin :
      (tree.name node).val ≤ (tree.minBoundedNameOf A removed).val) :
    ((tree.stage6 A removed).name node).val = (tree.name node).val :=
  stage6_nonempty_name_val_eq_oldName_of_removedBeforeName_eq_empty
    A tree removed hlabel
    (removedBeforeName_eq_empty_of_minBoundedNameOf_ge A tree removed
      hnodeBound hmin)

/--
Strict stage-(6) compaction of a nonempty survivor has a concrete source: some
removed node had a smaller old name.  This is the local arithmetic witness behind
any genuine name drop in Piterman's renumbering stage.
-/
theorem stage6_nonempty_name_val_lt_oldName_exists_removedBeforeName
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hcard :
      (tree.removedBeforeName A removed node).card ≤ (tree.name node).val)
    (hlt :
      ((tree.stage6 A removed).name node).val < (tree.name node).val) :
    ∃ old, old ∈ removed ∧ (tree.name old).val < (tree.name node).val := by
  classical
  have hcompactLt :
      (tree.compactedName A removed node).val < (tree.name node).val := by
    simpa [stage6_nonempty_name A tree removed hlabel] using hlt
  have hcompactEq :
      (tree.compactedName A removed node).val +
          (tree.removedBeforeName A removed node).card =
        (tree.name node).val :=
    compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
      hcard
  have hcardPos : 0 < (tree.removedBeforeName A removed node).card := by
    omega
  rcases Finset.card_pos.mp hcardPos with ⟨old, holdBefore⟩
  exact ⟨old, (mem_removedBeforeName A tree removed).mp holdBefore⟩

/--
Name-injective convenience form of
`stage6_nonempty_name_val_lt_oldName_exists_removedBeforeName`.
-/
theorem stage6_nonempty_name_val_lt_oldName_exists_removedBeforeName_of_removed_name_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hinjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hlt :
      ((tree.stage6 A removed).name node).val < (tree.name node).val) :
    ∃ old, old ∈ removed ∧ (tree.name old).val < (tree.name node).val :=
  stage6_nonempty_name_val_lt_oldName_exists_removedBeforeName A tree removed
    hlabel
    (removedBeforeName_card_le_name_of_removed_name_injective A tree removed
      hinjective)
    hlt

/--
Threshold form of the stage-(6) compaction witness.  If a nonempty survivor's
old name was at least `threshold`, but stage (6) compacts it below `threshold`,
then some removed node had pre-compaction name below `threshold`.  This is the
arithmetically sharp form needed for the lower-source no-leakage cutoff.
-/
theorem stage6_nonempty_name_val_lt_threshold_exists_removedBeforeName
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A} {threshold : Nat}
    (hlabel : tree.label node ≠ ∅)
    (hinjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hthreshold : threshold ≤ (tree.name node).val)
    (hlt :
      ((tree.stage6 A removed).name node).val < threshold) :
    ∃ old, old ∈ removed ∧ (tree.name old).val < threshold := by
  classical
  by_contra hno
  let before := tree.removedBeforeName A removed node
  let values : Finset Nat := before.image (fun old => (tree.name old).val)
  have hvalues_card : values.card = before.card := by
    exact Finset.card_image_of_injOn (s := before)
      (f := fun old => (tree.name old).val)
      (by
        intro left hleft right hright hname
        exact hinjective left right
          ((mem_removedBeforeName A tree removed).mp hleft).1
          ((mem_removedBeforeName A tree removed).mp hright).1
          (Fin.ext hname))
  have hvalues_subset :
      values ⊆
        (Finset.range (tree.name node).val) \ (Finset.range threshold) := by
    intro value hvalue
    change value ∈ before.image (fun old => (tree.name old).val) at hvalue
    rw [Finset.mem_image] at hvalue
    rcases hvalue with ⟨old, hold, hvalue⟩
    have hspec := (mem_removedBeforeName A tree removed).mp hold
    rw [Finset.mem_sdiff]
    constructor
    · rw [Finset.mem_range]
      omega
    · intro hsmall
      rw [Finset.mem_range] at hsmall
      exact hno ⟨old, hspec.1, by omega⟩
  have hrange_subset :
      Finset.range threshold ⊆ Finset.range (tree.name node).val := by
    intro value hvalue
    rw [Finset.mem_range] at hvalue ⊢
    omega
  have htarget_card :
      ((Finset.range (tree.name node).val) \ (Finset.range threshold)).card =
        (tree.name node).val - threshold := by
    simpa using Finset.card_sdiff_of_subset hrange_subset
  have hbefore_card_le :
      before.card ≤ (tree.name node).val - threshold := by
    have hvalues_le :
        values.card ≤
          ((Finset.range (tree.name node).val) \ (Finset.range threshold)).card :=
      Finset.card_le_card hvalues_subset
    rw [htarget_card] at hvalues_le
    rw [hvalues_card] at hvalues_le
    exact hvalues_le
  have hcompactEq :
      (tree.compactedName A removed node).val + before.card =
        (tree.name node).val := by
    simpa [before] using
      compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
        (node := node)
        (removedBeforeName_card_le_name_of_removed_name_injective A tree removed
          hinjective)
  have hstage6Lt :
      (tree.compactedName A removed node).val < threshold := by
    simpa [stage6_nonempty_name A tree removed hlabel] using hlt
  omega

theorem stage6_nonempty_same_name_minBoundedNameOf_gt
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node ≠ ∅)
    (hactive : tree.active node = true)
    (hnodeBound : (tree.name node).val < Fintype.card A.State)
    (hnotRemoved : node ∉ removed)
    (hinjective :
      ∀ left right,
        (left ∈ removed ∨ tree.active left = true) ->
        (right ∈ removed ∨ tree.active right = true) ->
        tree.name left = tree.name right ->
          left = right)
    (hnameSame :
      ((tree.stage6 A removed).name node).val = (tree.name node).val) :
    (tree.name node).val < (tree.minBoundedNameOf A removed).val := by
  classical
  by_contra hnot
  have hmin_le : (tree.minBoundedNameOf A removed).val ≤ (tree.name node).val := by
    omega
  have hmin_lt_card : (tree.minBoundedNameOf A removed).val < Fintype.card A.State := by
    omega
  rcases exists_node_name_eq_minBoundedNameOf_of_min_lt_card A tree removed
      hmin_lt_card with
    ⟨old, holdRemoved, holdName⟩
  have hstage6Name :
      ((tree.stage6 A removed).name node).val =
        (tree.compactedName A removed node).val := by
    rw [stage6_nonempty_name A tree removed hlabel]
  by_cases hlt : (tree.name old).val < (tree.name node).val
  · have holdBefore :
        old ∈ tree.removedBeforeName A removed node :=
      (mem_removedBeforeName A tree removed).mpr ⟨holdRemoved, hlt⟩
    have hcard_pos : 0 < (tree.removedBeforeName A removed node).card :=
      Finset.card_pos.mpr ⟨old, holdBefore⟩
    have hcard_le :
        (tree.removedBeforeName A removed node).card ≤ (tree.name node).val :=
      removedBeforeName_card_le_name_of_removed_name_injective A tree removed
        (by
          intro left right hleft hright hname
          exact hinjective left right (Or.inl hleft) (Or.inl hright) hname)
    have hcompact_eq :
        (tree.compactedName A removed node).val +
            (tree.removedBeforeName A removed node).card =
          (tree.name node).val :=
      compactedName_val_add_removedBeforeName_card_eq_oldName A tree removed
        hcard_le
    have hcompact_lt :
        (tree.compactedName A removed node).val < (tree.name node).val := by
      omega
    omega
  · have hnameEqVal : (tree.name old).val = (tree.name node).val := by
      have hle_old : (tree.name old).val ≤ (tree.name node).val := by
        simpa [holdName] using hmin_le
      omega
    have hnameEq : tree.name old = tree.name node := by
      apply Fin.ext
      exact hnameEqVal
    have holdEq : old = node :=
      hinjective old node (Or.inl holdRemoved) (Or.inr hactive) hnameEq
    exact hnotRemoved (by simpa [holdEq] using holdRemoved)

theorem stage5_stage6_nonempty_name_val_eq_oldName_of_e_ge
    [DecidableEq A.State]
    (tree : CompactTreeData A) (previouslyRemoved : Finset (Node A))
    {node : Node A}
    (hlabel : (tree.stage5 A previouslyRemoved).label node ≠ ∅)
    (hnodeBound :
      ((tree.stage5 A previouslyRemoved).name node).val <
        Fintype.card A.State)
    (he :
      ((tree.stage5 A previouslyRemoved).name node).val ≤
        ((tree.stage5 A previouslyRemoved).e).val) :
    (((tree.stage5 A previouslyRemoved).stage6 A
        (previouslyRemoved ∪ tree.emptyActiveNodes A)).name node).val =
      ((tree.stage5 A previouslyRemoved).name node).val := by
  let t5 := tree.stage5 A previouslyRemoved
  let removed := previouslyRemoved ∪ tree.emptyActiveNodes A
  have hmin :
      (t5.name node).val ≤ (t5.minBoundedNameOf A removed).val := by
    simpa [t5, removed, stage5, minBoundedNameOf] using he
  exact stage6_nonempty_name_val_eq_oldName_of_minBoundedNameOf_ge
    A t5 removed (by simpa [t5] using hlabel)
    (by simpa [t5] using hnodeBound) hmin

theorem stage6_empty_name [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    {node : Node A}
    (hlabel : tree.label node = ∅) :
    (tree.stage6 A removed).name node = tree.name node := by
  simp [stage6, hlabel]

theorem stage6_active [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    (tree.stage6 A removed).active node = tree.active node := rfl

theorem stage6_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    (tree.stage6 A removed).parent node = tree.parent node := rfl

theorem stage6_f_val [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A)) :
    ((tree.stage6 A removed).f).val = tree.f.val := by
  rfl

theorem stage6_e_val [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A)) :
    ((tree.stage6 A removed).e).val = tree.e.val := by
  rfl

theorem stage6_root_name_val [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hrootName : (tree.name (root A)).val = (rootName A).val) :
    ((tree.stage6 A removed).name (root A)).val = (rootName A).val := by
  have hzero : (tree.name (root A)).val = 0 := by
    simpa [rootName] using hrootName
  by_cases hlabel : tree.label (root A) = ∅
  · rw [stage6_empty_name A tree removed hlabel]
    exact hrootName
  · rw [stage6_nonempty_name A tree removed hlabel]
    simpa [rootName]
      using compactedName_val_eq_zero_of_name_zero A tree removed hzero

theorem stage6_preserves_label [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    (tree.stage6 A removed).label node = tree.label node := rfl

theorem stage6_children [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    (tree.stage6 A removed).children A node = tree.children A node := by
  simp [children, stage6]

theorem stage6_activeNodes [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A)) :
    (tree.stage6 A removed).activeNodes A = tree.activeNodes A := by
  simp [activeNodes, stage6]

theorem stage6_childLabelUnion [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (node : Node A) :
    (tree.stage6 A removed).childLabelUnion A node =
      tree.childLabelUnion A node := by
  simp [childLabelUnion, children, stage6]

theorem stage6_preserves_inactive_label [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.stage6 A removed).active node = false ->
      (tree.stage6 A removed).label node = ∅ := by
  intro node hactive
  rw [stage6_preserves_label A tree removed node]
  exact hinactiveLabel node (by simpa [stage6_active A tree removed node] using hactive)

theorem stage6_preserves_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < 2 * Fintype.card A.State) :
    ∀ node, (tree.stage6 A removed).active node = true ->
      ((tree.stage6 A removed).name node).val <
        2 * Fintype.card A.State := by
  intro node hactive
  have htree_active : tree.active node = true := by
    simpa [stage6_active A tree removed node] using hactive
  by_cases hlabel : tree.label node = ∅
  · rw [stage6_empty_name A tree removed hlabel]
    exact hbound node htree_active
  · rw [stage6_nonempty_name A tree removed hlabel]
    have hle := compactedName_le_oldName A tree removed node
    have hlt := hbound node htree_active
    omega

theorem stage6_final_name_bound [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hremovedNameInjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hcoverLower :
      ∀ node, tree.active node = true ->
        ∀ j : Nat, j < (tree.name node).val ->
          ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
            (tree.name old).val = j)
    (hactiveCard :
      (tree.activeNodes A).card ≤ Fintype.card A.State) :
    ∀ node, (tree.stage6 A removed).active node = true ->
      ((tree.stage6 A removed).name node).val < Fintype.card A.State := by
  intro node hactive
  have htree_active : tree.active node = true := by
    simpa [stage6_active A tree removed node] using hactive
  have hlabel : tree.label node ≠ ∅ :=
    hactiveNonempty node htree_active
  rw [stage6_nonempty_name A tree removed hlabel]
  exact (compactedName_lt_activeNodes_card A tree removed
    htree_active hactiveNotRemoved hremovedNameInjective
    (hcoverLower node htree_active)).trans_le hactiveCard

theorem stage6_name_lt_activeNodes_card [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hremovedNameInjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right)
    (hcoverLower :
      ∀ node, tree.active node = true ->
        ∀ j : Nat, j < (tree.name node).val ->
          ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
            (tree.name old).val = j) :
    ∀ node, (tree.stage6 A removed).active node = true ->
      ((tree.stage6 A removed).name node).val <
        ((tree.stage6 A removed).activeNodes A).card := by
  intro node hactive
  have htree_active : tree.active node = true := by
    simpa [stage6_active A tree removed node] using hactive
  have hlabel : tree.label node ≠ ∅ :=
    hactiveNonempty node htree_active
  rw [stage6_nonempty_name A tree removed hlabel]
  rw [stage6_activeNodes A tree removed]
  exact compactedName_lt_activeNodes_card A tree removed
    htree_active hactiveNotRemoved hremovedNameInjective
    (hcoverLower node htree_active)

theorem stage6_preserves_parent_active_and_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hinjective :
      ∀ left right,
        (left ∈ removed ∨ tree.active left = true) ->
        (right ∈ removed ∨ tree.active right = true) ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ node,
      (tree.stage6 A removed).active node = true ->
      node ≠ root A ->
        (tree.stage6 A removed).active
            ((tree.stage6 A removed).parent node) = true ∧
          ((tree.stage6 A removed).name
              ((tree.stage6 A removed).parent node)).val <
            ((tree.stage6 A removed).name node).val := by
  intro node hactive hnot_root
  have htree_active : tree.active node = true := by
    simpa [stage6_active A tree removed node] using hactive
  have hparent := hparentInvariant node htree_active hnot_root
  have hparent_active : tree.active (tree.parent node) = true := hparent.1
  have hnode_label : tree.label node ≠ ∅ :=
    hactiveNonempty node htree_active
  have hparent_label : tree.label (tree.parent node) ≠ ∅ :=
    hactiveNonempty (tree.parent node) hparent_active
  constructor
  · rw [stage6_parent A tree removed node]
    rw [stage6_active A tree removed (tree.parent node)]
    exact hparent_active
  · rw [stage6_parent A tree removed node]
    rw [stage6_nonempty_name A tree removed hparent_label]
    rw [stage6_nonempty_name A tree removed hnode_label]
    exact compactedName_lt_of_name_lt_left_not_removed_name_injective A tree removed
      hparent.2
      (hactiveNotRemoved (tree.parent node) hparent_active)
      (by
        intro left right hleft hright hname
        apply hinjective left right
        · rcases hleft with hleft_removed | hleft_parent
          · exact Or.inl hleft_removed
          · subst hleft_parent
            exact Or.inr hparent_active
        · rcases hright with hright_removed | hright_parent
          · exact Or.inl hright_removed
          · subst hright_parent
            exact Or.inr hparent_active
        · exact hname)

theorem stage6_preserves_name_injective [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hinjective :
      ∀ left right,
        (left ∈ removed ∨ tree.active left = true) ->
        (right ∈ removed ∨ tree.active right = true) ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.stage6 A removed).active left = true ->
      (tree.stage6 A removed).active right = true ->
      (tree.stage6 A removed).name left = (tree.stage6 A removed).name right ->
        left = right := by
  intro left right hleft hright hname
  have hleft_active : tree.active left = true := by
    simpa [stage6_active A tree removed left] using hleft
  have hright_active : tree.active right = true := by
    simpa [stage6_active A tree removed right] using hright
  have hleft_label : tree.label left ≠ ∅ :=
    hactiveNonempty left hleft_active
  have hright_label : tree.label right ≠ ∅ :=
    hactiveNonempty right hright_active
  rw [stage6_nonempty_name A tree removed hleft_label] at hname
  rw [stage6_nonempty_name A tree removed hright_label] at hname
  have hname_val :
      (tree.compactedName A removed left).val =
        (tree.compactedName A removed right).val :=
    congrArg Fin.val hname
  by_cases hlt : (tree.name left).val < (tree.name right).val
  · have hcompact_lt :
        (tree.compactedName A removed left).val <
          (tree.compactedName A removed right).val :=
      compactedName_lt_of_name_lt_left_not_removed_name_injective A tree removed
        hlt (hactiveNotRemoved left hleft_active)
        (by
          intro x y hx hy hxy
          apply hinjective x y
          · rcases hx with hx_removed | hx_left
            · exact Or.inl hx_removed
            · subst hx_left
              exact Or.inr hleft_active
          · rcases hy with hy_removed | hy_left
            · exact Or.inl hy_removed
            · subst hy_left
              exact Or.inr hleft_active
          · exact hxy)
    omega
  · by_cases hgt : (tree.name right).val < (tree.name left).val
    · have hcompact_lt :
          (tree.compactedName A removed right).val <
            (tree.compactedName A removed left).val :=
        compactedName_lt_of_name_lt_left_not_removed_name_injective A tree removed
          hgt (hactiveNotRemoved right hright_active)
          (by
            intro x y hx hy hxy
            apply hinjective x y
            · rcases hx with hx_removed | hx_right
              · exact Or.inl hx_removed
              · subst hx_right
                exact Or.inr hright_active
            · rcases hy with hy_removed | hy_right
              · exact Or.inl hy_removed
              · subst hy_right
                exact Or.inr hright_active
            · exact hxy)
      omega
    · have hold_val : (tree.name left).val = (tree.name right).val := by
        omega
      exact hinjective left right
        (Or.inr hleft_active)
        (Or.inr hright_active)
        (Fin.ext hold_val)

theorem stage6_preserves_child_label_subset [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.stage6 A removed).children A node ->
      (tree.stage6 A removed).label child ⊆
        (tree.stage6 A removed).label node := by
  intro node child hchild state hstate
  rw [stage6_preserves_label A tree removed child] at hstate
  rw [stage6_preserves_label A tree removed node]
  exact hchildSubset node child
    (by simpa [stage6_children A tree removed node] using hchild) hstate

theorem stage6_preserves_childLabelUnion_ssubset [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hproper :
      ∀ node, tree.active node = true ->
        tree.childLabelUnion A node ⊂ tree.label node) :
    ∀ node, (tree.stage6 A removed).active node = true ->
      (tree.stage6 A removed).childLabelUnion A node ⊂
        (tree.stage6 A removed).label node := by
  intro node hactive
  rw [stage6_childLabelUnion A tree removed node]
  rw [stage6_preserves_label A tree removed node]
  exact hproper node
    (by simpa [stage6_active A tree removed node] using hactive)

theorem stage6_preserves_sibling_disjoint [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hsiblingDisjoint :
      ∀ node left right,
        left ∈ tree.children A node ->
        right ∈ tree.children A node ->
        left ≠ right ->
          Disjoint (tree.label left) (tree.label right)) :
    ∀ node left right,
      left ∈ (tree.stage6 A removed).children A node ->
      right ∈ (tree.stage6 A removed).children A node ->
      left ≠ right ->
        Disjoint ((tree.stage6 A removed).label left)
          ((tree.stage6 A removed).label right) := by
  intro node left right hleft hright hne
  rw [stage6_preserves_label A tree removed left]
  rw [stage6_preserves_label A tree removed right]
  exact hsiblingDisjoint node left right
    (by simpa [stage6_children A tree removed node] using hleft)
    (by simpa [stage6_children A tree removed node] using hright)
    hne

theorem stage6_active_label_nonempty [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅) :
    ∀ node, (tree.stage6 A removed).active node = true ->
      (tree.stage6 A removed).label node ≠ ∅ := by
  intro node hactive
  rw [stage6_preserves_label A tree removed node]
  exact hactiveNonempty node
    (by simpa [stage6_active A tree removed node] using hactive)

theorem stage6_restores_consecutive [DecidableEq A.State]
    (tree : CompactTreeData A) (removed : Finset (Node A))
    (hactiveNonempty :
      ∀ node, tree.active node = true -> tree.label node ≠ ∅)
    (hactiveNotRemoved :
      ∀ node, tree.active node = true -> node ∉ removed)
    (hinjective :
      ∀ left right,
        (left ∈ removed ∨ tree.active left = true) ->
        (right ∈ removed ∨ tree.active right = true) ->
        tree.name left = tree.name right ->
          left = right)
    (hcoverLower :
      ∀ node, tree.active node = true ->
        ∀ j : Nat, j < (tree.name node).val ->
          ∃ old, (old ∈ removed ∨ tree.active old = true) ∧
            (tree.name old).val = j) :
    ∀ k : Nat, k < Fintype.card A.State ->
      (∃ node, (tree.stage6 A removed).active node = true ∧
        ((tree.stage6 A removed).name node).val = k) ->
        ∀ j : Nat, j < k ->
          ∃ node, (tree.stage6 A removed).active node = true ∧
            ((tree.stage6 A removed).name node).val = j := by
  classical
  have hremovedNameInjective :
      ∀ left right,
        left ∈ removed ->
        right ∈ removed ->
        tree.name left = tree.name right ->
          left = right := by
    intro left right hleft hright hname
    exact hinjective left right (Or.inl hleft) (Or.inl hright) hname
  have hstage6_nameLt :
      ∀ node, (tree.stage6 A removed).active node = true ->
        ((tree.stage6 A removed).name node).val <
          ((tree.stage6 A removed).activeNodes A).card :=
    stage6_name_lt_activeNodes_card A tree removed
      hactiveNonempty hactiveNotRemoved hremovedNameInjective hcoverLower
  have hstage6_injective :
      ∀ left right,
        (tree.stage6 A removed).active left = true ->
        (tree.stage6 A removed).active right = true ->
        (tree.stage6 A removed).name left =
          (tree.stage6 A removed).name right ->
          left = right :=
    stage6_preserves_name_injective A tree removed
      hactiveNonempty hactiveNotRemoved hinjective
  intro k _ hexists j hj
  rcases hexists with ⟨node, hactive, hname⟩
  have hk_card :
      k < ((tree.stage6 A removed).activeNodes A).card := by
    rw [← hname]
    exact hstage6_nameLt node hactive
  exact exists_active_name_eq_of_lt_activeNodes_card_of_bounded_injective
    A (tree.stage6 A removed) hstage6_injective hstage6_nameLt j
    (by omega)

/-- The only currently external choice in one Piterman transition: stage-2 fresh allocation. -/
structure TransitionPlan [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet) where
  stage2Plan : Stage2Plan A (tree.stage1 A letter)

theorem exists_transitionPlan_of_wellFormed
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (htree : tree.WellFormed A) :
    Nonempty (TransitionPlan A tree letter) := by
  rcases htree with
    ⟨_, _, _, _, _, hbound, hinjective, hconsecutive, _, _, _⟩
  have hstage2 :
      Nonempty (Stage2Plan A (tree.stage1 A letter)) :=
    exists_stage2Plan_of_active_name_bound_injective A (tree.stage1 A letter)
      (by
        intro node hnode
        exact hbound node (by simpa [stage1] using hnode))
      (by
        intro left right hleft hright hname
        exact hinjective left right
          (by simpa [stage1] using hleft)
          (by simpa [stage1] using hright)
          (by simpa [stage1] using hname))
      (by
        intro k hk hexists j hj
        apply hconsecutive k hk
        · rcases hexists with ⟨node, hactive, hname⟩
          exact ⟨node, by simpa [stage1] using hactive,
            by simpa [stage1] using hname⟩
        · exact hj)
  rcases hstage2 with ⟨stage2Plan⟩
  exact ⟨⟨stage2Plan⟩⟩

/-- One complete Piterman Section 3.2 transition, with explicit stage-2 allocation. -/
noncomputable def transitionWithPlan [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) : CompactTreeData A :=
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  t5.stage6 A stage5Removed

theorem transitionWithPlan_root_name_val [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootName : (tree.name (root A)).val = (rootName A).val) :
    ((tree.transitionWithPlan A letter plan).name (root A)).val =
      (rootName A).val := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht2_rootName :
      (t2.name (root A)).val = (rootName A).val := by
    have hname := stage2_root_name A t1 plan.stage2Plan ht1_rootActive
    rw [hname]
    simpa [t1] using hrootName
  have ht5_rootName :
      (t5.name (root A)).val = (rootName A).val := by
    simpa [t2, t3, t4, stage4Removed, t5] using ht2_rootName
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_root_name_val A t5 stage5Removed ht5_rootName)

theorem transitionWithPlan_root_parent [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A) :
    (tree.transitionWithPlan A letter plan).parent (root A) = root A := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    simpa [t1] using hrootParent
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    ht2_rootParent

theorem transitionWithPlan_root_active_of_stage4_root_label_nonempty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hrootLabel :
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A).label
          (root A) ≠ ∅) :
    (tree.transitionWithPlan A letter plan).active (root A) = true := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht2_rootActive : t2.active (root A) = true :=
    stage2_root_active A t1 plan.stage2Plan ht1_rootActive
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    simpa [t1] using hrootParent
  have ht3_rootActive : t3.active (root A) = true := by
    simpa [t3] using ht2_rootActive
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3] using ht2_rootParent
  have hnotGreen : ¬ t3.RemovedByGreen A (root A) :=
    root_not_removedByGreen A t3 ht3_rootParent
  have ht4_rootActive : t4.active (root A) = true := by
    rw [show t4.active (root A) = t3.active (root A) from
      stage4_keeps_unremoved_active A t3 hnotGreen]
    exact ht3_rootActive
  have ht4_rootLabel : t4.label (root A) ≠ ∅ := by
    simpa [t1, t2, t3, t4] using hrootLabel
  have hnotStage5 : ¬ t4.RemovedByStage5 A stage4Removed (root A) := by
    intro hremoved
    rcases hremoved with hgreen | hempty
    · exact hnotGreen ((mem_greenRemovedNodes A t3).mp hgreen)
    · exact ht4_rootLabel ((mem_emptyActiveNodes A t4).mp hempty).2
  have ht5_rootActive : t5.active (root A) = true := by
    rw [show t5.active (root A) = t4.active (root A) from
      stage5_keeps_unremoved_active A t4 stage4Removed hnotStage5]
    exact ht4_rootActive
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    ht5_rootActive

theorem transitionWithPlan_e_pos_of_stage4_root_label_nonempty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (htree : tree.WellFormed A)
    (hrootLabel :
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A).label
          (root A) ≠ ∅) :
    0 < ((tree.transitionWithPlan A letter plan).e).val := by
  classical
  rcases htree with
    ⟨hrootActive, hrootName, hrootParent, _hparentInvariant,
      _hinactiveLabel, _hbound, hinjective, _hconsecutive, _hproper,
      _hchildSubset, _hsiblingDisjoint⟩
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  by_contra hnotPos
  have hezero :
      ((tree.transitionWithPlan A letter plan).e).val = 0 := by omega
  have heqE :
      ((tree.transitionWithPlan A letter plan).e).val =
        (t4.minBoundedNameOf A stage5Removed).val := by
    simp [transitionWithPlan, t1, t2, t3, t4, stage4Removed,
      stage5Removed, stage5_e_val, stage6_e_val]
  have hminZero : (t4.minBoundedNameOf A stage5Removed).val = 0 := by
    omega
  have hcard_pos : 0 < Fintype.card A.State :=
    Fintype.card_pos_iff.mpr ⟨A.initial⟩
  rcases exists_node_name_eq_minBoundedNameOf_of_min_lt_card A t4
      stage5Removed (by omega) with
    ⟨removedNode, hremovedNode, hremovedNameMin⟩
  have hremovedName0 : (t5.name removedNode).val = 0 := by
    simpa [t5, stage5_name A t4 stage4Removed removedNode, hminZero] using
      hremovedNameMin
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht2_injective :
      ∀ left right,
        t2.active left = true ->
        t2.active right = true ->
        t2.name left = t2.name right ->
          left = right := by
    simpa [t2] using
      (stage2_preserves_name_injective A t1 plan.stage2Plan ht1_injective)
  have ht3_injective :
      ∀ left right,
        t3.active left = true ->
        t3.active right = true ->
        t3.name left = t3.name right ->
          left = right := by
    simpa [t3] using
      (stage3_preserves_name_injective A t2 ht2_injective)
  have ht5_rootActive : t5.active (root A) = true := by
    have hfinalRoot :
        (tree.transitionWithPlan A letter plan).active (root A) = true :=
      transitionWithPlan_root_active_of_stage4_root_label_nonempty
        A tree letter plan hrootActive hrootParent hrootLabel
    simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
      stage5Removed, stage6_active] using hfinalRoot
  have ht2_rootName :
      (t2.name (root A)).val = (rootName A).val := by
    have hname := stage2_root_name A t1 plan.stage2Plan
      (by simpa [t1] using hrootActive)
    rw [hname]
    simpa [t1] using hrootName
  have ht5_rootName : (t5.name (root A)).val = 0 := by
    have hname : (t5.name (root A)).val = (rootName A).val := by
      simpa [t2, t3, t4, stage4Removed, t5] using ht2_rootName
    simpa [rootName] using hname
  have hnameEq : t5.name removedNode = t5.name (root A) := by
    apply Fin.ext
    omega
  have hremovedEqRoot : removedNode = root A :=
    stage4_stage5_name_injective_on_removed_or_active A t3 ht3_injective
      removedNode (root A)
      (Or.inl (by simpa [t4, stage4Removed, stage5Removed] using hremovedNode))
      (Or.inr (by simpa [t4, stage4Removed, t5] using ht5_rootActive))
      (by simpa [t4, stage4Removed, t5] using hnameEq)
  have ht4_rootLabel : t4.label (root A) ≠ ∅ := by
    simpa [t1, t2, t3, t4] using hrootLabel
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan
      (by simpa [t1] using hrootActive)
    rw [hparent]
    simpa [t1] using hrootParent
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3] using ht2_rootParent
  have hrootNotRemoved : root A ∉ stage5Removed := by
    intro hrootRemoved
    rw [Finset.mem_union] at hrootRemoved
    rcases hrootRemoved with hgreen | hempty
    · exact root_not_removedByGreen A t3 ht3_rootParent
        ((mem_greenRemovedNodes A t3).mp (by
          simpa [stage4Removed] using hgreen))
    · exact ht4_rootLabel ((mem_emptyActiveNodes A t4).mp hempty).2
  exact hrootNotRemoved (by simpa [hremovedEqRoot] using hremovedNode)

theorem transitionWithPlan_preserves_name_injective
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ left right,
      (tree.transitionWithPlan A letter plan).active left = true ->
      (tree.transitionWithPlan A letter plan).active right = true ->
      (tree.transitionWithPlan A letter plan).name left =
        (tree.transitionWithPlan A letter plan).name right ->
        left = right := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht2_injective :
      ∀ left right,
        t2.active left = true ->
        t2.active right = true ->
        t2.name left = t2.name right ->
          left = right := by
    simpa [t2] using
      (stage2_preserves_name_injective A t1 plan.stage2Plan ht1_injective)
  have ht3_injective :
      ∀ left right,
        t3.active left = true ->
        t3.active right = true ->
        t3.name left = t3.name right ->
          left = right := by
    simpa [t3] using
      (stage3_preserves_name_injective A t2 ht2_injective)
  have ht5_active_nonempty :
      ∀ node, t5.active node = true -> t5.label node ≠ ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_active_label_nonempty A t3 (t3.greenRemovedNodes A))
  have ht5_active_not_removed :
      ∀ node, t5.active node = true -> node ∉ stage5Removed := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_active_not_removed A t3)
  have ht5_removed_or_active_injective :
      ∀ left right,
        (left ∈ stage5Removed ∨ t5.active left = true) ->
        (right ∈ stage5Removed ∨ t5.active right = true) ->
        t5.name left = t5.name right ->
          left = right := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_name_injective_on_removed_or_active A t3 ht3_injective)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_name_injective A t5 stage5Removed
      ht5_active_nonempty ht5_active_not_removed
      ht5_removed_or_active_injective)

theorem transitionWithPlan_preserves_inactive_label
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hinactiveLabel :
      ∀ node, tree.active node = false -> tree.label node = ∅) :
    ∀ node, (tree.transitionWithPlan A letter plan).active node = false ->
      (tree.transitionWithPlan A letter plan).label node = ∅ := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_inactive :
      ∀ node, t1.active node = false -> t1.label node = ∅ := by
    simpa [t1] using
      (stage1_preserves_inactive_label A tree letter hinactiveLabel)
  have ht3_inactive :
      ∀ node, t3.active node = false -> t3.label node = ∅ := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_inactive_label A t1
        plan.stage2Plan ht1_inactive)
  have ht5_inactive :
      ∀ node, t5.active node = false -> t5.label node = ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_preserves_inactive_label A t3
        (t3.greenRemovedNodes A) ht3_inactive)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_inactive_label A t5 stage5Removed ht5_inactive)

/--
`t3`→live label bridge.  A state in the post-stage-(3) label of a node carries
into the final live tree, provided the node is not removed by stage (4) (it is not
a descendant of a green node) nor by stage (5) (it is not empty among the
already-removed set).  Stages (4) and (5) only delete labels of removed nodes and
stage (6) merely renames, so an unremoved node keeps its full stage-(3) label.
This is the bridge used by the breakpoint kernel to move child-union coverage from
`t3` onto the live tree where settling is stated.
-/
theorem mem_transitionWithPlan_label_of_mem_stage3_label
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    {node : Node A} {state : A.State}
    (hstate :
      state ∈
        (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).label node)
    (hnotGreen :
      ¬ (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).RemovedByGreen
          A node)
    (hnotStage5 :
      ¬ ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A).RemovedByStage5
          A ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenRemovedNodes A)
          node) :
    state ∈ (tree.transitionWithPlan A letter plan).label node := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have h4 : t4.label node = t3.label node :=
    stage4_keeps_unremoved_label A t3 hnotGreen
  have h5 : t5.label node = t4.label node :=
    stage5_keeps_unremoved_label A t4 stage4Removed hnotStage5
  have hfinal :
      (tree.transitionWithPlan A letter plan).label node = t3.label node := by
    show (t5.stage6 A stage5Removed).label node = t3.label node
    rw [stage6_preserves_label A t5 stage5Removed node, h5, h4]
  rw [hfinal]
  exact hstate

/--
Reverse `t3`→live monotonicity: the final live label is contained in the
post-stage-(3) label, unconditionally (stages (4) and (5) only shrink labels and
stage (6) renames).  This pulls a live-tree label membership back onto `t3`,
where the breakpoint geometry is stated.
-/
theorem transitionWithPlan_label_subset_stage3
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) (node : Node A) :
    (tree.transitionWithPlan A letter plan).label node ⊆
      (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).label node := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  intro state hstate
  have hstate5 : state ∈ t5.label node := by
    have heq :
        (tree.transitionWithPlan A letter plan).label node = t5.label node := by
      show (t5.stage6 A stage5Removed).label node = t5.label node
      exact stage6_preserves_label A t5 stage5Removed node
    rwa [heq] at hstate
  exact stage4_label_subset A t3 node
    (stage5_label_subset A t4 stage4Removed node hstate5)

theorem transitionWithPlan_final_name_bound
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node, (tree.transitionWithPlan A letter plan).active node = true ->
      ((tree.transitionWithPlan A letter plan).name node).val <
        Fintype.card A.State := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht1_bound :
      ∀ node, t1.active node = true ->
        (t1.name node).val < Fintype.card A.State := by
    intro node hactive
    exact hbound node (by simpa [t1] using hactive)
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht1_consecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, t1.active node ∧ (t1.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, t1.active node ∧ (t1.name node).val = j := by
    intro k hk hexists j hj
    apply hconsecutive k hk
    · rcases hexists with ⟨node, hactive, hname⟩
      exact ⟨node, by simpa [t1] using hactive,
        by simpa [t1] using hname⟩
    · exact hj
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht1_childSubset :
      ∀ node child, child ∈ t1.children A node ->
        t1.label child ⊆ t1.label node := by
    simpa [t1] using
      (stage1_preserves_child_label_subset A tree letter hchildSubset)
  have ht3_parent :
      ∀ node, t3.active node = true -> node ≠ root A ->
        t3.active (t3.parent node) = true ∧
          (t3.name (t3.parent node)).val < (t3.name node).val := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_parent_active_and_name_lt A t1
        plan.stage2Plan ht1_parent)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1
        plan.stage2Plan ht1_parent ht1_childSubset)
  have ht3_sibling :
      ∀ node left right,
        left ∈ t3.children A node ->
        right ∈ t3.children A node ->
        left ≠ right ->
          Disjoint (t3.label left) (t3.label right) := by
    simpa [t2, t3] using
      (stage2_stage3_sibling_labels_disjoint A t1
        plan.stage2Plan ht1_parent ht1_injective)
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    simpa [t1] using hrootParent
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3] using ht2_rootParent
  have hcover_t3 :
      ∀ node, t3.active node = true ->
        ∀ j : Nat, j < (t3.name node).val ->
          ∃ old, t3.active old = true ∧ (t3.name old).val = j := by
    intro node hactive j hj
    have hnode_lt :
        (t3.name node).val <
          (t1.activeNodes A).card + (t1.stage2Triggers A).card := by
      exact stage2_stage3_active_name_lt_active_plus_triggers A t1
        plan.stage2Plan ht1_bound ht1_injective ht1_consecutive node hactive
    have hj_interval :
        j < (t1.activeNodes A).card + (t1.stage2Triggers A).card := by
      omega
    exact stage2_stage3_exists_active_name_eq_of_lt_active_plus_triggers A t1
      plan.stage2Plan ht1_bound ht1_injective ht1_consecutive j hj_interval
  have hcover_t5 :
      ∀ node, t5.active node = true ->
        ∀ j : Nat, j < (t5.name node).val ->
          ∃ old, (old ∈ stage5Removed ∨ t5.active old = true) ∧
            (t5.name old).val = j := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_packed_lower_name_coverage A t3 hcover_t3)
  have ht5_active_nonempty :
      ∀ node, t5.active node = true -> t5.label node ≠ ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_active_label_nonempty A t3 (t3.greenRemovedNodes A))
  have ht5_active_not_removed :
      ∀ node, t5.active node = true -> node ∉ stage5Removed := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_active_not_removed A t3)
  have ht3_injective :
      ∀ left right,
        t3.active left = true ->
        t3.active right = true ->
        t3.name left = t3.name right ->
          left = right := by
    have ht2_injective :
        ∀ left right,
          t2.active left = true ->
          t2.active right = true ->
          t2.name left = t2.name right ->
            left = right := by
      simpa [t2] using
        (stage2_preserves_name_injective A t1 plan.stage2Plan ht1_injective)
    simpa [t3] using
      (stage3_preserves_name_injective A t2 ht2_injective)
  have hstage5Removed_name_injective :
      ∀ left right,
        left ∈ stage5Removed ->
        right ∈ stage5Removed ->
        t5.name left = t5.name right ->
          left = right := by
    intro left right hleft hright hname
    exact stage4_stage5_name_injective_on_removed_or_active A t3 ht3_injective
      left right (Or.inl (by simpa [stage4Removed, stage5Removed] using hleft))
      (Or.inl (by simpa [stage4Removed, stage5Removed] using hright))
      (by simpa [t4, t5, stage4Removed] using hname)
  have ht5_card :
      (t5.activeNodes A).card ≤ Fintype.card A.State := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_activeNodes_card_le_state_card A t3 ht3_rootParent
        ht3_parent ht3_childSubset ht3_sibling)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_final_name_bound A t5 stage5Removed ht5_active_nonempty
      ht5_active_not_removed hstage5Removed_name_injective hcover_t5 ht5_card)

theorem transitionWithPlan_preserves_consecutive
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hbound :
      ∀ node, tree.active node = true ->
        (tree.name node).val < Fintype.card A.State)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hconsecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, tree.active node ∧ (tree.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, tree.active node ∧ (tree.name node).val = j)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ k : Nat, k < Fintype.card A.State ->
      (∃ node, (tree.transitionWithPlan A letter plan).active node = true ∧
        ((tree.transitionWithPlan A letter plan).name node).val = k) ->
        ∀ j : Nat, j < k ->
          ∃ node, (tree.transitionWithPlan A letter plan).active node = true ∧
            ((tree.transitionWithPlan A letter plan).name node).val = j := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht1_bound :
      ∀ node, t1.active node = true ->
        (t1.name node).val < Fintype.card A.State := by
    intro node hactive
    exact hbound node (by simpa [t1] using hactive)
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht1_consecutive :
      ∀ k : Nat, k < Fintype.card A.State ->
        (∃ node, t1.active node ∧ (t1.name node).val = k) ->
          ∀ j : Nat, j < k ->
            ∃ node, t1.active node ∧ (t1.name node).val = j := by
    intro k hk hexists j hj
    apply hconsecutive k hk
    · rcases hexists with ⟨node, hactive, hname⟩
      exact ⟨node, by simpa [t1] using hactive,
        by simpa [t1] using hname⟩
    · exact hj
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht1_childSubset :
      ∀ node child, child ∈ t1.children A node ->
        t1.label child ⊆ t1.label node := by
    simpa [t1] using
      (stage1_preserves_child_label_subset A tree letter hchildSubset)
  have ht3_parent :
      ∀ node, t3.active node = true -> node ≠ root A ->
        t3.active (t3.parent node) = true ∧
          (t3.name (t3.parent node)).val < (t3.name node).val := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_parent_active_and_name_lt A t1
        plan.stage2Plan ht1_parent)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1
        plan.stage2Plan ht1_parent ht1_childSubset)
  have ht3_sibling :
      ∀ node left right,
        left ∈ t3.children A node ->
        right ∈ t3.children A node ->
        left ≠ right ->
          Disjoint (t3.label left) (t3.label right) := by
    simpa [t2, t3] using
      (stage2_stage3_sibling_labels_disjoint A t1
        plan.stage2Plan ht1_parent ht1_injective)
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    simpa [t1] using hrootParent
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3] using ht2_rootParent
  have hcover_t3 :
      ∀ node, t3.active node = true ->
        ∀ j : Nat, j < (t3.name node).val ->
          ∃ old, t3.active old = true ∧ (t3.name old).val = j := by
    intro node hactive j hj
    have hnode_lt :
        (t3.name node).val <
          (t1.activeNodes A).card + (t1.stage2Triggers A).card := by
      exact stage2_stage3_active_name_lt_active_plus_triggers A t1
        plan.stage2Plan ht1_bound ht1_injective ht1_consecutive node hactive
    have hj_interval :
        j < (t1.activeNodes A).card + (t1.stage2Triggers A).card := by
      omega
    exact stage2_stage3_exists_active_name_eq_of_lt_active_plus_triggers A t1
      plan.stage2Plan ht1_bound ht1_injective ht1_consecutive j hj_interval
  have hcover_t5 :
      ∀ node, t5.active node = true ->
        ∀ j : Nat, j < (t5.name node).val ->
          ∃ old, (old ∈ stage5Removed ∨ t5.active old = true) ∧
            (t5.name old).val = j := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_packed_lower_name_coverage A t3 hcover_t3)
  have ht5_active_nonempty :
      ∀ node, t5.active node = true -> t5.label node ≠ ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_active_label_nonempty A t3 (t3.greenRemovedNodes A))
  have ht5_active_not_removed :
      ∀ node, t5.active node = true -> node ∉ stage5Removed := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_active_not_removed A t3)
  have ht3_injective :
      ∀ left right,
        t3.active left = true ->
        t3.active right = true ->
        t3.name left = t3.name right ->
          left = right := by
    have ht2_injective :
        ∀ left right,
          t2.active left = true ->
          t2.active right = true ->
          t2.name left = t2.name right ->
            left = right := by
      simpa [t2] using
        (stage2_preserves_name_injective A t1 plan.stage2Plan ht1_injective)
    simpa [t3] using
      (stage3_preserves_name_injective A t2 ht2_injective)
  have ht5_removed_or_active_injective :
      ∀ left right,
        (left ∈ stage5Removed ∨ t5.active left = true) ->
        (right ∈ stage5Removed ∨ t5.active right = true) ->
        t5.name left = t5.name right ->
          left = right := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_name_injective_on_removed_or_active A t3 ht3_injective)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_restores_consecutive A t5 stage5Removed
      ht5_active_nonempty ht5_active_not_removed
      ht5_removed_or_active_injective hcover_t5)

theorem transitionWithPlan_preserves_child_label_subset
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node child, child ∈ (tree.transitionWithPlan A letter plan).children A node ->
      (tree.transitionWithPlan A letter plan).label child ⊆
        (tree.transitionWithPlan A letter plan).label node := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht1_childSubset :
      ∀ node child, child ∈ t1.children A node ->
        t1.label child ⊆ t1.label node := by
    simpa [t1] using
      (stage1_preserves_child_label_subset A tree letter hchildSubset)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1
        plan.stage2Plan ht1_parent ht1_childSubset)
  have ht5_childSubset :
      ∀ node child, child ∈ t5.children A node ->
        t5.label child ⊆ t5.label node := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_preserves_child_label_subset A t3 ht3_childSubset)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_child_label_subset A t5 stage5Removed ht5_childSubset)

theorem transitionWithPlan_preserves_sibling_disjoint
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right) :
    ∀ node left right,
      left ∈ (tree.transitionWithPlan A letter plan).children A node ->
      right ∈ (tree.transitionWithPlan A letter plan).children A node ->
      left ≠ right ->
        Disjoint ((tree.transitionWithPlan A letter plan).label left)
          ((tree.transitionWithPlan A letter plan).label right) := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht3_siblingDisjoint :
      ∀ node left right,
        left ∈ t3.children A node ->
        right ∈ t3.children A node ->
        left ≠ right ->
          Disjoint (t3.label left) (t3.label right) := by
    simpa [t2, t3] using
      (stage2_stage3_sibling_labels_disjoint A t1
        plan.stage2Plan ht1_parent ht1_injective)
  have ht5_siblingDisjoint :
      ∀ node left right,
        left ∈ t5.children A node ->
        right ∈ t5.children A node ->
        left ≠ right ->
          Disjoint (t5.label left) (t5.label right) := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_preserves_sibling_disjoint A t3
        (t3.greenRemovedNodes A) ht3_siblingDisjoint)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_sibling_disjoint A t5 stage5Removed ht5_siblingDisjoint)

theorem transitionWithPlan_preserves_parent_active_and_name_lt
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hinjective :
      ∀ left right,
        tree.active left = true ->
        tree.active right = true ->
        tree.name left = tree.name right ->
          left = right)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node,
      (tree.transitionWithPlan A letter plan).active node = true ->
      node ≠ root A ->
        (tree.transitionWithPlan A letter plan).active
            ((tree.transitionWithPlan A letter plan).parent node) = true ∧
          ((tree.transitionWithPlan A letter plan).name
              ((tree.transitionWithPlan A letter plan).parent node)).val <
            ((tree.transitionWithPlan A letter plan).name node).val := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht1_injective :
      ∀ left right,
        t1.active left = true ->
        t1.active right = true ->
        t1.name left = t1.name right ->
          left = right := by
    simpa [t1] using
      (stage1_preserves_name_injective A tree letter hinjective)
  have ht3_parent :
      ∀ node, t3.active node = true -> node ≠ root A ->
        t3.active (t3.parent node) = true ∧
          (t3.name (t3.parent node)).val < (t3.name node).val := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_parent_active_and_name_lt A t1
        plan.stage2Plan ht1_parent)
  have ht3_injective :
      ∀ left right,
        t3.active left = true ->
        t3.active right = true ->
        t3.name left = t3.name right ->
          left = right := by
    have ht2_injective :
        ∀ left right,
          t2.active left = true ->
          t2.active right = true ->
          t2.name left = t2.name right ->
            left = right := by
      simpa [t2] using
        (stage2_preserves_name_injective A t1 plan.stage2Plan ht1_injective)
    simpa [t3] using
      (stage3_preserves_name_injective A t2 ht2_injective)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    have ht1_childSubset :
        ∀ node child, child ∈ t1.children A node ->
          t1.label child ⊆ t1.label node := by
      simpa [t1] using
        (stage1_preserves_child_label_subset A tree letter hchildSubset)
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1
        plan.stage2Plan ht1_parent ht1_childSubset)
  have ht5_parent :
      ∀ node, t5.active node = true -> node ≠ root A ->
        t5.active (t5.parent node) = true ∧
          (t5.name (t5.parent node)).val < (t5.name node).val := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_preserves_parent_active_and_name_lt A t3
        ht3_parent ht3_childSubset)
  have ht5_active_nonempty :
      ∀ node, t5.active node = true -> t5.label node ≠ ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_active_label_nonempty A t3 (t3.greenRemovedNodes A))
  have ht5_active_not_removed :
      ∀ node, t5.active node = true -> node ∉ stage5Removed := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_active_not_removed A t3)
  have ht5_removed_or_active_injective :
      ∀ left right,
        (left ∈ stage5Removed ∨ t5.active left = true) ->
        (right ∈ stage5Removed ∨ t5.active right = true) ->
        t5.name left = t5.name right ->
          left = right := by
    simpa [t4, t5, stage4Removed, stage5Removed] using
      (stage4_stage5_name_injective_on_removed_or_active A t3 ht3_injective)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_parent_active_and_name_lt A t5 stage5Removed
      ht5_parent ht5_active_nonempty ht5_active_not_removed
      ht5_removed_or_active_injective)

theorem transitionWithPlan_active_label_nonempty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter) :
    ∀ node, (tree.transitionWithPlan A letter plan).active node = true ->
      (tree.transitionWithPlan A letter plan).label node ≠ ∅ := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht5_active_nonempty :
      ∀ node, t5.active node = true -> t5.label node ≠ ∅ := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_active_label_nonempty A t3 (t3.greenRemovedNodes A))
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_active_label_nonempty A t5 stage5Removed ht5_active_nonempty)

theorem transitionWithPlan_name_val_eq_stage5_name_of_stage5_e_ge
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    {node : Node A} :
    let t1 := tree.stage1 A letter
    let t2 := t1.stage2 A plan.stage2Plan
    let t3 := t2.stage3 A
    let t4 := t3.stage4 A
    let stage4Removed := t3.greenRemovedNodes A
    let t5 := t4.stage5 A stage4Removed
    t5.label node ≠ ∅ ->
      (t5.name node).val < Fintype.card A.State ->
        (t5.name node).val ≤
          ((tree.transitionWithPlan A letter plan).e).val ->
          ((tree.transitionWithPlan A letter plan).name node).val =
            (t5.name node).val := by
  dsimp only
  intro hlabel hnodeBound he
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have he_t5 : (t5.name node).val ≤ (t5.e).val := by
    have he' : (t5.name node).val ≤
        ((tree.transitionWithPlan A letter plan).e).val := by
      simpa [t1, t2, t3, t4, stage4Removed, t5] using he
    simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
      stage5Removed, stage6_e_val] using he'
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
    stage5Removed] using
    (stage5_stage6_nonempty_name_val_eq_oldName_of_e_ge A t4 stage4Removed
      (node := node)
      (by simpa [t1, t2, t3, t4, stage4Removed, t5] using hlabel)
      (by simpa [t1, t2, t3, t4, stage4Removed, t5] using hnodeBound)
      he_t5)

theorem transitionWithPlan_stage4_keeps_active_of_name_le_f
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A} :
    let t1 := tree.stage1 A letter
    let t2 := t1.stage2 A plan.stage2Plan
    let t3 := t2.stage3 A
    t3.active node = true ->
      (t3.name node).val < Fintype.card A.State ->
        (t3.name node).val ≤
          ((tree.transitionWithPlan A letter plan).f).val ->
          (t3.stage4 A).active node = true := by
  dsimp only
  intro hnodeActive hnodeBound hle
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1, stage1_active A tree letter (root A)] using hrootActive
  have ht1_rootParent : t1.parent (root A) = root A := by
    simpa [t1, stage1] using hrootParent
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    exact ht1_rootParent
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3, stage3] using ht2_rootParent
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht3_parent :
      ∀ node, t3.active node = true -> node ≠ root A ->
        t3.active (t3.parent node) = true ∧
          (t3.name (t3.parent node)).val < (t3.name node).val := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_parent_active_and_name_lt A t1
        plan.stage2Plan ht1_parent)
  have hleStage4 :
      (t3.name node).val ≤ ((t3.stage4 A).f).val := by
    have hle' :
        (t3.name node).val ≤
          ((tree.transitionWithPlan A letter plan).f).val := by
      simpa [t1, t2, t3] using hle
    have hf :
        ((tree.transitionWithPlan A letter plan).f).val =
          ((t3.stage4 A).f).val := by
      simp [transitionWithPlan, t1, t2, t3, stage5_f_val, stage6_f_val]
    omega
  exact stage4_keeps_active_of_name_le_f A t3 ht3_rootParent ht3_parent
    hnodeActive hnodeBound hleStage4

theorem transitionWithPlan_preserves_active_name_of_no_smaller_event
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootParent : tree.parent (root A) = root A)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    {node : Node A} :
    let t1 := tree.stage1 A letter
    let t2 := t1.stage2 A plan.stage2Plan
    let t3 := t2.stage3 A
    t3.active node = true ->
      (t3.name node).val < Fintype.card A.State ->
        (t3.name node).val ≤
          ((tree.transitionWithPlan A letter plan).f).val ->
          (t3.name node).val <
            ((tree.transitionWithPlan A letter plan).e).val ->
            (tree.transitionWithPlan A letter plan).active node = true ∧
              ((tree.transitionWithPlan A letter plan).name node).val =
                (t3.name node).val := by
  dsimp only
  intro hnodeActive hnodeBound hf he
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have heLocal :
      (t3.name node).val <
        ((tree.transitionWithPlan A letter plan).e).val := by
    simpa [t1, t2, t3] using he
  have ht4Active : t4.active node = true := by
    simpa [t1, t2, t3, t4] using
      (transitionWithPlan_stage4_keeps_active_of_name_le_f A tree letter
        plan hrootActive hrootParent hparentInvariant
        (node := node) hnodeActive hnodeBound hf)
  have hnotStage5 : ¬ t4.RemovedByStage5 A stage4Removed node := by
    intro hremoved
    rcases hremoved with hstage4Removed | hempty
    · have hnotGreen : ¬ t3.RemovedByGreen A node :=
        (stage4_active_cases A t3 (by simpa [t4] using ht4Active)).2
      exact hnotGreen ((mem_greenRemovedNodes A t3).mp hstage4Removed)
    · have hminLe :
          (t4.minBoundedNameOf A (stage4Removed ∪ t4.emptyActiveNodes A)).val ≤
            (t4.name node).val := by
        have ht4Bound : (t4.name node).val < Fintype.card A.State := by
          simpa [t4, stage4_name A t3 node] using hnodeBound
        exact minBoundedNameOf_le_of_mem A t4
          (stage4Removed ∪ t4.emptyActiveNodes A)
          (Finset.mem_union_right stage4Removed hempty) ht4Bound
      have heqE :
          ((tree.transitionWithPlan A letter plan).e).val =
            (t4.minBoundedNameOf A
              (stage4Removed ∪ t4.emptyActiveNodes A)).val := by
        simp [transitionWithPlan, t1, t2, t3, t4, stage4Removed,
          stage5_e_val, stage6_e_val]
      have hnameT4 : (t4.name node).val = (t3.name node).val := by
        simp [t4, stage4_name A t3 node]
      omega
  have ht5Active : t5.active node = true := by
    rw [show t5.active node = t4.active node from
      stage5_keeps_unremoved_active A t4 stage4Removed hnotStage5]
    exact ht4Active
  have hfinalActive :
      (tree.transitionWithPlan A letter plan).active node = true := by
    simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
      stage5Removed, stage6_active A t5 stage5Removed node] using ht5Active
  have ht5Label : t5.label node ≠ ∅ :=
    stage5_active_label_nonempty A t4 stage4Removed ht5Active
  have ht5Bound : (t5.name node).val < Fintype.card A.State := by
    simpa [t5, t4, stage5_name A t4 stage4Removed node,
      stage4_name A t3 node] using hnodeBound
  have ht5NameEqT3 : (t5.name node).val = (t3.name node).val := by
    simp [t5, t4, stage5_name A t4 stage4Removed node,
      stage4_name A t3 node]
  have hleE :
      (t5.name node).val ≤
        ((tree.transitionWithPlan A letter plan).e).val := by
    omega
  have hfinalNameEqT5 :
      ((tree.transitionWithPlan A letter plan).name node).val =
        (t5.name node).val := by
    simpa [t1, t2, t3, t4, stage4Removed, t5] using
      (transitionWithPlan_name_val_eq_stage5_name_of_stage5_e_ge
        A tree letter plan (node := node) ht5Label ht5Bound hleE)
  have hfinalNameEqT3 :
      ((tree.transitionWithPlan A letter plan).name node).val =
        (t3.name node).val := by
    rw [hfinalNameEqT5, ht5NameEqT3]
  exact ⟨hfinalActive, hfinalNameEqT3⟩

theorem transitionWithPlan_preserves_childLabelUnion_ssubset
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hparentInvariant :
      ∀ node, tree.active node = true -> node ≠ root A ->
        tree.active (tree.parent node) = true ∧
          (tree.name (tree.parent node)).val < (tree.name node).val)
    (hchildSubset :
      ∀ node child, child ∈ tree.children A node ->
        tree.label child ⊆ tree.label node) :
    ∀ node, (tree.transitionWithPlan A letter plan).active node = true ->
      (tree.transitionWithPlan A letter plan).childLabelUnion A node ⊂
        (tree.transitionWithPlan A letter plan).label node := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have ht1_parent :
      ∀ node, t1.active node = true -> node ≠ root A ->
        t1.active (t1.parent node) = true ∧
          (t1.name (t1.parent node)).val < (t1.name node).val := by
    simpa [t1] using
      (stage1_preserves_parent_active_and_name_lt A tree letter
        hparentInvariant)
  have ht1_childSubset :
      ∀ node child, child ∈ t1.children A node ->
        t1.label child ⊆ t1.label node := by
    simpa [t1] using
      (stage1_preserves_child_label_subset A tree letter hchildSubset)
  have ht3_childSubset :
      ∀ node child, child ∈ t3.children A node ->
        t3.label child ⊆ t3.label node := by
    simpa [t2, t3] using
      (stage2_stage3_preserves_child_label_subset A t1
        plan.stage2Plan ht1_parent ht1_childSubset)
  have ht5_proper :
      ∀ node, t5.active node = true ->
        t5.childLabelUnion A node ⊂ t5.label node := by
    simpa [t4, t5, stage4Removed] using
      (stage4_stage5_preserves_childLabelUnion_ssubset A t3 ht3_childSubset)
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5, stage5Removed] using
    (stage6_preserves_childLabelUnion_ssubset A t5 stage5Removed ht5_proper)

theorem transitionWithPlan_preserves_wellFormed_of_stage4_root_label_nonempty
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (htree : tree.WellFormed A)
    (hrootLabel :
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A).label
        (root A) ≠ ∅) :
    (tree.transitionWithPlan A letter plan).WellFormed A := by
  rcases htree with
    ⟨hrootActive, hrootName, hrootParent, hparentInvariant,
      hinactiveLabel, hbound, hinjective, hconsecutive, hproper,
      hchildSubset, hsiblingDisjoint⟩
  exact
    ⟨transitionWithPlan_root_active_of_stage4_root_label_nonempty A tree
        letter plan hrootActive hrootParent hrootLabel,
      transitionWithPlan_root_name_val A tree letter plan
        hrootActive hrootName,
      transitionWithPlan_root_parent A tree letter plan
        hrootActive hrootParent,
      transitionWithPlan_preserves_parent_active_and_name_lt A tree letter
        plan hparentInvariant hinjective hchildSubset,
      transitionWithPlan_preserves_inactive_label A tree letter plan
        hinactiveLabel,
      transitionWithPlan_final_name_bound A tree letter plan
        hrootActive hrootParent hparentInvariant hbound hinjective
        hconsecutive hchildSubset,
      transitionWithPlan_preserves_name_injective A tree letter plan
        hinjective,
      transitionWithPlan_preserves_consecutive A tree letter plan
        hrootActive hrootParent hparentInvariant hbound hinjective
        hconsecutive hchildSubset,
      transitionWithPlan_preserves_childLabelUnion_ssubset A tree letter
        plan hparentInvariant hchildSubset,
      transitionWithPlan_preserves_child_label_subset A tree letter plan
        hparentInvariant hchildSubset,
      transitionWithPlan_preserves_sibling_disjoint A tree letter plan
        hparentInvariant hinjective⟩

theorem transitionWithPlan_root_label_subset_stepImage
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true) :
    (tree.transitionWithPlan A letter plan).label (root A) ⊆
      stepImage A letter (tree.label (root A)) := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  intro state hstate
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht2_rootLabel :
      t2.label (root A) = t1.label (root A) := by
    simpa [t2] using
      (stage2_preserves_active_node_label A t1 plan.stage2Plan
        ht1_rootActive)
  have hstate_t5 : state ∈ t5.label (root A) := by
    simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
      stage5Removed, stage6_preserves_label A t5 stage5Removed (root A)]
      using hstate
  have hstate_t4 : state ∈ t4.label (root A) :=
    stage5_label_subset A t4 stage4Removed (root A) hstate_t5
  have hstate_t3 : state ∈ t3.label (root A) :=
    stage4_label_subset A t3 (root A) hstate_t4
  have hstate_t2 : state ∈ t2.label (root A) :=
    stage3_label_subset A t2 (root A) hstate_t3
  rw [ht2_rootLabel] at hstate_t2
  simpa [t1, stage1] using hstate_t2

theorem stepImage_subset_transitionWithPlan_stage4_root_label
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootName : (tree.name (root A)).val = (rootName A).val)
    (hrootParent : tree.parent (root A) = root A) :
    stepImage A letter (tree.label (root A)) ⊆
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).stage4 A).label
        (root A) := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  intro state hstate
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht1_rootName : (t1.name (root A)).val = (rootName A).val := by
    simpa [t1, stage1] using hrootName
  have ht1_rootParent : t1.parent (root A) = root A := by
    simpa [t1, stage1] using hrootParent
  have ht2_rootLabel :
      t2.label (root A) = t1.label (root A) := by
    simpa [t2] using
      (stage2_preserves_active_node_label A t1 plan.stage2Plan
        ht1_rootActive)
  have ht2_rootName : (t2.name (root A)).val = (rootName A).val := by
    have hname := stage2_root_name A t1 plan.stage2Plan ht1_rootActive
    rw [hname]
    exact ht1_rootName
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    exact ht1_rootParent
  have hstate_t1 : state ∈ t1.label (root A) :=
    (mem_stage1_label A tree letter).mpr ((mem_stepImage A).mp hstate)
  have hstate_t2 : state ∈ t2.label (root A) := by
    rw [ht2_rootLabel]
    exact hstate_t1
  have hstate_t3 : state ∈ t3.label (root A) := by
    rw [show t3.label (root A) = t2.label (root A) by
      simpa [t3] using
        (stage3_root_label A t2 ht2_rootParent ht2_rootName)]
    exact hstate_t2
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3, stage3] using ht2_rootParent
  have hnotGreen : ¬ t3.RemovedByGreen A (root A) :=
    root_not_removedByGreen A t3 ht3_rootParent
  have hstate_t4 : state ∈ t4.label (root A) := by
    rw [show t4.label (root A) = t3.label (root A) from
      stage4_keeps_unremoved_label A t3 hnotGreen]
    exact hstate_t3
  simpa [t1, t2, t3, t4] using hstate_t4

theorem stepImage_subset_transitionWithPlan_root_label
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootName : (tree.name (root A)).val = (rootName A).val)
    (hrootParent : tree.parent (root A) = root A) :
    stepImage A letter (tree.label (root A)) ⊆
      (tree.transitionWithPlan A letter plan).label (root A) := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  intro state hstate
  have ht1_rootActive : t1.active (root A) = true := by
    simpa [t1] using hrootActive
  have ht1_rootName : (t1.name (root A)).val = (rootName A).val := by
    simpa [t1, stage1] using hrootName
  have ht1_rootParent : t1.parent (root A) = root A := by
    simpa [t1, stage1] using hrootParent
  have ht2_rootLabel :
      t2.label (root A) = t1.label (root A) := by
    simpa [t2] using
      (stage2_preserves_active_node_label A t1 plan.stage2Plan
        ht1_rootActive)
  have ht2_rootName : (t2.name (root A)).val = (rootName A).val := by
    have hname := stage2_root_name A t1 plan.stage2Plan ht1_rootActive
    rw [hname]
    exact ht1_rootName
  have ht2_rootParent : t2.parent (root A) = root A := by
    have hparent := stage2_root_parent A t1 plan.stage2Plan ht1_rootActive
    rw [hparent]
    exact ht1_rootParent
  have hstate_t1 : state ∈ t1.label (root A) := by
    exact (mem_stage1_label A tree letter).mpr ((mem_stepImage A).mp hstate)
  have hstate_t2 : state ∈ t2.label (root A) := by
    rw [ht2_rootLabel]
    exact hstate_t1
  have hstate_t3 : state ∈ t3.label (root A) := by
    rw [show t3.label (root A) = t2.label (root A) by
      simpa [t3] using
        (stage3_root_label A t2 ht2_rootParent ht2_rootName)]
    exact hstate_t2
  have ht3_rootParent : t3.parent (root A) = root A := by
    simpa [t3, stage3] using ht2_rootParent
  have hnotGreen : ¬ t3.RemovedByGreen A (root A) :=
    root_not_removedByGreen A t3 ht3_rootParent
  have hstate_t4 : state ∈ t4.label (root A) := by
    rw [show t4.label (root A) = t3.label (root A) from
      stage4_keeps_unremoved_label A t3 hnotGreen]
    exact hstate_t3
  have hnotStage5 : ¬ t4.RemovedByStage5 A stage4Removed (root A) := by
    intro hremoved
    rcases hremoved with hgreen | hempty
    · exact hnotGreen ((mem_greenRemovedNodes A t3).mp hgreen)
    · have hnonempty : t4.label (root A) ≠ ∅ := by
        exact Finset.ne_empty_of_mem hstate_t4
      exact hnonempty ((mem_emptyActiveNodes A t4).mp hempty).2
  have hstate_t5 : state ∈ t5.label (root A) := by
    rw [show t5.label (root A) = t4.label (root A) from
      stage5_keeps_unremoved_label A t4 stage4Removed hnotStage5]
    exact hstate_t4
  simpa [transitionWithPlan, t1, t2, t3, t4, stage4Removed, t5,
    stage5Removed, stage6_preserves_label A t5 stage5Removed (root A)]
    using hstate_t5

theorem transitionWithPlan_root_label_eq_stepImage
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hrootActive : tree.active (root A) = true)
    (hrootName : (tree.name (root A)).val = (rootName A).val)
    (hrootParent : tree.parent (root A) = root A) :
    (tree.transitionWithPlan A letter plan).label (root A) =
      stepImage A letter (tree.label (root A)) := by
  exact Finset.Subset.antisymm
    (transitionWithPlan_root_label_subset_stepImage A tree letter plan
      hrootActive)
    (stepImage_subset_transitionWithPlan_root_label A tree letter plan
      hrootActive hrootName hrootParent)

theorem transitionWithPlan_exists_green_name_eq_f
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hboundedGreen :
      ∃ green,
        green ∈
          (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenNodes
            A ∧
        ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).name
          green).val < Fintype.card A.State) :
    ∃ green,
      green ∈
        (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenNodes
          A ∧
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).name
        green).val =
        ((tree.transitionWithPlan A letter plan).f).val := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  obtain ⟨green, hgreen, hname⟩ :=
    exists_node_name_eq_minBoundedNameOf_of_bounded_nonempty A t3
      (t3.greenNodes A)
      (by simpa [t1, t2, t3] using hboundedGreen)
  refine ⟨green, by simpa [t1, t2, t3] using hgreen, ?_⟩
  have hf :
      ((tree.transitionWithPlan A letter plan).f).val =
        ((t3.stage4 A).f).val := by
    simp [transitionWithPlan, t1, t2, t3, stage5_f_val, stage6_f_val]
  rw [hf]
  simpa [t1, t2, t3, stage4_f_val] using hname

theorem transitionWithPlan_exists_green_name_eq_f_of_f_lt_card
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hfcard :
      ((tree.transitionWithPlan A letter plan).f).val <
        Fintype.card A.State) :
    ∃ green,
      green ∈
        (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenNodes
          A ∧
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).name
        green).val =
        ((tree.transitionWithPlan A letter plan).f).val := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  have hf :
      ((tree.transitionWithPlan A letter plan).f).val =
        ((t3.stage4 A).f).val := by
    simp [transitionWithPlan, t1, t2, t3, stage5_f_val, stage6_f_val]
  have hmin :
      (t3.minBoundedNameOf A (t3.greenNodes A)).val <
        Fintype.card A.State := by
    have hfstage4 : ((t3.stage4 A).f).val <
        Fintype.card A.State := by
      rw [← hf]
      exact hfcard
    simpa [stage4_f_val A t3] using hfstage4
  rcases exists_node_name_eq_minBoundedNameOf_of_min_lt_card A t3
      (t3.greenNodes A) hmin with
    ⟨green, hgreen, hname⟩
  refine ⟨green, by simpa [t1, t2, t3] using hgreen, ?_⟩
  rw [hf]
  simpa [t1, t2, t3, stage4_f_val] using hname

theorem transitionWithPlan_exists_green_name_eq_f_of_f_lt_e
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    (hfe :
      ((tree.transitionWithPlan A letter plan).f).val <
        ((tree.transitionWithPlan A letter plan).e).val) :
    ∃ green,
      green ∈
        (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenNodes
          A ∧
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).name
        green).val =
        ((tree.transitionWithPlan A letter plan).f).val := by
  have hfcard :
      ((tree.transitionWithPlan A letter plan).f).val <
        Fintype.card A.State := by
    have he_le :
        ((tree.transitionWithPlan A letter plan).e).val ≤
          Fintype.card A.State := by
      exact Nat.lt_succ_iff.mp ((tree.transitionWithPlan A letter plan).e).isLt
    omega
  exact transitionWithPlan_exists_green_name_eq_f_of_f_lt_card A tree letter
    plan hfcard

theorem transitionWithPlan_green_name_eq_f_label_nonempty_of_f_lt_e
    [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (plan : TransitionPlan A tree letter)
    {green : Node A}
    (hgreen :
      green ∈
        (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).greenNodes
          A)
    (hname :
      ((((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).name
        green).val =
        ((tree.transitionWithPlan A letter plan).f).val)
    (hfe :
      ((tree.transitionWithPlan A letter plan).f).val <
        ((tree.transitionWithPlan A letter plan).e).val) :
    (((tree.stage1 A letter).stage2 A plan.stage2Plan).stage3 A).label green ≠
      ∅ := by
  let t1 := tree.stage1 A letter
  let t2 := t1.stage2 A plan.stage2Plan
  let t3 := t2.stage3 A
  let t4 := t3.stage4 A
  let stage4Removed := t3.greenRemovedNodes A
  let t5 := t4.stage5 A stage4Removed
  let stage5Removed := stage4Removed ∪ t4.emptyActiveNodes A
  intro hempty
  have hgreen_t3 : green ∈ t3.greenNodes A := by
    simpa [t1, t2, t3] using hgreen
  have hgreenActive : t3.active green = true :=
    (mem_greenNodes A t3).mp hgreen_t3 |>.1
  have hremovedUnion :
      green ∈ stage4Removed ∪ t4.emptyActiveNodes A := by
    by_cases hremoved : t3.RemovedByGreen A green
    · exact Finset.mem_union_left _ ((mem_greenRemovedNodes A t3).mpr hremoved)
    · have hstage4Active : t4.active green = true := by
        simpa [t4] using
          (stage4_keeps_unremoved_active A t3 hremoved ▸ hgreenActive)
      have hstage4Label : t4.label green = ∅ := by
        rw [show t4.label green = t3.label green by
          simpa [t4] using stage4_keeps_unremoved_label A t3 hremoved]
        simpa [t1, t2, t3] using hempty
      exact Finset.mem_union_right _
        ((mem_emptyActiveNodes A t4).mpr ⟨hstage4Active, hstage4Label⟩)
  have hfcard :
      ((tree.transitionWithPlan A letter plan).f).val <
        Fintype.card A.State := by
    have he_le :
        ((tree.transitionWithPlan A letter plan).e).val ≤
          Fintype.card A.State :=
      Nat.lt_succ_iff.mp ((tree.transitionWithPlan A letter plan).e).isLt
    omega
  have hgreenBound : (t4.name green).val < Fintype.card A.State := by
    have hname_t4 :
        (t4.name green).val =
          ((tree.transitionWithPlan A letter plan).f).val := by
      simpa [t1, t2, t3, t4, stage4_name] using hname
    rw [hname_t4]
    exact hfcard
  have hmin_le :
      (t4.minBoundedNameOf A (stage4Removed ∪ t4.emptyActiveNodes A)).val ≤
        (t4.name green).val :=
    minBoundedNameOf_le_of_mem A t4
      (stage4Removed ∪ t4.emptyActiveNodes A) hremovedUnion hgreenBound
  have heqE :
      ((tree.transitionWithPlan A letter plan).e).val =
        (t4.minBoundedNameOf A (stage4Removed ∪ t4.emptyActiveNodes A)).val := by
    simp [transitionWithPlan, t1, t2, t3, t4, stage4Removed,
      stage5_e_val, stage6_e_val]
  have hname_t4 :
      (t4.name green).val =
        ((tree.transitionWithPlan A letter plan).f).val := by
    simpa [t1, t2, t3, t4, stage4_name] using hname
  omega

/-- One complete transition with the fresh stage-2 allocation chosen from well-formedness. -/
noncomputable def transitionFromWellFormed [DecidableEq A.State]
    (tree : CompactTreeData A) (letter : Alphabet)
    (htree : tree.WellFormed A) : CompactTreeData A :=
  tree.transitionWithPlan A letter
    (Classical.choice (exists_transitionPlan_of_wellFormed A tree letter htree))

abbrev LiveState [DecidableEq A.State] : Type _ :=
  { tree : CompactTreeData A // tree.WellFormed A }

abbrev DPWState [DecidableEq A.State] : Type _ :=
  Option (LiveState A)

theorem live_exists_descendant_label_frontier
    [DecidableEq A.State]
    (live : LiveState A)
    {node : Node A} {state : A.State}
    (hactive : live.1.active node = true)
    (hstate : state ∈ live.1.label node) :
    ∃ frontier,
      live.1.active frontier = true ∧
        live.1.IsAncestorOrSelf A node frontier ∧
          state ∈ live.1.label frontier ∧
            state ∉ live.1.childLabelUnion A frontier := by
  rcases live.2 with
    ⟨_hrootActive, _hrootName, _hrootParent, hparentInvariant,
      _hinactiveLabel, hbound, _hinjective, _hconsecutive, _hproper,
      _hchildSubset, _hsiblingDisjoint⟩
  exact exists_descendant_label_frontier A live.1 hparentInvariant hbound
    hactive hstate

theorem live_exists_root_label_frontier
    [DecidableEq A.State]
    (live : LiveState A)
    {state : A.State}
    (hstate : state ∈ live.1.label (root A)) :
    ∃ frontier,
      live.1.active frontier = true ∧
        live.1.IsAncestorOrSelf A (root A) frontier ∧
          state ∈ live.1.label frontier ∧
            state ∉ live.1.childLabelUnion A frontier := by
  exact live_exists_descendant_label_frontier A live live.2.1 hstate


end CompactTreeData
end Piterman
end NondetBuchiAutomaton
end DistributedSynthesis
