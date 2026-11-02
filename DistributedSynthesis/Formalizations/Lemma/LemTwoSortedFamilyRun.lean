/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Two-sorted family runs

This is the recursive layer needed after simultaneous root narrowing.  A
`family` state contains all hidden anchors compatible with one blind local
view and chooses one complete transition for the family.  A `chosen` state
records which objective candidate and successor family a direction selected;
it contributes the candidate priority and immediately returns to that family.

The separation is essential.  Rationalization happens at the finite family
state, which contains no distinguished real anchor.  It therefore cannot
choose different sender behavior for two hidden real anchors.  The chosen
state carries proof-only parity information but makes no strategy choice.
-/

namespace DistributedSynthesis

universe u v

/-- Alternating control/priority states of a hidden-root family run. -/
inductive TwoSortedFamilyState (Descriptor : Type u) where
  | family (roots : Finset Descriptor)
  | chosen (actual : Descriptor) (nextRoots : Finset Descriptor)

namespace TwoSortedFamilyState

variable {Descriptor : Type u} [Fintype Descriptor]

noncomputable instance : Fintype (TwoSortedFamilyState Descriptor) := by
  classical
  let Rep := Finset Descriptor ⊕ (Descriptor × Finset Descriptor)
  let e : TwoSortedFamilyState Descriptor ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .family roots => .inl roots
        | .chosen actual roots => .inr (actual, roots)
      invFun := fun state =>
        match state with
        | .inl roots => .family roots
        | .inr pair => .chosen pair.1 pair.2
      left_inv := by intro state; cases state <;> rfl
      right_inv := by intro state; cases state <;> rfl }
  exact Fintype.ofEquiv Rep e.symm

end TwoSortedFamilyState

/-- A family transition chooses, for every environment direction, the actual
objective descriptor and the whole next hidden-root family. -/
abbrev TwoSortedFamilySuccessor (Descriptor : Type u) (Branch : Type v) :=
  Branch → Descriptor × Finset Descriptor

/-- A neutral priority strictly above every shifted descriptor priority. -/
noncomputable def twoSortedFamilyNeutral
    {Descriptor : Type u} [Fintype Descriptor]
    (priority : Descriptor → Nat) : Nat := by
  classical
  exact Finset.univ.sup priority + 4

theorem twoSortedFamilyPriority_lt_neutral
    {Descriptor : Type u} [Fintype Descriptor]
    (priority : Descriptor → Nat) (descriptor : Descriptor) :
    priority descriptor + 2 < twoSortedFamilyNeutral priority := by
  classical
  have hle : priority descriptor ≤ Finset.univ.sup priority :=
    Finset.le_sup (Finset.mem_univ descriptor)
  simp only [twoSortedFamilyNeutral]
  omega

/-- Priority stream of an alternating family/chosen run. -/
noncomputable def twoSortedFamilyPrioritySequence
    {Descriptor : Type u} [Fintype Descriptor]
    (priority : Descriptor → Nat) (chosen : Nat → Descriptor) : Nat → Nat :=
  fun k => if k % 2 = 0 then twoSortedFamilyNeutral priority
    else priority (chosen (k / 2)) + 2

theorem seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
    {Descriptor : Type u} [Fintype Descriptor]
    (priority : Descriptor → Nat) (chosen : Nat → Descriptor) (q : Nat) :
    NatSeqSeenInfinitelyOften
        (twoSortedFamilyPrioritySequence priority chosen) q ↔
      q = twoSortedFamilyNeutral priority ∨
        NatSeqSeenInfinitelyOften (fun n => priority (chosen n) + 2) q := by
  constructor
  · intro hseen
    by_cases hneutral : q = twoSortedFamilyNeutral priority
    · exact Or.inl hneutral
    · right
      intro n
      obtain ⟨k, hk, hq⟩ := hseen (2 * n + 1)
      have hodd : k % 2 = 1 := by
        rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
        · simp [twoSortedFamilyPrioritySequence, heven] at hq
          exact absurd hq.symm hneutral
        · exact hodd
      refine ⟨k / 2, by omega, ?_⟩
      simpa [twoSortedFamilyPrioritySequence, hodd] using hq
  · rintro (rfl | hseen)
    · intro n
      refine ⟨2 * n, by omega, ?_⟩
      simp [twoSortedFamilyPrioritySequence]
    · intro n
      obtain ⟨k, hk, hq⟩ := hseen n
      refine ⟨2 * k + 1, by omega, ?_⟩
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simpa [twoSortedFamilyPrioritySequence, hdiv] using hq

/-- Inserting the high neutral family priority between candidate priorities
does not change min-even parity.  The candidate priorities are shifted by the
even constant two, so the result is equivalent to the original descriptor
priority stream. -/
theorem twoSortedFamilyPrioritySequence_minEven_iff
    {Descriptor : Type u} [Fintype Descriptor]
    (priority : Descriptor → Nat) (chosen : Nat → Descriptor) :
    NatSeqMinEvenParity
        (twoSortedFamilyPrioritySequence priority chosen) ↔
      NatSeqMinEvenParity (fun n => priority (chosen n)) := by
  let shifted : Nat → Nat := fun n => priority (chosen n) + 2
  let neutral := twoSortedFamilyNeutral priority
  have hlt : ∀ n, shifted n < neutral := fun n =>
    twoSortedFamilyPriority_lt_neutral priority (chosen n)
  have hfinite : (Set.range shifted).Finite := by
    refine (Set.finite_range (fun descriptor : Descriptor =>
      priority descriptor + 2)).subset ?_
    rintro value ⟨n, rfl⟩
    exact ⟨chosen n, rfl⟩
  constructor
  · intro hfamily
    obtain ⟨candidate, hcandidateSeen, hcandidateMin⟩ :=
      natSeq_exists_min_recurring shifted hfinite
    have hcandidateFamily : NatSeqSeenInfinitelyOften
        (twoSortedFamilyPrioritySequence priority chosen) candidate :=
      (seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
        priority chosen candidate).mpr (Or.inr hcandidateSeen)
    rcases hfamily with ⟨p, hpEven, hpSeen, hpMin⟩
    have hpNotNeutral : p ≠ neutral := by
      intro hp
      subst p
      obtain ⟨n, _, hn⟩ := hcandidateSeen 0
      have hcandidateLt : candidate < neutral := by
        rw [← hn]
        exact hlt n
      have hneutralLe : neutral ≤ candidate :=
        hpMin candidate hcandidateFamily
      omega
    have hpShifted : NatSeqSeenInfinitelyOften shifted p :=
      ((seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
        priority chosen p).mp hpSeen).resolve_left hpNotNeutral
    have hshifted : NatSeqMinEvenParity shifted :=
      ⟨p, hpEven, hpShifted, fun q hq =>
        hpMin q ((seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
          priority chosen q).mpr (Or.inr hq))⟩
    exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hshifted
  · intro horiginal
    have hshifted : NatSeqMinEvenParity shifted :=
      (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr horiginal
    rcases hshifted with ⟨p, hpEven, hpSeen, hpMin⟩
    obtain ⟨n, _, hpn⟩ := hpSeen 0
    have hpLt : p < neutral := by
      rw [← hpn]
      exact hlt n
    refine ⟨p, hpEven,
      (seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
        priority chosen p).mpr (Or.inr hpSeen), ?_⟩
    intro q hq
    rcases (seenInfinitelyOften_twoSortedFamilyPrioritySequence_iff
      priority chosen q).mp hq with rfl | hqShifted
    · exact Nat.le_of_lt hpLt
    · exact hpMin q hqShifted

/-- The generic two-sorted input-free run automaton.  `Allowed roots next` is
the sole model-specific transition law. -/
noncomputable def twoSortedFamilyRunAutomaton
    {Descriptor : Type u} {Branch : Type v}
    [Fintype Descriptor]
    (priority : Descriptor → Nat)
    (initialRoots : Finset Descriptor)
    (Allowed : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch → Prop) :
    InputFreeRunParityTreeAutomaton.{v, u} Branch := by
  classical
  exact {
    State := TwoSortedFamilyState Descriptor
    stateFinite := inferInstance
    initial := .family initialRoots
    delta := fun state _ children =>
      match state with
      | .family roots =>
          ∃ next, Allowed roots next ∧
            ∀ branch, children branch =
              .chosen (next branch).1 (next branch).2
      | .chosen _ nextRoots =>
          ∀ branch, children branch = .family nextRoots
    priority := fun state =>
      match state with
      | .family _ => twoSortedFamilyNeutral priority
      | .chosen actual _ => priority actual + 2
  }

namespace TwoSortedFamilyPolicy

variable {Descriptor : Type u} {Branch : Type v}
variable [Fintype Descriptor]
variable (priority : Descriptor → Nat)
variable (initialRoots : Finset Descriptor)
variable (Allowed : Finset Descriptor →
  TwoSortedFamilySuccessor Descriptor Branch → Prop)

noncomputable abbrev Automaton :=
  twoSortedFamilyRunAutomaton priority initialRoots Allowed

/-- A family state occurring in a rational run. -/
def Reachable
    (policy : (Automaton priority initialRoots Allowed).RationalTransitionPolicy)
    (roots : Finset Descriptor) : Prop :=
  ∃ node, policy.run node = .family roots

/-- At a reachable family state, one complete successor assignment is chosen
for the entire hidden family.  There is no distinguished-anchor parameter in
the statement or in the selected assignment. -/
theorem exists_shared_family_transition
    (policy : (Automaton priority initialRoots Allowed).RationalTransitionPolicy)
    (roots : Finset Descriptor)
    (hreachable : Reachable priority initialRoots Allowed policy roots) :
    ∃ next : TwoSortedFamilySuccessor Descriptor Branch,
      Allowed roots next ∧
      ∀ branch, policy.successor (.family roots) branch =
        .chosen (next branch).1 (next branch).2 := by
  obtain ⟨node, hnode⟩ := hreachable
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  simpa [Automaton, twoSortedFamilyRunAutomaton] using hlegal

/-- Chosen states have no strategy choice: every direction returns to the
recorded next family. -/
theorem successor_chosen_eq_family
    (policy : (Automaton priority initialRoots Allowed).RationalTransitionPolicy)
    (actual : Descriptor) (roots : Finset Descriptor)
    (hreachable : ∃ node, policy.run node = .chosen actual roots) :
    ∀ branch, policy.successor (.chosen actual roots) branch = .family roots := by
  obtain ⟨node, hnode⟩ := hreachable
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  simpa [Automaton, twoSortedFamilyRunAutomaton] using hlegal

/-! ## Building the accepting run before rationalization -/

/-- The deterministic unfolding of a complete family successor assignment.
The second step is forced and, in particular, cannot inspect its direction. -/
def stateStep
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    TwoSortedFamilyState Descriptor → Branch →
      TwoSortedFamilyState Descriptor
  | .family roots, branch =>
      .chosen (next roots branch).1 (next roots branch).2
  | .chosen _ roots, _ => .family roots

/-- Raw family run generated by the complete assignment `next`. -/
def deterministicRun
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    TreeNode Branch → TwoSortedFamilyState Descriptor :=
  fun node => node.foldl (stateStep next) (.family initialRoots)

section
omit [Fintype Descriptor]

@[simp] theorem deterministicRun_nil
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    deterministicRun initialRoots next [] = .family initialRoots := by
  rfl

theorem deterministicRun_append
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (node : TreeNode Branch) (branch : Branch) :
    deterministicRun initialRoots next (node ++ [branch]) =
      stateStep next (deterministicRun initialRoots next node) branch := by
  simp [deterministicRun, List.foldl_append]

/-- Even levels of the deterministic unfolding are family states and odd
levels are chosen states.  This is a proof invariant only; it supplies no
orientation or leader flag to a process. -/
theorem deterministicRun_shape
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) : ∀ k,
      (k % 2 = 0 → ∃ roots,
        deterministicRun initialRoots next (branchNode branch k) =
          .family roots) ∧
      (k % 2 = 1 → ∃ actual roots,
        deterministicRun initialRoots next (branchNode branch k) =
          .chosen actual roots) := by
  intro k
  induction k with
  | zero =>
      constructor
      · intro _
        exact ⟨initialRoots, rfl⟩
      · omega
  | succ k ih =>
      constructor
      · intro heven
        have hodd : k % 2 = 1 := by omega
        obtain ⟨actual, roots, hstate⟩ := ih.2 hodd
        refine ⟨roots, ?_⟩
        rw [branchNode, deterministicRun_append, hstate]
        rfl
      · intro hodd
        have heven : k % 2 = 0 := by omega
        obtain ⟨roots, hstate⟩ := ih.1 heven
        refine ⟨(next roots (branch k)).1,
          (next roots (branch k)).2, ?_⟩
        rw [branchNode, deterministicRun_append, hstate]
        rfl

end

/-- Objective descriptor selected at the `n`-th family transition along a
branch. -/
noncomputable def selectedDescriptor
    [Inhabited Descriptor]
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) (n : Nat) : Descriptor :=
  match deterministicRun initialRoots next (branchNode branch (2 * n + 1)) with
  | .chosen actual _ => actual
  | .family _ => default

theorem deterministicRun_priority_eq
    [Inhabited Descriptor]
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) : ∀ k,
    (twoSortedFamilyRunAutomaton priority initialRoots Allowed).priority
        (deterministicRun initialRoots next (branchNode branch k)) =
      twoSortedFamilyPrioritySequence priority
        (selectedDescriptor initialRoots next branch) k := by
  intro k
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · obtain ⟨roots, hstate⟩ :=
      (deterministicRun_shape initialRoots next branch k).1 heven
    rw [hstate]
    simp [twoSortedFamilyRunAutomaton,
      twoSortedFamilyPrioritySequence, heven]
  · obtain ⟨actual, roots, hstate⟩ :=
      (deterministicRun_shape initialRoots next branch k).2 hodd
    have hk : 2 * (k / 2) + 1 = k := by omega
    have hselected : selectedDescriptor initialRoots next branch (k / 2) =
        actual := by
      simp only [selectedDescriptor]
      rw [hk, hstate]
    rw [hstate]
    simp [twoSortedFamilyRunAutomaton,
      twoSortedFamilyPrioritySequence, hodd, hselected]

/-- A total allowed family assignment whose selected descriptors satisfy the
old epoch parity supplies an accepting run of the two-sorted automaton. -/
theorem deterministicRun_isAccepting
    [Inhabited Descriptor]
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (hallowed : ∀ roots, Allowed roots (next roots))
    (hparity : ∀ branch : Nat → Branch,
      NatSeqMinEvenParity (fun n =>
        priority (selectedDescriptor initialRoots next branch n))) :
    (Automaton priority initialRoots Allowed).IsAcceptingRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (deterministicRun initialRoots next) := by
  constructor
  · constructor
    · rfl
    · intro node
      change (twoSortedFamilyRunAutomaton priority initialRoots Allowed).delta
        (deterministicRun initialRoots next node) PUnit.unit
        (fun branch => deterministicRun initialRoots next (node ++ [branch]))
      cases hstate : deterministicRun initialRoots next node with
      | family roots =>
          refine ⟨next roots, hallowed roots, ?_⟩
          intro branch
          change deterministicRun initialRoots next (node ++ [branch]) = _
          rw [deterministicRun_append, hstate]
          rfl
      | chosen actual roots =>
          intro branch
          change deterministicRun initialRoots next (node ++ [branch]) = _
          rw [deterministicRun_append, hstate]
          rfl
  · intro branch
    rw [show (fun n =>
        (twoSortedFamilyRunAutomaton priority initialRoots Allowed).priority
          (deterministicRun initialRoots next (branchNode branch n))) =
        twoSortedFamilyPrioritySequence priority
          (selectedDescriptor initialRoots next branch) by
      funext n
      exact deterministicRun_priority_eq priority initialRoots Allowed next
        branch n]
    exact (twoSortedFamilyPrioritySequence_minEven_iff priority
      (selectedDescriptor initialRoots next branch)).mpr (hparity branch)

/-- The recursive family construction has no additional fixed-point
obstruction: after the model supplies one total allowed assignment and its
ordinary epoch-parity proof, the classical input-free rational-run theorem
returns a finite transition policy whose family moves are shared. -/
theorem nonempty_rationalPolicy_of_assignment
    [Inhabited Descriptor]
    (next : Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (hallowed : ∀ roots, Allowed roots (next roots))
    (hparity : ∀ branch : Nat → Branch,
      NatSeqMinEvenParity (fun n =>
        priority (selectedDescriptor initialRoots next branch n)))
    (basis : (Automaton priority initialRoots Allowed).RationalRunBasis) :
    Nonempty ((Automaton priority initialRoots Allowed).RationalTransitionPolicy) := by
  apply InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
    (Automaton priority initialRoots Allowed)
  apply basis
  exact ⟨deterministicRun initialRoots next,
    deterministicRun_isAccepting priority initialRoots Allowed next hallowed
      hparity⟩

/-! ## History-dependent raw runs

The preceding assignment theorem is useful when the semantic construction is
already state based.  It is deliberately not the general rationalization
step.  A raw distributed strategy may choose different complete family
transitions at two histories carrying the same finite root family.  The
following construction retains that history until `RationalRunBasis` is
applied.
-/

/-- Accumulating fold used by the genuinely history-dependent raw run. -/
def historyRunFold
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    TreeNode Branch × TwoSortedFamilyState Descriptor → Branch →
      TreeNode Branch × TwoSortedFamilyState Descriptor :=
  fun current branch =>
    (current.1 ++ [branch],
      stateStep (nextAt current.1) current.2 branch)

/-- Raw run whose family transition may depend on the complete proof
history.  This history is not a local control and disappears only after the
input-free rational-run theorem. -/
def historyRun
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    TreeNode Branch → TwoSortedFamilyState Descriptor :=
  fun node =>
    (node.foldl (historyRunFold nextAt) ([], .family initialRoots)).2

section
omit [Fintype Descriptor]

theorem historyRunFold_prefix
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (stem node : TreeNode Branch)
    (state : TwoSortedFamilyState Descriptor) :
    (node.foldl (historyRunFold nextAt) (stem, state)).1 =
      stem ++ node := by
  induction node generalizing stem state with
  | nil => simp
  | cons branch node ih =>
      simp only [List.foldl_cons, historyRunFold]
      rw [ih]
      simp [List.append_assoc]

@[simp] theorem historyRun_nil
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch) :
    historyRun initialRoots nextAt [] = .family initialRoots := by
  rfl

theorem historyRun_append
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (node : TreeNode Branch) (branch : Branch) :
    historyRun initialRoots nextAt (node ++ [branch]) =
      stateStep (nextAt node) (historyRun initialRoots nextAt node) branch := by
  simp only [historyRun, List.foldl_append, List.foldl_cons, List.foldl_nil,
    historyRunFold]
  rw [historyRunFold_prefix nextAt [] node (.family initialRoots)]
  rfl

end

omit [Fintype Descriptor] in
theorem historyRun_shape
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) : ∀ k,
      (k % 2 = 0 → ∃ roots,
        historyRun initialRoots nextAt (branchNode branch k) =
          .family roots) ∧
      (k % 2 = 1 → ∃ actual roots,
        historyRun initialRoots nextAt (branchNode branch k) =
          .chosen actual roots) := by
  intro k
  induction k with
  | zero =>
      constructor
      · intro _
        exact ⟨initialRoots, rfl⟩
      · omega
  | succ k ih =>
      constructor
      · intro heven
        have hodd : k % 2 = 1 := by omega
        obtain ⟨actual, roots, hstate⟩ := ih.2 hodd
        refine ⟨roots, ?_⟩
        rw [branchNode, historyRun_append, hstate]
        rfl
      · intro hodd
        have heven : k % 2 = 0 := by omega
        obtain ⟨roots, hstate⟩ := ih.1 heven
        let assignment := nextAt (branchNode branch k) roots
        refine ⟨(assignment (branch k)).1,
          (assignment (branch k)).2, ?_⟩
        rw [branchNode, historyRun_append, hstate]
        rfl

/-- Descriptor selected at the `n`-th family transition of a raw
history-dependent run. -/
noncomputable def historySelectedDescriptor
    [Inhabited Descriptor]
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) (n : Nat) : Descriptor :=
  match historyRun initialRoots nextAt (branchNode branch (2 * n + 1)) with
  | .chosen actual _ => actual
  | .family _ => default

theorem historyRun_priority_eq
    [Inhabited Descriptor]
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (branch : Nat → Branch) : ∀ k,
    (twoSortedFamilyRunAutomaton priority initialRoots Allowed).priority
        (historyRun initialRoots nextAt (branchNode branch k)) =
      twoSortedFamilyPrioritySequence priority
        (historySelectedDescriptor initialRoots nextAt branch) k := by
  intro k
  rcases Nat.mod_two_eq_zero_or_one k with heven | hodd
  · obtain ⟨roots, hstate⟩ :=
      (historyRun_shape initialRoots nextAt branch k).1 heven
    rw [hstate]
    simp [twoSortedFamilyRunAutomaton,
      twoSortedFamilyPrioritySequence, heven]
  · obtain ⟨actual, roots, hstate⟩ :=
      (historyRun_shape initialRoots nextAt branch k).2 hodd
    have hk : 2 * (k / 2) + 1 = k := by omega
    have hselected :
        historySelectedDescriptor initialRoots nextAt branch (k / 2) =
          actual := by
      simp only [historySelectedDescriptor]
      rw [hk, hstate]
    rw [hstate]
    simp [twoSortedFamilyRunAutomaton,
      twoSortedFamilyPrioritySequence, hodd, hselected]

/-- Legality and ordinary descriptor parity make the history-dependent raw
family tree an accepting run. -/
theorem historyRun_isAccepting
    [Inhabited Descriptor]
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (hallowed : ∀ node roots,
      historyRun initialRoots nextAt node = .family roots →
        Allowed roots (nextAt node roots))
    (hparity : ∀ branch : Nat → Branch,
      NatSeqMinEvenParity (fun n =>
        priority (historySelectedDescriptor initialRoots nextAt branch n))) :
    (Automaton priority initialRoots Allowed).IsAcceptingRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (historyRun initialRoots nextAt) := by
  constructor
  · constructor
    · rfl
    · intro node
      change (twoSortedFamilyRunAutomaton priority initialRoots Allowed).delta
        (historyRun initialRoots nextAt node) PUnit.unit
        (fun branch => historyRun initialRoots nextAt (node ++ [branch]))
      cases hstate : historyRun initialRoots nextAt node with
      | family roots =>
          refine ⟨nextAt node roots, hallowed node roots hstate, ?_⟩
          intro branch
          change historyRun initialRoots nextAt (node ++ [branch]) = _
          rw [historyRun_append, hstate]
          rfl
      | chosen actual roots =>
          intro branch
          change historyRun initialRoots nextAt (node ++ [branch]) = _
          rw [historyRun_append, hstate]
          rfl
  · intro branch
    rw [show (fun n =>
        (twoSortedFamilyRunAutomaton priority initialRoots Allowed).priority
          (historyRun initialRoots nextAt (branchNode branch n))) =
        twoSortedFamilyPrioritySequence priority
          (historySelectedDescriptor initialRoots nextAt branch) by
      funext n
      exact historyRun_priority_eq priority initialRoots Allowed nextAt branch n]
    exact (twoSortedFamilyPrioritySequence_minEven_iff priority
      (historySelectedDescriptor initialRoots nextAt branch)).mpr
        (hparity branch)

/-- Correct general recursion theorem.  The semantic family transition may
depend on the whole raw history; the rational-run basis, and only that basis,
turns it into a finite state-controlled shared policy. -/
theorem nonempty_rationalPolicy_of_historyAssignment
    [Inhabited Descriptor]
    (nextAt : TreeNode Branch → Finset Descriptor →
      TwoSortedFamilySuccessor Descriptor Branch)
    (hallowed : ∀ node roots,
      historyRun initialRoots nextAt node = .family roots →
        Allowed roots (nextAt node roots))
    (hparity : ∀ branch : Nat → Branch,
      NatSeqMinEvenParity (fun n =>
        priority (historySelectedDescriptor initialRoots nextAt branch n)))
    (basis : (Automaton priority initialRoots Allowed).RationalRunBasis) :
    Nonempty ((Automaton priority initialRoots Allowed).RationalTransitionPolicy) := by
  apply InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
    (Automaton priority initialRoots Allowed)
  apply basis
  exact ⟨historyRun initialRoots nextAt,
    historyRun_isAccepting priority initialRoots Allowed nextAt hallowed
      hparity⟩

end TwoSortedFamilyPolicy

end DistributedSynthesis
