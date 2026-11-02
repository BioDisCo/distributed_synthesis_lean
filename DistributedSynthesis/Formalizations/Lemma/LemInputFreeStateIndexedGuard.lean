/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemInputFreeRootForest

/-!
# Finite state-indexed one-shot guards

Different exits of the initial homogeneous phase carry different finite
overlap obligations.  Those obligations cannot be installed as different
automata and rationalized independently.  Instead, this construction stores
the obligation in the finite state reached below one common outer root.  It is
checked on that state's next transition and then erased permanently.

The guard is proof-side automaton state.  It is not an observation, a leader
signal, or a branch label available to either distributed process.
-/

namespace DistributedSynthesis

universe u w z

namespace InputFreeRunParityTreeAutomaton

variable {Branch : Type u} {Guard : Type z}

/-- A pending finite guard paired with the underlying parity state. -/
abbrev StateIndexedGuardState
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    (Guard : Type z) :=
  Option Guard × A.State

/-- Check a state-indexed guard once, then run the underlying automaton.  The
initial `none` is useful when the construction is used alone; an outer forest
root may override it with any `(some guard, state)` pair. -/
def stateIndexedGuarded
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop) :
    InputFreeRunParityTreeAutomaton.{u, max w z} Branch where
  State := StateIndexedGuardState A Guard
  stateFinite := inferInstance
  initial := (none, A.initial)
  delta state _ children :=
    match state.1 with
    | some guard =>
        ∃ next : Branch → A.State,
          Allowed guard state.2 next ∧
            children = fun branch => (none, next branch)
    | none =>
        ∃ next : Branch → A.State,
          A.delta state.2 PUnit.unit next ∧
            children = fun branch => (none, next branch)
  priority state := A.priority state.2

/-- Lift one underlying run with a pending guard at precisely its root. -/
def stateIndexedGuardedRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (guard : Guard) (run : TreeNode Branch → A.State) :
    TreeNode Branch → (A.stateIndexedGuarded Allowed).State
  | [] => (some guard, run [])
  | first :: rest => (none, run (first :: rest))

@[simp] theorem stateIndexedGuardedRun_nil
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (guard : Guard) (run : TreeNode Branch → A.State) :
    stateIndexedGuardedRun A Allowed guard run [] =
      (some guard, run []) :=
  rfl

@[simp] theorem stateIndexedGuardedRun_cons
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (guard : Guard) (run : TreeNode Branch → A.State)
    (first : Branch) (rest : TreeNode Branch) :
    stateIndexedGuardedRun A Allowed guard run (first :: rest) =
      (none, run (first :: rest)) :=
  rfl

@[simp] theorem stateIndexedGuardedRun_snd
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (guard : Guard) (run : TreeNode Branch → A.State)
    (node : TreeNode Branch) :
    (stateIndexedGuardedRun A Allowed guard run node).2 = run node := by
  cases node <;> rfl

/-- An accepting underlying run with the requested first-transition guard
lifts to the finite state-indexed extension. -/
theorem stateIndexedGuarded_isAcceptingRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (guard : Guard) (run : TreeNode Branch → A.State)
    (hrun : (A.withInitial (run [])).IsAcceptingRun uniqueTree run)
    (hguard : Allowed guard (run []) (fun branch => run [branch])) :
    ((A.stateIndexedGuarded Allowed).withInitial (some guard, run [])).IsAcceptingRun uniqueTree
        (stateIndexedGuardedRun A Allowed guard run) := by
  have hisRun :
      ((A.stateIndexedGuarded Allowed).withInitial (some guard, run [])).IsRun
        uniqueTree (stateIndexedGuardedRun A Allowed guard run) := by
    refine ⟨rfl, ?_⟩
    intro node
    cases node with
    | nil =>
        change ∃ next, Allowed guard (run []) next ∧
          (fun branch => stateIndexedGuardedRun A Allowed guard run [branch]) =
            fun branch => (none, next branch)
        exact ⟨fun branch => run [branch], hguard, by
          funext branch
          rfl⟩
    | cons first rest =>
        change ∃ next,
          A.delta (run (first :: rest)) PUnit.unit next ∧
            (fun branch => stateIndexedGuardedRun A Allowed guard run
              ((first :: rest) ++ [branch])) =
              fun branch => (none, next branch)
        refine ⟨fun branch => run ((first :: rest) ++ [branch]),
          ?_, ?_⟩
        · simpa only [withInitial, uniqueTree] using
            hrun.1.2 (first :: rest)
        funext branch
        rfl
  refine ⟨hisRun, ?_⟩
  intro branch
  have heq :
      (fun n => (A.stateIndexedGuarded Allowed).priority
        (stateIndexedGuardedRun A Allowed guard run
          (branchNode branch n))) =
        fun n => A.priority (run (branchNode branch n)) := by
    funext n
    change A.priority
      (stateIndexedGuardedRun A Allowed guard run
        (branchNode branch n)).2 = _
    rw [stateIndexedGuardedRun_snd]
  change NatSeqMinEvenParity (fun n =>
    (A.stateIndexedGuarded Allowed).priority
      (stateIndexedGuardedRun A Allowed guard run (branchNode branch n)))
  rw [heq]
  simpa only [withInitial] using hrun.2 branch

/-- Glue every state-indexed guarded recurrent run below one fresh root and
invoke the classical rational-run basis exactly once on the composite finite
automaton. -/
theorem rootStateIndexedGuardedForest_hasRationalRun
    (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
    [Fintype Guard]
    (Allowed : Guard → A.State → (Branch → A.State) → Prop)
    (OuterAllowed :
      (Branch → (A.stateIndexedGuarded Allowed).State) → Prop)
    (guard : Branch → Guard)
    (forest : Branch → TreeNode Branch → A.State)
    (hforest : ∀ branch,
      (A.withInitial (forest branch [])).IsAcceptingRun uniqueTree
        (forest branch))
    (hguard : ∀ branch,
      Allowed (guard branch) (forest branch [])
        (fun next => forest branch [next]))
    (houter : OuterAllowed
      (fun branch => (some (guard branch), forest branch [])))
    (basis :
      ((A.stateIndexedGuarded Allowed).rootGuarded OuterAllowed).RationalRunBasis) :
    ((A.stateIndexedGuarded Allowed).rootGuarded OuterAllowed).HasRationalRun := by
  apply rootGuardedForest_hasRationalRun
    (A.stateIndexedGuarded Allowed) OuterAllowed
    (fun branch => (some (guard branch), forest branch []))
    (fun branch => stateIndexedGuardedRun A Allowed (guard branch)
      (forest branch))
  · intro branch
    rfl
  · intro branch
    exact stateIndexedGuarded_isAcceptingRun A Allowed (guard branch)
      (forest branch) (hforest branch) (hguard branch)
  · exact houter
  · exact basis

/-! ## Activating a rational policy below the indexed guard -/

section PolicyActivation

variable
  (A : InputFreeRunParityTreeAutomaton.{u, w} Branch)
  [Fintype Guard]
  (Allowed : Guard → A.State → (Branch → A.State) → Prop)
  (initial : (A.stateIndexedGuarded Allowed).State)
  (policy : ((A.stateIndexedGuarded Allowed).withInitial initial).RationalTransitionPolicy)
  (guard : Guard)

/-- The indexed transition at the policy root exposes the promised guarded
underlying successor assignment. -/
theorem exists_allowed_at_stateIndexedGuard_root
    (hpending : (policy.run []).1 = some guard) :
    ∃ next : Branch → A.State,
      Allowed guard (policy.run []).2 next ∧
        ∀ branch, policy.run [branch] = (none, next branch) := by
  have hstate : policy.run [] = (some guard, (policy.run []).2) := by
    apply Prod.ext
    · exact hpending
    · rfl
  have hlegal := policy.legal_at []
  rw [hstate] at hlegal
  change ∃ next : Branch → A.State,
    Allowed guard (policy.run []).2 next ∧
      policy.successor (some guard, (policy.run []).2) =
        fun branch => (none, next branch) at hlegal
  rcases hlegal with ⟨next, hallowed, hchildren⟩
  refine ⟨next, hallowed, ?_⟩
  intro branch
  have hchild := policy.successor_at [] branch
  rw [hstate, hchildren] at hchild
  simpa using hchild.symm

/-- Every node strictly below the indexed root has consumed its pending
guard. -/
theorem stateIndexedGuardedPolicy_pending_none
    (hpending : (policy.run []).1 = some guard)
    (first : Branch) (node : TreeNode Branch) :
    (policy.run ([first] ++ node)).1 = none := by
  obtain ⟨next, _, hchildren⟩ :=
    exists_allowed_at_stateIndexedGuard_root A Allowed initial policy guard
      hpending
  induction node using List.reverseRecOn with
  | nil => simpa using congrArg Prod.fst (hchildren first)
  | @append_singleton node branch ih =>
      have hstate : policy.run ([first] ++ node) =
          (none, (policy.run ([first] ++ node)).2) := by
        apply Prod.ext
        · simpa using ih
        · rfl
      have hlegal := policy.legal_at ([first] ++ node)
      rw [hstate] at hlegal
      change ∃ next : Branch → A.State,
        A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
          policy.successor (none, (policy.run ([first] ++ node)).2) =
            fun direction => (none, next direction) at hlegal
      rcases hlegal with ⟨next, _, hnext⟩
      have hchild := policy.successor_at ([first] ++ node) branch
      rw [hstate, hnext] at hchild
      simpa [List.append_assoc] using congrArg Prod.fst hchild.symm

/-- After the guarded first transition, project to an ordinary rational
policy of the underlying automaton. -/
noncomputable def ordinaryPolicyBelowStateIndexedGuard
    (hpending : (policy.run []).1 = some guard)
    (first : Branch) :
    (A.withInitial (policy.run [first]).2).RationalTransitionPolicy where
  run := fun node => (policy.run ([first] ++ node)).2
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        have hnone := stateIndexedGuardedPolicy_pending_none
          A Allowed initial policy guard hpending first node
        have hstate : policy.run ([first] ++ node) =
            (none, (policy.run ([first] ++ node)).2) := by
          apply Prod.ext
          · simpa using hnone
          · rfl
        have hlegal := policy.legal_at ([first] ++ node)
        rw [hstate] at hlegal
        change ∃ next : Branch → A.State,
          A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
            policy.successor (none, (policy.run ([first] ++ node)).2) =
              fun direction => (none, next direction) at hlegal
        rcases hlegal with ⟨next, hdelta, hchildren⟩
        have hrunChildren :
            (fun branch =>
              (policy.run ([first] ++ (node ++ [branch]))).2) = next := by
          funext branch
          have hchild := policy.successor_at ([first] ++ node) branch
          rw [hstate, hchildren] at hchild
          simpa [List.append_assoc] using congrArg Prod.snd hchild.symm
        rw [← hrunChildren] at hdelta
        simpa only [withInitial, uniqueTree] using hdelta
    · intro tail
      have hparity := policy.accepts.2 (prefixedBranch first tail)
      have hshift := (natSeqMinEvenParity_shift
        (fun n => ((A.stateIndexedGuarded Allowed).withInitial initial).priority
          (policy.run (branchNode (prefixedBranch first tail) n))) 1).mpr
            hparity
      simpa [withInitial, stateIndexedGuarded,
        branchNode_prefixedBranch, Nat.add_comm] using hshift
  successor := fun state branch =>
    (policy.successor (none, state) branch).2
  successor_at := by
    intro node branch
    have hnone := stateIndexedGuardedPolicy_pending_none
      A Allowed initial policy guard hpending first node
    have hstate : policy.run ([first] ++ node) =
        (none, (policy.run ([first] ++ node)).2) := by
      apply Prod.ext
      · simpa using hnone
      · rfl
    have hchild := congrArg Prod.snd
      (policy.successor_at ([first] ++ node) branch)
    rw [hstate] at hchild
    simpa [List.append_assoc] using hchild
  legal_at := by
    intro node
    have hnone := stateIndexedGuardedPolicy_pending_none
      A Allowed initial policy guard hpending first node
    have hstate : policy.run ([first] ++ node) =
        (none, (policy.run ([first] ++ node)).2) := by
      apply Prod.ext
      · simpa using hnone
      · rfl
    have hlegal := policy.legal_at ([first] ++ node)
    rw [hstate] at hlegal
    change ∃ next : Branch → A.State,
      A.delta (policy.run ([first] ++ node)).2 PUnit.unit next ∧
        policy.successor (none, (policy.run ([first] ++ node)).2) =
          fun direction => (none, next direction) at hlegal
    rcases hlegal with ⟨next, hdelta, hchildren⟩
    have hnext :
        (fun branch =>
          (policy.successor
            (none, (policy.run ([first] ++ node)).2) branch).2) = next := by
      funext branch
      simpa using congrArg (fun children => (children branch).2) hchildren
    rw [hnext]
    simpa only [withInitial] using hdelta

/-- Retain the one-shot bit and reinterpret a fixed state-indexed guard as an
ordinary `rootGuarded` policy.  Unlike projection to the base state, this
adapter is sound even when the underlying root state occurs again later: the
fresh bit distinguishes the guarded occurrence from all ordinary ones. -/
noncomputable def rootGuardedPolicyOfStateIndexedGuard
    (hpending : (policy.run []).1 = some guard) :
    (((A.withInitial initial.2).rootGuarded
      (Allowed guard initial.2))).RationalTransitionPolicy where
  run := fun node =>
    (match node with | [] => true | _ :: _ => false, (policy.run node).2)
  accepts := by
    constructor
    · constructor
      · have hroot := policy.accepts.1.1
        apply Prod.ext
        · rfl
        · simpa [withInitial, rootGuarded] using congrArg Prod.snd hroot
      · intro node
        cases node with
        | nil =>
            have hroot := policy.accepts.1.1
            have hstate : policy.run [] = (some guard, initial.2) := by
              apply Prod.ext
              · exact hpending
              · simpa using congrArg Prod.snd hroot
            have hlegal := policy.accepts.1.2 ([] : TreeNode Branch)
            rw [hstate] at hlegal
            change ∃ next : Branch → A.State,
              Allowed guard initial.2 next ∧
                (fun branch => policy.run [branch]) =
                  fun branch => (none, next branch) at hlegal
            rcases hlegal with ⟨next, hallowed, hchildren⟩
            simp only [withInitial, rootGuarded, uniqueTree, List.nil_append,
              if_true]
            refine ⟨next, hallowed, ?_⟩
            funext branch
            exact congrArg (fun child => (false, child.2))
              (congrFun hchildren branch)
        | cons first rest =>
            have hnone := stateIndexedGuardedPolicy_pending_none
              A Allowed initial policy guard hpending first rest
            have hstate : policy.run (first :: rest) =
                (none, (policy.run (first :: rest)).2) := by
              apply Prod.ext
              · simpa using hnone
              · rfl
            have hlegal := policy.accepts.1.2 (first :: rest)
            rw [hstate] at hlegal
            change ∃ next : Branch → A.State,
              A.delta (policy.run (first :: rest)).2 PUnit.unit next ∧
                (fun branch => policy.run ((first :: rest) ++ [branch])) =
                  fun branch => (none, next branch) at hlegal
            rcases hlegal with ⟨next, hdelta, hchildren⟩
            simp only [withInitial, rootGuarded, uniqueTree, if_false]
            refine ⟨next, hdelta, ?_⟩
            funext branch
            exact congrArg (fun child => (false, child.2))
              (congrFun hchildren branch)
    · intro branch
      simpa [withInitial, rootGuarded] using policy.accepts.2 branch
  successor := fun state branch =>
    if state.1 then
      (false, (policy.successor (some guard, state.2) branch).2)
    else
      (false, (policy.successor (none, state.2) branch).2)
  successor_at := by
    intro node branch
    cases node with
    | nil =>
        have hroot := policy.accepts.1.1
        have hstate : policy.run [] = (some guard, initial.2) := by
          apply Prod.ext
          · exact hpending
          · simpa using congrArg Prod.snd hroot
        have hchild := policy.successor_at ([] : TreeNode Branch) branch
        rw [hstate] at hchild
        simp only [List.nil_append, if_true]
        have hsnd : (policy.run []).2 = initial.2 := by
          simpa using congrArg (fun p => p.2) hstate
        rw [hsnd]
        apply Prod.ext
        · rfl
        · simpa using congrArg Prod.snd hchild
    | cons first rest =>
        have hnone := stateIndexedGuardedPolicy_pending_none
          A Allowed initial policy guard hpending first rest
        have hstate : policy.run (first :: rest) =
            (none, (policy.run (first :: rest)).2) := by
          apply Prod.ext
          · simpa using hnone
          · rfl
        have hchild := policy.successor_at (first :: rest) branch
        rw [hstate] at hchild
        simp only [if_false]
        exact congrArg (fun child => (false, child.2)) hchild
  legal_at := by
    intro node
    cases node with
    | nil =>
        have hroot := policy.accepts.1.1
        have hstate : policy.run [] = (some guard, initial.2) := by
          apply Prod.ext
          · exact hpending
          · simpa using congrArg Prod.snd hroot
        have hlegal := policy.legal_at ([] : TreeNode Branch)
        rw [hstate] at hlegal
        change ∃ next : Branch → A.State,
          Allowed guard initial.2 next ∧
            policy.successor (some guard, initial.2) =
              fun branch => (none, next branch) at hlegal
        rcases hlegal with ⟨next, hallowed, hchildren⟩
        simp only [withInitial, rootGuarded, if_true]
        have hsnd : (policy.run []).2 = initial.2 := by
          simpa using congrArg (fun p => p.2) hstate
        rw [hsnd]
        refine ⟨next, hallowed, ?_⟩
        funext branch
        exact congrArg (fun child => (false, child.2))
          (congrFun hchildren branch)
    | cons first rest =>
        have hnone := stateIndexedGuardedPolicy_pending_none
          A Allowed initial policy guard hpending first rest
        have hstate : policy.run (first :: rest) =
            (none, (policy.run (first :: rest)).2) := by
          apply Prod.ext
          · simpa using hnone
          · rfl
        have hlegal := policy.legal_at (first :: rest)
        rw [hstate] at hlegal
        change ∃ next : Branch → A.State,
          A.delta (policy.run (first :: rest)).2 PUnit.unit next ∧
            policy.successor (none, (policy.run (first :: rest)).2) =
              fun branch => (none, next branch) at hlegal
        rcases hlegal with ⟨next, hdelta, hchildren⟩
        simp only [if_false]
        refine ⟨next, hdelta, ?_⟩
        funext branch
        exact congrArg (fun child => (false, child.2))
          (congrFun hchildren branch)

end PolicyActivation

end InputFreeRunParityTreeAutomaton

end DistributedSynthesis
