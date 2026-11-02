/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledEndToEndFixedPolicyParity

/-!
# Observable trees with one hidden fixed-policy root thread

The public observable tree must not carry the currently selected recurrent
root, its orientation, or a strict-leader bit.  This file packages the
proof-only alternative instead.  A hidden thread retains an actual recurrent
root below one fixed rational policy.  Its only live transitions are the
alternating `Allowed` edges of that policy; every other resolution enters a
harmless even sink.

The public letter is completely parametric and is ignored by the hidden
transition.  Thus this system can be coupled to any finite public family-move
tree.  Every live run is an `AlternatingThread`, so it has parity by
`PairedProfiledRationalPolicy.accepts_of_allowed_path`.  In particular, no
selected root can influence a public move.
-/

namespace DistributedSynthesis

universe l u v x y s o m

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

open ProfiledFixedPolicyRoot

noncomputable instance : Fintype (ProfiledFixedPolicyRoot A policy) := by
  classical
  let Rep := ProfiledPolicyRightMacro A policy ⊕
    ProfiledPolicyLeftMacro A policy
  let e : ProfiledFixedPolicyRoot A policy ≃ Rep :=
    { toFun := fun root =>
        match root with
        | .right source => .inl source
        | .left source => .inr source
      invFun := fun root =>
        match root with
        | .inl source => .right source
        | .inr source => .left source
      left_inv := by intro root; cases root <;> rfl
      right_inv := by intro root; cases root <;> rfl }
  exact Fintype.ofEquiv Rep e.symm

noncomputable instance : DecidableEq (ProfiledFixedPolicyRoot A policy) :=
  Classical.decEq _

/-- A proof-only actual root, or the accepting destination of a resolution
that is not a coherent alternating edge. -/
inductive ProfiledFixedPolicyThreadState where
  | live (root : ProfiledFixedPolicyRoot A policy)
  | dead

namespace ProfiledFixedPolicyThreadState

noncomputable instance : Fintype
    (ProfiledFixedPolicyThreadState A policy) := by
  classical
  let Rep := ProfiledFixedPolicyRoot A policy ⊕ Unit
  let e : ProfiledFixedPolicyThreadState A policy ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .live root => .inl root
        | .dead => .inr ()
      invFun := fun state =>
        match state with
        | .inl root => .live root
        | .inr _ => .dead
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        cases state with
        | inl root => rfl
        | inr value => cases value; rfl }
  exact Fintype.ofEquiv Rep e.symm

/-- Hidden fixed-policy root system over an arbitrary public alphabet.
Neither the public letter nor the public controller contains the live root. -/
noncomputable def system (Letter : Type l)
    (initialRoot : ProfiledFixedPolicyRoot A policy) :
    FiniteThreadSystem Letter := by
  classical
  exact {
    State := ProfiledFixedPolicyThreadState A policy
    stateFinite := inferInstance
    initial := .live initialRoot
    Resolution := ProfiledFixedPolicyRoot A policy
    step := fun source _ target =>
      match source with
      | .dead => .dead
      | .live current =>
          if AlternatingStep A policy current target then .live target
          else .dead
    priority := fun state =>
      match state with
      | .dead => 0
      | .live root => pairedProfiledEntryPriority A (root.state A policy)
  }

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem system_step_dead (Letter : Type l)
    (initialRoot target : ProfiledFixedPolicyRoot A policy)
    (letter : Letter) :
    (system A policy Letter initialRoot).step .dead letter target = .dead :=
  rfl

@[simp] theorem system_step_live_of (Letter : Type l)
    (initialRoot current target : ProfiledFixedPolicyRoot A policy)
    (letter : Letter)
    (hstep : AlternatingStep A policy current target) :
    (system A policy Letter initialRoot).step (.live current) letter target =
      .live target := by
  simp [system, hstep]

@[simp] theorem system_step_live_dead_of (Letter : Type l)
    (initialRoot current target : ProfiledFixedPolicyRoot A policy)
    (letter : Letter)
    (hstep : ¬ AlternatingStep A policy current target) :
    (system A policy Letter initialRoot).step (.live current) letter target =
      .dead := by
  simp [system, hstep]

/-- Once an incoherent resolution enters `dead`, every later hidden state is
`dead` as well. -/
theorem isRun_dead_persists (Letter : Type l)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (word : OmegaWord Letter)
    (run : Nat → ProfiledFixedPolicyThreadState A policy)
    (hrun : (system A policy Letter initialRoot).IsRun word run)
    {n : Nat} (hdead : run n = .dead) :
    ∀ k, run (n + k) = .dead := by
  intro k
  induction k with
  | zero => simpa using hdead
  | succ k ih =>
      rcases hrun.2 (n + k) with ⟨resolution, hnext⟩
      rw [Nat.add_succ, hnext, ih]
      rfl

end

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every concrete alternating root thread is represented literally as a
live run of the letter-independent hidden system.  This is the coverage
direction needed when an operational execution supplies the actual roots. -/
theorem AlternatingThread.isRun (Letter : Type l)
    (thread : AlternatingThread A policy) (word : OmegaWord Letter) :
    (system A policy Letter (thread.root 0)).IsRun word
      (fun n => .live (thread.root n)) := by
  constructor
  · rfl
  · intro n
    exact ⟨thread.root (n + 1), by
      rw [system_step_live_of A policy Letter (thread.root 0)
        (thread.root n) (thread.root (n + 1)) (word n) (thread.step n)]⟩

private theorem minEven_of_eventually_zero
    (priorities : Nat → Nat) (n : Nat)
    (hzero : ∀ k, priorities (n + k) = 0) :
    NatSeqMinEvenParity priorities := by
  have hshift : NatSeqMinEvenParity (fun k => priorities (n + k)) := by
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro base
      exact ⟨base, le_rfl, hzero base⟩
    · intro q _
      exact Nat.zero_le q
  exact (natSeqMinEvenParity_shift priorities n).mp hshift

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- Every run of the hidden system is min-even.  A run that ever makes an
incoherent choice is eventually zero.  Otherwise its live roots form one
exact `AlternatingThread` of the fixed policy. -/
theorem isRun_epochParity (Letter : Type l)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (word : OmegaWord Letter)
    (run : Nat → ProfiledFixedPolicyThreadState A policy)
    (hrun : (system A policy Letter initialRoot).IsRun word run) :
    NatSeqMinEvenParity (fun n =>
      (system A policy Letter initialRoot).priority (run n)) := by
  classical
  by_cases hever : ∃ n, run n = .dead
  · rcases hever with ⟨n, hdead⟩
    apply minEven_of_eventually_zero _ n
    intro k
    rw [isRun_dead_persists A policy Letter initialRoot word run hrun hdead k]
    rfl
  · let roots : Nat → ProfiledFixedPolicyRoot A policy := fun n =>
      match run n with
      | .live root => root
      | .dead => initialRoot
    have hlive : ∀ n, run n = .live (roots n) := by
      intro n
      cases hstate : run n with
      | live root => simp [roots, hstate]
      | dead => exact False.elim (hever ⟨n, hstate⟩)
    have hroot0 : roots 0 = initialRoot := by
      have h := (hlive 0).symm.trans hrun.1
      exact ProfiledFixedPolicyThreadState.live.inj h
    have hstep : ∀ n,
        AlternatingStep A policy (roots n) (roots (n + 1)) := by
      intro n
      rcases hrun.2 n with ⟨target, hnext⟩
      by_cases hallowed : AlternatingStep A policy (roots n) target
      · have htarget : roots (n + 1) = target := by
          have h := (hlive (n + 1)).symm.trans hnext
          rw [hlive n, system_step_live_of A policy Letter initialRoot
            (roots n) target (word n) hallowed] at h
          exact ProfiledFixedPolicyThreadState.live.inj h
        simpa [htarget] using hallowed
      · have hdead : run (n + 1) = .dead := by
          rw [hnext, hlive n,
            system_step_live_dead_of A policy Letter initialRoot
              (roots n) target (word n) hallowed]
        exact False.elim (hever ⟨n + 1, hdead⟩)
    let thread : AlternatingThread A policy := {
      root := roots
      initial := by simpa [hroot0] using hinitial
      step := hstep
    }
    have hparity := thread.epochParity A policy
    have hpriority :
        (fun n => (system A policy Letter initialRoot).priority (run n)) =
          fun n => pairedProfiledEntryPriority A ((roots n).state A policy) := by
      funext n
      rw [hlive n]
      rfl
    rw [hpriority]
    exact hparity

/-- The universal hidden-thread DPA accepts every public word.  The content is
not that public moves are irrelevant operationally; it is that parity of any
coherent actual-root trajectory is already guaranteed by the one fixed
policy. -/
theorem universalRunDPA_accepts (Letter : Type l)
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (word : OmegaWord Letter) :
    (system A policy Letter initialRoot).universalRunDPA.Accepts word := by
  rw [(system A policy Letter initialRoot).universalRunDPA_accepts_iff]
  intro run hrun
  exact isRun_epochParity A policy Letter initialRoot hinitial word run hrun

/-- Any valid public move tree wins after coupling it to the hidden fixed-
policy root system.  In particular, validity may enforce a simultaneous
family table, while the selected actual root remains proof-side. -/
theorem observableTree_winning_of_movesValid
    {Observation : Type o} {Move : Type m}
    [Fintype Observation] [Fintype Move] [Inhabited Observation]
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hvalid : ObservableMovesValid initialObservation Valid tree) :
    (observableThreadTreeMonitor
      (system A policy (Move × Observation) initialRoot)
      initialObservation Valid).WinningTree tree := by
  apply observableThreadTreeMonitor_winning_of
    (system A policy (Move × Observation) initialRoot)
    initialObservation Valid tree hvalid
  intro branch
  exact universalRunDPA_accepts A policy (Move × Observation) initialRoot
    hinitial (observableThreadWord tree branch)

/-- Checked Rabin extraction now yields one finite public controller.  Its
move depends only on the public observation history, never on the hidden
fixed-policy root. -/
theorem exists_finite_observableTable_of_movesValid
    {Observation : Type o} {Move : Type m}
    [Fintype Observation] [Fintype Move] [Inhabited Observation]
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initialObservation : Observation)
    (Valid : Observation → Move → Prop) [DecidableRel Valid]
    (tree : LabeledTree Observation Move)
    (hvalid : ObservableMovesValid initialObservation Valid tree) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (observableThreadTreeMonitor
          (system A policy (Move × Observation) initialRoot)
          initialObservation Valid).toRunAutomaton,
      (observableThreadTreeMonitor
        (system A policy (Move × Observation) initialRoot)
        initialObservation Valid).WinningTree
          table.toTransitionRationalTree.labeledTree := by
  apply exists_stateControlled_observableThreadTree_of_winning
    (system A policy (Move × Observation) initialRoot)
    initialObservation Valid tree
  exact observableTree_winning_of_movesValid A policy initialRoot hinitial
    initialObservation Valid tree hvalid

end

end ProfiledFixedPolicyThreadState

end

end DetParityAutomaton

end DistributedSynthesis
