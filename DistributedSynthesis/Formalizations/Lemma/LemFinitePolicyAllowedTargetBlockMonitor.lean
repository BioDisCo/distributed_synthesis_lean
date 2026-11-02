/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodePolicyImage
import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Sticky finite-policy target guards for block controllers

A recurrent block controller may expose, together with its physical output,
one proposed successor state for every finite closing row.  This file adds a
generic sticky monitor which checks that every proposal belongs to a fixed
finite-policy successor relation.  The wrapper deliberately knows nothing
about hierarchy, leaders, profiles, scans, or the physical meaning of a
closing row.

The safety bit is parity-visible: once an illegal target is emitted, priority
one persists forever.  Thus every winning narrowed controller emits only
allowed targets.  Conversely, a physical play which wins the base monitor and
whose targets are all allowed wins the wrapper.  Unconditional sender
narrowing can therefore be applied without rebuilding the target argument in
each concrete block monitor.
-/

namespace DistributedSynthesis

universe u v x y w i t

/-- A physical receiver output enriched by one proposed target per finite
closing index. -/
structure IndexedTargetReceiverOutput (ROut : Type x) (Index : Type i)
    (Target : Type t) where
  physical : ROut
  target : Index → Target
deriving Inhabited

noncomputable instance indexedTargetReceiverOutputFintype
    {ROut : Type x} {Index : Type i} {Target : Type t}
    [Fintype ROut] [Fintype Index] [Fintype Target] :
    Fintype (IndexedTargetReceiverOutput ROut Index Target) := by
  classical
  exact Fintype.ofEquiv (ROut × (Index → Target)) {
    toFun := fun output ↦ ⟨output.1, output.2⟩
    invFun := fun output ↦ (output.physical, output.target)
    left_inv := by intro output; cases output; rfl
    right_inv := by intro output; cases output; rfl
  }

/-- Forget target certificates from one realized block round. -/
def indexedTargetPhysicalLetter
    {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
    {Index : Type i} {Target : Type t}
    (letter : RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut) :
    RealizedBlockRound RIn SIn ROut SOut :=
  (letter.1, letter.2.1.physical, letter.2.2)

/-- Forget target certificates pointwise from a play. -/
def indexedTargetPhysicalPlay
    {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
    {Index : Type i} {Target : Type t}
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut) :
    Nat → RealizedBlockRound RIn SIn ROut SOut :=
  fun n ↦ indexedTargetPhysicalLetter (play n)

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable {Index : Type i} {Target : Type t}
variable [Fintype Index]
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- Add a sticky universal target-membership test to a physical block
monitor. -/
noncomputable def indexedAllowedTargetGuard (Allowed : Target → Prop) :
    BlockRecordMonitor.{u, v, max x i t, y, w} RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut := by
  classical
  exact {
    State := M.State × Bool
    stateFinite := inferInstance
    initial := (M.initial, true)
    step := fun state letter ↦
      (M.step state.1 (indexedTargetPhysicalLetter letter),
        state.2 && decide (∀ index, Allowed (letter.2.1.target index)))
    priority := fun state ↦ if state.2 then M.priority state.1 + 2 else 1
  }

@[simp] theorem indexedAllowedTargetGuard_initial (Allowed : Target → Prop) :
    (M.indexedAllowedTargetGuard (Index := Index) Allowed).initial =
      (M.initial, true) := rfl

/-- The first component of the guarded run is exactly the physical run. -/
theorem indexedAllowedTargetGuard_run_base
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut) : ∀ n,
    ((M.indexedAllowedTargetGuard Allowed).run play n).1 =
      M.run (indexedTargetPhysicalPlay play) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, BlockRecordMonitor.run]
      exact congrArg
        (fun state ↦ M.step state (indexedTargetPhysicalLetter (play n))) ih

/-- If every emitted target is allowed, the safety bit remains true. -/
theorem indexedAllowedTargetGuard_run_safe_of_allowed
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (hallowed : ∀ n index, Allowed ((play n).2.1.target index)) : ∀ n,
    ((M.indexedAllowedTargetGuard Allowed).run play n).2 = true := by
  classical
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run]
      change Bool.and
        ((M.indexedAllowedTargetGuard Allowed).run play n).2
        (decide (∀ index, Allowed ((play n).2.1.target index))) = true
      rw [ih, decide_eq_true (hallowed n)]
      rfl

/-- Once target safety fails, it remains failed forever. -/
theorem indexedAllowedTargetGuard_safe_false_persists
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (n : Nat)
    (hfalse : ((M.indexedAllowedTargetGuard Allowed).run play n).2 = false) :
    ∀ k, ((M.indexedAllowedTargetGuard Allowed).run play (n + k)).2 = false := by
  classical
  intro k
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      change Bool.and
        ((M.indexedAllowedTargetGuard Allowed).run play (n + k)).2 _ = false
      rw [ih]
      rfl

/-- Winning the guard forces target safety at every prefix. -/
theorem indexedAllowedTargetGuard_safe_of_wins
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (hwins : (M.indexedAllowedTargetGuard Allowed).WinsPlay play)
    (n : Nat) :
    ((M.indexedAllowedTargetGuard Allowed).run play n).2 = true := by
  by_contra hnot
  have hfalse :
      ((M.indexedAllowedTargetGuard Allowed).run play n).2 = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist := M.indexedAllowedTargetGuard_safe_false_persists
    Allowed play n hfalse
  have heventual : ∀ k, n ≤ k →
      (M.indexedAllowedTargetGuard Allowed).priority
        ((M.indexedAllowedTargetGuard Allowed).run play k) = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    change (if ((M.indexedAllowedTargetGuard Allowed).run play (n + j)).2
      then _ else 1) = 1
    rw [hpersist j]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwins

/-- Every certificate in a winning guarded play satisfies the checked
target relation. -/
theorem indexedAllowedTargetGuard_target_allowed_of_wins
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (hwins : (M.indexedAllowedTargetGuard Allowed).WinsPlay play)
    (n : Nat) (index : Index) :
    Allowed ((play n).2.1.target index) := by
  classical
  have hsafe := M.indexedAllowedTargetGuard_safe_of_wins Allowed play hwins (n + 1)
  rw [BlockRecordMonitor.run] at hsafe
  change Bool.and
    ((M.indexedAllowedTargetGuard Allowed).run play n).2
    (decide (∀ index, Allowed ((play n).2.1.target index))) = true at hsafe
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hsafe
  exact hsafe.2 index

/-- A winning guarded play remains winning after forgetting target
certificates. -/
theorem indexedAllowedTargetGuard_base_wins_of_wins
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (hwins : (M.indexedAllowedTargetGuard Allowed).WinsPlay play) :
    M.WinsPlay (indexedTargetPhysicalPlay play) := by
  unfold BlockRecordMonitor.WinsPlay at hwins ⊢
  have heq :
      (fun n ↦ (M.indexedAllowedTargetGuard Allowed).priority
        ((M.indexedAllowedTargetGuard Allowed).run play n)) =
      fun n ↦ M.priority (M.run (indexedTargetPhysicalPlay play) n) + 2 := by
    funext n
    change (if ((M.indexedAllowedTargetGuard Allowed).run play n).2
      then M.priority ((M.indexedAllowedTargetGuard Allowed).run play n).1 + 2
      else 1) = M.priority (M.run (indexedTargetPhysicalPlay play) n) + 2
    rw [M.indexedAllowedTargetGuard_safe_of_wins Allowed play hwins n,
      if_pos rfl, M.indexedAllowedTargetGuard_run_base Allowed play n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

/-- A physically winning play with only allowed targets wins the guarded
monitor. -/
theorem indexedAllowedTargetGuard_wins_of_base_wins_of_allowed
    (Allowed : Target → Prop)
    (play : Nat → RealizedBlockRound RIn SIn
      (IndexedTargetReceiverOutput ROut Index Target) SOut)
    (hbase : M.WinsPlay (indexedTargetPhysicalPlay play))
    (hallowed : ∀ n index, Allowed ((play n).2.1.target index)) :
    (M.indexedAllowedTargetGuard Allowed).WinsPlay play := by
  unfold BlockRecordMonitor.WinsPlay at hbase ⊢
  have hsafe := M.indexedAllowedTargetGuard_run_safe_of_allowed
    Allowed play hallowed
  have heq :
      (fun n ↦ (M.indexedAllowedTargetGuard Allowed).priority
        ((M.indexedAllowedTargetGuard Allowed).run play n)) =
      fun n ↦ M.priority (M.run (indexedTargetPhysicalPlay play) n) + 2 := by
    funext n
    change (if ((M.indexedAllowedTargetGuard Allowed).run play n).2
      then M.priority ((M.indexedAllowedTargetGuard Allowed).run play n).1 + 2
      else 1) = M.priority (M.run (indexedTargetPhysicalPlay play) n) + 2
    rw [hsafe n, if_pos rfl,
      M.indexedAllowedTargetGuard_run_base Allowed play n]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hbase

section NarrowedReadback

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [Fintype Target]
variable [DecidableEq RIn] [DecidableEq SIn]

/-- Every target physically read from a winning narrowed controller is
allowed. -/
theorem indexedAllowedTargetGuard_narrowed_target_allowed
    (Allowed : Target → Prop)
    (narrowed : LabeledTree SIn
      (NarrowedBlockLabel RIn SIn
        (IndexedTargetReceiverOutput ROut Index Target) SOut
        (M.indexedAllowedTargetGuard Allowed).State))
    (hthreads : NarrowedAllThreadsWin
      (M.indexedAllowedTargetGuard Allowed) narrowed)
    (env : Nat → RIn × SIn) (n : Nat) (index : Index) :
    Allowed
      ((treePlay
        (narrowedInducedTree (M.indexedAllowedTargetGuard Allowed) narrowed)
        env n).2.1.target index) := by
  let guard := M.indexedAllowedTargetGuard (Index := Index) Allowed
  let tree := narrowedInducedTree guard narrowed
  have htree : guard.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin guard hthreads
  have hplay : guard.WinsPlay (treePlay tree env) :=
    (guard.lift_winningTree_iff tree).mp htree env
  exact M.indexedAllowedTargetGuard_target_allowed_of_wins
    Allowed (treePlay tree env) hplay n index

variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Inhabited Target]

/-- Unconditional sender narrowing for a realizable physical block objective
enriched with the sticky allowed-target test. -/
theorem exists_indexedAllowedTarget_controller_of_realizable
    (Allowed : Target → Prop)
    (hrealizable :
      ∃ receiver : ReceiverBlockStrategy RIn SIn
          (IndexedTargetReceiverOutput ROut Index Target),
        ∃ sender : SenderBlockStrategy SIn SOut,
          ∀ env : Nat → RIn × SIn,
            (M.indexedAllowedTargetGuard Allowed).WinsPlay
              (pairPlay receiver sender env)) :
    ∃ controller :
        TransitionRationalTree.{v, max u v (max x i t) y w, w} SIn
        (NarrowedBlockLabel RIn SIn
          (IndexedTargetReceiverOutput ROut Index Target) SOut
          (M.indexedAllowedTargetGuard Allowed).State),
      NarrowedAllThreadsWin (M.indexedAllowedTargetGuard Allowed)
        controller.labeledTree :=
  (block_realizable_iff_implementable_controller_unconditional
    (M.indexedAllowedTargetGuard Allowed)).mp hrealizable

end NarrowedReadback

end BlockRecordMonitor

/-! ## Specialization to one finite-code rational policy -/

namespace SourceFreeBeliefFiniteCodePolicyImage

universe r m z s

variable {RawDirection : Type r} {Move : Type m} {BeliefCode : Type z}
variable [Fintype BeliefCode] [Nonempty RawDirection]
variable
  (D : DetParityAutomaton.{z, s} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (rawNext : BeliefCode → Move → RawDirection → BeliefCode)

/-- Receiver certificates whose targets are states of one selected
finite-code rational policy. -/
abbrev TargetReceiverOutput (ROut : Type x) (Index : Type i) :=
  IndexedTargetReceiverOutput ROut Index
    (State D initialCode Valid rawNext)

/-- The generic sticky guard instantiated with the finite image of one fixed
rational policy state. -/
noncomputable abbrev allowedTargetGuard
    {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
    {Index : Type i} [Fintype Index]
    (policy : Policy D initialCode Valid rawNext)
    (source : State D initialCode Valid rawNext)
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :
    BlockRecordMonitor RIn SIn
      (TargetReceiverOutput D initialCode Valid rawNext ROut Index) SOut :=
  M.indexedAllowedTargetGuard
    (AllowedTarget D initialCode Valid rawNext policy source)

end SourceFreeBeliefFiniteCodePolicyImage

end DistributedSynthesis
