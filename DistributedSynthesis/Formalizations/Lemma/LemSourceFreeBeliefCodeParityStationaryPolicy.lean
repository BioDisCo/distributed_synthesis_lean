/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Stationary tables for code-observable parity policies

The executable content of a code-observable rational policy is one move at
each finite state `(belief code, parity state)`.  This file makes that
stationary table explicit.  A valid table whose every direction branch is
accepted yields the existing `RationalTransitionPolicy`; conversely, every
such rational policy has an extension to a total stationary table which
agrees with its run and successor at every reachable state.

This equivalence records an important boundary for later hidden-thread
regularization.  A controller extracted with additional finite belief memory
does not inhabit the old policy type unless its chosen move factors through
the old finite state.
-/

namespace DistributedSynthesis

universe u v w z

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- A total move table indexed only by the code-observable policy state. -/
abbrev SourceFreeBeliefCodeParityStationaryTable
    (D : DetParityAutomaton.{z, w} BeliefCode) :=
  SourceFreeBeliefCodeParityFiniteState D → Move

/-- Successor induced by one stationary move table. -/
def sourceFreeBeliefCodeParityStationarySuccessor
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (direction : Direction) :
    SourceFreeBeliefCodeParityFiniteState D :=
  let move := table state
  let childCode := next state.1 move direction
  sourceFreeBeliefCodeParityControllerNext D state move childCode

/-- Finite state reached by folding the stationary successor table. -/
def sourceFreeBeliefCodeParityStationaryStateAt
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (node : TreeNode Direction) :
    SourceFreeBeliefCodeParityFiniteState D :=
  node.foldl (sourceFreeBeliefCodeParityStationarySuccessor D next table)
    (initialCode, D.initial)

omit [Fintype BeliefCode] in
@[simp] theorem sourceFreeBeliefCodeParityStationaryStateAt_nil
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D) :
    sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table [] =
      (initialCode, D.initial) :=
  rfl

omit [Fintype BeliefCode] in
theorem sourceFreeBeliefCodeParityStationaryStateAt_append
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (node : TreeNode Direction) (direction : Direction) :
    sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
        (node ++ [direction]) =
      sourceFreeBeliefCodeParityStationarySuccessor D next table
        (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
          node)
        direction := by
  simp [sourceFreeBeliefCodeParityStationaryStateAt, List.foldl_append]

/-- Successive child codes read along one stationary direction branch. -/
def sourceFreeBeliefCodeParityStationaryChildCodeWord
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (branch : Nat → Direction) : OmegaWord BeliefCode :=
  fun n ↦
    (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
      (branchNode branch (n + 1))).1

omit [Fintype BeliefCode] in
/-- The second stationary coordinate is exactly the DPA run on the child-code
word. -/
theorem sourceFreeBeliefCodeParityStationaryStateAt_snd_branchNode
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (branch : Nat → Direction) : ∀ n,
    (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
      (branchNode branch n)).2 =
        D.run
          (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode
            next table branch)
          n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        sourceFreeBeliefCodeParityStationaryStateAt_append]
      simp only [sourceFreeBeliefCodeParityStationarySuccessor,
        sourceFreeBeliefCodeParityControllerNext, DetParityAutomaton.run]
      rw [ih]
      change D.step
          (D.run
            (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode
              next table branch) n)
          _ =
        D.step
          (D.run
            (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode
              next table branch) n)
          (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode
            next table branch n)
      congr 1
      change next
          (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
            table (branchNode branch n)).1
          (table
            (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
              table (branchNode branch n)))
          (branch n) =
        (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
          (branchNode branch (n + 1))).1
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        sourceFreeBeliefCodeParityStationaryStateAt_append]
      rfl

/-- Node-local legality of a stationary move table. -/
def SourceFreeBeliefCodeParityStationaryTable.ValidAt
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D) : Prop :=
  ∀ node : TreeNode Direction,
    let state := sourceFreeBeliefCodeParityStationaryStateAt D initialCode
      next table node
    Valid state.1 (table state)

/-- Universal forward parity of a stationary move table. -/
def SourceFreeBeliefCodeParityStationaryTable.Accepts
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D) : Prop :=
  ∀ branch : Nat → Direction,
    D.Accepts
      (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode next
        table branch)

/-- A legal, universally accepting stationary table is an executable
code-observable rational policy. -/
noncomputable def
    SourceFreeBeliefCodeParityStationaryTable.toRationalPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityStationaryTable
      (Move := Move) D)
    (hvalid : table.ValidAt D initialCode Valid next)
    (haccepts : table.Accepts D initialCode next) :
    SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next where
  run := sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        refine ⟨table
          (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
            table node), hvalid node, ?_⟩
        intro direction
        change sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
            table (node ++ [direction]) = _
        rw [sourceFreeBeliefCodeParityStationaryStateAt_append]
        rfl
    · intro branch
      have hparity := (D.accepts_iff_natSeqMinEvenParity
        (sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode next
          table branch)).mp (haccepts branch)
      have heq :
          (fun n ↦
            (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
              |>.priority
                (sourceFreeBeliefCodeParityStationaryStateAt D initialCode
                  next table (branchNode branch n))) =
            fun n ↦ D.priority
              (D.run
                (sourceFreeBeliefCodeParityStationaryChildCodeWord D
                  initialCode next table branch) n) := by
        funext n
        change D.priority
            (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
              table (branchNode branch n)).2 = _
        rw [sourceFreeBeliefCodeParityStationaryStateAt_snd_branchNode]
      rw [heq]
      exact hparity
  successor := sourceFreeBeliefCodeParityStationarySuccessor D next table
  successor_at := by
    intro node direction
    exact (sourceFreeBeliefCodeParityStationaryStateAt_append D initialCode
      next table node direction).symm
  legal_at := by
    intro node
    refine ⟨table
      (sourceFreeBeliefCodeParityStationaryStateAt D initialCode next table
        node), hvalid node, ?_⟩
    intro direction
    rfl

namespace SourceFreeBeliefCodeParityRationalPolicy

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

/-- The root of every rational policy is reachable. -/
theorem initial_reachable
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) :
    policy.Reachable D initialCode Valid next (initialCode, D.initial) := by
  refine ⟨[], ?_⟩
  exact policy.accepts.1.1

/-- A rational policy determines a total stationary table.  At unreachable
states the root move is used only to totalize the finite function. -/
noncomputable def stationaryTable
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) :
    SourceFreeBeliefCodeParityStationaryTable (Move := Move) D := by
  classical
  let rootMove := Classical.choose
    (policy.exists_sourceFreeMove D initialCode Valid next
      (initialCode, D.initial)
      (policy.initial_reachable D initialCode Valid next))
  exact fun state ↦
    if h : policy.Reachable D initialCode Valid next state then
      Classical.choose
        (policy.exists_sourceFreeMove D initialCode Valid next state h)
    else rootMove

/-- At a reachable state, the extracted stationary move realizes the exact
rational successor table. -/
theorem stationaryTable_realizesAt
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (hreachable : policy.Reachable D initialCode Valid next state) :
    policy.MoveRealizesAt D initialCode Valid next state
      (policy.stationaryTable D initialCode Valid next state) := by
  simp only [stationaryTable, dif_pos hreachable]
  exact Classical.choose_spec
    (policy.exists_sourceFreeMove D initialCode Valid next state hreachable)

/-- The stationary successor reconstructed from a rational policy agrees with
that policy at every reachable state. -/
theorem stationarySuccessor_eq
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (direction : Direction)
    (hreachable : policy.Reachable D initialCode Valid next state) :
    sourceFreeBeliefCodeParityStationarySuccessor D next
        (policy.stationaryTable D initialCode Valid next) state direction =
      policy.successor state direction := by
  have hrealizes := policy.stationaryTable_realizesAt D initialCode Valid next
    state hreachable
  exact (hrealizes.2 direction).symm

/-- Folding the reconstructed stationary table gives exactly the selected
rational run at every finite node. -/
theorem stationaryStateAt_eq_run
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) : ∀ node : TreeNode Direction,
    sourceFreeBeliefCodeParityStationaryStateAt D initialCode next
        (policy.stationaryTable D initialCode Valid next) node =
      policy.run node := by
  intro node
  induction node using List.reverseRecOn with
  | nil =>
      simpa using policy.accepts.1.1.symm
  | append_singleton node direction ih =>
      rw [sourceFreeBeliefCodeParityStationaryStateAt_append, ih,
        policy.stationarySuccessor_eq D initialCode Valid next
          (policy.run node) direction ⟨node, rfl⟩,
        policy.successor_at]

/-- The stationary table extracted from a rational policy is legal at every
state reached by its own fold. -/
theorem stationaryTable_validAt
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) :
    (policy.stationaryTable D initialCode Valid next).ValidAt D initialCode
      Valid next := by
  intro node
  rw [policy.stationaryStateAt_eq_run D initialCode Valid next node]
  exact (policy.stationaryTable_realizesAt D initialCode Valid next
    (policy.run node) ⟨node, rfl⟩).1

/-- The stationary table extracted from a rational policy preserves its
universal forward parity. -/
theorem stationaryTable_accepts
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) :
    (policy.stationaryTable D initialCode Valid next).Accepts D initialCode
      next := by
  intro branch
  let word := sourceFreeBeliefCodeParityStationaryChildCodeWord D initialCode
    next (policy.stationaryTable D initialCode Valid next) branch
  have hparity := policy.accepts.2 branch
  have heq :
      (fun n ↦
        (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
          |>.priority (policy.run (branchNode branch n))) =
        fun n ↦ D.priority (D.run word n) := by
    funext n
    change D.priority (policy.run (branchNode branch n)).2 =
      D.priority (D.run word n)
    rw [← sourceFreeBeliefCodeParityStationaryStateAt_snd_branchNode D
      initialCode next (policy.stationaryTable D initialCode Valid next)
      branch n,
      policy.stationaryStateAt_eq_run D initialCode Valid next
        (branchNode branch n)]
  rw [heq] at hparity
  exact (D.accepts_iff_natSeqMinEvenParity word).mpr hparity

end SourceFreeBeliefCodeParityRationalPolicy

/-- Exact existence interface: code-observable rational policies and legal,
universally accepting stationary tables carry the same information. -/
theorem exists_sourceFreeBeliefCodeParityStationaryTable_iff
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    (∃ table : SourceFreeBeliefCodeParityStationaryTable (Move := Move) D,
        table.ValidAt D initialCode Valid next ∧
          table.Accepts D initialCode next) ↔
      Nonempty
        (SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next) := by
  constructor
  · rintro ⟨table, hvalid, haccepts⟩
    exact ⟨table.toRationalPolicy D initialCode Valid next hvalid haccepts⟩
  · rintro ⟨policy⟩
    exact ⟨policy.stationaryTable D initialCode Valid next,
      policy.stationaryTable_validAt D initialCode Valid next,
      policy.stationaryTable_accepts D initialCode Valid next⟩

end

end DistributedSynthesis
