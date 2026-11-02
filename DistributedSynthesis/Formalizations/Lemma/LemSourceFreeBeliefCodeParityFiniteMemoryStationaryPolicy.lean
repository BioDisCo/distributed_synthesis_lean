/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityFiniteMemoryPolicy

/-!
# Stationary tables for finite-memory code-parity policies

The enriched owner-fibre automaton must choose executable finite data before
it has proved that the resulting policy is accepting.  The existing
`RationalTransitionPolicy` type cannot serve as that data: it already bundles
the global parity proof.

This file separates the two.  A finite-memory stationary table chooses one
move and one next-memory value at each augmented code-parity state and
direction.  Its public child code and DPA state remain forced.  Node-local
validity and universal parity then convert the table to the existing certified
policy.  Conversely, every certified finite-memory policy yields such a table
with exactly the same reachable run and successor function.
-/

namespace DistributedSynthesis

universe u v w z m

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable {Memory : Type m}
variable [Fintype BeliefCode] [Fintype Memory]

private abbrev FiniteMemoryState
    (D : DetParityAutomaton.{z, w} BeliefCode) :=
  SourceFreeBeliefCodeParityFiniteMemoryState D Memory

/-- Finite executable data: a move and a memory update at every augmented
policy state. -/
structure SourceFreeBeliefCodeParityFiniteMemoryStationaryTable
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (Memory : Type m) (Move : Type v) (Direction : Type u) where
  move : SourceFreeBeliefCodeParityFiniteMemoryState D Memory → Move
  memoryNext :
    SourceFreeBeliefCodeParityFiniteMemoryState D Memory → Direction →
      Memory

noncomputable instance [Fintype Move] [Fintype Direction]
    (D : DetParityAutomaton.{z, w} BeliefCode) :
    Fintype
      (SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory Move
        Direction) := by
  classical
  letI : Fintype D.State := D.stateFinite
  let State := SourceFreeBeliefCodeParityFiniteMemoryState D Memory
  let Rep := (State → Move) × (State → Direction → Memory)
  let equiv :
      SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory Move
          Direction ≃
        Rep := {
    toFun := fun table ↦ (table.move, table.memoryNext)
    invFun := fun data ↦ ⟨data.1, data.2⟩
    left_inv := by intro table; cases table; rfl
    right_inv := by intro data; cases data; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- The public component is forced by the chosen move and requested
direction; only the last coordinate comes from `memoryNext`. -/
def sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction)
    (state : FiniteMemoryState (Memory := Memory) D)
    (direction : Direction) :
    FiniteMemoryState (Memory := Memory) D :=
  let move := table.move state
  let childCode := next state.1.1 move direction
  (sourceFreeBeliefCodeParityControllerNext D state.1 move childCode,
    table.memoryNext state direction)

/-- State reached by folding the stationary augmented successor. -/
def sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction)
    (node : TreeNode Direction) :
    FiniteMemoryState (Memory := Memory) D :=
  node.foldl
    (sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor D next table)
    ((initialCode, D.initial), initialMemory)

omit [Fintype BeliefCode] [Fintype Memory] in
@[simp] theorem
    sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_nil
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction) :
    sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
      initialMemory next table [] = ((initialCode, D.initial), initialMemory) :=
  rfl

omit [Fintype BeliefCode] [Fintype Memory] in
theorem sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction)
    (node : TreeNode Direction) (direction : Direction) :
    sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
        initialMemory next table (node ++ [direction]) =
      sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor D next table
        (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
          initialMemory next table node)
        direction := by
  simp [sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt,
    List.foldl_append]

/-- Successive public child codes along a stationary branch. -/
def sourceFreeBeliefCodeParityFiniteMemoryStationaryChildCodeWord
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction)
    (branch : Nat → Direction) : OmegaWord BeliefCode :=
  fun n ↦
    (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
      initialMemory next table (branchNode branch (n + 1))).1.1

omit [Fintype BeliefCode] [Fintype Memory] in
/-- The stored DPA coordinate is the literal run on the public child-code
word; the extra memory cannot alter it. -/
theorem
    sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_dpa_branchNode
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory
      Move Direction)
    (branch : Nat → Direction) : ∀ n,
    (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
      initialMemory next table (branchNode branch n)).1.2 =
      D.run
        (sourceFreeBeliefCodeParityFiniteMemoryStationaryChildCodeWord D
          initialCode initialMemory next table branch)
        n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append]
      simp only [sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor,
        sourceFreeBeliefCodeParityControllerNext, DetParityAutomaton.run]
      rw [ih]
      congr 1
      change next
          (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
            initialCode initialMemory next table
              (branchNode branch n)).1.1
          (table.move
            (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
              initialCode initialMemory next table (branchNode branch n)))
          (branch n) =
        (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
          initialMemory next table (branchNode branch (n + 1))).1.1
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append]
      rfl

namespace SourceFreeBeliefCodeParityFiniteMemoryStationaryTable

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode) (initialMemory : Memory)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (table : SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory Move
    Direction)

/-- Node-local legality on the states reached by this table. -/
def ValidAt : Prop :=
  ∀ node : TreeNode Direction,
    let state :=
      sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
        initialMemory next table node
    Valid state.1.1 (table.move state)

/-- Universal forward parity of the public code-parity projection. -/
def Accepts : Prop :=
  ∀ branch : Nat → Direction,
    D.Accepts
      (sourceFreeBeliefCodeParityFiniteMemoryStationaryChildCodeWord D
        initialCode initialMemory next table branch)

/-- A legal, universally accepting finite stationary table is the existing
certified finite-memory policy. -/
noncomputable def toFiniteMemoryPolicy
    (hvalid : table.ValidAt D initialCode initialMemory Valid next)
    (haccepts : table.Accepts D initialCode initialMemory next) :
    SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode initialMemory
      Valid next where
  run := sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
    initialMemory next table
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        refine ⟨table.move
          (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
            initialCode initialMemory next table node), hvalid node, ?_⟩
        intro direction
        change
          (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
            initialCode initialMemory next table
              (node ++ [direction])).1 = _
        rw [sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append]
        rfl
    · intro branch
      let word :=
        sourceFreeBeliefCodeParityFiniteMemoryStationaryChildCodeWord D
          initialCode initialMemory next table branch
      have hparity :=
        (D.accepts_iff_natSeqMinEvenParity
          word).mp
          (haccepts branch)
      have heq :
          (fun n ↦
            (sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton D initialCode
              initialMemory Valid next).priority
              (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
                initialCode initialMemory next table
                  (branchNode branch n))) =
            fun n ↦ D.priority (D.run word n) := by
        funext n
        change D.priority
            (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D
              initialCode initialMemory next table
                (branchNode branch n)).1.2 = _
        rw [sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_dpa_branchNode]
      rw [heq]
      exact hparity
  successor :=
    sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor D next table
  successor_at := by
    intro node direction
    exact
      (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append D
        initialCode initialMemory next table node direction).symm
  legal_at := by
    intro node
    refine ⟨table.move
      (sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
        initialMemory next table node), hvalid node, ?_⟩
    intro direction
    rfl

end SourceFreeBeliefCodeParityFiniteMemoryStationaryTable

namespace SourceFreeBeliefCodeParityFiniteMemoryPolicy

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode) (initialMemory : Memory)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

/-- Extract a total finite stationary table.  At unreachable states its move
is totalized by the root move; its memory update is always the policy's
literal successor memory. -/
noncomputable def stationaryTable
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory Move
      Direction := by
  classical
  let initialState : FiniteMemoryState (Memory := Memory) D :=
    ((initialCode, D.initial), initialMemory)
  have hinitial : policy.Reachable D initialCode initialMemory Valid next
      initialState := ⟨[], policy.accepts.1.1⟩
  let rootMove := Classical.choose
    (policy.exists_move D initialCode initialMemory Valid next initialState
      hinitial)
  exact {
    move := fun state ↦
      if h : policy.Reachable D initialCode initialMemory Valid next state then
        Classical.choose
          (policy.exists_move D initialCode initialMemory Valid next state h)
      else rootMove
    memoryNext := fun state direction ↦
      (policy.successor state direction).2 }

/-- At a reachable state, the extracted move realizes the policy's public
successor. -/
theorem stationaryTable_move_realizesAt
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : FiniteMemoryState (Memory := Memory) D)
    (hreachable : policy.Reachable D initialCode initialMemory Valid next
      state) :
    policy.MoveRealizesAt D initialCode initialMemory Valid next state
      (policy.stationaryTable D initialCode initialMemory Valid next |>.move
        state) := by
  simp only [stationaryTable, dif_pos hreachable]
  exact Classical.choose_spec
    (policy.exists_move D initialCode initialMemory Valid next state hreachable)

/-- The reconstructed stationary successor is exact at every reachable
state, including the extra memory coordinate. -/
theorem stationarySuccessor_eq
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : FiniteMemoryState (Memory := Memory) D)
    (direction : Direction)
    (hreachable : policy.Reachable D initialCode initialMemory Valid next
      state) :
    sourceFreeBeliefCodeParityFiniteMemoryStationarySuccessor D next
        (policy.stationaryTable D initialCode initialMemory Valid next) state
        direction =
      policy.successor state direction := by
  apply Prod.ext
  · exact (policy.stationaryTable_move_realizesAt D initialCode
      initialMemory Valid next state hreachable).2 direction |>.symm
  · rfl

/-- Folding the extracted table reproduces the certified policy run. -/
theorem stationaryStateAt_eq_run
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) : ∀ node : TreeNode Direction,
    sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt D initialCode
        initialMemory next
        (policy.stationaryTable D initialCode initialMemory Valid next) node =
      policy.run node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact policy.accepts.1.1.symm
  | append_singleton node direction ih =>
      rw [sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_append, ih,
        policy.stationarySuccessor_eq D initialCode initialMemory Valid next
          (policy.run node) direction ⟨node, rfl⟩,
        policy.successor_at]

theorem stationaryTable_validAt
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    (policy.stationaryTable D initialCode initialMemory Valid next).ValidAt D
      initialCode initialMemory Valid next := by
  intro node
  rw [policy.stationaryStateAt_eq_run D initialCode initialMemory Valid next
    node]
  exact (policy.stationaryTable_move_realizesAt D initialCode initialMemory
    Valid next (policy.run node) ⟨node, rfl⟩).1

theorem stationaryTable_accepts
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    (policy.stationaryTable D initialCode initialMemory Valid next).Accepts D
      initialCode initialMemory next := by
  intro branch
  let word :=
    sourceFreeBeliefCodeParityFiniteMemoryStationaryChildCodeWord D
      initialCode initialMemory next
        (policy.stationaryTable D initialCode initialMemory Valid next) branch
  have hparity := policy.accepts.2 branch
  have heq :
      (fun n ↦
        (sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton D initialCode
          initialMemory Valid next).priority
          (policy.run (branchNode branch n))) =
        fun n ↦ D.priority (D.run word n) := by
    funext n
    change D.priority (policy.run (branchNode branch n)).1.2 =
      D.priority (D.run word n)
    rw [←
      sourceFreeBeliefCodeParityFiniteMemoryStationaryStateAt_dpa_branchNode D
        initialCode initialMemory next
          (policy.stationaryTable D initialCode initialMemory Valid next)
            branch n,
      policy.stationaryStateAt_eq_run D initialCode initialMemory Valid next
        (branchNode branch n)]
  rw [heq] at hparity
  exact (D.accepts_iff_natSeqMinEvenParity word).mpr hparity

end SourceFreeBeliefCodeParityFiniteMemoryPolicy

/-- Exact data/proof separation for the augmented policy interface. -/
theorem exists_sourceFreeBeliefCodeParityFiniteMemoryStationaryTable_iff
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    (∃ table :
        SourceFreeBeliefCodeParityFiniteMemoryStationaryTable D Memory Move
          Direction,
      table.ValidAt D initialCode initialMemory Valid next ∧
        table.Accepts D initialCode initialMemory next) ↔
      Nonempty
        (SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
          initialMemory Valid next) := by
  constructor
  · rintro ⟨table, hvalid, haccepts⟩
    exact ⟨table.toFiniteMemoryPolicy D initialCode initialMemory Valid next
      hvalid haccepts⟩
  · rintro ⟨policy⟩
    exact ⟨policy.stationaryTable D initialCode initialMemory Valid next,
      policy.stationaryTable_validAt D initialCode initialMemory Valid next,
      policy.stationaryTable_accepts D initialCode initialMemory Valid next⟩

/-! ## Finite successor tables when the move type is not finite

The stationary table above stores a move and is finite only when `Move` is
finite.  Some applications use an intentionally infinite raw witness type.
Their executable content is nevertheless finite: a rational policy stores
only its successor function on finite augmented states and finite public
directions.  Legality then asserts, locally and propositionally, that one raw
move realizes the stored public successors. -/

/-- The finite executable content of an augmented rational policy.  Raw moves
are not stored in this type. -/
structure SourceFreeBeliefCodeParityFiniteMemoryTransitionTable
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (Memory : Type m) (Direction : Type u) where
  successor :
    SourceFreeBeliefCodeParityFiniteMemoryState D Memory → Direction →
      SourceFreeBeliefCodeParityFiniteMemoryState D Memory

noncomputable instance [Fintype Direction]
    (D : DetParityAutomaton.{z, w} BeliefCode) :
    Fintype
      (SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
        Direction) := by
  classical
  letI : Fintype D.State := D.stateFinite
  let State := SourceFreeBeliefCodeParityFiniteMemoryState D Memory
  let Rep := State → Direction → State
  let equiv :
      SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
          Direction ≃ Rep := {
    toFun := fun table ↦ table.successor
    invFun := fun successor ↦ ⟨successor⟩
    left_inv := by intro table; cases table; rfl
    right_inv := by intro successor; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

/-- State reached by folding a finite successor table. -/
def sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (table : SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
      Direction)
    (node : TreeNode Direction) :
    SourceFreeBeliefCodeParityFiniteMemoryState D Memory :=
  node.foldl table.successor ((initialCode, D.initial), initialMemory)

omit [Fintype BeliefCode] [Fintype Memory] in
@[simp] theorem
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_nil
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (table : SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
      Direction) :
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
      initialMemory table [] = ((initialCode, D.initial), initialMemory) :=
  rfl

omit [Fintype Memory] [Fintype BeliefCode] in
theorem sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (table : SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
      Direction)
    (node : TreeNode Direction) (direction : Direction) :
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
        initialMemory table (node ++ [direction]) =
      table.successor
        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
          initialMemory table node)
        direction := by
  simp [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt,
    List.foldl_append]

namespace SourceFreeBeliefCodeParityFiniteMemoryTransitionTable

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode) (initialMemory : Memory)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (table : SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
    Direction)

/-- At every reachable table state, one raw move is legal and realizes the
entire stored public successor map. -/
def ValidAt : Prop :=
  ∀ node : TreeNode Direction,
    let state :=
      sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
        initialMemory table node
    ∃ move : Move,
      Valid state.1.1 move ∧
        ∀ direction,
          (table.successor state direction).1 =
            sourceFreeBeliefCodeParityControllerNext D state.1 move
              (next state.1.1 move direction)

/-- Universal parity of the finite successor table. -/
def Accepts : Prop :=
  ∀ branch : Nat → Direction,
    NatSeqMinEvenParity
      (fun n ↦
        D.priority
          (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D
            initialCode initialMemory table (branchNode branch n)).1.2)

/-- Certify a finite successor table by supplying its two proof
obligations. -/
def toFiniteMemoryPolicy
    (hvalid : table.ValidAt D initialCode initialMemory Valid next)
    (haccepts : table.Accepts D initialCode initialMemory) :
    SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode initialMemory
      Valid next where
  run := sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
    initialMemory table
  accepts := by
    constructor
    · constructor
      · rfl
      · intro node
        rcases hvalid node with ⟨move, hmove, hchildren⟩
        refine ⟨move, hmove, ?_⟩
        intro direction
        change
          (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D
              initialCode initialMemory table (node ++ [direction])).1 = _
        rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append]
        exact hchildren direction
    · exact haccepts
  successor := table.successor
  successor_at := by
    intro node direction
    exact
      (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append D
        initialCode initialMemory table node direction).symm
  legal_at := hvalid

end SourceFreeBeliefCodeParityFiniteMemoryTransitionTable

namespace SourceFreeBeliefCodeParityFiniteMemoryPolicy

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode) (initialMemory : Memory)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

/-- Forget the proofs and retain exactly the finite successor function. -/
def transitionTable
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory Direction :=
  ⟨policy.successor⟩

/-- Folding the extracted successor table reproduces the policy run. -/
theorem transitionStateAt_eq_run
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) : ∀ node : TreeNode Direction,
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt D initialCode
        initialMemory policy.transitionTable node =
      policy.run node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => exact policy.accepts.1.1.symm
  | append_singleton node direction ih =>
      rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append, ih]
      change policy.successor (policy.run node) direction =
        policy.run (node ++ [direction])
      rw [policy.successor_at]

/-- The extracted finite successor table retains local legality. -/
theorem transitionTable_validAt
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    policy.transitionTable.ValidAt D initialCode initialMemory Valid next := by
  intro node
  rw [policy.transitionStateAt_eq_run D initialCode initialMemory Valid next]
  simpa only [transitionTable] using policy.legal_at node

/-- The extracted finite successor table retains universal parity. -/
theorem transitionTable_accepts
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next) :
    policy.transitionTable.Accepts D initialCode initialMemory := by
  intro branch
  have haccepts := policy.accepts.2 branch
  simpa only [sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton,
    transitionStateAt_eq_run] using haccepts

end SourceFreeBeliefCodeParityFiniteMemoryPolicy

/-- Exact finite-data/proof separation, with no finiteness hypothesis on the
raw move type. -/
theorem exists_sourceFreeBeliefCodeParityFiniteMemoryTransitionTable_iff
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    (∃ table :
        SourceFreeBeliefCodeParityFiniteMemoryTransitionTable D Memory
          Direction,
      table.ValidAt D initialCode initialMemory Valid next ∧
        table.Accepts D initialCode initialMemory) ↔
      Nonempty
        (SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
          initialMemory Valid next) := by
  constructor
  · rintro ⟨table, hvalid, haccepts⟩
    exact ⟨table.toFiniteMemoryPolicy D initialCode initialMemory Valid next
      hvalid haccepts⟩
  · rintro ⟨policy⟩
    exact ⟨policy.transitionTable,
      policy.transitionTable_validAt D initialCode initialMemory Valid next,
      policy.transitionTable_accepts D initialCode initialMemory Valid next⟩

end

end DistributedSynthesis
