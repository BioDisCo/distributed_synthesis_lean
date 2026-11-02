/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityStationaryPolicy

/-!
# Finite-memory code-observable parity policies

The ordinary code-observable policy has state `(belief code, parity state)`.
An output-aware hidden-thread regularization may additionally need a finite
public belief monitor.  This file adds exactly that coordinate while keeping
the semantic transition check on the old public state.

The automaton transition chooses one move.  For every direction, the public
component of the child is forced to be the literal code/DPA successor; the
additional finite-memory component may be updated by the chosen transition
table.  Thus the extra coordinate cannot alter the advertised semantic child,
but later policy selection may use it when choosing the next move.
-/

namespace DistributedSynthesis

universe u v w z m

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable {Memory : Type m}
variable [Fintype BeliefCode] [Fintype Memory]

/-- Public code/parity state paired with one additional finite controller
coordinate. -/
abbrev SourceFreeBeliefCodeParityFiniteMemoryState
    (D : DetParityAutomaton.{z, w} BeliefCode) (Memory : Type m) :=
  SourceFreeBeliefCodeParityFiniteState D × Memory

/-- Input-free policy automaton with explicit finite memory. -/
noncomputable def sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    InputFreeRunParityTreeAutomaton.{u, max w z m} Direction where
  State := SourceFreeBeliefCodeParityFiniteMemoryState D Memory
  stateFinite := inferInstance
  initial := ((initialCode, D.initial), initialMemory)
  delta state _ children :=
    ∃ move : Move,
      Valid state.1.1 move ∧
        ∀ direction,
          (children direction).1 =
            sourceFreeBeliefCodeParityControllerNext D state.1 move
              (next state.1.1 move direction)
  priority state := D.priority state.1.2

/-- A rational policy allowed to retain one explicit finite memory
coordinate. -/
abbrev SourceFreeBeliefCodeParityFiniteMemoryPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode) (initialMemory : Memory)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :=
  (sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton D initialCode
    initialMemory Valid next).RationalTransitionPolicy

namespace SourceFreeBeliefCodeParityFiniteMemoryPolicy

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode) (initialMemory : Memory)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

/-- Reachability in the selected finite-memory run. -/
def Reachable
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : SourceFreeBeliefCodeParityFiniteMemoryState D Memory) : Prop :=
  ∃ node, policy.run node = state

/-- One move realizes the complete public successor at a finite-memory
state.  The child memory is intentionally not constrained by this predicate;
it is the additional controller update selected by the rational policy. -/
def MoveRealizesAt
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : SourceFreeBeliefCodeParityFiniteMemoryState D Memory)
    (move : Move) : Prop :=
  Valid state.1.1 move ∧
    ∀ direction,
      (policy.successor state direction).1 =
        sourceFreeBeliefCodeParityControllerNext D state.1 move
          (next state.1.1 move direction)

/-- Legality exposes one shared move and its complete public successor table
at every reachable augmented state. -/
theorem exists_move
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : SourceFreeBeliefCodeParityFiniteMemoryState D Memory)
    (hreachable : policy.Reachable D initialCode initialMemory Valid next
      state) :
    ∃ move : Move,
      policy.MoveRealizesAt D initialCode initialMemory Valid next state
        move := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  simpa [sourceFreeBeliefCodeParityFiniteMemoryRunAutomaton, MoveRealizesAt]
    using hlegal

/-- Every table successor of a reachable state remains reachable. -/
theorem successor_reachable
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (state : SourceFreeBeliefCodeParityFiniteMemoryState D Memory)
    (hreachable : policy.Reachable D initialCode initialMemory Valid next
      state)
    (direction : Direction) :
    policy.Reachable D initialCode initialMemory Valid next
      (policy.successor state direction) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [direction], ?_⟩
  rw [← policy.successor_at node direction, hnode]

/-- Forgetting the added memory along a policy run still follows the literal
code/DPA transition selected by the exposed move. -/
theorem exists_public_successor_move
    (policy : SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode
      initialMemory Valid next)
    (node : TreeNode Direction) :
    ∃ move : Move,
      Valid (policy.run node).1.1 move ∧
        ∀ direction,
          (policy.run (node ++ [direction])).1 =
            sourceFreeBeliefCodeParityControllerNext D (policy.run node).1
              move (next (policy.run node).1.1 move direction) := by
  obtain ⟨move, hmove⟩ := policy.exists_move D initialCode initialMemory Valid
    next (policy.run node) ⟨node, rfl⟩
  refine ⟨move, hmove.1, ?_⟩
  intro direction
  rw [← policy.successor_at node direction]
  exact hmove.2 direction

end SourceFreeBeliefCodeParityFiniteMemoryPolicy

/-! ## Retaining a finite semantic coordinate -/

namespace SourceFreeBeliefCodeParityCertificate

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, m}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid next
    raw)

include certificate

/-- The canonical code-parity run follows the literal semantic move.  This
version exposes that move, rather than merely inverting the existential
transition predicate. -/
theorem run_append_with_semanticMove
    (node : TreeNode Direction) (direction : Direction) :
    SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw
        (node ++ [direction]) =
      sourceFreeBeliefCodeParityControllerNext D
        (SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw
          node)
        (raw.move (raw.stateAt node))
        (next (raw.code (raw.stateAt node))
          (raw.move (raw.stateAt node)) direction) := by
  apply Prod.ext
  · change raw.code (raw.stateAt (node ++ [direction])) = _
    rw [raw.stateAt_append]
    exact certificate.next_code node direction
  · change (raw.codeParityStateAt D (node ++ [direction])).2 = _
    rw [raw.codeParityStateAt_append]
    simp only
    rw [raw.codeParityStateAt_fst]
    congr 1
    exact certificate.next_code node direction

variable [Fintype raw.Semantic]

/-- When the semantic coordinate of a code-parity certificate is itself
finite, retain it literally as the additional policy memory.  This avoids a
second positionalization that could merge two semantic states carrying
different moves. -/
noncomputable def toFiniteMemoryPolicy :
    SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode raw.initial
      Valid next where
  run := fun node ↦
    (SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw
      node, raw.stateAt node)
  accepts := by
    have hisRun := certificate.isRun D initialCode Valid next raw
    have hisAccepting :=
      certificate.isAcceptingRun D initialCode Valid next raw
    constructor
    · constructor
      · apply Prod.ext
        · exact hisRun.1
        · rfl
      · intro node
        refine ⟨raw.move (raw.stateAt node), certificate.valid node, ?_⟩
        intro direction
        exact certificate.run_append_with_semanticMove D initialCode Valid next
          raw node direction
    · exact hisAccepting.2
  successor := fun state direction ↦
    let move := raw.move state.2
    let childCode := next state.1.1 move direction
    (sourceFreeBeliefCodeParityControllerNext D state.1 move childCode,
      raw.step state.2 direction)
  successor_at := by
    intro node direction
    apply Prod.ext
    · change
        sourceFreeBeliefCodeParityControllerNext D
            (SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next
              raw node)
            (raw.move (raw.stateAt node))
            (next
              (SourceFreeBeliefCodeParityCertificate.run D initialCode Valid
                next raw node).1
              (raw.move (raw.stateAt node)) direction) =
          SourceFreeBeliefCodeParityCertificate.run D initialCode Valid next raw
            (node ++ [direction])
      exact (certificate.run_append_with_semanticMove D initialCode Valid next
        raw node direction).symm
    · exact (raw.stateAt_append node direction).symm
  legal_at := by
    intro node
    refine ⟨raw.move (raw.stateAt node), certificate.valid node, ?_⟩
    intro direction
    rfl

@[simp] theorem toFiniteMemoryPolicy_run_memory
    (node : TreeNode Direction) :
    (toFiniteMemoryPolicy D initialCode Valid next raw certificate |>.run
      node).2 = raw.stateAt node :=
  rfl

end SourceFreeBeliefCodeParityCertificate

/-! ## The old interface is the unit-memory case -/

/-- Embed an ordinary code-observable rational policy into the explicit
finite-memory interface with `Unit` memory. -/
noncomputable def SourceFreeBeliefCodeParityRationalPolicy.withUnitMemory
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next) :
    SourceFreeBeliefCodeParityFiniteMemoryPolicy D initialCode () Valid next
      where
  run := fun node ↦ (policy.run node, ())
  accepts := by
    constructor
    · constructor
      · exact Prod.ext policy.accepts.1.1 rfl
      · intro node
        rcases policy.legal_at node with ⟨move, hvalid, hchildren⟩
        refine ⟨move, hvalid, ?_⟩
        intro direction
        change policy.run (node ++ [direction]) = _
        rw [← policy.successor_at node direction]
        exact hchildren direction
    · exact policy.accepts.2
  successor := fun state direction ↦
    (policy.successor state.1 direction, ())
  successor_at := by
    intro node direction
    apply Prod.ext
    · exact policy.successor_at node direction
    · rfl
  legal_at := by
    intro node
    rcases policy.legal_at node with ⟨move, hvalid, hchildren⟩
    refine ⟨move, hvalid, ?_⟩
    intro direction
    exact hchildren direction

@[simp] theorem
    SourceFreeBeliefCodeParityRationalPolicy.withUnitMemory_run_fst
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next)
    (node : TreeNode Direction) :
    (policy.withUnitMemory D initialCode Valid next |>.run node).1 =
      policy.run node :=
  rfl

@[simp] theorem
    SourceFreeBeliefCodeParityRationalPolicy.withUnitMemory_successor_fst
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
      next)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (direction : Direction) :
    (policy.withUnitMemory D initialCode Valid next |>.successor
      (state, ()) direction).1 = policy.successor state direction :=
  rfl

end

end DistributedSynthesis
