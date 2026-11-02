/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedObservableInputFreeRationalization

/-!
# Source-free belief-node rationalization

This is the generic Bérard-style interface needed by a delay-one belief-node
construction.  A semantic node may contain arbitrary exact histories, but
those histories occur only in the raw nonemptiness witness.  The input-free
run automaton sees a finite `BeliefCode`, chooses one shared `Move`, and
computes every child code through the source-free function `next`.

The transition predicate `Valid` deliberately has no semantic-source
argument.  Consequently, after the input-free rational-run theorem reuses a
complete transition at another occurrence of the same finite state, its move
remains meaningful there.  Any model-specific representative, exact history,
orientation witness, or leader bit belongs in `Semantic`, never in `Valid` or
the finite automaton state.

Parity is checked by an arbitrary finite hidden-thread system.  Its universal
run DPA is carried in the finite automaton state, so the semantic premise is
the exact global statement that this DPA accepts the move/direction word on
every branch.  No raw-word splicing or block-local acceptance premise is used.
-/

namespace DistributedSynthesis

universe u v w x z a

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/--
The finite source-free input-free automaton.  A transition chooses one move
for the complete belief node.  The finite belief successor and the universal
hidden-thread successor are then determined for every environment direction.
-/
noncomputable def sourceFreeBeliefNodeRunAutomaton
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    InputFreeRunParityTreeAutomaton.{u, max w z} Direction where
  State := BeliefCode × U.universalRunDPA.State
  stateFinite := inferInstance
  initial := (initialCode, U.universalRunDPA.initial)
  delta state _ children :=
    ∃ move : Move,
      Valid state.1 move ∧
        ∀ direction,
          children direction =
            (next state.1 move direction,
              U.universalRunDPA.step state.2 (move, direction))
  priority state := U.universalRunDPA.priority state.2

/--
An unrestricted semantic unfolding.  `Semantic` may contain exact histories,
pointed pairs, or any other proof-side data; it is intentionally not required
to be finite.  Its public label is only the shared source-free move.
-/
structure SourceFreeBeliefSemanticTree
    (Direction : Type u) (Move : Type v) (BeliefCode : Type z) where
  Semantic : Type a
  initial : Semantic
  step : Semantic → Direction → Semantic
  code : Semantic → BeliefCode
  move : Semantic → Move

namespace SourceFreeBeliefSemanticTree

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)

/-- Exact semantic belief reached below a finite direction history. -/
def stateAt (node : TreeNode Direction) : raw.Semantic :=
  node.foldl raw.step raw.initial

omit [Fintype BeliefCode] in
@[simp] theorem stateAt_nil : raw.stateAt [] = raw.initial :=
  rfl

omit [Fintype BeliefCode] in
theorem stateAt_append (node : TreeNode Direction) (direction : Direction) :
    raw.stateAt (node ++ [direction]) =
      raw.step (raw.stateAt node) direction := by
  simp [stateAt, List.foldl_append]

/-- The shared move tree exposed by the semantic unfolding. -/
def moveTree : LabeledTree Direction Move :=
  fun node => raw.move (raw.stateAt node)

end SourceFreeBeliefSemanticTree

/--
The exact model obligations for one raw semantic unfolding.

`next_code` is Bérard's source-free T1 equation.  It is strictly different
from saying that two semantic representatives with equal codes happen to have
matching selected continuations: the right-hand side contains no semantic
representative at all.

`accepts` is the global universal hidden-thread parity statement.  In a model
instantiation it is normally proved by flattening each hidden thread to one
genuine execution of the original winning strategy.
-/
structure SourceFreeBeliefSemanticCertificate
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode) : Prop where
  initial_code : raw.code raw.initial = initialCode
  valid : ∀ node,
    Valid (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node))
  next_code : ∀ node direction,
    raw.code (raw.step (raw.stateAt node) direction) =
      next (raw.code (raw.stateAt node))
        (raw.move (raw.stateAt node)) direction
  accepts : ∀ branch : Nat → Direction,
    U.universalRunDPA.Accepts
      (observableThreadWord raw.moveTree branch)

namespace SourceFreeBeliefSemanticCertificate

variable
  (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefSemanticCertificate U initialCode Valid next
    raw)

/-- The finite run induced by the semantic unfolding before rationalization. -/
noncomputable def run :
    TreeNode Direction →
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).State :=
  fun node =>
    (raw.code (raw.stateAt node),
      codedObservableControlAt U raw.moveTree node)

include certificate

/-- The semantic code equation and the universal-DPA fold give a legal run. -/
theorem isRun :
    (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).IsRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (run U initialCode Valid next raw) := by
  constructor
  · apply Prod.ext
    · exact certificate.initial_code
    · rfl
  · intro node
    refine ⟨raw.move (raw.stateAt node), certificate.valid node, ?_⟩
    intro direction
    apply Prod.ext
    · change raw.code (raw.stateAt (node ++ [direction])) = _
      rw [raw.stateAt_append]
      exact certificate.next_code node direction
    · change codedObservableControlAt U raw.moveTree
          (node ++ [direction]) = _
      exact codedObservableControlAt_append U raw.moveTree node direction

/-- Global universal hidden-thread parity is exactly the run's parity. -/
theorem isAcceptingRun :
    (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).IsAcceptingRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (run U initialCode Valid next raw) := by
  refine ⟨certificate.isRun U initialCode Valid next raw, ?_⟩
  intro branch
  have hparity :=
    (U.universalRunDPA.accepts_iff_natSeqMinEvenParity
      (observableThreadWord raw.moveTree branch)).mp
        (certificate.accepts branch)
  have heq :
      (fun n =>
        (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).priority
          (run U initialCode Valid next raw
            (branchNode branch n))) =
        fun n => U.universalRunDPA.priority
          (U.universalRunDPA.run
            (observableThreadWord raw.moveTree branch) n) := by
    funext n
    change U.universalRunDPA.priority
        (codedObservableControlAt U raw.moveTree (branchNode branch n)) = _
    rw [codedObservableControlAt_branchNode]
  rw [heq]
  exact hparity

/--
One application of the input-free rational-run basis regularizes the whole
source-free belief tree.  No semantic representative occurs in the returned
automaton, its transition predicate, or this theorem's conclusion.
-/
theorem hasRationalRun
    (basis :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).RationalRunBasis) :
    (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next).HasRationalRun := by
  apply basis
  exact ⟨run U initialCode Valid next raw,
    certificate.isAcceptingRun U initialCode Valid next raw⟩

end SourceFreeBeliefSemanticCertificate

end

end DistributedSynthesis
