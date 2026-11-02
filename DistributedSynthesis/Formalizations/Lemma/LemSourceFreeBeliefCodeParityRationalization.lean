/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodeRationalization

/-!
# Source-free rationalization with a code-observable parity monitor

The generic source-free construction may carry a deterministic objective
monitor whose alphabet still contains the raw environment direction.  Even
when the next public belief code is finite, that presentation leaves a
separate locality question: does the monitor step factor through the next
code?

This file records the clean presentation used when the objective is already
determined by the sequence of finite belief codes.  The deterministic parity
automaton reads the *child code*.  Consequently the complete finite successor
is definitionally a function of the current finite state, the chosen move,
and the child code.  No representative, direction, orientation, or leader bit
occurs in that table.
-/

namespace DistributedSynthesis

universe u v w z a

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- The input-free run automaton whose objective monitor reads the finite
child belief code rather than the raw direction that produced it. -/
noncomputable def sourceFreeBeliefCodeParityRunAutomaton
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :
    InputFreeRunParityTreeAutomaton.{u, max w z} Direction where
  State := BeliefCode × D.State
  stateFinite := inferInstance
  initial := (initialCode, D.initial)
  delta state _ children :=
    ∃ move : Move,
      Valid state.1 move ∧
        ∀ direction,
          let childCode := next state.1 move direction
          children direction = (childCode, D.step state.2 childCode)
  priority state := D.priority state.2

/-- The objective word below one semantic branch consists of the successive
child codes.  Its letter at time `n` is the code at depth `n + 1`. -/
def SourceFreeBeliefSemanticTree.childCodeWord
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (branch : Nat → Direction) : OmegaWord BeliefCode :=
  fun n => raw.code (raw.stateAt (branchNode branch (n + 1)))

/-- Simultaneously fold the exact semantic state and the code-observable DPA
control along one finite direction word. -/
def SourceFreeBeliefSemanticTree.codeParityStateAt
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (node : TreeNode Direction) : raw.Semantic × D.State :=
  node.foldl
    (fun current direction =>
      let child := raw.step current.1 direction
      (child, D.step current.2 (raw.code child)))
    (raw.initial, D.initial)

namespace SourceFreeBeliefSemanticTree

variable
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (D : DetParityAutomaton.{z, w} BeliefCode)

section
omit [Fintype BeliefCode]

@[simp] theorem codeParityStateAt_nil :
    raw.codeParityStateAt D [] = (raw.initial, D.initial) :=
  rfl

theorem codeParityStateAt_append
    (node : TreeNode Direction) (direction : Direction) :
    raw.codeParityStateAt D (node ++ [direction]) =
      let child := raw.step (raw.codeParityStateAt D node).1 direction
      (child,
        D.step (raw.codeParityStateAt D node).2 (raw.code child)) := by
  simp [codeParityStateAt, List.foldl_append]

/-- The semantic projection of the simultaneous fold is the ordinary exact
semantic state at that node. -/
theorem codeParityStateAt_fst (node : TreeNode Direction) :
    (raw.codeParityStateAt D node).1 = raw.stateAt node := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node direction ih =>
      rw [codeParityStateAt_append, raw.stateAt_append]
      simp only
      rw [ih]

/-- Along a branch, the monitor projection of the simultaneous fold is the
ordinary DPA run on the successive child-code word. -/
theorem codeParityStateAt_snd_branchNode
    (branch : Nat → Direction) (n : Nat) :
    (raw.codeParityStateAt D (branchNode branch n)).2 =
      D.run (raw.childCodeWord branch) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        codeParityStateAt_append]
      simp only
      rw [ih, codeParityStateAt_fst]
      change D.step (D.run (raw.childCodeWord branch) n)
          (raw.code (raw.step (raw.stateAt (branchNode branch n))
            (branch n))) =
        D.step (D.run (raw.childCodeWord branch) n)
          (raw.childCodeWord branch n)
      congr 1
      change raw.code (raw.step (raw.stateAt (branchNode branch n))
          (branch n)) =
        raw.code (raw.stateAt (branchNode branch (n + 1)))
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        raw.stateAt_append]

end

end SourceFreeBeliefSemanticTree

/-- Exact semantic obligations for the code-observable presentation. -/
structure SourceFreeBeliefCodeParityCertificate
    (D : DetParityAutomaton.{z, w} BeliefCode)
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
    D.Accepts (raw.childCodeWord branch)

namespace SourceFreeBeliefCodeParityCertificate

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)
  (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
    Direction Move BeliefCode)
  (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid next
    raw)

/-- The finite run induced by the exact semantic unfolding. -/
noncomputable def run
    (node : TreeNode Direction) :
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next).State :=
  (raw.code (raw.stateAt node), (raw.codeParityStateAt D node).2)

include certificate

theorem isRun :
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next).IsRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (run D initialCode Valid next raw) := by
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
    · change (raw.codeParityStateAt D (node ++ [direction])).2 = _
      rw [raw.codeParityStateAt_append]
      simp only
      rw [raw.codeParityStateAt_fst]
      congr 1
      exact certificate.next_code node direction

theorem isAcceptingRun :
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.IsAcceptingRun InputFreeRunParityTreeAutomaton.uniqueTree
        (run D initialCode Valid next raw) := by
  refine ⟨certificate.isRun D initialCode Valid next raw, ?_⟩
  intro branch
  have haccepts := certificate.accepts branch
  have heq :
      (fun n =>
        (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
          |>.priority
            (run D initialCode Valid next raw (branchNode branch n))) =
        fun n => D.priority (D.run (raw.childCodeWord branch) n) := by
    funext n
    change D.priority (raw.codeParityStateAt D (branchNode branch n)).2 = _
    rw [raw.codeParityStateAt_snd_branchNode]
  rw [heq]
  exact (D.accepts_iff_natSeqMinEvenParity
    (raw.childCodeWord branch)).mp haccepts

/-- One rational-basis application regularizes the code-observable semantic
tree. -/
theorem hasRationalRun
    (basis :
      (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
        |>.RationalRunBasis) :
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.HasRationalRun := by
  apply basis
  exact ⟨run D initialCode Valid next raw,
    certificate.isAcceptingRun D initialCode Valid next raw⟩

end SourceFreeBeliefCodeParityCertificate

/-! ## Definitional finite-controller factorization -/

/-- Complete finite state of the code-observable rational policy. -/
abbrev SourceFreeBeliefCodeParityFiniteState
    (D : DetParityAutomaton.{z, w} BeliefCode) := BeliefCode × D.State

/-- The finite successor table reads only the child code. -/
def sourceFreeBeliefCodeParityControllerNext
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (_move : Move) (childCode : BeliefCode) :
    SourceFreeBeliefCodeParityFiniteState D :=
  (childCode, D.step state.2 childCode)

omit [Fintype BeliefCode] in
@[simp] theorem sourceFreeBeliefCodeParityControllerNext_spec
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (state : SourceFreeBeliefCodeParityFiniteState D)
    (move : Move) (direction : Direction) :
    sourceFreeBeliefCodeParityControllerNext D state move
        (next state.1 move direction) =
      (next state.1 move direction,
        D.step state.2 (next state.1 move direction)) :=
  rfl

/-! ## Reading the finite move from a rational code-observable policy -/

abbrev SourceFreeBeliefCodeParityRationalPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) :=
  (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
    |>.RationalTransitionPolicy

namespace SourceFreeBeliefCodeParityRationalPolicy

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (next : BeliefCode → Move → Direction → BeliefCode)

/-- Reachability inside the selected rational run. -/
def Reachable
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next)
    (state : (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.State) : Prop :=
  ∃ node, policy.run node = state

/-- One move realizes the complete code-observable transition at a finite
policy state. -/
def MoveRealizesAt
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next)
    (state : (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.State)
    (move : Move) : Prop :=
  Valid state.1 move ∧
    ∀ direction,
      let childCode := next state.1 move direction
      policy.successor state direction =
        (childCode, D.step state.2 childCode)

/-- At every reachable policy state, legality exposes one shared finite move
and its complete child-code-observable successor table. -/
theorem exists_sourceFreeMove
    (policy : SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next)
    (state : (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.State)
    (hreachable : policy.Reachable D initialCode Valid next state) :
    ∃ move : Move, policy.MoveRealizesAt D initialCode Valid next state move := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  simpa [sourceFreeBeliefCodeParityRunAutomaton] using hlegal

end SourceFreeBeliefCodeParityRationalPolicy

namespace SourceFreeBeliefCodeParityCertificate

/-- The code-observable semantic certificate and one rational basis yield an
executable finite transition policy. -/
theorem nonempty_rationalPolicy
    (D : DetParityAutomaton.{z, w} BeliefCode)
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (raw : SourceFreeBeliefSemanticTree.{u, v, z, a}
      Direction Move BeliefCode)
    (certificate : SourceFreeBeliefCodeParityCertificate D initialCode Valid
      next raw)
    (basis : (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid next)
      |>.RationalRunBasis) :
    Nonempty
      (SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid next) := by
  apply InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
  exact certificate.hasRationalRun D initialCode Valid next raw basis

end SourceFreeBeliefCodeParityCertificate

end

end DistributedSynthesis
