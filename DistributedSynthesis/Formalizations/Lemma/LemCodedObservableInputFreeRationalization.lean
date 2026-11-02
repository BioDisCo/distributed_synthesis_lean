/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemObservableThreadTreeRationalization
import DistributedSynthesis.Formalizations.Theorem.ThmInputFreeRationalRun

/-!
# Input-free rationalization over exact observations

The arbitrary-direction input-free rational-run theorem does not require the
tree direction type to be finite.  Consequently an exact (and generally
infinite) local observation may remain a proof-side tree direction while the
run automaton stores only a finite public code and a finite universal-thread
monitor state.

This file proves that positive statement.  It also records the exact limit of
the construction: the extracted rational policy still has a successor of
type

`FiniteState -> ExactObservation -> FiniteState`.

Nothing in `RationalTransitionPolicy` says that this function factors through
a finite, recursively updateable local summary.  The final Boolean example is
a kernel-checked witness: even with a constant finite code, a perfectly legal
rational transition policy may distinguish the two exact observations.
-/

namespace DistributedSynthesis

universe u v w x z

section CodedObservable

variable {Observation : Type u} {Move : Type v} {Code : Type z}
variable [Fintype Code]

/-- Finite run state for an observable tree with arbitrary observation type.
The exact observation is deliberately absent. -/
abbrev CodedObservableInputFreeState
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation)) :=
  Code × S.universalRunDPA.State

/--
An input-free run automaton over possibly infinite observations.  At a node it
chooses one finite move for the current finite code.  Every exact next
observation is then followed simultaneously by the finite public code and the
universal hidden-thread DPA.
-/
noncomputable def codedObservableInputFreeRunAutomaton
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code → Move → Prop) :
    InputFreeRunParityTreeAutomaton.{u, max w z} Observation where
  State := CodedObservableInputFreeState (Code := Code) S
  stateFinite := inferInstance
  initial := (code initialObservation, S.universalRunDPA.initial)
  delta state _ children :=
    ∃ move : Move,
      Valid state.1 move ∧
        ∀ observation,
          children observation =
            (code observation,
              S.universalRunDPA.step state.2 (move, observation))
  priority state := S.universalRunDPA.priority state.2

/-- Fold a finite observation history while retaining the prefix needed to
read the move at its parent node. -/
noncomputable def codedObservablePrefixControl
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move) (node : TreeNode Observation) :
    TreeNode Observation × S.universalRunDPA.State :=
  node.foldl
    (fun current observation =>
      (current.1 ++ [observation],
        S.universalRunDPA.step current.2
          (tree current.1, observation)))
    ([], S.universalRunDPA.initial)

@[simp] theorem codedObservablePrefixControl_fst
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move) : ∀ node,
    (codedObservablePrefixControl S tree node).1 = node := by
  intro node
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node observation ih =>
      rw [codedObservablePrefixControl, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change
        (codedObservablePrefixControl S tree node).1 ++ [observation] =
          node ++ [observation]
      rw [ih]

/-- Universal-DPA control after a finite observation history. -/
noncomputable def codedObservableControlAt
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move) (node : TreeNode Observation) :
    S.universalRunDPA.State :=
  (codedObservablePrefixControl S tree node).2

@[simp] theorem codedObservableControlAt_nil
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move) :
    codedObservableControlAt S tree [] = S.universalRunDPA.initial :=
  rfl

theorem codedObservableControlAt_append
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move) (node : TreeNode Observation)
    (observation : Observation) :
    codedObservableControlAt S tree (node ++ [observation]) =
      S.universalRunDPA.step (codedObservableControlAt S tree node)
        (tree node, observation) := by
  unfold codedObservableControlAt codedObservablePrefixControl
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  change S.universalRunDPA.step
      (codedObservableControlAt S tree node)
      (tree (codedObservablePrefixControl S tree node).1, observation) = _
  rw [codedObservablePrefixControl_fst]
  rfl

/-- Run induced by a history-dependent move tree.  The exact current
observation is immediately collapsed to its finite code. -/
noncomputable def codedObservableRun
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (tree : LabeledTree Observation Move) :
    TreeNode Observation →
      CodedObservableInputFreeState (Code := Code) S :=
  fun node =>
    (code (observableAt initialObservation node),
      codedObservableControlAt S tree node)

/-- Node-local legality of a history-dependent move tree. -/
def CodedObservableMovesValid
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code → Move → Prop)
    (tree : LabeledTree Observation Move) : Prop :=
  ∀ node,
    Valid (code (observableAt initialObservation node)) (tree node)

private theorem observableAt_append_singleton
    (initialObservation : Observation) (node : TreeNode Observation)
    (observation : Observation) :
    observableAt initialObservation (node ++ [observation]) = observation := by
  simp [observableAt]

/-- Every locally valid exact-observation tree supplies a legal run of the
finite-state coded automaton. -/
theorem codedObservableRun_isRun
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code → Move → Prop)
    (tree : LabeledTree Observation Move)
    (hvalid : CodedObservableMovesValid initialObservation code Valid tree) :
    (codedObservableInputFreeRunAutomaton S initialObservation code Valid).IsRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (codedObservableRun S initialObservation code tree) := by
  constructor
  · rfl
  · intro node
    refine ⟨tree node, hvalid node, ?_⟩
    intro observation
    apply Prod.ext
    · simp [codedObservableRun,
        observableAt_append_singleton initialObservation node observation]
    · exact codedObservableControlAt_append S tree node observation

/-- The finite control read at depth `n` is the DPA run on the corresponding
public move/exact-observation word. -/
theorem codedObservableControlAt_branchNode
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (tree : LabeledTree Observation Move)
    (branch : Nat → Observation) : ∀ n,
    codedObservableControlAt S tree (branchNode branch n) =
      S.universalRunDPA.run (observableThreadWord tree branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        codedObservableControlAt_append, ih]
      rfl

/-- If every universal hidden-thread word is accepted, the coded run retains
that parity verbatim. -/
theorem codedObservableRun_isAcceptingRun
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code → Move → Prop)
    (tree : LabeledTree Observation Move)
    (hvalid : CodedObservableMovesValid initialObservation code Valid tree)
    (hbundle : ∀ branch : Nat → Observation,
      S.universalRunDPA.Accepts (observableThreadWord tree branch)) :
    (codedObservableInputFreeRunAutomaton S initialObservation code Valid).IsAcceptingRun
      InputFreeRunParityTreeAutomaton.uniqueTree
      (codedObservableRun S initialObservation code tree) := by
  refine ⟨codedObservableRun_isRun S initialObservation code Valid tree
    hvalid, ?_⟩
  intro branch
  have hparity :=
    (S.universalRunDPA.accepts_iff_natSeqMinEvenParity
      (observableThreadWord tree branch)).mp (hbundle branch)
  have heq :
      (fun n =>
        (codedObservableInputFreeRunAutomaton S initialObservation code Valid).priority
          (codedObservableRun S initialObservation code tree
            (branchNode branch n))) =
        fun n => S.universalRunDPA.priority
          (S.universalRunDPA.run (observableThreadWord tree branch) n) := by
    funext n
    change S.universalRunDPA.priority
        (codedObservableControlAt S tree (branchNode branch n)) = _
    rw [codedObservableControlAt_branchNode]
  rw [heq]
  exact hparity

/-- Apply the arbitrary-direction Bérard basis only after exact-observation
legality and hidden-thread parity have been combined in one run. -/
theorem codedObservable_hasRationalRun
    (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
    (initialObservation : Observation) (code : Observation → Code)
    (Valid : Code → Move → Prop)
    (tree : LabeledTree Observation Move)
    (hvalid : CodedObservableMovesValid initialObservation code Valid tree)
    (hbundle : ∀ branch : Nat → Observation,
      S.universalRunDPA.Accepts (observableThreadWord tree branch))
    (basis :
      (codedObservableInputFreeRunAutomaton S initialObservation code Valid).RationalRunBasis) :
    (codedObservableInputFreeRunAutomaton S initialObservation code Valid).HasRationalRun := by
  apply basis
  exact ⟨codedObservableRun S initialObservation code tree,
    codedObservableRun_isAcceptingRun S initialObservation code Valid tree
      hvalid hbundle⟩

/-- Exact extra law needed to turn the arbitrary-observation successor into a
transition on a finite observation code. -/
def InputFreeRunParityTreeAutomaton.RationalTransitionPolicy.SuccessorRespectsCode
    {B : Type u} {C : Type z} [Fintype C]
    {T : InputFreeRunParityTreeAutomaton.{u, w} B}
    (policy : T.RationalTransitionPolicy) (code : B → C) : Prop :=
  ∀ state left right, code left = code right →
    policy.successor state left = policy.successor state right

/-- `SuccessorRespectsCode` is exactly, not merely necessarily, the existence
of a successor table on the finite code.  Values outside the image of `code`
are harmlessly completed by the automaton's initial state. -/
theorem InputFreeRunParityTreeAutomaton.RationalTransitionPolicy.successorRespectsCode_iff_exists_factor
    {B : Type u} {C : Type z} [Fintype C]
    {T : InputFreeRunParityTreeAutomaton.{u, w} B}
    (policy : T.RationalTransitionPolicy) (code : B → C) :
    policy.SuccessorRespectsCode code ↔
      ∃ next : T.State → C → T.State,
        ∀ state observation,
          policy.successor state observation = next state (code observation) := by
  classical
  constructor
  · intro hrespect
    let next : T.State → C → T.State := fun state currentCode =>
      if h : ∃ observation, code observation = currentCode then
        policy.successor state (Classical.choose h)
      else T.initial
    refine ⟨next, ?_⟩
    intro state observation
    change policy.successor state observation =
      if h : ∃ candidate, code candidate = code observation then
        policy.successor state (Classical.choose h)
      else T.initial
    rw [dif_pos ⟨observation, rfl⟩]
    apply hrespect
    exact (Classical.choose_spec
      (show ∃ candidate, code candidate = code observation from
        ⟨observation, rfl⟩)).symm
  · rintro ⟨next, hnext⟩ state left right hcode
    rw [hnext, hnext, hcode]

/-- When the observation itself is already the finite public class, the
oracle issue disappears definitionally: use the identity code.  This does
not prove that an exact-history move tree descends to those classes. -/
theorem InputFreeRunParityTreeAutomaton.RationalTransitionPolicy.successorRespectsIdentity
    {B : Type u} [Fintype B]
    {T : InputFreeRunParityTreeAutomaton.{u, w} B}
    (policy : T.RationalTransitionPolicy) :
    policy.SuccessorRespectsCode (fun observation : B => observation) := by
  intro state left right heq
  exact congrArg (policy.successor state) heq

end CodedObservable

/-! ## The arbitrary-branch policy interface does not imply factorization -/

/-- A harmless input-free automaton in which every transition is legal and
every state has even priority. -/
def boolObservationOracleAutomaton :
    InputFreeRunParityTreeAutomaton Bool where
  State := Bool
  stateFinite := inferInstance
  initial := false
  delta _ _ _ := True
  priority _ := 0

/-- A rational run whose finite state is simply the latest exact Boolean
observation. -/
def boolObservationOracleRun : TreeNode Bool → Bool :=
  fun node => node.getLast?.getD false

@[simp] theorem boolObservationOracleRun_nil :
    boolObservationOracleRun [] = false :=
  rfl

@[simp] theorem boolObservationOracleRun_append
    (node : TreeNode Bool) (observation : Bool) :
    boolObservationOracleRun (node ++ [observation]) = observation := by
  simp [boolObservationOracleRun]

/-- A legal rational policy may inspect the complete branch value even when
the advertised finite code is constant. -/
def boolObservationOraclePolicy :
    boolObservationOracleAutomaton.RationalTransitionPolicy where
  run := boolObservationOracleRun
  accepts := by
    constructor
    · exact ⟨rfl, fun _ => trivial⟩
    · intro branch
      refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
      · intro n
        exact ⟨n, le_rfl, rfl⟩
      · intro q _
        exact Nat.zero_le q
  successor := fun _ observation => observation
  successor_at := by
    intro node observation
    exact (boolObservationOracleRun_append node observation).symm
  legal_at := fun _ => trivial

/-- Constant public code. -/
def boolObservationUnitCode (_ : Bool) : Unit := ()

/-- Rationality over arbitrary observations alone does not provide the code
factorization required by a finite local summary update. -/
theorem boolObservationOraclePolicy_not_respectsUnitCode :
    ¬ boolObservationOraclePolicy.SuccessorRespectsCode
      boolObservationUnitCode := by
  intro hrespect
  have h := hrespect false false true rfl
  exact Bool.noConfusion h

end DistributedSynthesis
