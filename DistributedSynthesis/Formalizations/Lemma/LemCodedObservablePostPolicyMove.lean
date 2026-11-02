/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemCodedObservableInputFreeRationalization

/-!
# Recovering the raw joint move after one global rationalization

`codedObservableInputFreeRunAutomaton` deliberately permits an arbitrary
(possibly infinite) move type.  This is the correct place to put a
simultaneous family of semantic block lambdas: the automaton state remains
finite, while the move occurs only under the existential transition law.

This file supplies the post-policy inversion needed by the paired-profiled
recut.  At every reachable finite policy state it recovers one literal raw
move whose response to *every* exact observation is the successor of that
same rational policy.  Later finite block narrowing can therefore check
closes against `AllowedTarget`; it never compares with an independently
rationalized family controller and does not require the successor to factor
through the public code.
-/

namespace DistributedSynthesis

universe u v w x z

section

variable {Observation : Type u} {Move : Type v} {Code : Type z}
variable [Fintype Code]
variable
  (S : FiniteThreadSystem.{max u v, w, x} (Move × Observation))
  (initialObservation : Observation) (code : Observation → Code)
  (Valid : Code → Move → Prop)

namespace CodedObservablePostPolicy

noncomputable abbrev Automaton :=
  codedObservableInputFreeRunAutomaton S initialObservation code Valid

/-- A finite policy state occurs in the one globally rationalized run. -/
def Reachable
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    (state : CodedObservableInputFreeState (Code := Code) S) : Prop :=
  ∃ node, policy.run node = state

/-- The raw move selected at one reachable finite policy state.  No finiteness
instance is required for `Move`. -/
structure SelectedMoveAt
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    (state : CodedObservableInputFreeState (Code := Code) S) where
  move : Move
  valid : Valid state.1 move
  successor_eq : ∀ observation,
    policy.successor state observation =
      (code observation,
        S.universalRunDPA.step state.2 (move, observation))

/-- Invert the existential move in `delta` at a reachable state of the one
rational policy.  The returned equality is simultaneous over all exact
observations. -/
theorem nonempty_selectedMoveAt_of_reachable
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    (state : CodedObservableInputFreeState (Code := Code) S)
    (hreachable : Reachable S initialObservation code Valid policy state) :
    Nonempty (SelectedMoveAt S initialObservation code Valid policy state) := by
  rcases hreachable with ⟨node, hnode⟩
  have hlegal := policy.legal_at node
  rw [hnode] at hlegal
  rcases hlegal with ⟨move, hvalid, hsuccessor⟩
  exact ⟨⟨move, hvalid, hsuccessor⟩⟩

/-- Finite-image edge relation used by post-policy block regularization.  The
exact observation remains a proof witness and is not a local leader or
orientation signal. -/
def AllowedTarget
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    (source target : CodedObservableInputFreeState (Code := Code) S) : Prop :=
  ∃ observation, policy.successor source observation = target

/-- Policy-image edges preserve reachability. -/
theorem reachable_of_allowedTarget
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    {source target : CodedObservableInputFreeState (Code := Code) S}
    (hsource : Reachable S initialObservation code Valid policy source)
    (hedge : AllowedTarget S initialObservation code Valid policy source
      target) :
    Reachable S initialObservation code Valid policy target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hedge with ⟨observation, hobservation⟩
  refine ⟨node ++ [observation], ?_⟩
  rw [← policy.successor_at node observation, hnode, hobservation]

/-- Arbitrary mixing of edges from the finite image of one rational policy
remains accepting.  This is the generic form of the old paired-entry
`accepts_of_allowed_path` argument and is what makes post-policy block
regularization sound. -/
theorem accepts_of_allowedTarget_path
    (policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy)
    (states : Nat → CodedObservableInputFreeState (Code := Code) S)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n,
      AllowedTarget S initialObservation code Valid policy (states n)
        (states (n + 1))) :
    NatSeqMinEvenParity (fun n ↦
      (Automaton S initialObservation code Valid).priority (states n)) := by
  classical
  choose branch hbranch using hstep
  have hstates : ∀ n, states n = policy.run (branchNode branch n) := by
    intro n
    induction n with
    | zero => exact hzero
    | succ n ih =>
        rw [branchNode, ← policy.successor_at (branchNode branch n) (branch n),
          ← ih]
        exact (hbranch n).symm
  have haccepts := policy.accepts.2 branch
  convert haccepts using 1
  funext n
  rw [hstates n]

/-- Every literal response of the recovered raw move is an edge of the same
outer rational policy. -/
theorem SelectedMoveAt.allowedTarget
    {policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy}
    {state : CodedObservableInputFreeState (Code := Code) S}
    (selected : SelectedMoveAt S initialObservation code Valid policy state)
    (observation : Observation) :
    AllowedTarget S initialObservation code Valid policy state
      (code observation,
        S.universalRunDPA.step state.2 (selected.move, observation)) := by
  exact ⟨observation, selected.successor_eq observation⟩

/-- The package produced after the single global basis call.  It retains one
finite rational policy and exposes raw moves only by legality inversion at
its reachable states. -/
structure Package where
  policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy
  selected : ∀ state,
    Reachable S initialObservation code Valid policy state →
      Nonempty (SelectedMoveAt S initialObservation code Valid policy state)

/-- One exact-observation move tree, one hidden-thread acceptance proof, and
one `RationalRunBasis` call produce the post-policy package. -/
theorem nonempty_package_of_tree
    (tree : LabeledTree Observation Move)
    (hvalid : CodedObservableMovesValid initialObservation code Valid tree)
    (hbundle : ∀ branch : Nat → Observation,
      S.universalRunDPA.Accepts (observableThreadWord tree branch))
    (basis : (Automaton S initialObservation code Valid).RationalRunBasis) :
    Nonempty (Package S initialObservation code Valid) := by
  have hrational : (Automaton S initialObservation code Valid).HasRationalRun :=
    codedObservable_hasRationalRun S initialObservation code Valid tree hvalid
      hbundle basis
  rcases InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      (Automaton S initialObservation code Valid) hrational with ⟨policy⟩
  refine ⟨⟨policy, ?_⟩⟩
  intro state hreachable
  exact nonempty_selectedMoveAt_of_reachable S initialObservation code Valid
    policy state hreachable

/-! ## Explicit joint-move specialization -/

/-- Right and left raw semantic families can be selected as one outer move.
Both projections then share the `successor_eq` field of one
`SelectedMoveAt`; no equality between separate rational choices is needed. -/
abbrev JointMove (RightMove : Type v) (LeftMove : Type v) :=
  RightMove × LeftMove

/-- The two projections occur literally in the one letter used by the outer
policy successor.  This is the equation consumed by the two post-policy block
narrowings. -/
theorem SelectedMoveAt.joint_successor_eq
    {RightMove LeftMove : Type v}
    {S : FiniteThreadSystem.{max u v, w, x}
      (JointMove RightMove LeftMove × Observation)}
    {initialObservation : Observation} {code : Observation → Code}
    {Valid : Code → JointMove RightMove LeftMove → Prop}
    {policy : (Automaton S initialObservation code Valid).RationalTransitionPolicy}
    {state : CodedObservableInputFreeState (Code := Code) S}
    (selected : SelectedMoveAt S initialObservation code Valid policy state)
    (observation : Observation) :
    policy.successor state observation =
      (code observation,
        S.universalRunDPA.step state.2
          ((selected.move.1, selected.move.2), observation)) :=
  selected.successor_eq observation

end CodedObservablePostPolicy

end

end DistributedSynthesis
