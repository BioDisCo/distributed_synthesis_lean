/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefNodeRationalization

/-!
# The exact direction quotient needed by a source-free rational policy

The source-free belief successor makes the *belief-code* component of every
child a function of the current code, the chosen move, and the environment
direction.  A rational transition policy nevertheless also carries the
finite universal-thread control.  That control advances on the full letter
`(move, direction)`.

Consequently source-freeness alone does not make the complete finite
controller successor independent of the raw direction.  This file identifies
the exact missing local law: on every fibre of the next-belief-code map, the
universal-thread DPA step must be constant.  The law is equivalent to the
existence of precisely the desired finite successor table

`current finite state -> chosen move -> next belief code -> next finite state`.

Thus this is both a positive adapter and a fail-fast boundary theorem.  A
single pair of directions with equal next belief code but different monitor
successors refutes the factorization; no acceptance or rationality argument
can repair that local collision.
-/

namespace DistributedSynthesis

universe u v w x z

section

variable {Direction : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode]

/-- The finite state actually carried by the source-free run automaton: the
public belief code together with the universal hidden-thread control. -/
abbrev SourceFreeBeliefFiniteState
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction)) :=
  BeliefCode × U.universalRunDPA.State

/-- The smallest local-observability law which allows the universal-thread
control to forget the raw direction after the next belief code is known.

The current thread control is quantified explicitly: it is part of the
finite controller state, not part of the public belief code. -/
def SourceFreeBeliefThreadStepObservable
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (next : BeliefCode → Move → Direction → BeliefCode) : Prop :=
  ∀ (code : BeliefCode) (control : U.universalRunDPA.State)
      (move : Move) (left right : Direction),
    next code move left = next code move right →
      U.universalRunDPA.step control (move, left) =
        U.universalRunDPA.step control (move, right)

/-- Exact factorization requested by a finite local controller.  It may use
the current finite state and the already chosen move, but its environment
argument is only the next finite belief code. -/
def SourceFreeBeliefControllerFactorizes
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (next : BeliefCode → Move → Direction → BeliefCode) : Prop :=
  ∃ controllerNext :
      SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U → Move →
        BeliefCode → SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U,
    ∀ state move direction,
      controllerNext state move (next state.1 move direction) =
        (next state.1 move direction,
          U.universalRunDPA.step state.2 (move, direction))

omit [Fintype BeliefCode] in
/-- Fibre-constancy of the monitor step is exactly equivalent to existence of
the desired finite controller successor table.  Values at next codes outside
the image of a direction are completed with the DPA initial state. -/
theorem sourceFreeBeliefThreadStepObservable_iff_controllerFactorizes
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (next : BeliefCode → Move → Direction → BeliefCode) :
    SourceFreeBeliefThreadStepObservable U next ↔
      SourceFreeBeliefControllerFactorizes U next := by
  classical
  constructor
  · intro hobservable
    let monitorNext : BeliefCode → U.universalRunDPA.State → Move →
        BeliefCode → U.universalRunDPA.State :=
      fun code control move childCode =>
        if h : ∃ direction, next code move direction = childCode then
          U.universalRunDPA.step control (move, Classical.choose h)
        else
          U.universalRunDPA.initial
    let controllerNext :
        SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U → Move →
          BeliefCode →
            SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U :=
      fun state move childCode =>
        (childCode, monitorNext state.1 state.2 move childCode)
    refine ⟨controllerNext, ?_⟩
    intro state move direction
    apply Prod.ext
    · rfl
    · change monitorNext state.1 state.2 move
          (next state.1 move direction) = _
      simp only [monitorNext]
      split
      next h =>
        apply hobservable state.1 state.2 move
        exact Classical.choose_spec h
      next h =>
        exact (h ⟨direction, rfl⟩).elim
  · rintro ⟨controllerNext, hcontroller⟩
    intro code control move left right hcode
    have hpairs :
        (next code move left,
            U.universalRunDPA.step control (move, left)) =
          (next code move right,
            U.universalRunDPA.step control (move, right)) := by
      calc
        (next code move left,
            U.universalRunDPA.step control (move, left)) =
            controllerNext (code, control) move (next code move left) :=
              (hcontroller (code, control) move left).symm
        _ = controllerNext (code, control) move (next code move right) := by
              rw [hcode]
        _ = (next code move right,
            U.universalRunDPA.step control (move, right)) :=
              hcontroller (code, control) move right
    exact congrArg Prod.snd hpairs

omit [Fintype BeliefCode] in
/-- A same-next-code/different-monitor-step collision is an exact local
refutation of the desired finite controller factorization. -/
theorem not_sourceFreeBeliefControllerFactorizes_of_collision
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (next : BeliefCode → Move → Direction → BeliefCode)
    (code : BeliefCode) (control : U.universalRunDPA.State) (move : Move)
    (left right : Direction)
    (hcode : next code move left = next code move right)
    (hstep : U.universalRunDPA.step control (move, left) ≠
      U.universalRunDPA.step control (move, right)) :
    ¬ SourceFreeBeliefControllerFactorizes U next := by
  intro hfactor
  have hobservable :=
    (sourceFreeBeliefThreadStepObservable_iff_controllerFactorizes U next).2
      hfactor
  exact hstep (hobservable code control move left right hcode)

/-! ## What a rational transition policy supplies unconditionally -/

/-- At every node of a rational policy, source-freeness supplies a move for
which the two successor projections have the advertised equations.  This is
the strongest unconditional decomposition: the monitor projection still
mentions the raw direction. -/
theorem InputFreeRunParityTreeAutomaton.RationalTransitionPolicy.exists_sourceFreeMove_components_at
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
        |>.RationalTransitionPolicy)
    (node : TreeNode Direction) :
    ∃ move : Move,
      Valid (policy.run node).1 move ∧
        ∀ direction,
          (policy.successor (policy.run node) direction).1 =
              next (policy.run node).1 move direction ∧
            (policy.successor (policy.run node) direction).2 =
              U.universalRunDPA.step (policy.run node).2 (move, direction) := by
  rcases policy.legal_at node with ⟨move, hvalid, hsuccessor⟩
  refine ⟨move, hvalid, ?_⟩
  intro direction
  have heq := hsuccessor direction
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- Under the exact local-observability law, the policy successor at every
reachable node rewrites through the finite controller table and no longer
mentions the raw direction except while computing the next belief code. -/
theorem InputFreeRunParityTreeAutomaton.RationalTransitionPolicy.exists_sourceFreeMove_factor_at
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (policy :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
        |>.RationalTransitionPolicy)
    (controllerNext :
      SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U → Move →
        BeliefCode → SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U)
    (hcontroller : ∀ state move direction,
      controllerNext state move (next state.1 move direction) =
        (next state.1 move direction,
          U.universalRunDPA.step state.2 (move, direction)))
    (node : TreeNode Direction) :
    ∃ move : Move,
      Valid (policy.run node).1 move ∧
        ∀ direction,
          policy.successor (policy.run node) direction =
            controllerNext (policy.run node) move
              (next (policy.run node).1 move direction) := by
  rcases policy.legal_at node with ⟨move, hvalid, hsuccessor⟩
  refine ⟨move, hvalid, ?_⟩
  intro direction
  exact (hsuccessor direction).trans
    (hcontroller (policy.run node) move direction).symm

/-! ## Packaged adapter from `HasRationalRun` -/

/-- A rational policy together with the finite successor table justified by
the local-observability law. -/
structure SourceFreeFactoredRationalTransitionPolicy
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode) where
  policy :
    (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
      |>.RationalTransitionPolicy
  controllerNext :
    SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U → Move →
      BeliefCode → SourceFreeBeliefFiniteState (BeliefCode := BeliefCode) U
  controllerNext_spec : ∀ state move direction,
    controllerNext state move (next state.1 move direction) =
      (next state.1 move direction,
        U.universalRunDPA.step state.2 (move, direction))

/-- `HasRationalRun` plus the exact local-observability law yields the clean
finite controller package.  Neither premise alone implies the other. -/
theorem nonempty_sourceFreeFactoredRationalTransitionPolicy_of_hasRationalRun
    (U : FiniteThreadSystem.{max u v, w, x} (Move × Direction))
    (initialCode : BeliefCode)
    (Valid : BeliefCode → Move → Prop)
    (next : BeliefCode → Move → Direction → BeliefCode)
    (hrational :
      (sourceFreeBeliefNodeRunAutomaton U initialCode Valid next)
        |>.HasRationalRun)
    (hobservable : SourceFreeBeliefThreadStepObservable U next) :
    Nonempty
      (SourceFreeFactoredRationalTransitionPolicy U initialCode Valid next) := by
  rcases InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
      _ hrational with ⟨policy⟩
  rcases
      (sourceFreeBeliefThreadStepObservable_iff_controllerFactorizes U next).1
        hobservable with
    ⟨controllerNext, hcontroller⟩
  exact ⟨{
    policy := policy
    controllerNext := controllerNext
    controllerNext_spec := hcontroller
  }⟩

end

end DistributedSynthesis
