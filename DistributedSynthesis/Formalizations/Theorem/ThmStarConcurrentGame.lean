/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype
import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState
import DistributedSynthesis.Formalizations.Theorem.ThmShadowRealizability
import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame

/-!
# The star game: the θ̄-coordinatized model as a finite concurrent game

This file defines `starGame`, the finite concurrent game of the full
`{←,→,↔}` model to which the Transport C engine
(`dynamicHierarchy_finiteStateSolvable_of_shadowCerts`) is applied.  Its
arena uses the following observations and actions:

* **Memoryless arena dispatch.**  Actions are read at *every* round: a
  process's output at a receiving round is its committed `recv` table
  applied to the pre-round core and both inputs; at a blind round it is
  its committed `blind` table applied to a private control and its own
  input.  Strategies that commit the same plan every round make the plan
  the whole program; the atom-indexed table arguments carry all
  information dispatch, so committing never requires knowing the atom.
* **The blind control enrichment.**  The private control `W` of a process
  is (re)entered from the pre-round core and both inputs at each of its
  receiving rounds and stepped on own inputs while blind.  A single
  `blind` table serves genuine and directly reversed blocks alike; this
  is what dissolves the `b_new` output ambiguity structurally: the rounds
  a process cannot distinguish by receipts are served by one table applied
  to identical arguments.
* **Constant observations.**  Both observation alphabets are `PUnit`.
  The information discipline is entirely arena-side: receive tables may
  read the full pre-round core because a receiving process learns the
  complete past in the model (`recv_view_determines_prefix`), while blind
  tables read only the own-input-driven control.  Receipt-faithful
  observation payloads are provably *wrong* here: any payload carrying
  live position data breaks perfect-recall determination after a role
  swap (the summary-merging mechanism), whereas constant observations
  make `DynamicHierarchy` hold strictly -- `starGame_dynamicHierarchy`
  below -- so the engine applies without any fringe compilation.

The core tracks the objective automaton state (so the game's parity
sequence is `A.priority` along the induced run; no block pasting), the
minimum-priority state since the last synchronization, the atom snapshot
of the last synchronization, the entry atom of the current directly
reversed chain, and the block-structure kind driven by the graph letters.
-/

namespace DistributedSynthesis

universe u

variable {In₁ In₂ Out₁ Out₂ : Type u}

namespace DetParityAutomaton

variable
  (A : DetParityAutomaton.{u, u} (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/-- Block-structure kinds: at a synchronization boundary, inside a genuine
block of either orientation, or inside a directly reversed block of either
orientation. -/
inductive StarKind where
  | boundary
  | leftBlock
  | rightBlock
  | revRight
  | revLeft
  deriving DecidableEq, Fintype, Inhabited

/-- The kind machine, driven by the round graphs: the own-orientation
letter continues a block, `both` synchronizes, and the opposite letter
directly reverses. -/
def starKindStep : StarKind -> Graph -> StarKind
  | _, Graph.both => StarKind.boundary
  | StarKind.boundary, Graph.left => StarKind.leftBlock
  | StarKind.boundary, Graph.right => StarKind.rightBlock
  | StarKind.leftBlock, Graph.left => StarKind.leftBlock
  | StarKind.leftBlock, Graph.right => StarKind.revRight
  | StarKind.rightBlock, Graph.right => StarKind.rightBlock
  | StarKind.rightBlock, Graph.left => StarKind.revLeft
  | StarKind.revRight, Graph.right => StarKind.revRight
  | StarKind.revRight, Graph.left => StarKind.revLeft
  | StarKind.revLeft, Graph.left => StarKind.revLeft
  | StarKind.revLeft, Graph.right => StarKind.revRight

/-- The public core of a star position: block-structure kind, objective
automaton state, minimum-priority state since the last synchronization,
the atom emitted by the last synchronization, and the entry atom of the
current directly reversed chain (meaningful in reversed kinds). -/
structure StarCore (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂)) where
  kind : StarKind
  state : A.State
  minState : A.State
  atom : A.State × A.State
  entry : A.State × A.State

/-- The core as a plain tuple, for the finiteness instances. -/
def starCoreEquiv :
    StarCore (In₁ := In₁) (In₂ := In₂) A ≃
      StarKind × A.State × A.State ×
        (A.State × A.State) × (A.State × A.State) where
  toFun core := (core.kind, core.state, core.minState, core.atom, core.entry)
  invFun data :=
    { kind := data.1, state := data.2.1, minState := data.2.2.1,
      atom := data.2.2.2.1, entry := data.2.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

/-- The initial core. -/
def starInitialCore : StarCore (In₁ := In₁) (In₂ := In₂) A where
  kind := StarKind.boundary
  state := A.initial
  minState := A.initial
  atom := (A.initial, A.initial)
  entry := (A.initial, A.initial)

/--
Process one's commitment.  `recv` fires at rounds process one receives
(graphs `left` and `both`, which it cannot distinguish: one table, no
graph argument); `blind` fires at `right` rounds through the private
control, which `enter` (re)initializes from the pre-round core at each
receiving round and `step` advances on own inputs.  `init` is the control
before the first receive.
-/
structure StarPlanOne (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂)) (W₁ W₂ : Type u) where
  init : W₁
  enter : W₁ -> W₂ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₁ × In₂ -> W₁
  step : W₁ -> In₁ -> W₁
  recv : W₁ -> W₂ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₁ × In₂ -> Out₁
  blind : W₁ -> In₁ -> Out₁

/-- Process two's commitment, the mirror: `recv` fires at graphs `right`
and `both` (indistinguishable to process two), `blind` at `left` rounds. -/
structure StarPlanTwo (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂)) (W₁ W₂ : Type u) where
  init : W₂
  enter : W₂ -> W₁ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₂ × In₁ -> W₂
  step : W₂ -> In₂ -> W₂
  recv : W₂ -> W₁ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₂ × In₁ -> Out₂
  blind : W₂ -> In₂ -> Out₂

variable {W₁ W₂ : Type u}

section Instances

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Fintype A.State]

instance : DecidableEq (StarCore (In₁ := In₁) (In₂ := In₂) A) :=
  (starCoreEquiv A).decidableEq

instance : Fintype (StarCore (In₁ := In₁) (In₂ := In₂) A) :=
  Fintype.ofEquiv _ (starCoreEquiv A).symm

set_option synthInstance.maxSize 512 in
instance [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂] :
    Fintype (StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :=
  Fintype.ofEquiv
    (W₁ ×
      (W₁ -> W₂ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₁ × In₂ -> W₁) ×
      (W₁ -> In₁ -> W₁) ×
      (W₁ -> W₂ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₁ × In₂ -> Out₁) ×
      (W₁ -> In₁ -> Out₁))
    {
      toFun := fun d => ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2⟩
      invFun := fun p => (p.init, p.enter, p.step, p.recv, p.blind)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

set_option synthInstance.maxSize 512 in
instance [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂] :
    Fintype (StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :=
  Fintype.ofEquiv
    (W₂ ×
      (W₂ -> W₁ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₂ × In₁ -> W₂) ×
      (W₂ -> In₂ -> W₂) ×
      (W₂ -> W₁ -> StarCore (In₁ := In₁) (In₂ := In₂) A -> In₂ × In₁ -> Out₂) ×
      (W₂ -> In₂ -> Out₂))
    {
      toFun := fun d => ⟨d.1, d.2.1, d.2.2.1, d.2.2.2.1, d.2.2.2.2⟩
      invFun := fun p => (p.init, p.enter, p.step, p.recv, p.blind)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
    }

end Instances

instance [Inhabited Out₁] [Inhabited W₁] :
    Inhabited (StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :=
  ⟨{
      init := default
      enter := fun _ _ _ _ => default
      step := fun control _ => control
      recv := fun _ _ _ _ => default
      blind := fun _ _ => default
    }⟩

instance [Inhabited Out₂] [Inhabited W₂] :
    Inhabited (StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂) :=
  ⟨{
      init := default
      enter := fun _ _ _ _ => default
      step := fun control _ => control
      recv := fun _ _ _ _ => default
      blind := fun _ _ => default
    }⟩

/-- A star state: the public core and the two private blind controls.
`none` marks a control that has not been entered yet; a blind round then
reads the current commitment's `init`. -/
abbrev StarState (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂)) (W₁ W₂ : Type u) :=
  StarCore (In₁ := In₁) (In₂ := In₂) A × Option W₁ × Option W₂

variable {A}

/-- Process one's output for the round: receive table at `left`/`both`
(one table, so the round's `b_old` bit cannot influence it), blind table
at `right`. -/
def starOutputOne (core : StarCore (In₁ := In₁) (In₂ := In₂) A)
    (w₁ : Option W₁) (w₂ : Option W₂)
    (a₁ : StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (a₂ : StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (round : EnvironmentRound In₁ In₂) : Out₁ :=
  match round.graph with
  | Graph.right => a₁.blind (w₁.getD a₁.init) round.inputOne
  | _ => a₁.recv (w₁.getD a₁.init) (w₂.getD a₂.init) core
      (round.inputOne, round.inputTwo)

/-- Process two's output for the round, the mirror. -/
def starOutputTwo (core : StarCore (In₁ := In₁) (In₂ := In₂) A)
    (w₁ : Option W₁) (w₂ : Option W₂)
    (a₁ : StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (a₂ : StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (round : EnvironmentRound In₁ In₂) : Out₂ :=
  match round.graph with
  | Graph.left => a₂.blind (w₂.getD a₂.init) round.inputTwo
  | _ => a₂.recv (w₂.getD a₂.init) (w₁.getD a₁.init) core
      (round.inputTwo, round.inputOne)

/-- The star transition: build the round record from the dispatched
outputs, advance the objective automaton, the kind machine, the boundary
bookkeeping, and the two private controls. -/
def starNext (state : StarState (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (a₁ : StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (a₂ : StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂)
    (round : EnvironmentRound In₁ In₂) :
    StarState (In₁ := In₁) (In₂ := In₂) A W₁ W₂ :=
  let core := state.1
  let w₁ := state.2.1
  let w₂ := state.2.2
  let out₁ := starOutputOne core w₁ w₂ a₁ a₂ round
  let out₂ := starOutputTwo core w₁ w₂ a₁ a₂ round
  let next :=
    A.step core.state
      { inputOne := round.inputOne
        inputTwo := round.inputTwo
        graph := round.graph
        outputOne := out₁
        outputTwo := out₂ }
  let sync := round.graph = Graph.both
  ({ kind := starKindStep core.kind round.graph
     state := next
     minState := if sync then next else A.minPriorityState core.minState next
     atom := if sync then (next, core.minState) else core.atom
     entry :=
       if core.kind = StarKind.leftBlock ∧ round.graph = Graph.right ∨
           core.kind = StarKind.rightBlock ∧ round.graph = Graph.left ∨
           core.kind = StarKind.revRight ∧ round.graph = Graph.left ∨
           core.kind = StarKind.revLeft ∧ round.graph = Graph.right then
         (next, A.minPriorityState core.minState next)
       else core.entry },
    (match round.graph with
      | Graph.right => some (a₁.step (w₁.getD a₁.init) round.inputOne)
      | _ =>
          some (a₁.enter (w₁.getD a₁.init) (w₂.getD a₂.init) core
            (round.inputOne, round.inputTwo))),
    (match round.graph with
      | Graph.left => some (a₂.step (w₂.getD a₂.init) round.inputTwo)
      | _ =>
          some (a₂.enter (w₂.getD a₂.init) (w₁.getD a₁.init) core
            (round.inputTwo, round.inputOne))))

variable (A)

/--
The star game.  Actions are star plans read at every round, Nature is the
environment round, observations are constant (`PUnit`): the information
discipline is arena-side, and perfect-recall information sets are
trivially comparable, so the game has strict dynamic hierarchical
information (`starGame_dynamicHierarchy`).
-/
def starGame (W₁ W₂ : Type u)
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
    [DecidableEq In₁] [DecidableEq In₂]
    [Fintype A.State] [DecidableEq A.State]
    [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂] :
    FiniteConcurrentGame.{u} where
  State := StarState (In₁ := In₁) (In₂ := In₂) A W₁ W₂
  Action1 := StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂
  Action2 := StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂
  Nature := EnvironmentRound In₁ In₂
  Observation1 := PUnit
  Observation2 := PUnit
  stateFinite := inferInstance
  action1Finite := inferInstance
  action2Finite := inferInstance
  natureFinite := inferInstance
  observation1Finite := inferInstance
  observation2Finite := inferInstance
  initial := (starInitialCore (In₁ := In₁) (In₂ := In₂) A, none, none)
  next := starNext
  observe1 _ := PUnit.unit
  observe2 _ := PUnit.unit
  priority state := A.priority state.1.state

section Hierarchy

variable {A}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype A.State] [DecidableEq A.State]
variable [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]

/-- Constant observation lists are determined by their length, and both
players' lists share the length of the state sequence. -/
theorem starGame_observations_length_eq
    (history : (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).PlayHistory) :
    history.observations1.length = history.observations2.length := by
  simp [FiniteConcurrentGame.PlayHistory.observations1,
    FiniteConcurrentGame.PlayHistory.observations2]

/-- **The star game has strict dynamic hierarchical information.**  Both
observation alphabets are `PUnit`, so an observation list carries exactly
its length; two histories with equal player-one lists have state
sequences of equal length, hence equal player-two lists. -/
theorem starGame_dynamicHierarchy :
    (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).DynamicHierarchy := by
  intro history
  left
  intro alternative halt
  have hlen : alternative.observations2.length =
      history.observations2.length := by
    rw [<- starGame_observations_length_eq alternative,
      <- starGame_observations_length_eq history, halt]
  apply List.ext_getElem hlen
  intro n h₁ h₂
  exact Subsingleton.elim (α := PUnit) _ _

end Hierarchy

section EngineApplication

variable {A}
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype A.State] [DecidableEq A.State]
variable [Fintype W₁] [DecidableEq W₁] [Fintype W₂] [DecidableEq W₂]
variable [Inhabited Out₁] [Inhabited Out₂] [Inhabited W₁] [Inhabited W₂]

instance : Inhabited (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Action1 :=
  ⟨(default : StarPlanOne (In₁ := In₁) (In₂ := In₂) A W₁ W₂)⟩

instance : Inhabited (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Action2 :=
  ⟨(default : StarPlanTwo (In₁ := In₁) (In₂ := In₂) A W₁ W₂)⟩

instance :
    Inhabited (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Observation1 :=
  ⟨PUnit.unit⟩

instance :
    Inhabited (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).Observation2 :=
  ⟨PUnit.unit⟩

/--
**The Transport C engine applies to the star game.**  Because the star
game has strict dynamic hierarchical information, its finite-state
synthesis certificate (finite-memory completeness plus an effective
decision of perfect-recall realizability) follows from exactly the two
published imports at its shadow arena: Reif/Berwanger--Mathew--van den
Bogaard leader-arena completeness and finite-parity-game solvability.
-/
theorem starGame_finiteStateSolvable
    (hc : (A.starGame (In₁ := In₁) (In₂ := In₂) W₁ W₂).ShadowLeaderArenaComplete)
    (hd : (A.starGame (In₁ := In₁) (In₂ := In₂)
        W₁ W₂).commonSignalShadowGame.LeaderArenaWinDecidable) :
    Nonempty (A.starGame (In₁ := In₁) (In₂ := In₂)
      W₁ W₂).FiniteStateSynthesisCertificate :=
  FiniteConcurrentGame.dynamicHierarchy_finiteStateSolvable_of_shadowCerts
    _ starGame_dynamicHierarchy hc hd

end EngineApplication

end DetParityAutomaton

end DistributedSynthesis
