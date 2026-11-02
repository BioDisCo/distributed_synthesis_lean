/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemRationalrun

/-!
# One-directional finite-memory theorem

This file packages the cited one-directional finite-memory theorem in the
interface form used by the main proof.  It also records the stronger
controller-exposing one-directional extraction as an explicit external
interface: the finite-game construction supplies finite local transducers, and
the checked proof only consumes that data through the fields below.
-/

namespace DistributedSynthesis

universe u v w x monitorLetter monitorId monitorState player output observation memory

/--
The one-directional block problem associated with a common boundary state.
The interface records the two semantic identifications used in the paper:
accepted trees are exactly realizable block strategies, and rational accepted
trees are exactly finite-summary strategies.
-/
structure OneDirectionalFiniteMemoryProblem
    (Boundary : Type u) (Branch : Type v) (Alphabet : Type w) where
  boundaryFinite : Fintype Boundary
  treeAutomaton : Boundary -> InputFreeParityTreeAutomaton.{v, w, x} Branch Alphabet
  realizable : Boundary -> Prop
  finiteSummaryRealizable : Boundary -> Prop
  accepts_iff_realizable :
    ∀ boundary,
      (∃ tree : LabeledTree Branch Alphabet,
        (treeAutomaton boundary).acceptsTree tree) ↔ realizable boundary
  rational_iff_finiteSummary :
    ∀ boundary, RationalAcceptedBy.{v, w, x} (treeAutomaton boundary) ↔
      finiteSummaryRealizable boundary
  finiteSummary_sound :
    ∀ boundary,
      finiteSummaryRealizable boundary ->
        ∃ tree : LabeledTree Branch Alphabet,
          (treeAutomaton boundary).acceptsTree tree

attribute [instance] OneDirectionalFiniteMemoryProblem.boundaryFinite

/--
A finite family of deterministic monitors reset at the opening synchronized
boundary of a one-directional block.

The paper calls these regular monitors.  In this interface, regularity is
represented by finite deterministic state spaces and a deterministic update.
The actual acceptance predicates tested by the monitors are part of the
soundness predicate of the extraction problem below.
-/
structure OneDirectionalDeterministicMonitorFamily
    (Letter : Type monitorLetter) where
  Monitor : Type monitorId
  monitorFinite : Fintype Monitor
  State : Monitor -> Type monitorState
  stateFinite : (monitor : Monitor) -> Fintype (State monitor)
  initial : (monitor : Monitor) -> State monitor
  update : (monitor : Monitor) -> State monitor -> Letter -> State monitor

attribute [instance] OneDirectionalDeterministicMonitorFamily.monitorFinite
attribute [instance] OneDirectionalDeterministicMonitorFamily.stateFinite

/--
The finite local transducer strategy promised by the controller-exposing
one-directional extraction.

For each process/player, `Observation` is the finite current-observation
alphabet `Oᵢ`, `Memory` is the finite memory set `Mᵢ`, `initial` is the memory
chosen for the fixed boundary state, `update` is the deterministic local memory
transition, and `choose` is the local output table.
-/
structure OneDirectionalLocalTransducerStrategy
    (Player : Type player) (Output : Player -> Type output) where
  Observation : Player -> Type observation
  observationFinite : (i : Player) -> Fintype (Observation i)
  Memory : Player -> Type memory
  memoryFinite : (i : Player) -> Fintype (Memory i)
  initial : (i : Player) -> Memory i
  update : (i : Player) -> Memory i -> Observation i -> Memory i
  choose : (i : Player) -> Memory i -> Observation i -> Output i

attribute [instance] OneDirectionalLocalTransducerStrategy.observationFinite
attribute [instance] OneDirectionalLocalTransducerStrategy.memoryFinite

/--
External interface for Lemma `lem:berardcontrollerextraction`.

The base `OneDirectionalFiniteMemoryProblem` still records the Bérard
strategy-tree/rational-run problem.  The additional fields record the fixed
finite monitor family and the semantic predicate saying that a local
transducer strategy wins the one-directional block game and updates those
monitors correctly.

The field `controller_extraction` is the external finite-game theorem used by
the paper: whenever the base one-directional block problem is realizable at a
boundary, there is a finite local transducer strategy satisfying the semantic
predicate.  The finite-game synthesis proof that produces this field is not
derived from `TransitionRationalAcceptedBy` in Lean.
-/
structure OneDirectionalControllerExtractionProblem
    (Boundary : Type u) (Branch : Type v) (Alphabet : Type w)
    (MonitorLetter : Type monitorLetter)
    (Player : Type player) (Output : Player -> Type output) where
  base : OneDirectionalFiniteMemoryProblem.{u, v, w, x} Boundary Branch Alphabet
  monitors :
    OneDirectionalDeterministicMonitorFamily.{monitorLetter, monitorId, monitorState}
      MonitorLetter
  localWinsAndUpdates :
    Boundary ->
      OneDirectionalLocalTransducerStrategy.{player, output, observation, memory}
        Player Output -> Prop
  controller_extraction :
    ∀ boundary,
      base.realizable boundary ->
        ∃ strategy :
          OneDirectionalLocalTransducerStrategy.{player, output, observation, memory}
            Player Output,
          localWinsAndUpdates boundary strategy

namespace OneDirectionalControllerExtractionProblem

/-- The local-transducer realizability predicate exposed by the extraction interface. -/
def locallyRealizable
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    {MonitorLetter : Type monitorLetter}
    {Player : Type player} {Output : Player -> Type output}
    (problem :
      OneDirectionalControllerExtractionProblem.{u, v, w, x, monitorLetter,
        monitorId, monitorState, player, output, observation, memory}
        Boundary Branch Alphabet MonitorLetter Player Output)
    (boundary : Boundary) : Prop :=
  ∃ strategy :
    OneDirectionalLocalTransducerStrategy.{player, output, observation, memory}
      Player Output,
    problem.localWinsAndUpdates boundary strategy

end OneDirectionalControllerExtractionProblem

/--
Theorem `thm:berardfinitememory`: for every boundary state, realizability of
the one-directional block problem is equivalent to realizability by a
finite-summary strategy.
-/
theorem berard_finite_memory
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    (problem : OneDirectionalFiniteMemoryProblem.{u, v, w, x} Boundary Branch Alphabet)
    (boundary : Boundary) :
    problem.realizable boundary ↔ problem.finiteSummaryRealizable boundary := by
  constructor
  · intro hrealizable
    have haccepts :
        ∃ tree : LabeledTree Branch Alphabet,
          (problem.treeAutomaton boundary).acceptsTree tree :=
      (problem.accepts_iff_realizable boundary).2 hrealizable
    have hrational : RationalAcceptedBy (problem.treeAutomaton boundary) :=
      rational_run (problem.treeAutomaton boundary) haccepts
    exact (problem.rational_iff_finiteSummary boundary).1 hrational
  · intro hfinite
    have haccepts := problem.finiteSummary_sound boundary hfinite
    exact (problem.accepts_iff_realizable boundary).1 haccepts

/--
Controller-exposing form of the one-directional Bérard construction.

From a realizable one-directional block problem, the accepted tree can be
chosen with an explicit finite transition graph.  This is the form needed by
the no-direct reachable-controller proof.
-/
theorem berard_transition_rational_controller_of_realizable
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    (problem : OneDirectionalFiniteMemoryProblem.{u, v, w, x} Boundary Branch Alphabet)
    (boundary : Boundary)
    (hrealizable : problem.realizable boundary) :
    TransitionRationalAcceptedBy (problem.treeAutomaton boundary) := by
  have haccepts :
      ∃ tree : LabeledTree Branch Alphabet,
        (problem.treeAutomaton boundary).acceptsTree tree :=
    (problem.accepts_iff_realizable boundary).2 hrealizable
  exact transition_rational_run (problem.treeAutomaton boundary) haccepts

/--
Finite-summary version of the controller-exposing Bérard construction.
-/
theorem berard_transition_rational_controller_of_finiteSummary
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    (problem : OneDirectionalFiniteMemoryProblem.{u, v, w, x} Boundary Branch Alphabet)
    (boundary : Boundary)
    (hfinite : problem.finiteSummaryRealizable boundary) :
    TransitionRationalAcceptedBy (problem.treeAutomaton boundary) := by
  have haccepts := problem.finiteSummary_sound boundary hfinite
  exact transition_rational_run (problem.treeAutomaton boundary) haccepts

/--
Lemma `lem:berardcontrollerextraction`: controller-exposing one-directional
extraction.

For a one-directional block problem equipped with a finite deterministic monitor
family, realizability at a boundary yields finite local transducers whose
semantic predicate records winningness and correct monitor updates.
-/
theorem berard_controller_exposing_one_directional_extraction
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    {MonitorLetter : Type monitorLetter}
    {Player : Type player} {Output : Player -> Type output}
    (problem :
      OneDirectionalControllerExtractionProblem.{u, v, w, x, monitorLetter,
        monitorId, monitorState, player, output, observation, memory}
        Boundary Branch Alphabet MonitorLetter Player Output)
    (boundary : Boundary)
    (hrealizable : problem.base.realizable boundary) :
    problem.locallyRealizable boundary :=
  problem.controller_extraction boundary hrealizable

/--
Finite-summary version of the controller-exposing extraction.

This is often the convenient downstream form: once the ordinary Bérard theorem
has converted finite-summary realizability back to realizability, the external
controller extraction supplies the local transducers.
-/
theorem berard_controller_exposing_one_directional_extraction_of_finiteSummary
    {Boundary : Type u} {Branch : Type v} {Alphabet : Type w}
    {MonitorLetter : Type monitorLetter}
    {Player : Type player} {Output : Player -> Type output}
    (problem :
      OneDirectionalControllerExtractionProblem.{u, v, w, x, monitorLetter,
        monitorId, monitorState, player, output, observation, memory}
        Boundary Branch Alphabet MonitorLetter Player Output)
    (boundary : Boundary)
    (hfinite : problem.base.finiteSummaryRealizable boundary) :
    problem.locallyRealizable boundary := by
  exact problem.controller_extraction boundary
    ((berard_finite_memory problem.base boundary).2 hfinite)

end DistributedSynthesis
