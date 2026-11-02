/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmSummaryHierarchicalGame
import DistributedSynthesis.Formalizations.Lemma.LemDelayonehierarchy

/-!
# The delay-one view hierarchy of the summary hierarchical game

This file supplies the hierarchy applicability fact of the corrected
Theorem-10 platform (`ThmSummaryHierarchicalGame.lean`) for paper
`prop:starcomplete`, in the form the model actually provides: the delay-one,
fringe-aware transport of Proposition `prop:dynhier` and Lemma
`lem:delayonehierarchy` to the concrete arena.

**Why not the strict form.**  The strict per-history statement
`SummaryGameDynamicHierarchy A M` -- comparability of the two full
summary-observation lists at every arena history -- is refutable for every
summary automaton `M` that distinguishes anything:

* at a history whose pending round is one-way, say `left`, the receiver's
  observation cannot separate `left` from `both` (its `M.advance` component
  is literally the same function in both cases -- the one-bit fringe of
  `thm:onebitfringe`), while the sender's observation differs (`stepNoRecv`
  versus `stepRecv`); and the sender never sees the receiver-side input, so
  neither side determines the other;
* no bounded delay repairs this at summary granularity: extending the
  `left`/`both` fork by `right` rounds keeps player one's observations equal
  while player two's differ at every position after the fork, and finite
  summary folds must merge distinct player-one observation prefixes
  (pigeonhole), so player-two-equal alternatives exist whose player-one lists
  differ unboundedly deep.

**What is true.**  The hierarchy of the model lives one granularity below,
at the level of views (`def:views`), where a receive stores the sender's
entire prior view.  Transported to the arena through the platform's own
absorption laws (the tracked summary pair is the pair of view folds,
`SummaryTracking.summaryOf_recordFold`), it becomes the following delay-one,
fringe-aware statement, proved here:

* each side's pending view determines its own full observation list
  (`summaryGame_observations_one/two`: the observation list is the `M.read`
  image of the view's ancestor chain);
* the pending round's **receiver's view determines the sender's settled
  observation prefix** -- everything but the last, still-fringed entry
  (`summaryGame_viewOne_determines_settledTwo` and its mirror), with the
  same-graph one-way cases discharged by `lem:delayonehierarchy`
  (`delayOneHierarchy_left/right/both`) and the mixed `left`/`both` cases by
  the receive-constructor injectivity that `thm:onebitfringe` leaves intact;
* the packaged disjunction `summaryGameDelayOneViewHierarchy_holds`: at every
  arena history one of the two directions holds, the direction given by the
  pending graph, and the underlying containment is exactly `prop:dynhier`.

This is the exact applicability input for the finite-state engine: per the
interface file (`ThmDynamicHierarchyFiniteState.lean`), a bounded-delay
hierarchy determines the settled prefix, and the engine must remove the
delayed suffix by a finite-fringe compilation before the strict form is
invoked.
-/

namespace DistributedSynthesis

universe u v x y

section ViewChain

variable {In₁ : Type u} {In₂ : Type v}

/-- The ancestor chain of a view: the view itself preceded by all its own
earlier views.  A process's perfect-recall observation history is the
`M.read` image of this chain, because each view retains its predecessor. -/
def View.selfChain : {p : Proc} -> View In₁ In₂ p -> List (View In₁ In₂ p)
  | _, .empty p => [.empty p]
  | _, .recv prevSelf inputSelf prevOther inputOther =>
      View.selfChain prevSelf ++ [.recv prevSelf inputSelf prevOther inputOther]
  | _, .noRecv prevSelf inputSelf =>
      View.selfChain prevSelf ++ [.noRecv prevSelf inputSelf]

end ViewChain

section NextViewChain

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- One environment move extends process one's ancestor chain by the next
view. -/
theorem selfChain_nextView_one
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂) :
    (nextView Proc.one h env).selfChain =
      (currentView Proc.one h).selfChain ++ [nextView Proc.one h env] := by
  cases hGraph : env.graph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph, View.selfChain,
      currentView]

/-- One environment move extends process two's ancestor chain by the next
view. -/
theorem selfChain_nextView_two
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂) :
    (nextView Proc.two h env).selfChain =
      (currentView Proc.two h).selfChain ++ [nextView Proc.two h env] := by
  cases hGraph : env.graph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph, View.selfChain,
      currentView]

/-- Views ignore outputs: appending the realized record of an environment
move yields exactly the next view. -/
theorem currentView_append_environmentRecord (d : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂)
    (outputOne : Out₁) (outputTwo : Out₂) :
    currentView d
        (History.append h
          { inputOne := env.inputOne
            inputTwo := env.inputTwo
            graph := env.graph
            outputOne := outputOne
            outputTwo := outputTwo }) =
      nextView d h env := by
  cases d <;> cases hGraph : env.graph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph, currentView,
      viewPair_append, advanceViews]

/-- The receiver's next view on a `left` or `both` round is the receive
constructor on the two settled views; the graph itself is not recorded --
this is the one-bit fringe of `thm:onebitfringe`. -/
theorem nextView_one_recv_shape
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂)
    (hrecv : env.graph = Graph.left ∨ env.graph = Graph.both) :
    nextView Proc.one h env =
      View.recv (currentView Proc.one h) (.inl env.inputOne)
        (currentView Proc.two h) (.inr env.inputTwo) := by
  rcases hrecv with hGraph | hGraph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph, currentView]

/-- The mirror shape for process two on a `right` or `both` round. -/
theorem nextView_two_recv_shape
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂)
    (hrecv : env.graph = Graph.right ∨ env.graph = Graph.both) :
    nextView Proc.two h env =
      View.recv (currentView Proc.two h) (.inr env.inputTwo)
        (currentView Proc.one h) (.inl env.inputOne) := by
  rcases hrecv with hGraph | hGraph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph, currentView]

/-- A next view is never the empty view. -/
theorem nextView_ne_empty (d : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂) (env : EnvironmentRound In₁ In₂) :
    nextView d h env ≠ View.empty d := by
  cases d <;> cases hGraph : env.graph <;>
    simp [nextView, advanceViewsWithEnvironment, hGraph]

end NextViewChain

namespace FiniteConcurrentGame

/-- Dropping the one-round delay window from an extended trace recovers the
settled trace. -/
theorem settledPrefix_one_append {α : Type u}
    (trace : List α) (last : α) :
    settledPrefix 1 (trace ++ [last]) = trace := by
  simp [settledPrefix]

end FiniteConcurrentGame

namespace DetParityAutomaton

open FiniteEpochTransformer FiniteConcurrentGame

variable {In₁ In₂ Out₁ Out₂ : Type u}
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)

/-- The environment round left pending by an arena history. -/
def summaryGamePending :
    (A.summaryHierarchicalGame M).PlayHistory ->
      Option (EnvironmentRound In₁ In₂)
  | .initial => none
  | .step _ _ _ nature => some nature

/-- The real rounds an arena history has absorbed: each step records the
previously pending round with the two chosen outputs; the first step absorbs
nothing (Nature only installs round zero). -/
def summaryGameRecorded :
    (A.summaryHierarchicalGame M).PlayHistory ->
      History In₁ In₂ Graph Out₁ Out₂
  | .initial => []
  | .step history outputOne outputTwo _ =>
      match summaryGamePending A M history with
      | none => summaryGameRecorded history
      | some pending =>
          History.append (summaryGameRecorded history)
            { inputOne := pending.inputOne
              inputTwo := pending.inputTwo
              graph := pending.graph
              outputOne := outputOne
              outputTwo := outputTwo }

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Only the empty arena history has no pending round. -/
theorem summaryGamePending_eq_none_iff
    (history : (A.summaryHierarchicalGame M).PlayHistory) :
    summaryGamePending A M history = none ↔ history = .initial := by
  cases history <;> simp [summaryGamePending]

/-- The pending view of a side: its view of the recorded history extended by
the pending environment round; the empty view at the empty history. -/
def summaryGamePendingView (d : Proc) :
    (A.summaryHierarchicalGame M).PlayHistory -> View In₁ In₂ d
  | .initial => View.empty d
  | .step history outputOne outputTwo nature =>
      nextView d
        (summaryGameRecorded A M (.step history outputOne outputTwo nature))
        nature

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- At a pending arena history, the pending view is the next view of the
recorded history under the pending round. -/
theorem summaryGamePendingView_eq_nextView (d : Proc)
    (history : (A.summaryHierarchicalGame M).PlayHistory)
    (pending : EnvironmentRound In₁ In₂)
    (hpending : summaryGamePending A M history = some pending) :
    summaryGamePendingView A M d history =
      nextView d (summaryGameRecorded A M history) pending := by
  cases history with
  | initial => simp [summaryGamePending] at hpending
  | step history outputOne outputTwo nature =>
      obtain rfl : nature = pending := by
        simpa [summaryGamePending] using hpending
      rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- **Realization invariant**: the last arena state carries exactly the
record fold of the recorded real history, paired with the pending round. -/
theorem summaryGame_lastState
    (history : (A.summaryHierarchicalGame M).PlayHistory) :
    history.lastState =
      match summaryGamePending A M history with
      | none => Sum.inl Unit.unit
      | some pending =>
          Sum.inr
            (recordFold (A.summaryGameTransformer M)
              (A.summaryInitialBoundary M) (summaryGameRecorded A M history),
              pending) := by
  induction history with
  | initial => rfl
  | step history outputOne outputTwo nature ih =>
      cases hpending : summaryGamePending A M history with
      | none =>
          have hinit : history = .initial :=
            (summaryGamePending_eq_none_iff A M history).mp hpending
          subst hinit
          rfl
      | some pending =>
          simp only [hpending] at ih
          have hrec :
              summaryGameRecorded A M
                  (.step history outputOne outputTwo nature) =
                History.append (summaryGameRecorded A M history)
                  { inputOne := pending.inputOne
                    inputTwo := pending.inputTwo
                    graph := pending.graph
                    outputOne := outputOne
                    outputTwo := outputTwo } := by
            simp [summaryGameRecorded, hpending]
          show
            (A.summaryHierarchicalGame M).next history.lastState
                outputOne outputTwo nature =
              Sum.inr
                (recordFold (A.summaryGameTransformer M)
                  (A.summaryInitialBoundary M)
                  (summaryGameRecorded A M
                    (.step history outputOne outputTwo nature)),
                  nature)
          rw [ih, summaryHierarchicalGame_next_pending, hrec,
            recordFold_append]
          rfl

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [Inhabited In₁] [Inhabited In₂]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- The adequacy law at the arena: the observation of side `d` in a pending
state reached by a recorded history is the summary read of its next view.
This is the platform's absorption lemma (`summaryOf_recordFold`) composed
with the joint one-round view update. -/
theorem fringeDecoder_recordFold (d : Proc)
    (h : History In₁ In₂ Graph Out₁ Out₂)
    (env : EnvironmentRound In₁ In₂) :
    (A.summaryGameTracking M).fringeDecoder d
        (recordFold (A.summaryGameTransformer M)
          (A.summaryInitialBoundary M) h) env =
      M.read (nextView d h env) := by
  unfold FiniteEpochTransformer.SummaryTracking.fringeDecoder
  rw [(A.summaryGameTracking M).summaryOf_recordFold
      (A.summaryInitialBoundary M) rfl h]
  have hadvance :
      M.advance (M.readPair (viewPair h)) env.graph env.inputOne
          env.inputTwo =
        M.readPair (advanceViewsWithEnvironment (viewPair h) env) :=
    (M.readPair_advanceViewsWithEnvironment (viewPair h) env).symm
  rw [hadvance]
  cases d <;> rfl

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- The settled view of the step history equals the previous pending view:
absorption does not change what the last pending round showed. -/
theorem currentView_summaryGameRecorded_step (d : Proc)
    (history : (A.summaryHierarchicalGame M).PlayHistory)
    (outputOne : Out₁) (outputTwo : Out₂)
    (nature : EnvironmentRound In₁ In₂) :
    currentView d
        (summaryGameRecorded A M (.step history outputOne outputTwo nature)) =
      summaryGamePendingView A M d history := by
  cases hpending : summaryGamePending A M history with
  | none =>
      have hinit : history = .initial :=
        (summaryGamePending_eq_none_iff A M history).mp hpending
      subst hinit
      cases d <;> rfl
  | some pending =>
      rw [summaryGamePendingView_eq_nextView A M d history pending hpending]
      have hrec :
          summaryGameRecorded A M
              (.step history outputOne outputTwo nature) =
            History.append (summaryGameRecorded A M history)
              { inputOne := pending.inputOne
                inputTwo := pending.inputTwo
                graph := pending.graph
                outputOne := outputOne
                outputTwo := outputTwo } := by
        simp [summaryGameRecorded, hpending]
      rw [hrec, currentView_append_environmentRecord]

/-- **Observation lists are view reads**: process one's arena observation
list is the `M.read` image of the ancestor chain of its pending view. -/
theorem summaryGame_observations_one
    (history : (A.summaryHierarchicalGame M).PlayHistory) :
    history.observations1 =
      (summaryGamePendingView A M Proc.one history).selfChain.map M.read := by
  induction history with
  | initial =>
      show [_] = _
      simp [summaryGamePendingView, View.selfChain]
      rfl
  | step history outputOne outputTwo nature ih =>
      have hlast :
          (A.summaryHierarchicalGame M).observe1
              ((A.summaryHierarchicalGame M).next history.lastState
                outputOne outputTwo nature) =
            M.read
              (nextView Proc.one
                (summaryGameRecorded A M
                  (.step history outputOne outputTwo nature))
                nature) := by
        have hstate :=
          summaryGame_lastState A M
            (.step history outputOne outputTwo nature)
        show
          (A.summaryHierarchicalGame M).observe1
              (FiniteConcurrentGame.PlayHistory.lastState
                (.step history outputOne outputTwo nature)) = _
        rw [hstate]
        show
          (A.summaryGameTracking M).fringeDecoder Proc.one
              (recordFold (A.summaryGameTransformer M)
                (A.summaryInitialBoundary M)
                (summaryGameRecorded A M
                  (.step history outputOne outputTwo nature)))
              nature = _
        exact fringeDecoder_recordFold A M Proc.one _ nature
      rw [FiniteConcurrentGame.PlayHistory.observations1_step, ih, hlast,
        show
          summaryGamePendingView A M Proc.one
              (.step history outputOne outputTwo nature) =
            nextView Proc.one
              (summaryGameRecorded A M
                (.step history outputOne outputTwo nature)) nature from rfl,
        selfChain_nextView_one,
        currentView_summaryGameRecorded_step A M Proc.one history outputOne
          outputTwo nature,
        List.map_append]
      rfl

/-- **Observation lists are view reads**, process two. -/
theorem summaryGame_observations_two
    (history : (A.summaryHierarchicalGame M).PlayHistory) :
    history.observations2 =
      (summaryGamePendingView A M Proc.two history).selfChain.map M.read := by
  induction history with
  | initial =>
      show [_] = _
      simp [summaryGamePendingView, View.selfChain]
      rfl
  | step history outputOne outputTwo nature ih =>
      have hlast :
          (A.summaryHierarchicalGame M).observe2
              ((A.summaryHierarchicalGame M).next history.lastState
                outputOne outputTwo nature) =
            M.read
              (nextView Proc.two
                (summaryGameRecorded A M
                  (.step history outputOne outputTwo nature))
                nature) := by
        have hstate :=
          summaryGame_lastState A M
            (.step history outputOne outputTwo nature)
        show
          (A.summaryHierarchicalGame M).observe2
              (FiniteConcurrentGame.PlayHistory.lastState
                (.step history outputOne outputTwo nature)) = _
        rw [hstate]
        show
          (A.summaryGameTracking M).fringeDecoder Proc.two
              (recordFold (A.summaryGameTransformer M)
                (A.summaryInitialBoundary M)
                (summaryGameRecorded A M
                  (.step history outputOne outputTwo nature)))
              nature = _
        exact fringeDecoder_recordFold A M Proc.two _ nature
      rw [FiniteConcurrentGame.PlayHistory.observations2_step, ih, hlast,
        show
          summaryGamePendingView A M Proc.two
              (.step history outputOne outputTwo nature) =
            nextView Proc.two
              (summaryGameRecorded A M
                (.step history outputOne outputTwo nature)) nature from rfl,
        selfChain_nextView_two,
        currentView_summaryGameRecorded_step A M Proc.two history outputOne
          outputTwo nature,
        List.map_append]
      rfl

/-- **Own-information consistency, no delay**: equal pending views give equal
full own observation lists, on both sides. -/
theorem summaryGame_observations_one_of_pendingView_eq
    (history alternative : (A.summaryHierarchicalGame M).PlayHistory)
    (hview :
      summaryGamePendingView A M Proc.one alternative =
        summaryGamePendingView A M Proc.one history) :
    alternative.observations1 = history.observations1 := by
  rw [summaryGame_observations_one, summaryGame_observations_one, hview]

/-- Mirror of `summaryGame_observations_one_of_pendingView_eq`. -/
theorem summaryGame_observations_two_of_pendingView_eq
    (history alternative : (A.summaryHierarchicalGame M).PlayHistory)
    (hview :
      summaryGamePendingView A M Proc.two alternative =
        summaryGamePendingView A M Proc.two history) :
    alternative.observations2 = history.observations2 := by
  rw [summaryGame_observations_two, summaryGame_observations_two, hview]

/-- The settled observation prefix of process two at a pending history is the
read image of its settled (pre-pending) view chain. -/
theorem settledPrefix_observations_two
    (history : (A.summaryHierarchicalGame M).PlayHistory)
    (pending : EnvironmentRound In₁ In₂)
    (hpending : summaryGamePending A M history = some pending) :
    settledPrefix 1 history.observations2 =
      (currentView Proc.two
          (summaryGameRecorded A M history)).selfChain.map M.read := by
  rw [summaryGame_observations_two,
    summaryGamePendingView_eq_nextView A M Proc.two history pending hpending,
    selfChain_nextView_two, List.map_append]
  exact settledPrefix_one_append _ _

/-- The settled observation prefix of process one at a pending history. -/
theorem settledPrefix_observations_one
    (history : (A.summaryHierarchicalGame M).PlayHistory)
    (pending : EnvironmentRound In₁ In₂)
    (hpending : summaryGamePending A M history = some pending) :
    settledPrefix 1 history.observations1 =
      (currentView Proc.one
          (summaryGameRecorded A M history)).selfChain.map M.read := by
  rw [summaryGame_observations_one,
    summaryGamePendingView_eq_nextView A M Proc.one history pending hpending,
    selfChain_nextView_one, List.map_append]
  exact settledPrefix_one_append _ _

end

end DetParityAutomaton

section SettledViews

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
  [Inhabited Out₁] [Inhabited Out₂]

/-- The settled views agree whenever the two receivers' pending views agree:
the same-graph one-way case is Lemma `lem:delayonehierarchy`
(`delayOneHierarchy_left`), the `both`/`both` case is
`delayOneHierarchy_both`, and the mixed `left`/`both` cases follow from
receive-constructor injectivity, which is exactly the information the
one-bit fringe of `thm:onebitfringe` cannot remove. -/
theorem settledView_two_eq_of_nextViewOne_eq
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (env env' : EnvironmentRound In₁ In₂)
    (hrecv : env.graph = Graph.left ∨ env.graph = Graph.both)
    (hrecv' : env'.graph = Graph.left ∨ env'.graph = Graph.both)
    (hview : nextView Proc.one h' env' = nextView Proc.one h env) :
    currentView Proc.two h' = currentView Proc.two h := by
  rcases hrecv with hg | hg <;> rcases hrecv' with hg' | hg'
  · -- both `left`: `lem:delayonehierarchy`, through realized records
    have happend :
        currentView Proc.one
            (History.append h'
              { inputOne := env'.inputOne
                inputTwo := env'.inputTwo
                graph := env'.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) =
          currentView Proc.one
            (History.append h
              { inputOne := env.inputOne
                inputTwo := env.inputTwo
                graph := env.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) := by
      rw [currentView_append_environmentRecord,
        currentView_append_environmentRecord]
      exact hview
    exact delayOneHierarchy_left _ _ _ _ hg' hg happend
  · -- mixed `left`/`both`: the fringe case, by receive injectivity
    rw [nextView_one_recv_shape h env (Or.inl hg),
      nextView_one_recv_shape h' env' (Or.inr hg')] at hview
    exact (View.recv.inj hview).2.2.1
  · -- mixed `both`/`left`: the fringe case, by receive injectivity
    rw [nextView_one_recv_shape h env (Or.inr hg),
      nextView_one_recv_shape h' env' (Or.inl hg')] at hview
    exact (View.recv.inj hview).2.2.1
  · -- both `both`: `lem:delayonehierarchy`, `↔` case
    have happend :
        currentView Proc.one
            (History.append h'
              { inputOne := env'.inputOne
                inputTwo := env'.inputTwo
                graph := env'.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) =
          currentView Proc.one
            (History.append h
              { inputOne := env.inputOne
                inputTwo := env.inputTwo
                graph := env.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) := by
      rw [currentView_append_environmentRecord,
        currentView_append_environmentRecord]
      exact hview
    exact (delayOneHierarchy_both _ _ _ _ hg' hg happend).2

/-- Mirror of `settledView_two_eq_of_nextViewOne_eq`, through
`delayOneHierarchy_right` and receive injectivity. -/
theorem settledView_one_eq_of_nextViewTwo_eq
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (env env' : EnvironmentRound In₁ In₂)
    (hrecv : env.graph = Graph.right ∨ env.graph = Graph.both)
    (hrecv' : env'.graph = Graph.right ∨ env'.graph = Graph.both)
    (hview : nextView Proc.two h' env' = nextView Proc.two h env) :
    currentView Proc.one h' = currentView Proc.one h := by
  rcases hrecv with hg | hg <;> rcases hrecv' with hg' | hg'
  · -- both `right`: `lem:delayonehierarchy`, through realized records
    have happend :
        currentView Proc.two
            (History.append h'
              { inputOne := env'.inputOne
                inputTwo := env'.inputTwo
                graph := env'.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) =
          currentView Proc.two
            (History.append h
              { inputOne := env.inputOne
                inputTwo := env.inputTwo
                graph := env.graph
                outputOne := (default : Out₁)
                outputTwo := (default : Out₂) }) := by
      rw [currentView_append_environmentRecord,
        currentView_append_environmentRecord]
      exact hview
    exact delayOneHierarchy_right _ _ _ _ hg' hg happend
  · -- mixed `right`/`both`: the fringe case, by receive injectivity
    rw [nextView_two_recv_shape h env (Or.inl hg),
      nextView_two_recv_shape h' env' (Or.inr hg')] at hview
    exact (View.recv.inj hview).2.2.1
  · -- mixed `both`/`right`: the fringe case, by receive injectivity
    rw [nextView_two_recv_shape h env (Or.inr hg),
      nextView_two_recv_shape h' env' (Or.inl hg')] at hview
    exact (View.recv.inj hview).2.2.1
  · -- both `both`: by receive injectivity of the mirror shape
    rw [nextView_two_recv_shape h env (Or.inr hg),
      nextView_two_recv_shape h' env' (Or.inr hg')] at hview
    exact (View.recv.inj hview).2.2.1

end SettledViews

namespace DetParityAutomaton

open FiniteEpochTransformer FiniteConcurrentGame

variable {In₁ In₂ Out₁ Out₂ : Type u}
  [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
  [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
  (A : DetParityAutomaton.{u, u}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))
  (M : LocalSummaryAutomaton.{u, u, u} In₁ In₂)

omit [Inhabited In₁] [Inhabited In₂] in
/-- **Receiver determines the sender's settled observations** (`left` and
`both` pending rounds): if the pending round delivers to process one, then
process one's pending view determines process two's entire settled arena
observation prefix. -/
theorem summaryGame_viewOne_determines_settledTwo
    (history alternative : (A.summaryHierarchicalGame M).PlayHistory)
    (pending : EnvironmentRound In₁ In₂)
    (hpending : summaryGamePending A M history = some pending)
    (hrecv : pending.graph = Graph.left ∨ pending.graph = Graph.both)
    (hview :
      summaryGamePendingView A M Proc.one alternative =
        summaryGamePendingView A M Proc.one history) :
    settledPrefix 1 alternative.observations2 =
      settledPrefix 1 history.observations2 := by
  rw [summaryGamePendingView_eq_nextView A M Proc.one history pending
    hpending] at hview
  cases halt : summaryGamePending A M alternative with
  | none =>
      exfalso
      have hinit : alternative = .initial :=
        (summaryGamePending_eq_none_iff A M alternative).mp halt
      subst hinit
      exact
        nextView_ne_empty Proc.one (summaryGameRecorded A M history) pending
          hview.symm
  | some pending' =>
      rw [summaryGamePendingView_eq_nextView A M Proc.one alternative pending'
        halt] at hview
      have hrecv' :
          pending'.graph = Graph.left ∨ pending'.graph = Graph.both := by
        cases hg' : pending'.graph with
        | left => exact Or.inl rfl
        | both => exact Or.inr rfl
        | right =>
            exfalso
            rw [nextView_one_recv_shape _ pending hrecv] at hview
            revert hview
            simp [nextView, advanceViewsWithEnvironment, hg']
      have hsettled :=
        settledView_two_eq_of_nextViewOne_eq
          (summaryGameRecorded A M history)
          (summaryGameRecorded A M alternative) pending pending'
          hrecv hrecv' hview
      rw [settledPrefix_observations_two A M history pending hpending,
        settledPrefix_observations_two A M alternative pending' halt,
        hsettled]

omit [Inhabited In₁] [Inhabited In₂] in
/-- Mirror: **the receiver determines the sender's settled observations** on
`right` and `both` pending rounds. -/
theorem summaryGame_viewTwo_determines_settledOne
    (history alternative : (A.summaryHierarchicalGame M).PlayHistory)
    (pending : EnvironmentRound In₁ In₂)
    (hpending : summaryGamePending A M history = some pending)
    (hrecv : pending.graph = Graph.right ∨ pending.graph = Graph.both)
    (hview :
      summaryGamePendingView A M Proc.two alternative =
        summaryGamePendingView A M Proc.two history) :
    settledPrefix 1 alternative.observations1 =
      settledPrefix 1 history.observations1 := by
  rw [summaryGamePendingView_eq_nextView A M Proc.two history pending
    hpending] at hview
  cases halt : summaryGamePending A M alternative with
  | none =>
      exfalso
      have hinit : alternative = .initial :=
        (summaryGamePending_eq_none_iff A M alternative).mp halt
      subst hinit
      exact
        nextView_ne_empty Proc.two (summaryGameRecorded A M history) pending
          hview.symm
  | some pending' =>
      rw [summaryGamePendingView_eq_nextView A M Proc.two alternative pending'
        halt] at hview
      have hrecv' :
          pending'.graph = Graph.right ∨ pending'.graph = Graph.both := by
        cases hg' : pending'.graph with
        | right => exact Or.inl rfl
        | both => exact Or.inr rfl
        | left =>
            exfalso
            rw [nextView_two_recv_shape _ pending hrecv] at hview
            revert hview
            simp [nextView, advanceViewsWithEnvironment, hg']
      have hsettled :=
        settledView_one_eq_of_nextViewTwo_eq
          (summaryGameRecorded A M history)
          (summaryGameRecorded A M alternative) pending pending'
          hrecv hrecv' hview
      rw [settledPrefix_observations_one A M history pending hpending,
        settledPrefix_observations_one A M alternative pending' halt,
        hsettled]

/--
**The delay-one view hierarchy of the summary hierarchical game** -- the
proved restatement of the platform's hierarchy residual (see the module
docstring for why the strict `SummaryGameDynamicHierarchy` is refutable).
At every arena history one side's pending view determines both its own full
observation list and the other side's settled observation prefix; the
direction is the pending round's receiver.
-/
def SummaryGameDelayOneViewHierarchy : Prop :=
  ∀ history : (A.summaryHierarchicalGame M).PlayHistory,
    (∀ alternative : (A.summaryHierarchicalGame M).PlayHistory,
        summaryGamePendingView A M Proc.one alternative =
            summaryGamePendingView A M Proc.one history ->
          alternative.observations1 = history.observations1 ∧
            settledPrefix 1 alternative.observations2 =
              settledPrefix 1 history.observations2) ∨
      (∀ alternative : (A.summaryHierarchicalGame M).PlayHistory,
          summaryGamePendingView A M Proc.two alternative =
              summaryGamePendingView A M Proc.two history ->
            alternative.observations2 = history.observations2 ∧
              settledPrefix 1 alternative.observations1 =
                settledPrefix 1 history.observations1)

omit [Inhabited In₁] [Inhabited In₂] in
/-- **The summary hierarchical game satisfies the delay-one view hierarchy**
(the arena transport of `prop:dynhier` and `lem:delayonehierarchy`, with the
delay window forced by `thm:onebitfringe`). -/
theorem summaryGameDelayOneViewHierarchy_holds :
    SummaryGameDelayOneViewHierarchy A M := by
  intro history
  cases hpending : summaryGamePending A M history with
  | none =>
      have hinit : history = .initial :=
        (summaryGamePending_eq_none_iff A M history).mp hpending
      subst hinit
      left
      intro alternative hview
      have halt : alternative = .initial := by
        cases halt' : summaryGamePending A M alternative with
        | none =>
            exact (summaryGamePending_eq_none_iff A M alternative).mp halt'
        | some pending' =>
            exfalso
            rw [summaryGamePendingView_eq_nextView A M Proc.one alternative
              pending' halt'] at hview
            exact
              nextView_ne_empty Proc.one
                (summaryGameRecorded A M alternative) pending' hview
      subst halt
      exact ⟨rfl, rfl⟩
  | some pending =>
      cases hg : pending.graph with
      | left =>
          left
          intro alternative hview
          exact
            ⟨summaryGame_observations_one_of_pendingView_eq A M history
                alternative hview,
              summaryGame_viewOne_determines_settledTwo A M history
                alternative pending hpending (Or.inl hg) hview⟩
      | right =>
          right
          intro alternative hview
          exact
            ⟨summaryGame_observations_two_of_pendingView_eq A M history
                alternative hview,
              summaryGame_viewTwo_determines_settledOne A M history
                alternative pending hpending (Or.inl hg) hview⟩
      | both =>
          left
          intro alternative hview
          exact
            ⟨summaryGame_observations_one_of_pendingView_eq A M history
                alternative hview,
              summaryGame_viewOne_determines_settledTwo A M history
                alternative pending hpending (Or.inr hg) hview⟩

end DetParityAutomaton

end DistributedSynthesis
