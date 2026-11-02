/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmLocalSummaryAutomaton

/-!
# Finite belief summaries of a global round machine

This is the reusable state-tracking half of localizing a finite global Moore
machine.  Each process stores the finite set of global controls compatible
with its finite summary.  A no-receive update fixes the locally known graph
and input and quantifies over the hidden partner input.  A receive update
intersects the two delivered pre-round beliefs and admits the two graphs the
receiver cannot distinguish.

No transition is told a strict leader.  The remaining, deliberately separate
condition for strategy extraction is output uniformity on the reachable
beliefs.  In the profiled construction this is exactly the continuation-level
law exposed by `ThmPairedProfiledOperationalDiamond`.
-/

namespace DistributedSynthesis

universe u v w

/-- A finite global Moore control updated by complete environment rounds. -/
structure FiniteGlobalRoundMachine (In₁ : Type u) (In₂ : Type v) where
  State : Type w
  stateFinite : Fintype State
  initial : State
  step : State → EnvironmentRound In₁ In₂ → State

attribute [instance] FiniteGlobalRoundMachine.stateFinite

namespace FiniteGlobalRoundMachine

variable {In₁ : Type u} {In₂ : Type v}
variable [Fintype In₁] [Fintype In₂]
variable (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)

/-- Possible next controls when process one does not receive.  Its local view
fixes graph `right` and its own input, but hides process two's input. -/
noncomputable def beliefNoRecvOne (K : Finset G.State) (inputOne : In₁) :
    Finset G.State := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ K, ∃ inputTwo : In₂,
      target = G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right }

/-- Process-two mirror: no receipt fixes graph `left`. -/
noncomputable def beliefNoRecvTwo (K : Finset G.State) (inputTwo : In₂) :
    Finset G.State := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ K, ∃ inputOne : In₁,
      target = G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left }

/-- Process one receives on either `left` or `both`.  The delivered partner
belief is intersected with its own pre-round belief. -/
noncomputable def beliefRecvOne (self other : Finset G.State)
    (inputOne : In₁) (inputTwo : In₂) : Finset G.State := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ self, source ∈ other ∧
      (target = G.step source
          { inputOne := inputOne, inputTwo := inputTwo, graph := .left } ∨
        target = G.step source
          { inputOne := inputOne, inputTwo := inputTwo, graph := .both })

/-- Process-two receive mirror. -/
noncomputable def beliefRecvTwo (self other : Finset G.State)
    (inputTwo : In₂) (inputOne : In₁) : Finset G.State := by
  classical
  exact Finset.univ.filter fun target =>
    ∃ source ∈ self, source ∈ other ∧
      (target = G.step source
          { inputOne := inputOne, inputTwo := inputTwo, graph := .right } ∨
        target = G.step source
          { inputOne := inputOne, inputTwo := inputTwo, graph := .both })

/-- The finite local-summary automaton of global-control beliefs. -/
noncomputable def beliefSummaryAutomaton :
    LocalSummaryAutomaton In₁ In₂ where
  Summary _ := Finset G.State
  finite _ := inferInstance
  initial _ := {G.initial}
  stepNoRecv
    | .one, K, .inl inputOne => G.beliefNoRecvOne K inputOne
    | .two, K, .inr inputTwo => G.beliefNoRecvTwo K inputTwo
    | _, K, _ => K
  stepRecv
    | .one, self, .inl inputOne, other, .inr inputTwo =>
        G.beliefRecvOne self other inputOne inputTwo
    | .two, self, .inr inputTwo, other, .inl inputOne =>
        G.beliefRecvTwo self other inputTwo inputOne
    | _, self, _, _, _ => self

/-- The same joint update with its finite-set result type exposed. -/
noncomputable def beliefAdvance
    (pair : Finset G.State × Finset G.State)
    (round : EnvironmentRound In₁ In₂) :
    Finset G.State × Finset G.State :=
  match round.graph with
  | .left =>
      (G.beliefRecvOne pair.1 pair.2 round.inputOne round.inputTwo,
        G.beliefNoRecvTwo pair.2 round.inputTwo)
  | .right =>
      (G.beliefNoRecvOne pair.1 round.inputOne,
        G.beliefRecvTwo pair.2 pair.1 round.inputTwo round.inputOne)
  | .both =>
      (G.beliefRecvOne pair.1 pair.2 round.inputOne round.inputTwo,
        G.beliefRecvTwo pair.2 pair.1 round.inputTwo round.inputOne)

/-- `beliefAdvance` is definitionally the joint update of the packaged local
summary automaton. -/
theorem beliefSummaryAutomaton_advance
    (pair : Finset G.State × Finset G.State)
    (round : EnvironmentRound In₁ In₂) :
    G.beliefSummaryAutomaton.advance pair round.graph
        round.inputOne round.inputTwo = G.beliefAdvance pair round := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph <;> rfl

omit [Fintype In₁] in
@[simp] theorem mem_beliefNoRecvOne
    (K : Finset G.State) (source : G.State) (hsource : source ∈ K)
    (inputOne : In₁) (inputTwo : In₂) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } ∈
      G.beliefNoRecvOne K inputOne := by
  classical
  simp [beliefNoRecvOne]
  exact ⟨source, hsource, inputTwo, rfl⟩

omit [Fintype In₂] in
@[simp] theorem mem_beliefNoRecvTwo
    (K : Finset G.State) (source : G.State) (hsource : source ∈ K)
    (inputOne : In₁) (inputTwo : In₂) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } ∈
      G.beliefNoRecvTwo K inputTwo := by
  classical
  simp [beliefNoRecvTwo]
  exact ⟨source, hsource, inputOne, rfl⟩

section
omit [Fintype In₁] [Fintype In₂]

theorem mem_beliefRecvOne_left
    (self other : Finset G.State) (source : G.State)
    (hself : source ∈ self) (hother : source ∈ other)
    (inputOne : In₁) (inputTwo : In₂) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .left } ∈
      G.beliefRecvOne self other inputOne inputTwo := by
  classical
  simp [beliefRecvOne]
  exact ⟨source, hself, hother, Or.inl rfl⟩

theorem mem_beliefRecvOne_both
    (self other : Finset G.State) (source : G.State)
    (hself : source ∈ self) (hother : source ∈ other)
    (inputOne : In₁) (inputTwo : In₂) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both } ∈
      G.beliefRecvOne self other inputOne inputTwo := by
  classical
  simp [beliefRecvOne]
  exact ⟨source, hself, hother, Or.inr rfl⟩

theorem mem_beliefRecvTwo_right
    (self other : Finset G.State) (source : G.State)
    (hself : source ∈ self) (hother : source ∈ other)
    (inputTwo : In₂) (inputOne : In₁) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .right } ∈
      G.beliefRecvTwo self other inputTwo inputOne := by
  classical
  simp [beliefRecvTwo]
  exact ⟨source, hself, hother, Or.inl rfl⟩

theorem mem_beliefRecvTwo_both
    (self other : Finset G.State) (source : G.State)
    (hself : source ∈ self) (hother : source ∈ other)
    (inputTwo : In₂) (inputOne : In₁) :
    G.step source
        { inputOne := inputOne, inputTwo := inputTwo, graph := .both } ∈
      G.beliefRecvTwo self other inputTwo inputOne := by
  classical
  simp [beliefRecvTwo]
  exact ⟨source, hself, hother, Or.inr rfl⟩

end

/-- One complete round preserves membership of the real global control in
both local beliefs. -/
theorem step_mem_advance
    (pair : Finset G.State × Finset G.State)
    (source : G.State) (hOne : source ∈ pair.1)
    (hTwo : source ∈ pair.2) (round : EnvironmentRound In₁ In₂) :
    G.step source round ∈ (G.beliefAdvance pair round).1 ∧
      G.step source round ∈ (G.beliefAdvance pair round).2 := by
  rcases round with ⟨inputOne, inputTwo, graph⟩
  cases graph with
  | left =>
      constructor
      · simpa [beliefAdvance] using
          G.mem_beliefRecvOne_left pair.1 pair.2 source hOne hTwo
            inputOne inputTwo
      · simpa [beliefAdvance] using
          G.mem_beliefNoRecvTwo pair.2 source hTwo inputOne inputTwo
  | right =>
      constructor
      · simpa [beliefAdvance] using
          G.mem_beliefNoRecvOne pair.1 source hOne inputOne inputTwo
      · simpa [beliefAdvance] using
          G.mem_beliefRecvTwo_right pair.2 pair.1 source hTwo hOne
            inputTwo inputOne
  | both =>
      constructor
      · simpa [beliefAdvance] using
          G.mem_beliefRecvOne_both pair.1 pair.2 source hOne hTwo
            inputOne inputTwo
      · simpa [beliefAdvance] using
          G.mem_beliefRecvTwo_both pair.2 pair.1 source hTwo hOne
            inputTwo inputOne

/-- Global control after a finite environment prefix. -/
def stateAfter (rounds : List (EnvironmentRound In₁ In₂)) : G.State :=
  rounds.foldl G.step G.initial

/-- The pair of local beliefs after the same finite prefix. -/
noncomputable def beliefsAfter
    (rounds : List (EnvironmentRound In₁ In₂)) :
    Finset G.State × Finset G.State :=
  rounds.foldl
    G.beliefAdvance ({G.initial}, {G.initial})

/-- The real global control is represented in both local beliefs after every
finite environment prefix. -/
theorem stateAfter_mem_beliefsAfter
    (rounds : List (EnvironmentRound In₁ In₂)) :
    G.stateAfter rounds ∈ (G.beliefsAfter rounds).1 ∧
      G.stateAfter rounds ∈ (G.beliefsAfter rounds).2 := by
  induction rounds using List.reverseRecOn with
  | nil =>
      simp [stateAfter, beliefsAfter, beliefSummaryAutomaton]
  | append_singleton rounds round ih =>
      simp only [stateAfter, beliefsAfter, List.foldl_append,
        List.foldl_cons, List.foldl_nil]
      exact G.step_mem_advance (G.beliefsAfter rounds)
        (G.stateAfter rounds) ih.1 ih.2 round

/-! ## The explicit dangerous-zone gate -/

/-- A candidate output is independent of the representative chosen from one
finite belief. -/
def BeliefUniform {Out : Type*}
    (output : G.State → Out) (K : Finset G.State) : Prop :=
  ∀ left ∈ K, ∀ right ∈ K, output left = output right

/-- Read an output from an arbitrary representative of a nonempty belief.
The fallback is used only on the totalized unreachable empty case. -/
noncomputable def beliefOutput {Out : Type*} [Inhabited Out]
    (output : G.State → Out) (K : Finset G.State) : Out :=
  if h : K.Nonempty then output h.choose else default

omit [Fintype In₁] [Fintype In₂] in
/-- Coverage plus uniformity identifies the representative output with the
real global-control output. -/
theorem beliefOutput_eq_of_mem_of_uniform
    {Out : Type*} [Inhabited Out]
    (output : G.State → Out) (K : Finset G.State)
    (huniform : G.BeliefUniform output K)
    (state : G.State) (hstate : state ∈ K) :
    G.beliefOutput output K = output state := by
  have hnonempty : K.Nonempty := ⟨state, hstate⟩
  rw [beliefOutput, dif_pos hnonempty]
  exact huniform hnonempty.choose hnonempty.choose_spec state hstate

/-- The exact remaining premise for local output extraction from a finite
global machine: both process outputs are uniform on every reachable local
belief. -/
def ReachableBeliefsUniform {Out₁ Out₂ : Type*}
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂) : Prop :=
  ∀ rounds : List (EnvironmentRound In₁ In₂),
    G.BeliefUniform outputOne (G.beliefsAfter rounds).1 ∧
      G.BeliefUniform outputTwo (G.beliefsAfter rounds).2

end FiniteGlobalRoundMachine

end DistributedSynthesis
