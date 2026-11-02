/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemSubstitutiontransducer

/-!
# Direct-reversal closure as a regular transduction
-/

namespace DistributedSynthesis

universe u v w x y

/-- A deterministic finite word automaton. -/
structure WordDFA (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  step : State -> Alphabet -> State
  accept : State -> Prop

attribute [instance] WordDFA.stateFinite

/-- Run a DFA from an arbitrary state. -/
def WordDFA.runFrom
    {Alphabet : Type u}
    (A : WordDFA Alphabet)
    (state : A.State)
    (word : List Alphabet) :
    A.State :=
  word.foldl A.step state

/-- DFA acceptance. -/
def WordDFA.Accepts
    {Alphabet : Type u}
    (A : WordDFA Alphabet)
    (word : List Alphabet) :
    Prop :=
  A.accept (A.runFrom A.initial word)

@[simp]
theorem WordDFA.runFrom_nil
    {Alphabet : Type u}
    (A : WordDFA Alphabet)
    (state : A.State) :
    A.runFrom state [] = state := by
  rfl

theorem WordDFA.runFrom_append
    {Alphabet : Type u}
    (A : WordDFA Alphabet)
    (state : A.State)
    (first second : List Alphabet) :
    A.runFrom state (first ++ second) =
      A.runFrom (A.runFrom state first) second := by
  simp [WordDFA.runFrom, List.foldl_append]

/-- A finite nondeterministic word automaton. -/
structure WordNFA (Alphabet : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State -> Prop
  step : State -> Alphabet -> State -> Prop
  accept : State -> Prop

attribute [instance] WordNFA.stateFinite

/-- NFA paths. -/
def WordNFA.Path
    {Alphabet : Type u}
    (A : WordNFA Alphabet) :
    A.State -> List Alphabet -> A.State -> Prop
  | state, [], final =>
      final = state
  | state, letter :: rest, final =>
      ∃ mid, A.step state letter mid ∧ A.Path mid rest final

/-- NFA acceptance. -/
def WordNFA.Accepts
    {Alphabet : Type u}
    (A : WordNFA Alphabet)
    (word : List Alphabet) :
    Prop :=
  ∃ initial final, A.initial initial ∧ A.Path initial word final ∧ A.accept final

/--
The product of a transducer with a target DFA.  Its language is the inverse
image of the DFA language under the transducer relation.
-/
def transducerPreimageNFA
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer Input Output)
    (B : WordDFA.{v, w} Output) :
    WordNFA Input where
  State := T.State × B.State
  stateFinite := inferInstance
  initial := fun state => T.initial state.1 ∧ state.2 = B.initial
  step := fun state input next =>
    ∃ emitted,
      T.step state.1 input emitted next.1 ∧
        next.2 = B.runFrom state.2 emitted
  accept := fun state => T.accept state.1 ∧ B.accept state.2

/--
Product paths are exactly transducer paths whose emitted output drives the
target DFA from the second component of the initial state to the second
component of the final state.
-/
theorem transducerPreimageNFA_path_iff
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer Input Output)
    (B : WordDFA.{v, w} Output)
    (input : List Input)
    (startT : T.State)
    (startB : B.State)
    (finalT : T.State)
    (finalB : B.State) :
    (transducerPreimageNFA T B).Path (startT, startB) input (finalT, finalB) ↔
      ∃ output,
        T.Path startT input output finalT ∧
          finalB = B.runFrom startB output := by
  induction input generalizing startT startB with
  | nil =>
      constructor
      · intro h
        cases h
        exact ⟨[], by simp [FiniteStateTransducer.Path], by simp [WordDFA.runFrom]⟩
      · intro h
        rcases h with ⟨output, hpath, hrun⟩
        rcases hpath with ⟨houtput, hfinal⟩
        subst output
        subst finalT
        simp [WordDFA.runFrom] at hrun
        subst finalB
        rfl
  | cons inputHead rest ih =>
      constructor
      · intro h
        rcases h with ⟨mid, hstep, hpath⟩
        rcases mid with ⟨midT, midB⟩
        rcases hstep with ⟨emitted, hTstep, hmidB⟩
        rcases (ih midT midB).mp hpath with ⟨restOutput, hTpath, hrunRest⟩
        have hmidB' : midB = B.runFrom startB emitted := by
          simpa using hmidB
        refine ⟨emitted ++ restOutput, ?_, ?_⟩
        · exact ⟨emitted, restOutput, midT, hTstep, hTpath, rfl⟩
        · calc
            finalB = B.runFrom midB restOutput := hrunRest
            _ = B.runFrom (B.runFrom startB emitted) restOutput := by rw [hmidB']
            _ = B.runFrom startB (emitted ++ restOutput) := by
              rw [WordDFA.runFrom_append]
      · intro h
        rcases h with ⟨output, hTpath, hrun⟩
        rcases hTpath with ⟨emitted, restOutput, midT, hTstep, hTpathRest, houtput⟩
        let midB := B.runFrom startB emitted
        refine ⟨(midT, midB), ?_, ?_⟩
        · exact ⟨emitted, hTstep, rfl⟩
        · apply (ih midT midB).mpr
          refine ⟨restOutput, hTpathRest, ?_⟩
          subst output
          rw [WordDFA.runFrom_append] at hrun
          exact hrun

/--
The product NFA accepts exactly those old words that have some transducer
output accepted by the target DFA.
-/
theorem transducerPreimageNFA_accepts_iff
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer Input Output)
    (B : WordDFA.{v, w} Output)
    (input : List Input) :
    (transducerPreimageNFA T B).Accepts input ↔
      ∃ output, T.Accepts input output ∧ B.Accepts output := by
  constructor
  · intro h
    rcases h with ⟨initial, final, hinitial, hpath, haccept⟩
    rcases initial with ⟨initialT, initialB⟩
    rcases final with ⟨finalT, finalB⟩
    rcases hinitial with ⟨hTinitial, hBinitial⟩
    rcases haccept with ⟨hTaccept, hBaccept⟩
    rcases
      (transducerPreimageNFA_path_iff T B input initialT initialB finalT finalB).mp
        hpath with
      ⟨output, hTpath, hrun⟩
    refine ⟨output, ?_, ?_⟩
    · exact ⟨initialT, finalT, hTinitial, hTaccept, hTpath⟩
    · rw [WordDFA.Accepts, ← hBinitial, ← hrun]
      exact hBaccept
  · intro h
    rcases h with ⟨output, hTaccepts, hBaccepts⟩
    rcases hTaccepts with ⟨initialT, finalT, hTinitial, hTaccept, hTpath⟩
    refine
      ⟨(initialT, B.initial),
        (finalT, B.runFrom B.initial output),
        ⟨hTinitial, rfl⟩,
        ?_,
        ⟨hTaccept, hBaccepts⟩⟩
    exact
      (transducerPreimageNFA_path_iff T B input initialT B.initial finalT
        (B.runFrom B.initial output)).mpr
        ⟨output, hTpath, rfl⟩

/-- A transducer is functional on its accepted relation. -/
def FunctionalTransduction
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer Input Output) :
    Prop :=
  ∀ input output₁ output₂,
    T.Accepts input output₁ ->
      T.Accepts input output₂ ->
        output₁ = output₂

/--
Paper-facing core of `lem:reversalregulartransduction`: a functional finite
transducer is a functional rational transduction, and every DFA-recognized
new-side atom has an effectively finite NFA preimage over old paths.
-/
theorem direct_reversal_closure_functional_regular_transduction
    {OldEdge : Type u} {NewEdge : Type v}
    (T : FiniteStateTransducer.{u, v, x} OldEdge NewEdge)
    (hfunctional : FunctionalTransduction T)
    (newAtom : WordDFA.{v, y} NewEdge) :
    FunctionalTransduction T ∧
      ∃ oldRecognizer : WordNFA.{u, max x y} OldEdge,
        ∀ oldPath,
          oldRecognizer.Accepts oldPath ↔
            ∃ newPath, T.Accepts oldPath newPath ∧ newAtom.Accepts newPath := by
  exact
    ⟨hfunctional,
      ⟨transducerPreimageNFA T newAtom,
        transducerPreimageNFA_accepts_iff T newAtom⟩⟩

end DistributedSynthesis
