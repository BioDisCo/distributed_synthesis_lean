/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemRegularpredecessor

/-!
# Fixed-input finite-horizon regular objectives
-/

namespace DistributedSynthesis

universe u v w x

/-- Concatenating two NFA paths is equivalent to choosing an intermediate state. -/
theorem WordNFA.path_append
    {Alphabet : Type u}
    (A : WordNFA.{u, v} Alphabet)
    (start : A.State)
    (first second : List Alphabet)
    (final : A.State) :
    A.Path start (first ++ second) final ↔
      ∃ mid, A.Path start first mid ∧ A.Path mid second final := by
  induction first generalizing start with
  | nil =>
      constructor
      · intro h
        exact ⟨start, rfl, h⟩
      · intro h
        rcases h with ⟨mid, hfirst, hsecond⟩
        cases hfirst
        exact hsecond
  | cons head tail ih =>
      constructor
      · intro h
        rcases h with ⟨mid₁, hstep, htail⟩
        rcases (ih mid₁).mp htail with ⟨mid₂, hfirst, hsecond⟩
        exact ⟨mid₂, ⟨mid₁, hstep, hfirst⟩, hsecond⟩
      · intro h
        rcases h with ⟨mid₂, hfirst, hsecond⟩
        rcases hfirst with ⟨mid₁, hstep, htail⟩
        exact ⟨mid₁, hstep, (ih mid₁).mpr ⟨mid₂, htail, hsecond⟩⟩

/--
The product of a finite transducer with a target NFA.  It recognizes the
preimage of the target NFA language under the transducer relation.
-/
def transducerPreimageNFATarget
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer.{u, v, w} Input Output)
    (A : WordNFA.{v, x} Output) :
    WordNFA.{u, max w x} Input where
  State := T.State × A.State
  stateFinite := inferInstance
  initial := fun state => T.initial state.1 ∧ A.initial state.2
  step := fun state input next =>
    ∃ emitted,
      T.step state.1 input emitted next.1 ∧
        A.Path state.2 emitted next.2
  accept := fun state => T.accept state.1 ∧ A.accept state.2

/-- Product paths for the NFA-target preimage construction. -/
theorem transducerPreimageNFATarget_path_iff
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer.{u, v, w} Input Output)
    (A : WordNFA.{v, x} Output)
    (input : List Input)
    (startT : T.State)
    (startA : A.State)
    (finalT : T.State)
    (finalA : A.State) :
    (transducerPreimageNFATarget T A).Path (startT, startA) input (finalT, finalA) ↔
      ∃ output,
        T.Path startT input output finalT ∧
          A.Path startA output finalA := by
  induction input generalizing startT startA with
  | nil =>
      constructor
      · intro h
        cases h
        exact ⟨[], by simp [FiniteStateTransducer.Path], rfl⟩
      · intro h
        rcases h with ⟨output, hTpath, hApath⟩
        rcases hTpath with ⟨houtput, hfinalT⟩
        subst output
        subst finalT
        cases hApath
        rfl
  | cons inputHead rest ih =>
      constructor
      · intro h
        rcases h with ⟨mid, hstep, hpath⟩
        rcases mid with ⟨midT, midA⟩
        rcases hstep with ⟨emitted, hTstep, hAemitted⟩
        rcases (ih midT midA).mp hpath with ⟨restOutput, hTrest, hArest⟩
        refine ⟨emitted ++ restOutput, ?_, ?_⟩
        · exact ⟨emitted, restOutput, midT, hTstep, hTrest, rfl⟩
        · exact (A.path_append startA emitted restOutput finalA).mpr
            ⟨midA, hAemitted, hArest⟩
      · intro h
        rcases h with ⟨output, hTpath, hApath⟩
        rcases hTpath with ⟨emitted, restOutput, midT, hTstep, hTrest, houtput⟩
        subst output
        rcases (A.path_append startA emitted restOutput finalA).mp hApath with
          ⟨midA, hAemitted, hArest⟩
        refine ⟨(midT, midA), ?_, ?_⟩
        · exact ⟨emitted, hTstep, hAemitted⟩
        · exact (ih midT midA).mpr ⟨restOutput, hTrest, hArest⟩

/-- Acceptance correctness for the NFA-target preimage construction. -/
theorem transducerPreimageNFATarget_accepts_iff
    {Input : Type u} {Output : Type v}
    (T : FiniteStateTransducer.{u, v, w} Input Output)
    (A : WordNFA.{v, x} Output)
    (input : List Input) :
    (transducerPreimageNFATarget T A).Accepts input ↔
      ∃ output, T.Accepts input output ∧ A.Accepts output := by
  constructor
  · intro h
    rcases h with ⟨initial, final, hinitial, hpath, haccept⟩
    rcases initial with ⟨initialT, initialA⟩
    rcases final with ⟨finalT, finalA⟩
    rcases hinitial with ⟨hTinitial, hAinitial⟩
    rcases haccept with ⟨hTaccept, hAaccept⟩
    rcases
      (transducerPreimageNFATarget_path_iff T A input initialT initialA finalT finalA).mp
        hpath with
      ⟨output, hTpath, hApath⟩
    exact
      ⟨output,
        ⟨initialT, finalT, hTinitial, hTaccept, hTpath⟩,
        ⟨initialA, finalA, hAinitial, hApath, hAaccept⟩⟩
  · intro h
    rcases h with ⟨output, hTaccepts, hAaccepts⟩
    rcases hTaccepts with ⟨initialT, finalT, hTinitial, hTaccept, hTpath⟩
    rcases hAaccepts with ⟨initialA, finalA, hAinitial, hApath, hAaccept⟩
    exact
      ⟨(initialT, initialA), (finalT, finalA),
        ⟨hTinitial, hAinitial⟩,
        (transducerPreimageNFATarget_path_iff T A input initialT initialA finalT finalA).mpr
          ⟨output, hTpath, hApath⟩,
        ⟨hTaccept, hAaccept⟩⟩

/-- The terminal DFA viewed as an NFA. -/
def WordDFA.toNFA
    {Alphabet : Type u}
    (A : WordDFA.{u, v} Alphabet) :
    WordNFA Alphabet where
  State := A.State
  stateFinite := inferInstance
  initial := fun state => state = A.initial
  step := fun state letter next => next = A.step state letter
  accept := A.accept

@[simp]
theorem WordDFA.toNFA_path_iff
    {Alphabet : Type u}
    (A : WordDFA.{u, v} Alphabet)
    (word : List Alphabet)
    (start final : A.State) :
    A.toNFA.Path start word final ↔ final = A.runFrom start word := by
  induction word generalizing start with
  | nil =>
      rfl
  | cons head tail ih =>
      constructor
      · intro h
        rcases h with ⟨mid, hstep, hpath⟩
        subst mid
        exact (ih (A.step start head)).mp hpath
      · intro h
        exact ⟨A.step start head, rfl, (ih (A.step start head)).mpr h⟩

theorem WordDFA.toNFA_accepts_iff
    {Alphabet : Type u}
    (A : WordDFA.{u, v} Alphabet)
    (word : List Alphabet) :
    A.toNFA.Accepts word ↔ A.Accepts word := by
  constructor
  · intro h
    rcases h with ⟨initial, final, hinitial, hpath, haccept⟩
    subst initial
    have hfinal := (A.toNFA_path_iff word A.initial final).mp hpath
    rwa [WordDFA.Accepts, ← hfinal]
  · intro h
    exact
      ⟨A.initial, A.runFrom A.initial word, rfl,
        (A.toNFA_path_iff word A.initial (A.runFrom A.initial word)).mpr rfl,
        h⟩

/-- The same DFA-as-NFA construction, lifted to a larger state universe. -/
def WordDFA.toNFAAs
    {Alphabet : Type u}
    (A : WordDFA.{u, x} Alphabet) :
    WordNFA.{u, max v x} Alphabet where
  State := ULift.{max v x, x} A.State
  stateFinite := inferInstance
  initial := fun state => state.down = A.initial
  step := fun state letter next => next.down = A.step state.down letter
  accept := fun state => A.accept state.down

theorem WordDFA.toNFAAs_path_iff
    {Alphabet : Type u}
    (A : WordDFA.{u, x} Alphabet)
    (word : List Alphabet)
    (start final : (A.toNFAAs : WordNFA.{u, max v x} Alphabet).State) :
    (A.toNFAAs : WordNFA.{u, max v x} Alphabet).Path start word final ↔
      final.down = A.runFrom start.down word := by
  induction word generalizing start with
  | nil =>
      cases start with
      | up startState =>
        cases final with
        | up finalState =>
          simp [WordNFA.Path, WordDFA.runFrom]
          constructor
          · intro h
            cases h
            rfl
          · intro h
            cases h
            rfl
  | cons head tail ih =>
      constructor
      · intro h
        rcases h with ⟨mid, hstep, hpath⟩
        have hmid : mid.down = A.step start.down head := hstep
        have htail := (ih mid).mp hpath
        rw [htail, hmid]
        rfl
      · intro h
        let mid : (A.toNFAAs : WordNFA.{u, max v x} Alphabet).State :=
          ULift.up (A.step start.down head)
        exact ⟨mid, rfl, (ih mid).mpr h⟩

theorem WordDFA.toNFAAs_accepts_iff
    {Alphabet : Type u}
    (A : WordDFA.{u, x} Alphabet)
    (word : List Alphabet) :
    (A.toNFAAs : WordNFA.{u, max v x} Alphabet).Accepts word ↔ A.Accepts word := by
  constructor
  · intro h
    rcases h with ⟨initial, final, hinitial, hpath, haccept⟩
    have hfinal :
        final.down = A.runFrom A.initial word := by
      rw [← hinitial]
      exact (A.toNFAAs_path_iff word initial final).mp hpath
    rwa [WordDFA.Accepts, ← hfinal]
  · intro h
    let initial : (A.toNFAAs : WordNFA.{u, max v x} Alphabet).State :=
      ULift.up A.initial
    let final : (A.toNFAAs : WordNFA.{u, max v x} Alphabet).State :=
      ULift.up (A.runFrom A.initial word)
    exact
      ⟨initial, final, rfl,
        (A.toNFAAs_path_iff word initial final).mpr rfl,
        h⟩

/--
Semantic fixed-horizon objective: after the listed one-round substitutions,
some locally uniform successor chain reaches the terminal language.
-/
def FixedHorizonCanReach
    {Edge : Type u} {Label : Type v}
    [Fintype Label]
    (schemes : List (FiniteSubstitutionScheme.{u, u, v, w} Edge Edge Label))
    (terminal : WordDFA.{u, x} Edge) :
    List Edge -> Prop
  | word =>
      match schemes with
      | [] => terminal.Accepts word
      | scheme :: rest =>
          ∃ successor,
            successor ∈ scheme.SuccessorWords word ∧
              FixedHorizonCanReach rest terminal successor

/-- Backward regular recognizer computed by iterating the one-step predecessor. -/
def fixedHorizonBackwardRecognizer
    {Edge : Type u} {Label : Type v}
    [Fintype Label]
    (schemes : List (FiniteSubstitutionScheme.{u, u, v, w} Edge Edge Label))
    (terminal : WordDFA.{u, x} Edge) :
    WordNFA.{u, max v x} Edge :=
  match schemes with
  | [] => terminal.toNFAAs
  | scheme :: rest =>
      transducerPreimageNFATarget
        (substitutionTransducer scheme)
        (fixedHorizonBackwardRecognizer rest terminal)

/--
Theorem `thm:finitehorizonregular`: the fixed-input finite-horizon objective
is recognized by the finite automaton obtained by backward iteration of the
regular one-step predecessor.
-/
theorem fixed_input_finite_horizon_regular_objectives
    {Edge : Type u} {Label : Type v}
    [Fintype Label]
    (schemes : List (FiniteSubstitutionScheme.{u, u, v, w} Edge Edge Label))
    (terminal : WordDFA.{u, x} Edge) :
    ∃ recognizer : WordNFA.{u, max v x} Edge,
      ∀ initialWord,
        recognizer.Accepts initialWord ↔
          FixedHorizonCanReach schemes terminal initialWord := by
  refine ⟨fixedHorizonBackwardRecognizer schemes terminal, ?_⟩
  induction schemes with
  | nil =>
      intro initialWord
      exact terminal.toNFAAs_accepts_iff initialWord
  | cons scheme rest ih =>
      intro initialWord
      rw [fixedHorizonBackwardRecognizer, transducerPreimageNFATarget_accepts_iff]
      constructor
      · intro h
        rcases h with ⟨successor, htransducer, hrest⟩
        have hsuccessor :
            successor ∈ scheme.SuccessorWords initialWord := by
          have hmem :
              successor ∈
                ({ output |
                  (substitutionTransducer scheme).Accepts initialWord output } :
                    Set (List Edge)) := htransducer
          simpa [finite_transducer_form_of_one_round_substitution scheme initialWord]
            using hmem
        exact ⟨successor, hsuccessor, (ih successor).mp hrest⟩
      · intro h
        rcases h with ⟨successor, hsuccessor, hrest⟩
        have htransducer :
            (substitutionTransducer scheme).Accepts initialWord successor := by
          have hmem :
              successor ∈
                ({ output |
                  (substitutionTransducer scheme).Accepts initialWord output } :
                    Set (List Edge)) := by
            simpa [finite_transducer_form_of_one_round_substitution scheme initialWord]
              using hsuccessor
          exact hmem
        exact ⟨successor, htransducer, (ih successor).mpr hrest⟩

end DistributedSynthesis
