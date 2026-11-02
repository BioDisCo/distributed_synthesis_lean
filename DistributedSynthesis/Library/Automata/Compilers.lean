/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefAlternatingAutomata
import DistributedSynthesis.Formalizations.Definition.DefNondeterministicOmegaAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators

/-! # Generic word-automata compiler interfaces
Language-correct compilation records and their composition adapters.
Extracted from the automata backend without changing declarations.
These interfaces assert semantic correctness, not encoded computability, and
do not import distributed strategies, synthesis, or the mixed backend. -/

namespace DistributedSynthesis

universe u v w a b x y z

/-- A certified conversion from a language-certified APA to a DPA. -/
structure APAToDPACompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (apaCert : A.LanguageCertificate) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ word ∈ apaCert.initialLanguage

/-- Package a DPA language-recognition proof as an APA initial-language compilation. -/
def APAToDPACompilation.ofRecognizes
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (dpa : DetParityAutomaton.{u, w} Alphabet)
    (h : dpa.Recognizes apaCert.initialLanguage) :
    APAToDPACompilation.{u, v, w} A apaCert where
  dpa := dpa
  correct := h

/-- A state-wise certified conversion from APA state languages to DPA state languages. -/
structure APAToDPAStateCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (apaCert : A.LanguageCertificate) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  stateOf : A.State -> dpa.State
  initial_state : stateOf A.initial = dpa.initial
  correctFrom :
    ∀ (state : A.State) (word : OmegaWord Alphabet),
      dpa.AcceptsFrom (stateOf state) word ↔ word ∈ apaCert.language state

/--
Package ordinary recognition proofs for each rebased DPA initial state as a
state-wise APA-to-DPA compilation.
-/
def APAToDPAStateCompilation.ofWithInitialRecognizers
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (dpa : DetParityAutomaton.{u, w} Alphabet)
    (stateOf : A.State -> dpa.State)
    (initial_state : stateOf A.initial = dpa.initial)
    (h :
      ∀ state : A.State,
        (dpa.withInitial (stateOf state)).Recognizes (apaCert.language state)) :
    APAToDPAStateCompilation.{u, v, w} A apaCert where
  dpa := dpa
  stateOf := stateOf
  initial_state := initial_state
  correctFrom := by
    intro state word
    rw [← DetParityAutomaton.withInitial_accepts_iff]
    exact h state word

/-- A state-wise APA-to-DPA compilation yields the usual initial-language compilation. -/
def APAToDPAStateCompilation.toInitialCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {apaCert : A.LanguageCertificate}
    (det : APAToDPAStateCompilation.{u, v, w} A apaCert) :
    APAToDPACompilation.{u, v, w} A apaCert where
  dpa := det.dpa
  correct := by
    intro word
    change det.dpa.AcceptsFrom det.dpa.initial word ↔ word ∈ apaCert.initialLanguage
    rw [← det.initial_state]
    exact det.correctFrom A.initial word

/-- A certified determinization theorem stated directly against APA run-tree acceptance. -/
structure APARunToDPACompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ A.Accepts word

/--
A uniform determinizer for APA run-tree semantics over a fixed alphabet.

This is the reusable automata-theory backend target beneath the canonical LTL
frontend: once supplied, every APA with finite state space over `Alphabet` has
a language-equivalent DPA.
-/
structure APARunToDPACompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
      APARunToDPACompilation.{u, v, w} A

/--
A state-wise APA-language determinization plus a state-wise run-language
certificate yields the direct run-semantics determinization statement.
-/
def APAToDPAStateCompilation.toRunCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {cert : A.RunLanguageCertificate}
    (det : APAToDPAStateCompilation.{u, v, w} A cert.toLanguageCertificate) :
    APARunToDPACompilation.{u, v, w} A where
  dpa := det.dpa
  correct := by
    intro word
    change det.dpa.AcceptsFrom det.dpa.initial word ↔ A.Accepts word
    rw [← det.initial_state]
    trans word ∈ cert.toLanguageCertificate.language A.initial
    · exact det.correctFrom A.initial word
    · exact (cert.initial_accepts_iff word).symm

/--
Turn a run-semantics determinization plus a run-language certificate into the
language-certificate form used by the LTL backend composition.
-/
def APARunToDPACompilation.toLanguageCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {cert : A.RunLanguageCertificate}
    (det : APARunToDPACompilation.{u, v, w} A) :
    APAToDPACompilation.{u, v, w} A cert.toLanguageCertificate where
  dpa := det.dpa
  correct := by
    intro word
    trans A.Accepts word
    · exact det.correct word
    trans word ∈ cert.toLanguageCertificate.language A.initial
    · exact cert.initial_accepts_iff word
    · rfl

namespace APARunToDPACompiler

/--
Apply a uniform run-semantics APA determinizer to an APA equipped with a
run-language certificate.
-/
def toLanguageCompilation
    {Alphabet : Type u}
    (compiler : APARunToDPACompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (cert : A.RunLanguageCertificate) :
    APAToDPACompilation.{u, v, w} A cert.toLanguageCertificate :=
  (compiler.compile A).toLanguageCompilation

end APARunToDPACompiler

/-- A certified determinization from one nondeterministic Büchi automaton to a DPA. -/
structure NondetBuchiToDPACompilation
    {Alphabet : Type u}
    (A : NondetBuchiAutomaton.{u, v} Alphabet) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ A.Accepts word

/-- A certified determinization from one nondeterministic Streett automaton to a DPA. -/
structure NondetStreettToDPACompilation
    {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) where
  dpa : DetParityAutomaton.{u, a} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ A.Accepts word

/-- A certified determinization from one nondeterministic Muller automaton to a DPA. -/
structure NondetMullerToDPACompilation
    {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) where
  dpa : DetParityAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      dpa.Accepts word ↔ A.Accepts word

/-- A certified translation from one nondeterministic Streett automaton to Muller. -/
structure NondetStreettToMullerCompilation
    {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) where
  muller : NondetMullerAutomaton.{u, a} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      muller.Accepts word ↔ A.Accepts word

/-- A certified translation from one nondeterministic Muller automaton to Streett. -/
structure NondetMullerToStreettCompilation
    {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) where
  streett : NondetStreettAutomaton.{u, w, a} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      streett.Accepts word ↔ A.Accepts word

namespace NondetBuchiToDPACompilation

/--
A Streett determinization theorem immediately determinizes Büchi automata via
the one-pair Büchi-as-Streett embedding.
-/
def ofStreett
    {Alphabet : Type u}
    {A : NondetBuchiAutomaton.{u, v} Alphabet}
    (det : NondetStreettToDPACompilation.{u, v, 0, w} A.toStreett) :
    NondetBuchiToDPACompilation.{u, v, w} A where
  dpa := det.dpa
  correct := by
    intro word
    trans A.toStreett.Accepts word
    · exact det.correct word
    · exact A.toStreett_accepts_iff word

end NondetBuchiToDPACompilation

namespace NondetMullerToStreettCompilation

/-- The standard nondeterministic Muller-to-Streett translation. -/
def ofToStreett
    {Alphabet : Type u}
    (A : NondetMullerAutomaton.{u, v} Alphabet) :
    NondetMullerToStreettCompilation.{u, v, v, v} A where
  streett := A.toStreett
  correct := A.toStreett_accepts_iff

/-- Compose a Muller-to-Streett translation with Streett determinization. -/
def toDPACompilation
    {Alphabet : Type u}
    {A : NondetMullerAutomaton.{u, v} Alphabet}
    (compilation : NondetMullerToStreettCompilation.{u, v, w, a} A)
    (det :
      NondetStreettToDPACompilation.{u, w, a, b} compilation.streett) :
      NondetMullerToDPACompilation.{u, v, b} A where
  dpa := det.dpa
  correct := by
    intro word
    trans compilation.streett.Accepts word
    · exact det.correct word
    · exact compilation.correct word

end NondetMullerToStreettCompilation

namespace NondetStreettToMullerCompilation

/-- The standard same-graph Streett-to-Muller translation. -/
def ofToMuller
    {Alphabet : Type u}
    (A : NondetStreettAutomaton.{u, v, w} Alphabet) :
    NondetStreettToMullerCompilation.{u, v, w, v} A where
  muller := A.toMuller
  correct := A.toMuller_accepts_iff

/-- Compose a Streett-to-Muller translation with nondeterministic Muller determinization. -/
def toDPACompilation
    {Alphabet : Type u}
    {A : NondetStreettAutomaton.{u, v, w} Alphabet}
    (compilation : NondetStreettToMullerCompilation.{u, v, w, a} A)
    (det :
      NondetMullerToDPACompilation.{u, a, b} compilation.muller) :
    NondetStreettToDPACompilation.{u, v, w, b} A where
  dpa := det.dpa
  correct := by
    intro word
    trans compilation.muller.Accepts word
    · exact det.correct word
    · exact compilation.correct word

end NondetStreettToMullerCompilation

/--
A uniform Piterman/Safra-style determinizer for nondeterministic Büchi
automata over a fixed alphabet.
-/
structure NondetBuchiToDPACompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : NondetBuchiAutomaton.{u, v} Alphabet,
      NondetBuchiToDPACompilation.{u, v, w} A

/--
A uniform Piterman/Safra-style determinizer for nondeterministic Streett
automata over a fixed alphabet.

This is the Lean-facing target corresponding to Piterman's construction
`NSW -> DPW`; the construction itself must instantiate this compiler without
axioms.
-/
structure NondetStreettToDPACompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : NondetStreettAutomaton.{u, v, w} Alphabet,
      NondetStreettToDPACompilation.{u, v, w, a} A

/--
A uniform determinizer for nondeterministic Muller automata.  This can either
be supplied directly, or obtained by composing a Muller-to-Streett translation
with a Piterman/Safra Streett determinizer.
-/
structure NondetMullerToDPACompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : NondetMullerAutomaton.{u, v} Alphabet,
      NondetMullerToDPACompilation.{u, v, w} A

/-- A uniform translation from nondeterministic Muller automata to Streett. -/
structure NondetMullerToStreettCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : NondetMullerAutomaton.{u, v} Alphabet,
      NondetMullerToStreettCompilation.{u, v, w, a} A

/-- A uniform same-graph translation from nondeterministic Streett automata to Muller. -/
structure NondetStreettToMullerCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : NondetStreettAutomaton.{u, v, w} Alphabet,
      NondetStreettToMullerCompilation.{u, v, w, a} A

namespace NondetStreettToDPACompiler

/-- A uniform Streett determinizer also supplies the Büchi determinizer. -/
def toBuchiCompiler
    {Alphabet : Type u}
    (compiler : NondetStreettToDPACompiler.{u, v, 0, w} Alphabet) :
    NondetBuchiToDPACompiler.{u, v, w} Alphabet where
  compile := fun A =>
    NondetBuchiToDPACompilation.ofStreett (compiler.compile A.toStreett)

end NondetStreettToDPACompiler

namespace NondetStreettToMullerCompiler

/-- Uniform standard same-graph Streett-to-Muller compiler. -/
def standard
    (Alphabet : Type u) :
    NondetStreettToMullerCompiler.{u, v, w, v} Alphabet where
  compile := fun A => NondetStreettToMullerCompilation.ofToMuller A

/-- Compose a uniform Streett-to-Muller translation with Muller determinization. -/
def toDPACompiler
    {Alphabet : Type u}
    (compiler : NondetStreettToMullerCompiler.{u, v, w, a} Alphabet)
    (determinizer : NondetMullerToDPACompiler.{u, a, b} Alphabet) :
    NondetStreettToDPACompiler.{u, v, w, b} Alphabet where
  compile := fun A =>
    (compiler.compile A).toDPACompilation
      (determinizer.compile (compiler.compile A).muller)

end NondetStreettToMullerCompiler

namespace NondetMullerToDPACompiler

/--
A nondeterministic Muller determinizer also supplies a Streett determinizer via
the standard same-graph Streett-to-Muller translation.
-/
def toStreettCompiler
    {Alphabet : Type u}
    (compiler : NondetMullerToDPACompiler.{u, v, w} Alphabet) :
    NondetStreettToDPACompiler.{u, v, a, w} Alphabet :=
  (NondetStreettToMullerCompiler.standard Alphabet).toDPACompiler compiler

end NondetMullerToDPACompiler

namespace NondetMullerToStreettCompiler

/-- Uniform standard nondeterministic Muller-to-Streett compiler. -/
def standard
    (Alphabet : Type u) :
    NondetMullerToStreettCompiler.{u, v, v, v} Alphabet where
  compile := fun A => NondetMullerToStreettCompilation.ofToStreett A

/-- Compose a uniform Muller-to-Streett translation with a Streett determinizer. -/
def toDPACompiler
    {Alphabet : Type u}
    (compiler : NondetMullerToStreettCompiler.{u, v, w, a} Alphabet)
    (determinizer : NondetStreettToDPACompiler.{u, w, a, b} Alphabet) :
    NondetMullerToDPACompiler.{u, v, b} Alphabet where
  compile := fun A =>
    (compiler.compile A).toDPACompilation
      (determinizer.compile (compiler.compile A).streett)

end NondetMullerToStreettCompiler

/-- A certified translation from APA run-tree semantics to a nondeterministic Büchi automaton. -/
structure APARunToNondetBuchiCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  buchi : NondetBuchiAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      buchi.Accepts word ↔ A.Accepts word

/-- A certified translation from APA run-tree semantics to a nondeterministic Streett automaton. -/
structure APARunToNondetStreettCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  streett : NondetStreettAutomaton.{u, w, a} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      streett.Accepts word ↔ A.Accepts word

/-- A certified translation from APA run-tree semantics to a nondeterministic Muller automaton. -/
structure APARunToNondetMullerCompilation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  muller : NondetMullerAutomaton.{u, w} Alphabet
  correct :
    ∀ word : OmegaWord Alphabet,
      muller.Accepts word ↔ A.Accepts word

namespace APARunToNondetStreettCompilation

/-- Compose an APA-to-Streett translation with Streett determinization. -/
def toDPACompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetStreettCompilation.{u, v, w, a} A)
    (det :
      NondetStreettToDPACompilation.{u, w, a, b} compilation.streett) :
    APARunToDPACompilation.{u, v, b} A where
  dpa := det.dpa
  correct := by
    intro word
    trans compilation.streett.Accepts word
    · exact det.correct word
    · exact compilation.correct word

end APARunToNondetStreettCompilation

namespace APARunToNondetMullerCompilation

/-- Compose an APA-to-Muller translation with Muller determinization. -/
def toDPACompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetMullerCompilation.{u, v, w} A)
    (det : NondetMullerToDPACompilation.{u, w, a} compilation.muller) :
    APARunToDPACompilation.{u, v, a} A where
  dpa := det.dpa
  correct := by
    intro word
    trans compilation.muller.Accepts word
    · exact det.correct word
    · exact compilation.correct word

/-- Compose an APA-to-Muller translation with Muller-to-Streett translation. -/
def toStreettCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetMullerCompilation.{u, v, w} A)
    (mullerToStreett :
      NondetMullerToStreettCompilation.{u, w, a, b} compilation.muller) :
    APARunToNondetStreettCompilation.{u, v, a, b} A where
  streett := mullerToStreett.streett
  correct := by
    intro word
    trans compilation.muller.Accepts word
    · exact mullerToStreett.correct word
    · exact compilation.correct word

/-- Compose APA-to-Muller, Muller-to-Streett, and Streett determinization. -/
def toDPACompilationViaStreett
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetMullerCompilation.{u, v, w} A)
    (mullerToStreett :
      NondetMullerToStreettCompilation.{u, w, a, b} compilation.muller)
    (det :
      NondetStreettToDPACompilation.{u, a, b, c} mullerToStreett.streett) :
    APARunToDPACompilation.{u, v, c} A :=
  (compilation.toStreettCompilation mullerToStreett).toDPACompilation det

end APARunToNondetMullerCompilation

namespace APARunToNondetBuchiCompilation

/-- Any APA-to-Büchi translation is also an APA-to-Streett translation. -/
def toStreettCompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetBuchiCompilation.{u, v, w} A) :
    APARunToNondetStreettCompilation.{u, v, w, 0} A where
  streett := compilation.buchi.toStreett
  correct := by
    intro word
    trans compilation.buchi.Accepts word
    · exact compilation.buchi.toStreett_accepts_iff word
    · exact compilation.correct word

/-- Compose an APA-to-Büchi translation with Büchi determinization. -/
def toDPACompilation
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (compilation : APARunToNondetBuchiCompilation.{u, v, w} A)
    (det : NondetBuchiToDPACompilation.{u, w, a} compilation.buchi) :
    APARunToDPACompilation.{u, v, a} A where
  dpa := det.dpa
  correct := by
    intro word
    trans compilation.buchi.Accepts word
    · exact det.correct word
    · exact compilation.correct word

end APARunToNondetBuchiCompilation

/-- A uniform APA-to-Büchi translation over a fixed alphabet. -/
structure APARunToNondetBuchiCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
      APARunToNondetBuchiCompilation.{u, v, w} A

/-- A uniform APA-to-Streett translation over a fixed alphabet. -/
structure APARunToNondetStreettCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
      APARunToNondetStreettCompilation.{u, v, w, a} A

/-- A uniform APA-to-Muller translation over a fixed alphabet. -/
structure APARunToNondetMullerCompiler
    (Alphabet : Type u) where
  compile :
    ∀ A : AlternatingParityAutomaton.{u, v} Alphabet,
      APARunToNondetMullerCompilation.{u, v, w} A

namespace APARunToNondetBuchiCompiler

/-- A uniform APA-to-Büchi compiler is also a uniform APA-to-Streett compiler. -/
def toStreettCompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet) :
    APARunToNondetStreettCompiler.{u, v, w, 0} Alphabet where
  compile := fun A => (compiler.compile A).toStreettCompilation

/-- Compose a uniform APA-to-Büchi translation with a uniform Büchi determinizer. -/
def toDPACompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (determinizer : NondetBuchiToDPACompiler.{u, w, a} Alphabet) :
    APARunToDPACompiler.{u, v, a} Alphabet where
  compile := fun A =>
    (compiler.compile A).toDPACompilation
      (determinizer.compile (compiler.compile A).buchi)

end APARunToNondetBuchiCompiler

namespace APARunToNondetMullerCompiler

/-- Compose a uniform APA-to-Muller translation with a uniform Muller determinizer. -/
def toDPACompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetMullerCompiler.{u, v, w} Alphabet)
    (determinizer : NondetMullerToDPACompiler.{u, w, a} Alphabet) :
    APARunToDPACompiler.{u, v, a} Alphabet where
  compile := fun A =>
    (compiler.compile A).toDPACompilation
      (determinizer.compile (compiler.compile A).muller)

/--
Compose a uniform APA-to-Muller translation with Muller-to-Streett and
Streett-to-DPA compilers.
-/
def toDPACompilerViaStreett
    {Alphabet : Type u}
    (compiler : APARunToNondetMullerCompiler.{u, v, w} Alphabet)
    (mullerToStreett : NondetMullerToStreettCompiler.{u, w, a, b} Alphabet)
    (determinizer : NondetStreettToDPACompiler.{u, a, b, c} Alphabet) :
    APARunToDPACompiler.{u, v, c} Alphabet where
  compile := fun A =>
    let comp := compiler.compile A
    let m2s := mullerToStreett.compile comp.muller
    comp.toDPACompilationViaStreett m2s (determinizer.compile m2s.streett)

/--
Compose a uniform APA-to-Muller translation with the proved standard
Muller-to-Streett bridge and a Streett-to-DPA determinizer.
-/
def toDPACompilerViaStandardStreett
    {Alphabet : Type u}
    (compiler : APARunToNondetMullerCompiler.{u, v, w} Alphabet)
    (determinizer : NondetStreettToDPACompiler.{u, w, w, a} Alphabet) :
    APARunToDPACompiler.{u, v, a} Alphabet :=
  compiler.toDPACompilerViaStreett
    (NondetMullerToStreettCompiler.standard Alphabet)
    determinizer

end APARunToNondetMullerCompiler

namespace APARunToNondetStreettCompiler

/-- Compose a uniform APA-to-Streett translation with a uniform Streett determinizer. -/
def toDPACompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetStreettCompiler.{u, v, w, a} Alphabet)
    (determinizer : NondetStreettToDPACompiler.{u, w, a, b} Alphabet) :
    APARunToDPACompiler.{u, v, b} Alphabet where
  compile := fun A =>
    (compiler.compile A).toDPACompilation
      (determinizer.compile (compiler.compile A).streett)

end APARunToNondetStreettCompiler

end DistributedSynthesis
