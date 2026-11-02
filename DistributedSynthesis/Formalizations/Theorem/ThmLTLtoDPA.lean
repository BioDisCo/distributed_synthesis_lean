/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Fintype.Basic
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmMullerCombinators
import DistributedSynthesis.Formalizations.Theorem.ThmMullerToDPA

/-!
# LTL-to-deterministic-parity compilation interface

This module isolates the reusable bridge needed by the main theorem after a
compiler has been supplied: an LTL formula over finitely many atoms,
interpreted on letters, is represented by a certified deterministic parity
automaton recognizing the same omega-language.

The construction of such a compiler is represented as a record, so downstream
formalizations do not assume decidability of realizability or hide automata
correctness inside the synthesis theorem.  A later constructive development
can instantiate this record by proving a concrete LTL-to-DPA translation.
-/

namespace DistributedSynthesis

universe u v w x

/-- A certified deterministic-parity automaton for one LTL formula. -/
structure LTLFormulaDPACompilation
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (φ : LTL AP) where
  dpa : DetParityAutomaton.{v, w} Letter
  correct :
    ∀ word : OmegaWord Letter,
      dpa.Accepts word ↔ LTL.Satisfies interp word φ

namespace LTLFormulaDPACompilation

/-- The universal DPA compiles `⊤`. -/
def verum
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop) :
    LTLFormulaDPACompilation.{u, v, w} interp LTL.verum where
  dpa := (DetParityAutomaton.topAt : DetParityAutomaton.{v, w} Letter)
  correct := by
    intro word
    simp [LTL.Satisfies]

/-- The empty DPA compiles `⊥`. -/
def falsum
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop) :
    LTLFormulaDPACompilation.{u, v, w} interp LTL.falsum where
  dpa := (DetParityAutomaton.bottomAt : DetParityAutomaton.{v, w} Letter)
  correct := by
    intro word
    simp [LTL.Satisfies]

/-- A one-letter test DPA compiles an atomic proposition. -/
def atom
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (ap : AP) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.atom ap) where
  dpa := by
    haveI : DecidablePred (fun letter => interp ap letter) := dec ap
    exact DetParityAutomaton.letterTest (fun letter => interp ap letter)
  correct := by
    intro word
    haveI : DecidablePred (fun letter => interp ap letter) := dec ap
    simp [LTL.Satisfies, DetParityAutomaton.letterTest_accepts_iff]

/-- Delay a compiled DPA to compile `X φ`. -/
def next
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ : LTL AP}
    (compilation : LTLFormulaDPACompilation.{u, v, w} interp φ) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.next φ) where
  dpa := compilation.dpa.next
  correct := by
    intro word
    exact
      DetParityAutomaton.next_recognizes_ltl_next
        interp φ compilation.dpa compilation.correct word

/-- Pull a single-formula compilation back along an alphabet map. -/
def comap
    {AP : Type u}
    {Letter : Type v}
    {Letter' : Type x}
    {interp : AP -> Letter -> Prop}
    {φ : LTL AP}
    (compilation : LTLFormulaDPACompilation.{u, v, w} interp φ)
    (f : Letter' -> Letter) :
    LTLFormulaDPACompilation.{u, x, w}
      (fun ap letter => interp ap (f letter)) φ where
  dpa := compilation.dpa.comap f
  correct := by
    intro word
    rw [DetParityAutomaton.comap_accepts_iff]
    rw [compilation.correct]
    exact LTL.satisfies_word_map interp f word φ

/-- Normalize a formula compilation by shifting every priority up by two. -/
def shiftPriorityTwo
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ : LTL AP}
    (compilation : LTLFormulaDPACompilation.{u, v, w} interp φ) :
    LTLFormulaDPACompilation.{u, v, w} interp φ where
  dpa := compilation.dpa.shiftPriority 2
  correct := by
    intro word
    rw [DetParityAutomaton.shiftPriority_two_accepts_iff]
    exact compilation.correct word

/-- Complement a single-formula compilation to compile `¬ φ`. -/
def neg
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ : LTL AP}
    (compilation : LTLFormulaDPACompilation.{u, v, w} interp φ) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.neg φ) where
  dpa := compilation.dpa.shiftPriority 1
  correct := by
    intro word
    rw [DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts]
    rw [compilation.correct word]
    rfl

/--
Release is the dual of until.  This gives a certified release compiler from
the already compiled negated subformulas and a certified until compiler.
-/
def releaseViaUntil
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ ψ : LTL AP}
    (untilComp :
      LTLFormulaDPACompilation.{u, v, w}
        interp (LTL.until (LTL.neg φ) (LTL.neg ψ))) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.release φ ψ) where
  dpa := untilComp.dpa.shiftPriority 1
  correct := by
    intro word
    rw [DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts]
    rw [untilComp.correct word]
    constructor
    · intro hnotUntil n
      by_cases hψ : LTL.Satisfies interp (OmegaWord.drop word n) ψ
      · exact Or.inl hψ
      · right
        by_contra hnoBefore
        have hallBefore :
            ∀ k : Nat, k < n ->
              ¬ LTL.Satisfies interp (OmegaWord.drop word k) φ := by
          intro k hk hφ
          exact hnoBefore ⟨k, hk, hφ⟩
        exact hnotUntil ⟨n, hψ, hallBefore⟩
    · intro hrelease huntil
      rcases huntil with ⟨n, hnotψ, hbefore⟩
      rcases hrelease n with hψ | hφBefore
      · exact hnotψ hψ
      · rcases hφBefore with ⟨k, hk, hφ⟩
        exact hbefore k hk hφ

/--
Compile a conjunction through the deterministic Muller Boolean product,
assuming a certified Muller-to-DPA conversion for that product.
-/
def conjOfMullerToDPA
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ ψ : LTL AP}
    (left : LTLFormulaDPACompilation.{u, v, w} interp φ)
    (right : LTLFormulaDPACompilation.{u, v, w} interp ψ)
    (det :
      (left.dpa.toMuller.inter right.dpa.toMuller).ToDPACompilation) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.conj φ ψ) where
  dpa := det.dpa
  correct := by
    intro word
    rw [det.correct]
    rw [DetMullerAutomaton.inter_accepts_iff]
    rw [DetParityAutomaton.toMuller_accepts_iff]
    rw [DetParityAutomaton.toMuller_accepts_iff]
    rw [left.correct word, right.correct word]
    rfl

/--
Compile a disjunction through the deterministic Muller Boolean product,
assuming a certified Muller-to-DPA conversion for that product.
-/
def disjOfMullerToDPA
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ ψ : LTL AP}
    (left : LTLFormulaDPACompilation.{u, v, w} interp φ)
    (right : LTLFormulaDPACompilation.{u, v, w} interp ψ)
    (det :
      (left.dpa.toMuller.union right.dpa.toMuller).ToDPACompilation) :
    LTLFormulaDPACompilation.{u, v, w} interp (LTL.disj φ ψ) where
  dpa := det.dpa
  correct := by
    intro word
    rw [det.correct]
    rw [DetMullerAutomaton.union_accepts_iff]
    rw [DetParityAutomaton.toMuller_accepts_iff]
    rw [DetParityAutomaton.toMuller_accepts_iff]
    rw [left.correct word, right.correct word]
    rfl

/-- A single-formula compilation recognizes its certified LTL language. -/
theorem recognizes
    {AP : Type u}
    {Letter : Type v}
    {interp : AP -> Letter -> Prop}
    {φ : LTL AP}
    (compilation : LTLFormulaDPACompilation.{u, v, w} interp φ) :
    compilation.dpa.Recognizes (LTL.Language interp φ) := by
  intro word
  exact compilation.correct word

end LTLFormulaDPACompilation

/--
Closure operations sufficient to recursively compile arbitrary LTL formulas.

The operations for `¬` and `X` are supplied by the generic DPA combinators
above.  The remaining fields are exactly the genuine automata backend
obligations at the requested state universe: constants, atomic tests, Boolean
product closure, and the two temporal fixed-point constructors.
-/
structure LTLDPABuildingBlocks
    (AP : Type u)
    (Letter : Type v) where
  interp : AP -> Letter -> Prop
  verum : LTLFormulaDPACompilation.{u, v, w} interp LTL.verum
  falsum : LTLFormulaDPACompilation.{u, v, w} interp LTL.falsum
  atom :
    ∀ ap : AP,
      LTLFormulaDPACompilation.{u, v, w} interp (LTL.atom ap)
  conj :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.conj φ ψ)
  disj :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.disj φ ψ)
  untilC :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)
  releaseC :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.release φ ψ)

/--
Closure operations for arbitrary LTL where Boolean closure is routed through
deterministic Muller products.

This isolates the genuine remaining conversion theorem needed by the reusable
automata backend: once every deterministic Muller automaton over the letter
alphabet can be converted to an equivalent DPA at the target state universe,
conjunction and disjunction are no longer separate assumptions.
-/
structure LTLDPAMullerBuildingBlocks
    (AP : Type u)
    (Letter : Type v) where
  interp : AP -> Letter -> Prop
  verum : LTLFormulaDPACompilation.{u, v, w} interp LTL.verum
  falsum : LTLFormulaDPACompilation.{u, v, w} interp LTL.falsum
  atom :
    ∀ ap : AP,
      LTLFormulaDPACompilation.{u, v, w} interp (LTL.atom ap)
  mullerToDPA :
    ∀ A : DetMullerAutomaton.{v, w} Letter,
      DetMullerAutomaton.ToDPACompilation.{v, w, w} A
  untilC :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)
  releaseC :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.release φ ψ)

/--
Muller-backed closure operations where release is derived from until and
priority-shift complementation.  This is the reusable backend shape matching
the fixed-point duality `φ R ψ = ¬(¬φ U ¬ψ)`.
-/
structure LTLDPAUntilMullerBuildingBlocks
    (AP : Type u)
    (Letter : Type v) where
  interp : AP -> Letter -> Prop
  verum : LTLFormulaDPACompilation.{u, v, w} interp LTL.verum
  falsum : LTLFormulaDPACompilation.{u, v, w} interp LTL.falsum
  atom :
    ∀ ap : AP,
      LTLFormulaDPACompilation.{u, v, w} interp (LTL.atom ap)
  mullerToDPA :
    ∀ A : DetMullerAutomaton.{v, w} Letter,
      DetMullerAutomaton.ToDPACompilation.{v, w, w} A
  untilC :
    ∀ {φ ψ : LTL AP},
      LTLFormulaDPACompilation.{u, v, w} interp φ ->
      LTLFormulaDPACompilation.{u, v, w} interp ψ ->
        LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)

namespace LTLDPAMullerBuildingBlocks

/--
Build Muller-backed LTL closure blocks using the proved LAR Muller-to-DPA
construction.  After this point, Boolean closure no longer needs a certificate
field; constants and atoms are generic, so only the temporal fixed-point
automata remain as LTL-specific backend inputs.
-/
noncomputable def ofLAR
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ))
    (releaseC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.release φ ψ)) :
    LTLDPAMullerBuildingBlocks.{u, v, w} AP Letter where
  interp := interp
  verum := LTLFormulaDPACompilation.verum interp
  falsum := LTLFormulaDPACompilation.falsum interp
  atom := fun ap => (LTLFormulaDPACompilation.atom interp dec ap).shiftPriorityTwo
  mullerToDPA := fun A =>
    DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation (A := A)
  untilC := untilC
  releaseC := releaseC

/--
Muller-backed closure blocks induce the ordinary LTL/DPA closure interface.
-/
def toBuildingBlocks
    {AP : Type u}
    {Letter : Type v}
    (blocks : LTLDPAMullerBuildingBlocks.{u, v, w} AP Letter) :
    LTLDPABuildingBlocks.{u, v, w} AP Letter where
  interp := blocks.interp
  verum := blocks.verum
  falsum := blocks.falsum
  atom := blocks.atom
  conj := by
    intro φ ψ left right
    exact left.conjOfMullerToDPA right
      (blocks.mullerToDPA (left.dpa.toMuller.inter right.dpa.toMuller))
  disj := by
    intro φ ψ left right
    exact left.disjOfMullerToDPA right
      (blocks.mullerToDPA (left.dpa.toMuller.union right.dpa.toMuller))
  untilC := blocks.untilC
  releaseC := blocks.releaseC

end LTLDPAMullerBuildingBlocks

namespace LTLDPAUntilMullerBuildingBlocks

/--
Until-only Muller-backed blocks induce the ordinary Muller-backed closure
interface by deriving release through the fixed-point duality.
-/
def toMullerBuildingBlocks
    {AP : Type u}
    {Letter : Type v}
    (blocks : LTLDPAUntilMullerBuildingBlocks.{u, v, w} AP Letter) :
    LTLDPAMullerBuildingBlocks.{u, v, w} AP Letter where
  interp := blocks.interp
  verum := blocks.verum
  falsum := blocks.falsum
  atom := blocks.atom
  mullerToDPA := blocks.mullerToDPA
  untilC := blocks.untilC
  releaseC := by
    intro φ ψ left right
    exact
      (blocks.untilC left.neg right.neg).releaseViaUntil

/--
Build until-only Muller-backed LTL closure blocks using the proved LAR
Muller-to-DPA construction.  Release is not an independent assumption.
-/
noncomputable def ofLAR
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)) :
    LTLDPAUntilMullerBuildingBlocks.{u, v, w} AP Letter where
  interp := interp
  verum := LTLFormulaDPACompilation.verum interp
  falsum := LTLFormulaDPACompilation.falsum interp
  atom := fun ap => (LTLFormulaDPACompilation.atom interp dec ap).shiftPriorityTwo
  mullerToDPA := fun A =>
    DetMullerAutomaton.LAR.eventAutomaton_toDPACompilation (A := A)
  untilC := untilC

end LTLDPAUntilMullerBuildingBlocks

namespace LTLDPABuildingBlocks

/-- Recursively compile an arbitrary LTL formula from certified closure blocks. -/
def compileFormula
    {AP : Type u}
    {Letter : Type v}
    (blocks : LTLDPABuildingBlocks.{u, v, w} AP Letter) :
    ∀ φ : LTL AP, LTLFormulaDPACompilation.{u, v, w} blocks.interp φ
  | LTL.verum => blocks.verum
  | LTL.falsum => blocks.falsum
  | LTL.atom ap => blocks.atom ap
  | LTL.neg φ => (compileFormula blocks φ).neg
  | LTL.conj φ ψ => blocks.conj (compileFormula blocks φ) (compileFormula blocks ψ)
  | LTL.disj φ ψ => blocks.disj (compileFormula blocks φ) (compileFormula blocks ψ)
  | LTL.next φ => (compileFormula blocks φ).next
  | LTL.until φ ψ => blocks.untilC (compileFormula blocks φ) (compileFormula blocks ψ)
  | LTL.release φ ψ => blocks.releaseC (compileFormula blocks φ) (compileFormula blocks ψ)

end LTLDPABuildingBlocks

/--
A certified LTL-to-DPA compiler for a fixed atomic-proposition type and
letter interpretation.
-/
structure LTLToDPACompiler
    (AP : Type u)
    (Letter : Type v)
    [DecidableEq AP] where
  interp : AP -> Letter -> Prop
  compile : LTL AP -> DetParityAutomaton.{v, w} Letter
  correct :
    ∀ (φ : LTL AP) (word : OmegaWord Letter),
      (compile φ).Accepts word ↔ LTL.Satisfies interp word φ

/-- Closure blocks induce a full certified LTL-to-DPA compiler. -/
def LTLDPABuildingBlocks.toCompiler
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (blocks : LTLDPABuildingBlocks.{u, v, w} AP Letter) :
    LTLToDPACompiler.{u, v, w} AP Letter where
  interp := blocks.interp
  compile := fun φ => (blocks.compileFormula φ).dpa
  correct := by
    intro φ word
    exact (blocks.compileFormula φ).correct word

namespace LTLDPAMullerBuildingBlocks

/--
Muller-backed closure blocks induce a full certified LTL-to-DPA compiler.
-/
def toCompiler
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (blocks : LTLDPAMullerBuildingBlocks.{u, v, w} AP Letter) :
    LTLToDPACompiler.{u, v, w} AP Letter :=
  blocks.toBuildingBlocks.toCompiler

end LTLDPAMullerBuildingBlocks

namespace LTLDPAUntilMullerBuildingBlocks

/--
Until-only Muller-backed closure blocks induce a full certified LTL-to-DPA
compiler.
-/
def toCompiler
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (blocks : LTLDPAUntilMullerBuildingBlocks.{u, v, w} AP Letter) :
    LTLToDPACompiler.{u, v, w} AP Letter :=
  blocks.toMullerBuildingBlocks.toCompiler

end LTLDPAUntilMullerBuildingBlocks

/-- Direct LAR-backed compiler constructor from constants/atoms/Boolean closure
provided generically, plus caller-supplied until/release constructors. -/
noncomputable def LTLToDPACompiler.ofLAR
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ))
    (releaseC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.release φ ψ)) :
    LTLToDPACompiler.{u, v, w} AP Letter :=
  (LTLDPAMullerBuildingBlocks.ofLAR interp dec untilC releaseC).toCompiler

/-- Direct LAR-backed compiler constructor where release is derived from until. -/
noncomputable def LTLToDPACompiler.ofUntilLAR
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC :
      ∀ {φ ψ : LTL AP},
        LTLFormulaDPACompilation.{u, v, w} interp φ ->
        LTLFormulaDPACompilation.{u, v, w} interp ψ ->
          LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)) :
    LTLToDPACompiler.{u, v, w} AP Letter :=
  (LTLDPAUntilMullerBuildingBlocks.ofLAR interp dec untilC).toCompiler

/--
The single temporal constructor still needed after the generic backend
supplies constants, atomic tests, complementation, next, Boolean closure
through Muller products, LAR Muller-to-DPA conversion, and release by duality.
-/
abbrev LTLUntilDPAConstructor
    {AP : Type u}
    {Letter : Type v}
    (interp : AP -> Letter -> Prop) :=
  ∀ {φ ψ : LTL AP},
    LTLFormulaDPACompilation.{u, v, w} interp φ ->
    LTLFormulaDPACompilation.{u, v, w} interp ψ ->
      LTLFormulaDPACompilation.{u, v, w} interp (LTL.until φ ψ)

namespace LTLUntilDPAConstructor

/--
A certified `until` constructor is enough to obtain a full certified
LTL-to-DPA compiler, using only the proved generic DPA/Muller combinators.
-/
noncomputable def toCompiler
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC : LTLUntilDPAConstructor.{u, v, w} interp) :
    LTLToDPACompiler.{u, v, w} AP Letter :=
  LTLToDPACompiler.ofUntilLAR interp dec untilC

/-- Correctness theorem for the compiler induced by a certified `until` constructor. -/
theorem toCompiler_correct
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC : LTLUntilDPAConstructor.{u, v, w} interp)
    (φ : LTL AP)
    (word : OmegaWord Letter) :
    ((toCompiler interp dec untilC).compile φ).Accepts word ↔
      LTL.Satisfies interp word φ :=
  (toCompiler interp dec untilC).correct φ word

/--
Language-level LTL-to-DPA theorem from a certified `until` constructor.  This
is the narrow reusable automata target left for arbitrary full LTL.
-/
theorem ltl_to_dpa
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (interp : AP -> Letter -> Prop)
    (dec : ∀ ap letter, Decidable (interp ap letter))
    (untilC : LTLUntilDPAConstructor.{u, v, w} interp)
    (φ : LTL AP) :
    ∃ A : DetParityAutomaton.{v, w} Letter,
      ∀ word : OmegaWord Letter,
        A.Accepts word ↔ LTL.Satisfies interp word φ :=
  ⟨(toCompiler interp dec untilC).compile φ,
    (toCompiler interp dec untilC).correct φ⟩

end LTLUntilDPAConstructor

/-- The language-level theorem exposed by a certified LTL-to-DPA compiler. -/
theorem ltl_to_dpa
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    (φ : LTL AP) :
    ∃ A : DetParityAutomaton.{v, w} Letter,
      ∀ word : OmegaWord Letter,
        A.Accepts word ↔ LTL.Satisfies compiler.interp word φ :=
  ⟨compiler.compile φ, compiler.correct φ⟩

/-- A compiler recognizes exactly the LTL language of each compiled formula. -/
theorem ltl_to_dpa_recognizes
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    (φ : LTL AP) :
    (compiler.compile φ).Recognizes (LTL.Language compiler.interp φ) := by
  intro word
  exact compiler.correct φ word

/-- Extract the certified single-formula compilation supplied by a full compiler. -/
def LTLToDPACompiler.compileFormula
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    (φ : LTL AP) :
    LTLFormulaDPACompilation.{u, v, w} compiler.interp φ where
  dpa := compiler.compile φ
  correct := compiler.correct φ

/--
Any full certified LTL-to-DPA compiler supplies the `until` constructor
interface by compiling the until formula directly.

This bridge lets proofs that produce a full compiler feed endpoints stated in
terms of the smaller reusable `LTLUntilDPAConstructor` target.
-/
def LTLToDPACompiler.toUntilConstructor
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter) :
    LTLUntilDPAConstructor.{u, v, w} compiler.interp :=
  fun {φ} {ψ} _left _right =>
    compiler.compileFormula (LTL.until φ ψ)

@[simp]
theorem LTLToDPACompiler.toUntilConstructor_correct
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    {φ ψ : LTL AP}
    (left : LTLFormulaDPACompilation.{u, v, w} compiler.interp φ)
    (right : LTLFormulaDPACompilation.{u, v, w} compiler.interp ψ)
    (word : OmegaWord Letter) :
    ((compiler.toUntilConstructor left right).dpa).Accepts word ↔
      LTL.Satisfies compiler.interp word (LTL.until φ ψ) :=
  (compiler.toUntilConstructor left right).correct word

/-- Normalize every output automaton of a certified compiler by adding two priorities. -/
def LTLToDPACompiler.shiftPriorityTwo
    {AP : Type u}
    {Letter : Type v}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter) :
    LTLToDPACompiler.{u, v, w} AP Letter where
  interp := compiler.interp
  compile := fun φ => (compiler.compile φ).shiftPriority 2
  correct := by
    intro φ word
    rw [DetParityAutomaton.shiftPriority_two_accepts_iff]
    exact compiler.correct φ word

/--
Transport a certified LTL-to-DPA compiler along an alphabet map.

This is useful when a reusable compiler is stated over an abstract letter type
but the synthesis problem uses richer round records: atoms are interpreted by
first mapping the richer letter into the compiler's letter type, and the
compiled DPA is pulled back by `DetParityAutomaton.comap`.
-/
def LTLToDPACompiler.comap
    {AP : Type u}
    {Letter : Type v}
    {Letter' : Type x}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    (f : Letter' -> Letter) :
    LTLToDPACompiler.{u, x, w} AP Letter' where
  interp := fun ap letter => compiler.interp ap (f letter)
  compile := fun φ => (compiler.compile φ).comap f
  correct := by
    intro φ word
    rw [DetParityAutomaton.comap_accepts_iff]
    simpa [OmegaWord.map, LTL.Satisfies] using
      compiler.correct φ (OmegaWord.map f word)

/-- Correctness of the compiler pullback, stated as a theorem for rewriting. -/
theorem LTLToDPACompiler.comap_correct
    {AP : Type u}
    {Letter : Type v}
    {Letter' : Type x}
    [DecidableEq AP]
    (compiler : LTLToDPACompiler.{u, v, w} AP Letter)
    (f : Letter' -> Letter)
    (φ : LTL AP)
    (word : OmegaWord Letter') :
    ((compiler.comap f).compile φ).Accepts word ↔
      LTL.Satisfies (fun ap letter => compiler.interp ap (f letter)) word φ :=
  (compiler.comap f).correct φ word

end DistributedSynthesis
