/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemMM2SourceSemantics
import Mathlib.Computability.Reduce

/-! # Explicit interface for the classical source undecidability theorem

`SourceUndecidability` is a proposition passed to consumers as an explicit
hypothesis. No inhabitant, axiom, global instance, or proof hole is supplied.
The mathematical proof cites the classical source theorem; a later Lean
port need only construct this proposition for the fixed encoding below.
-/
namespace DistributedSynthesis.CounterMachine.MM2

def Instr.equivCode : Instr ≃ Bool × Option Nat where
  toFun
    | .incA => (false,none)
    | .incB => (true,none)
    | .decA j => (false,some j)
    | .decB j => (true,some j)
  invFun
    | (false,none) => .incA
    | (true,none) => .incB
    | (false,some j) => .decA j
    | (true,some j) => .decB j
  left_inv := by intro i; cases i <;> rfl
  right_inv := by rintro ⟨b,n⟩; cases b <;> cases n <;> rfl
instance : Primcodable Instr := Primcodable.ofEquiv (Bool × Option Nat) Instr.equivCode

/-- The only deferred source theorem. The encoding is the list encoding
induced by `Instr.equivCode`; halting is relational, at any missing address,
from address one and counters zero. -/
structure SourceUndecidability : Prop where
  zeroHalting_not_computable : ¬ ComputablePred ZeroHalts

namespace SourceUndecidability

theorem nonhalting_not_computable (source : SourceUndecidability) :
    ¬ ComputablePred (fun P : Program ↦ ¬ ZeroHalts P) := by
  intro h
  exact source.zeroHalting_not_computable (h.not.of_eq (fun _ ↦ not_not))

/-- Consumers must exhibit a computable reduction, not just a semantic
equivalence. This keeps the deferred source theorem separate from compiler
effectivity, which remains our own proof obligation. -/
theorem transfer (source : SourceUndecidability) {Target : Type*} [Primcodable Target]
    (problem : Target → Prop)
    (reduction : (fun P : Program ↦ ¬ ZeroHalts P) ≤₀ problem) :
    ¬ ComputablePred problem := by
  intro h
  exact source.nonhalting_not_computable
    (ComputablePred.computable_of_manyOneReducible reduction h)

/-- A future universality port can discharge the interface by reducing
Mathlib's fixed-input halting problem to the exact source predicate. -/
theorem of_halting_reduction
    (reduction : (fun c : Nat.Partrec.Code ↦ (Nat.Partrec.Code.eval c 0).Dom) ≤₀ ZeroHalts) :
    SourceUndecidability := by
  constructor
  intro h
  exact ComputablePred.halting_problem 0
    (ComputablePred.computable_of_manyOneReducible reduction h)

end SourceUndecidability
end DistributedSynthesis.CounterMachine.MM2
