/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.PostfixFold
import DistributedSynthesis.Formalizations.Definition.DefPositiveBoolean

/-! # Postfix positive Boolean formulas

The representation reuses the finite LTL token alphabet. Quoted formulas use
only constants, atoms, conjunction, and disjunction. Other operators decode
to false; the shared stack evaluator specifies all malformed inputs.
-/

namespace DistributedSynthesis.EncodedPositiveBoolean
open EncodedFiniteLTL
variable {A B : Type*}

def quote : PosBool A → Code A
  | .verum => truth
  | .falsum => falsity
  | .atom a => atom a
  | .conj p q => binary 3 (quote p) (quote q)
  | .disj p q => binary 4 (quote p) (quote q)

def embed : PosBool A → LTL A
  | .verum => .verum
  | .falsum => .falsum
  | .atom a => .atom a
  | .conj p q => .conj (embed p) (embed q)
  | .disj p q => .disj (embed p) (embed q)

theorem quote_rep (p : PosBool A) : Represents (quote p) (embed p) := by
  induction p with
  | verum => exact truth_rep
  | falsum => exact falsity_rep
  | atom a => exact atom_rep a
  | conj p q hp hq => exact conj_rep hp hq
  | disj p q hp hq => exact disj_rep hp hq

def algebra : PostfixFold.Algebra A (PosBool A) where
  truth := .verum
  falsity := .falsum
  atom := .atom
  conj := .conj
  disj := .disj
  neg := fun _ => .falsum
  next := fun _ => .falsum
  «until» := fun _ _ => .falsum
  «release» := fun _ _ => .falsum

def decode (c : Code A) : PosBool A := PostfixFold.run algebra c

theorem decode_quote (p : PosBool A) : decode (quote p) = p := by
  rw [decode, PostfixFold.run_correct, (quote_rep p).decode]
  induction p <;> simp_all [PostfixFold.formula, algebra, embed]

theorem quote_injective : Function.Injective (quote (A := A)) := by
  intro p q h
  simpa only [decode_quote] using congrArg decode h

theorem atom_mem_quote (p : PosBool A) (a : A) : .inl a ∈ quote p ↔ a ∈ p.atoms := by
  induction p <;> simp_all [quote, truth, falsity, atom, binary, PosBool.atoms]

end DistributedSynthesis.EncodedPositiveBoolean
