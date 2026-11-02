/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.EncodedPositiveLTL
import DistributedSynthesis.Library.Automata.LTLTranslation

/-! # Numeric state and priority tables for the LTL compiler

State codes are positive-normal-form subformulas, in root-first order with
duplicates retained. The first-occurrence lookup in `EncodedPositiveLTL`
injectively numbers the distinct semantic subformulas. This module constructs
state/priority data, not transition tables or a complete automaton compiler.
-/

namespace DistributedSynthesis.EncodedLTLStates
open EncodedPositiveLTL
variable {A : Type*}

theorem quote_length (p : PositiveLTL A) : (quote p).length = p.size := by
  induction p <;> simp_all [quote, EncodedFiniteLTL.truth, EncodedFiniteLTL.falsity,
    EncodedFiniteLTL.atom, EncodedFiniteLTL.unary, EncodedFiniteLTL.binary, PositiveLTL.size,
    Nat.add_assoc]

def isUntil (c : Code A) : Bool :=
  match c.reverse.head? with
  | some (.inr k) => k == 6
  | _ => false

def priority (root state : Code A) : Nat :=
  2 * (root.length - state.length) + if isUntil state then 1 else 0

theorem priority_quote (root state : PositiveLTL A) :
    priority (quote root) (quote state) = PositiveLTL.alternatingPriority root state := by
  unfold priority
  rw [quote_length, quote_length]
  cases state <;> simp [isUntil, quote, EncodedFiniteLTL.truth, EncodedFiniteLTL.falsity,
    EncodedFiniteLTL.atom, EncodedFiniteLTL.unary, EncodedFiniteLTL.binary,
    PositiveLTL.alternatingPriority]

def compile (c : EncodedFiniteLTL.Code A) : List (Code A) × List Nat :=
  (states c, (states c).map (priority (normalize c)))

theorem compile_correct (c : EncodedFiniteLTL.Code A) :
    compile c =
      ((PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas.map quote,
       (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas.map
         (PositiveLTL.alternatingPriority (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)))) := by
  simp only [compile, states_eq, normalize_eq, List.map_map, Function.comp_def, priority_quote]

section Computability
variable [Primcodable A]

theorem isUntil_primrec : Primrec (isUntil (A := A)) := by
  have htest : Primrec (fun t : (Bool × A) ⊕ Fin 8 =>
      match t with | .inl _ => false | .inr k => k == 6) := by
    exact (Primrec.sumCasesOn Primrec.id (Primrec.const false).to₂
      (Primrec.beq.comp Primrec.snd (Primrec.const (6 : Fin 8))).to₂).of_eq
      (fun t => by cases t <;> rfl)
  exact (Primrec.option_casesOn (Primrec.list_head?.comp Primrec.list_reverse)
    (Primrec.const false) (htest.comp Primrec.snd).to₂).of_eq
      (fun c => by
        cases h : c.reverse.head? with
        | none => simp [isUntil, h]
        | some t => cases t <;> simp [isUntil, h])

theorem priority_primrec : Primrec₂ (priority (A := A)) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.fst)
        (Primrec.list_length.comp Primrec.snd)))
    (Primrec.ite (Primrec.eq.comp (isUntil_primrec.comp Primrec.snd) (Primrec.const true))
      (Primrec.const 1) (Primrec.const 0))

theorem compile_primrec : Primrec (compile (A := A)) :=
  states_primrec.pair (Primrec.list_map states_primrec
    ((priority_primrec.comp (normalize_primrec.comp Primrec.fst) Primrec.snd).to₂))

end Computability
end DistributedSynthesis.EncodedLTLStates
