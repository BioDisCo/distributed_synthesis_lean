/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.PostfixFold
import DistributedSynthesis.Library.Logic.LTL

/-! # Numeric positive-normal-form compilation and subformula enumeration

Signed atoms are pairs `(polarity, atom)`. Output codes use the existing
postfix operators but no negation operator. Both polarities are constructed
together, so input negation only swaps the pair. All input strings, including
malformed ones, retain the existing total decoding convention.
-/

namespace DistributedSynthesis.EncodedPositiveLTL
open EncodedFiniteLTL

abbrev Code (A : Type*) := EncodedFiniteLTL.Code (Bool × A)
variable {A : Type*}

def quote : PositiveLTL A → Code A
  | .verum => truth
  | .falsum => falsity
  | .lit l => atom (l.positive, l.atom)
  | .conj p q => binary 3 (quote p) (quote q)
  | .disj p q => binary 4 (quote p) (quote q)
  | .next p => unary 5 (quote p)
  | .until p q => binary 6 (quote p) (quote q)
  | .release p q => binary 7 (quote p) (quote q)

def embed : PositiveLTL A → LTL (Bool × A)
  | .verum => .verum
  | .falsum => .falsum
  | .lit l => .atom (l.positive, l.atom)
  | .conj p q => .conj (embed p) (embed q)
  | .disj p q => .disj (embed p) (embed q)
  | .next p => .next (embed p)
  | .until p q => .until (embed p) (embed q)
  | .release p q => .release (embed p) (embed q)

theorem quote_rep (p : PositiveLTL A) : Represents (quote p) (embed p) := by
  induction p with
  | verum => exact truth_rep
  | falsum => exact falsity_rep
  | lit l => exact atom_rep _
  | conj p q hp hq => exact conj_rep hp hq
  | disj p q hp hq => exact disj_rep hp hq
  | next p hp => exact next_rep hp
  | «until» p q hp hq => exact binary_rep 6 .until (fun _ _ _ => rfl) hp hq
  | «release» p q hp hq => exact release_rep hp hq

def positiveAlgebra : PostfixFold.Algebra (Bool × A) (PositiveLTL A) where
  truth := .verum
  falsity := .falsum
  atom := fun a => .lit ⟨a.1, a.2⟩
  neg := PositiveLTL.negate
  conj := .conj
  disj := .disj
  next := .next
  «until» := .until
  «release» := .release

def decode (c : Code A) : PositiveLTL A := PostfixFold.run positiveAlgebra c

theorem decode_quote (p : PositiveLTL A) : decode (quote p) = p := by
  rw [decode, PostfixFold.run_correct, (quote_rep p).decode]
  induction p <;> simp_all [embed, PostfixFold.formula, positiveAlgebra]

theorem quote_injective : Function.Injective (quote (A := A)) := by
  intro p q h
  simpa only [decode_quote] using congrArg decode h

private theorem negate_negate (p : PositiveLTL A) : p.negate.negate = p := by
  induction p <;> simp_all [PositiveLTL.negate]

def normalizeAlgebra : PostfixFold.Algebra A (Code A × Code A) where
  truth := (truth, falsity)
  falsity := (falsity, truth)
  atom := fun a => (atom (true, a), atom (false, a))
  neg := Prod.swap
  conj := fun p q => (binary 3 p.1 q.1, binary 4 p.2 q.2)
  disj := fun p q => (binary 4 p.1 q.1, binary 3 p.2 q.2)
  next := fun p => (unary 5 p.1, unary 5 p.2)
  «until» := fun p q => (binary 6 p.1 q.1, binary 7 p.2 q.2)
  «release» := fun p q => (binary 7 p.1 q.1, binary 6 p.2 q.2)

def normalize (c : EncodedFiniteLTL.Code A) : Code A :=
  (PostfixFold.run normalizeAlgebra c).1

theorem normalize_formula (p : LTL A) : PostfixFold.formula normalizeAlgebra p =
    (quote (PositiveLTL.ofLTL p), quote (PositiveLTL.ofLTL p).negate) := by
  induction p <;> simp_all [PostfixFold.formula, normalizeAlgebra, PositiveLTL.ofLTL,
    quote, PositiveLTL.negate, negate_negate]

theorem normalize_eq (c : EncodedFiniteLTL.Code A) :
    normalize c = quote (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)) := by
  rw [normalize, PostfixFold.run_correct, normalize_formula]

theorem normalize_correct (c : EncodedFiniteLTL.Code A) :
    decode (normalize c) = PositiveLTL.ofLTL (EncodedFiniteLTL.decode c) := by
  rw [normalize_eq, decode_quote]

theorem quote_negation_free (p : PositiveLTL A) :
    (.inr 2 : EncodedFiniteLTL.Token (Bool × A)) ∉ quote p := by
  induction p <;> simp_all [quote, truth, falsity, atom, unary, binary]

theorem normalize_negation_free (c : EncodedFiniteLTL.Code A) :
    (.inr 2 : EncodedFiniteLTL.Token (Bool × A)) ∉ normalize c := by
  rw [normalize_eq]
  exact quote_negation_free _

theorem satisfies_normalize {Letter : Type*} (interp : A → Letter → Prop)
    (word : OmegaWord Letter) (c : EncodedFiniteLTL.Code A) :
    PositiveLTL.Satisfies interp word (decode (normalize c)) ↔
      LTL.Satisfies interp word (EncodedFiniteLTL.decode c) := by
  rw [normalize_correct]
  exact PositiveLTL.satisfies_ofLTL interp word _

def closureUnary (k : Fin 8) (p : Code A × List (Code A)) : Code A × List (Code A) :=
  let c := unary k p.1
  (c, c :: p.2)

def closureBinary (k : Fin 8) (p q : Code A × List (Code A)) : Code A × List (Code A) :=
  let c := binary k p.1 q.1
  (c, c :: (p.2 ++ q.2))

def closureAlgebra : PostfixFold.Algebra (Bool × A) (Code A × List (Code A)) where
  truth := (truth, [truth])
  falsity := (falsity, [falsity])
  atom := fun a => (atom a, [atom a])
  neg := closureUnary 2
  conj := closureBinary 3
  disj := closureBinary 4
  next := closureUnary 5
  «until» := closureBinary 6
  «release» := closureBinary 7

/-- Root first; repeated subformulas are retained. -/
def closure (c : Code A) : List (Code A) := (PostfixFold.run closureAlgebra c).2

theorem closure_formula (p : PositiveLTL A) :
    PostfixFold.formula closureAlgebra (embed p) = (quote p, p.subformulas.map quote) := by
  induction p <;> simp_all [PostfixFold.formula, embed, closureAlgebra, closureUnary,
    closureBinary, quote, PositiveLTL.subformulas]

theorem closure_quote (p : PositiveLTL A) : closure (quote p) = p.subformulas.map quote := by
  rw [closure, PostfixFold.run_correct, (quote_rep p).decode, closure_formula]

def states (c : EncodedFiniteLTL.Code A) : List (Code A) := closure (normalize c)

theorem states_eq (c : EncodedFiniteLTL.Code A) :
    states c = (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas.map quote := by
  rw [states, normalize_eq, closure_quote]

section Computability
variable [Primcodable A]

theorem normalize_effective : PostfixFold.Effective (normalizeAlgebra (A := A)) := by
  constructor
  · exact ((atom_primrec.comp ((Primrec.const true).pair Primrec.id)).pair
      (atom_primrec.comp ((Primrec.const false).pair Primrec.id)))
  · exact Primrec.snd.pair Primrec.fst
  · exact ((binary_primrec 3).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((binary_primrec 4).comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  · exact ((binary_primrec 4).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((binary_primrec 3).comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  · exact ((unary_primrec 5).comp Primrec.fst).pair ((unary_primrec 5).comp Primrec.snd)
  · exact ((binary_primrec 6).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((binary_primrec 7).comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  · exact ((binary_primrec 7).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      ((binary_primrec 6).comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem normalize_primrec : Primrec (normalize (A := A)) :=
  Primrec.fst.comp (PostfixFold.run_primrec normalizeAlgebra normalize_effective)

theorem closureUnary_primrec (k : Fin 8) : Primrec (closureUnary (A := A) k) :=
  ((unary_primrec k).comp Primrec.fst).pair
    (Primrec.list_cons.comp ((unary_primrec k).comp Primrec.fst) Primrec.snd)

theorem closureBinary_primrec (k : Fin 8) : Primrec₂ (closureBinary (A := A) k) := by
  have hc : Primrec (fun x : (Code A × List (Code A)) × (Code A × List (Code A)) =>
      binary k x.1.1 x.2.1) := (binary_primrec (A := Bool × A) k).comp
    (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
  exact hc.pair (Primrec.list_cons.comp hc
    (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)))

theorem closure_effective : PostfixFold.Effective (closureAlgebra (A := A)) := by
  constructor
  · exact atom_primrec.pair (Primrec.list_cons.comp atom_primrec (Primrec.const []))
  · exact closureUnary_primrec 2
  · exact closureBinary_primrec 3
  · exact closureBinary_primrec 4
  · exact closureUnary_primrec 5
  · exact closureBinary_primrec 6
  · exact closureBinary_primrec 7

theorem closure_primrec : Primrec (closure (A := A)) :=
  Primrec.snd.comp (PostfixFold.run_primrec closureAlgebra closure_effective)

theorem states_primrec : Primrec (states (A := A)) := closure_primrec.comp normalize_primrec

end Computability

section Numbering
variable [DecidableEq A]
local instance : BEq (Code A) := instBEqOfDecidableEq

/-- First occurrence; absent queries return the list length. -/
def index (c : EncodedFiniteLTL.Code A) (p : Code A) : Nat := (states c).idxOf p

omit [DecidableEq A] in
theorem quote_mem_states (c : EncodedFiniteLTL.Code A) (p : PositiveLTL A) :
    quote p ∈ states c ↔ p ∈ (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas := by
  rw [states_eq]
  simp only [List.mem_map]
  constructor
  · rintro ⟨q, hq, he⟩
    exact quote_injective he ▸ hq
  · intro h
    exact ⟨p, h, rfl⟩

def number (c : EncodedFiniteLTL.Code A)
    (p : (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).Subformula) : Fin (states c).length :=
  ⟨index c (quote p.val), List.idxOf_lt_length_of_mem ((quote_mem_states c p.val).mpr p.property)⟩

theorem number_lookup (c : EncodedFiniteLTL.Code A)
    (p : (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).Subformula) :
    (states c)[(number c p).val]? = some (quote p.val) := by
  exact List.getElem?_idxOf ((quote_mem_states c p.val).mpr p.property)

theorem number_injective (c : EncodedFiniteLTL.Code A) : Function.Injective (number c) := by
  intro p q h
  have he := congrArg (fun i : Fin (states c).length => (states c)[i.val]?) h
  dsimp only at he
  rw [number_lookup, number_lookup] at he
  exact Subtype.ext (quote_injective (Option.some.inj he))

/-- Decode any list position, including a repeated subformula occurrence. -/
def occurrence (c : EncodedFiniteLTL.Code A) (i : Fin (states c).length) :
    (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).Subformula :=
  let h : i.val < (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas.length := by
    simpa only [states_eq, List.length_map] using i.isLt
  ⟨(PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).subformulas[i.val], List.getElem_mem h⟩

omit [DecidableEq A] in
theorem occurrence_lookup (c : EncodedFiniteLTL.Code A) (i : Fin (states c).length) :
    (states c)[i.val]? = some (quote (occurrence c i).val) := by
  rw [List.getElem?_eq_getElem i.isLt]
  simp only [states_eq, List.getElem_map, occurrence]

theorem occurrence_number (c : EncodedFiniteLTL.Code A) :
    Function.LeftInverse (occurrence c) (number c) := by
  intro p
  have h := (occurrence_lookup c (number c p)).symm.trans (number_lookup c p)
  exact Subtype.ext (quote_injective (Option.some.inj h))

theorem index_primrec [Primcodable A] : Primrec₂ (index (A := A)) :=
  Primrec.list_idxOf.comp Primrec.snd (states_primrec.comp Primrec.fst)

end Numbering
end DistributedSynthesis.EncodedPositiveLTL
