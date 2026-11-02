/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.AlternatingRetraction
import DistributedSynthesis.Library.Automata.EncodedLTLTransitions
import DistributedSynthesis.Library.Automata.WeakComputable
import DistributedSynthesis.Library.Automata.EncodedSupportTables

/-! # Semantics of the finite numeric LTL state carrier

Every occurrence is decoded to a semantic subformula. Successor references use
first occurrences. The retraction lemma handles the redundant positions and
supplies a valid weakness measure. This is a semantic interpretation of the
numeric frontend, not a numeric computability proof for the breakpoint stage.
-/

namespace DistributedSynthesis.EncodedLTLAutomaton
open EncodedPositiveLTL
open AlternatingParityAutomaton
variable {A : Type*} [DecidableEq A]

abbrev root (c : EncodedFiniteLTL.Code A) := PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)

def interp (a : A) (valuation : List A) : Prop := a ∈ valuation
def dec (a : A) (valuation : List A) : Decidable (interp a valuation) :=
  inferInstanceAs (Decidable (a ∈ valuation))

@[reducible] noncomputable def source (c : EncodedFiniteLTL.Code A) :=
  PositiveLTL.closureAPA (root c) interp dec

@[reducible] noncomputable def automaton (c : EncodedFiniteLTL.Code A) :
    AlternatingParityAutomaton (List A) :=
  Retraction.automaton (source c) (number c) (occurrence c)

theorem accepts_iff (c : EncodedFiniteLTL.Code A) (word : OmegaWord (List A)) :
    (automaton c).Accepts word ↔ LTL.Satisfies interp word (EncodedFiniteLTL.decode c) :=
  (Retraction.accepts_iff (source c) (number c) (occurrence c) (occurrence_number c) word).trans
    ((PositiveLTL.subformulaClosure_accepts_iff_satisfies (root c) interp dec word).trans
      (PositiveLTL.satisfies_ofLTL interp word _))

noncomputable def measure (c : EncodedFiniteLTL.Code A) : (automaton c).State → Nat :=
  Retraction.measure (source c) (number c) (occurrence c) (fun p => p.val.size)

theorem weak (c : EncodedFiniteLTL.Code A) : SelfOrDecreasing (automaton c) (measure c) :=
  Retraction.selfOrDecreasing (source c) (number c) (occurrence c) (occurrence_number c)
    (fun p => p.val.size) (PositiveLTL.subformulaClosure_selfOrDecreasing (root c) interp dec)

theorem initial_zero (c : EncodedFiniteLTL.Code A) : (automaton c).initial.val = 0 :=
  EncodedLTLTransitions.name_root c

private theorem map_pmap {B C D : Type*} (p : PosBool B)
    (f : ∀ b, b ∈ p.atoms → C) (g : C → D) (h : B → D)
    (he : ∀ b hb, g (f b hb) = h b) : (p.pmap f).map g = p.map h := by
  induction p with
  | verum => rfl
  | falsum => rfl
  | atom a => simp only [PosBool.pmap, PosBool.map, he]
  | conj p q hp hq =>
    simp only [PosBool.pmap, PosBool.map]
    congr 1
    · exact hp _ (fun b _ => he b _)
    · exact hq _ (fun b _ => he b _)

  | disj p q hp hq =>
    simp only [PosBool.pmap, PosBool.map]
    congr 1
    · exact hp _ (fun b _ => he b _)
    · exact hq _ (fun b _ => he b _)

private theorem map_map {B C D : Type*} (p : PosBool B) (f : B → C) (g : C → D) :
    (p.map f).map g = p.map (g ∘ f) := by
  induction p <;> simp_all [PosBool.map]

/-- The semantic automaton uses exactly the compiled transition code. -/
theorem transition_correct (c : EncodedFiniteLTL.Code A) (v : List A)
    (i : Fin (states c).length) :
    EncodedPositiveBoolean.decode
      (EncodedLTLTransitions.transition (c, v) (quote (occurrence c i).val)) =
      ((automaton c).step i v).map Fin.val := by
  letI : ∀ a v, Decidable (interp (A := A) a v) := dec
  rw [EncodedLTLTransitions.transition_correct_of_interp (c, v) interp v (fun _ => Iff.rfl)]
  change _ = (PosBool.map (number c)
      (PositiveLTL.subformulaTransition (root c) interp (occurrence c i) v)).map Fin.val
  rw [map_map]
  unfold PositiveLTL.subformulaTransition
  symm
  apply map_pmap
  intro p hp
  rfl

theorem row_lookup (c : EncodedFiniteLTL.Code A) (v : List A)
    (i : Fin (states c).length) :
    EncodedSupportTables.lookup (EncodedLTLTransitions.row (c, v)) i.val =
      EncodedLTLTransitions.transition (c, v) (quote (occurrence c i).val) := by
  simp only [EncodedSupportTables.lookup, EncodedLTLTransitions.row, List.getElem?_map,
    occurrence_lookup, Option.map_some, Option.getD_some]

theorem row_correct (c : EncodedFiniteLTL.Code A) (v : List A)
    (i : Fin (states c).length) :
    EncodedPositiveBoolean.decode
      (EncodedSupportTables.lookup (EncodedLTLTransitions.row (c, v)) i.val) =
        ((automaton c).step i v).map Fin.val := by
  rw [row_lookup, transition_correct]

theorem priority_correct (c : EncodedFiniteLTL.Code A) (i : Fin (states c).length) :
    (EncodedLTLStates.compile c).2[i.val]?.getD 0 = (automaton c).priority i := by
  simp only [EncodedLTLStates.compile, List.getElem?_map, occurrence_lookup,
    Option.map_some, Option.getD_some, normalize_eq, EncodedLTLStates.priority_quote]
  rfl

/-- Primitive-recursive simultaneous support enumeration for the actual LTL row. -/
def supportTables (ctx : EncodedLTLTransitions.Context A) (frontier : List Nat) :=
  EncodedSupportTables.enumerateTables (EncodedLTLTransitions.row ctx) frontier

theorem supportTables_primrec [Primcodable A] : Primrec₂ (supportTables (A := A)) :=
  EncodedSupportTables.enumerateTables_primrec.comp
    (EncodedLTLTransitions.row_primrec.comp Primrec.fst) Primrec.snd

noncomputable def stepAt (ctx : EncodedLTLTransitions.Context A) (q : Nat) :
    PosBool (Fin (states ctx.1).length) :=
  if h : q < (states ctx.1).length then (automaton ctx.1).step ⟨q, h⟩ ctx.2 else .falsum

theorem supportTables_correct (ctx : EncodedLTLTransitions.Context A) (frontier : List Nat)
    (hb : ∀ q ∈ frontier, q < (states ctx.1).length)
    (selected : List (Nat × Finset (Fin (states ctx.1).length))) :
    (∃ table ∈ supportTables ctx frontier,
      EncodedSupportTables.decoded (states ctx.1).length table = selected) ↔
      List.Forall₂ (fun entry q => entry.1 = q ∧ EncodedSupports.Valid (stepAt ctx q) entry.2)
        selected frontier := by
  apply EncodedSupportTables.tables_complete
  intro q hq
  simpa only [stepAt, dif_pos (hb q hq)] using row_correct ctx.1 ctx.2 ⟨q, hb q hq⟩

/-- Existing weak alternation removal applies to the numeric carrier as well. -/
theorem buchi_accepts_iff (c : EncodedFiniteLTL.Code A) (word : OmegaWord (List A)) :
    (WeakComputable.buchi (automaton c)).Accepts word ↔
      LTL.Satisfies interp word (EncodedFiniteLTL.decode c) :=
  (WeakComputable.buchi_accepts_iff (automaton c) (measure c) (weak c) word).trans
    (accepts_iff c word)

end DistributedSynthesis.EncodedLTLAutomaton
