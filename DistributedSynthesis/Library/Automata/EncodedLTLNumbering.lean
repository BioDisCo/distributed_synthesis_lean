/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLBreakpoints
import DistributedSynthesis.Library.Automata.EncodedPitermanCompiler
import Mathlib.Data.List.NodupEquivFin

/-! # Explicit numbering of the LTL breakpoint automaton

Numbers are positions in the already computed, duplicate-free list of subset
pairs. The numeric operations use list search, not a chosen finite-type
equivalence. The semantic equivalence below certifies exactly that search.
-/

namespace DistributedSynthesis.EncodedLTLNumbering
open EncodedLTLBreakpoints
local instance : BEq FiniteSubsets.Pair := instBEqOfDecidableEq
variable {A : Type*} [DecidableEq A]

def name (c : EncodedFiniteLTL.Code A) (s : FiniteSubsets.Pair) : Nat := (stateCodes c).idxOf s
def edges (ctx : EncodedLTLTransitions.Context A) : EncodedPitermanTransition.Edges :=
  (EncodedLTLBreakpoints.edges ctx).map (fun e => (name ctx.1 e.1, name ctx.1 e.2))
def accepting (c : EncodedFiniteLTL.Code A) : List Nat := (acceptingCodes c).map (name c)
def compile (x : EncodedFiniteLTL.Code A × List (List A)) : EncodedPitermanCompiler.Input :=
  ((stateCodes x.1).length, name x.1 initial, accepting x.1,
    x.2.map (fun a => edges (x.1, a)))

omit [DecidableEq A] in
theorem name_primrec [Primcodable A] : Primrec₂ (name (A := A)) :=
  Primrec.list_idxOf.comp Primrec.snd (stateCodes_primrec.comp Primrec.fst)
theorem edges_primrec [Primcodable A] : Primrec (edges (A := A)) :=
  Primrec.list_map EncodedLTLBreakpoints.edges_primrec
    ((name_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (name_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))).to₂
omit [DecidableEq A] in
theorem accepting_primrec [Primcodable A] : Primrec (accepting (A := A)) :=
  Primrec.list_map acceptingCodes_primrec name_primrec
theorem compile_primrec [Primcodable A] : Primrec (compile (A := A)) :=
  (Primrec.list_length.comp (stateCodes_primrec.comp Primrec.fst)).pair
    ((name_primrec.comp Primrec.fst (Primrec.const initial)).pair
      ((accepting_primrec.comp Primrec.fst).pair
        (Primrec.list_map Primrec.snd
          (edges_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂)))

omit [DecidableEq A] in
theorem stateCodes_nodup (c : EncodedFiniteLTL.Code A) : (stateCodes c).Nodup :=
  (List.nodup_sublists'.mpr List.nodup_range).product
    (List.nodup_sublists'.mpr List.nodup_range)

def equiv (c : EncodedFiniteLTL.Code A) : (buchi c).State ≃ Fin (stateCodes c).length :=
  (List.Nodup.getEquiv (stateCodes c) (stateCodes_nodup c)).symm

instance stateDecidableEq (c : EncodedFiniteLTL.Code A) : DecidableEq (buchi c).State :=
  inferInstanceAs (DecidableEq {s : FiniteSubsets.Pair // s ∈ stateCodes c})

theorem card_eq (c : EncodedFiniteLTL.Code A) : Fintype.card (buchi c).State = (stateCodes c).length := by
  simpa using Fintype.card_congr (equiv c)

def number (c : EncodedFiniteLTL.Code A) : (buchi c).State ≃ Fin (Fintype.card (buchi c).State) :=
  (equiv c).trans (finCongr (card_eq c).symm)

theorem number_val (c : EncodedFiniteLTL.Code A) (s : (buchi c).State) :
    (number c s).val = name c s.val := rfl

theorem name_injective (c : EncodedFiniteLTL.Code A) {s t : FiniteSubsets.Pair}
    (hs : s ∈ stateCodes c) (ht : t ∈ stateCodes c) (h : name c s = name c t) : s = t :=
  congrArg Subtype.val ((equiv c).injective
    (show equiv c ⟨s, hs⟩ = equiv c ⟨t, ht⟩ from Fin.ext h))

theorem edges_correct (c : EncodedFiniteLTL.Code A) (a : List A) (s t : (buchi c).State) :
    ((number c s).val, (number c t).val) ∈ edges (c, a) ↔ (buchi c).step s a t := by
  simp only [edges, List.mem_map, number_val]
  constructor
  · rintro ⟨⟨u, v⟩, hm, he⟩
    obtain ⟨hu, hv⟩ := Prod.mk.inj he
    obtain ⟨hu', hv', hstep⟩ := (mem_edges (c, a) u v).mp hm
    obtain rfl := name_injective c hu' s.property hu
    obtain rfl := name_injective c hv' t.property hv
    exact hstep
  · intro h
    exact ⟨(s.val, t.val), (mem_edges (c, a) _ _).mpr ⟨s.property, t.property, h⟩, rfl⟩

theorem accepting_correct (c : EncodedFiniteLTL.Code A) (s : (buchi c).State) :
    (number c s).val ∈ accepting c ↔ (buchi c).accepting s := by
  simp only [accepting, List.mem_map, number_val]
  constructor
  · rintro ⟨t, ht, he⟩
    have ht' := List.mem_filter.mp ht
    obtain rfl := name_injective c ht'.1 s.property he
    change EncodedLTLBreakpoints.accepting c s.val
    exact of_decide_eq_true ht'.2
  · intro h
    exact ⟨s.val, List.mem_filter.mpr ⟨s.property, decide_eq_true h⟩, rfl⟩

end DistributedSynthesis.EncodedLTLNumbering
