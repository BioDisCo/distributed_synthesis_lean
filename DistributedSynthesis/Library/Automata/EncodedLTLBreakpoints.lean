/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLAutomaton
import DistributedSynthesis.Library.Automata.EncodedBreakpoints

/-! # Uniform numeric LTL-to-Büchi breakpoint interface

The state list, initial state, accepting test, and full transition predicate use
fixed numeric/list encodings. Their semantics are the existing weak-alternation
removal construction; duplicate subformula occurrences require no new assumption.
-/

namespace DistributedSynthesis.EncodedLTLBreakpoints
open FiniteSubsets EncodedPositiveLTL AlternatingParityAutomaton
variable {A : Type*} [DecidableEq A]

def stateCodes (c : EncodedFiniteLTL.Code A) : List Pair := pairs (states c).length
def initial : Pair := ([0], [])
def accepting (c : EncodedFiniteLTL.Code A) (s : Pair) : Prop :=
  normalize (states c).length s.2 = []
instance (c : EncodedFiniteLTL.Code A) (s : Pair) : Decidable (accepting c s) :=
  inferInstanceAs (Decidable (normalize (states c).length s.2 = []))

def transition (x : EncodedLTLTransitions.Context A × Pair × Pair) : Prop :=
  EncodedBreakpoints.step ((states x.1.1).length, EncodedLTLTransitions.row x.1,
    (EncodedLTLStates.compile x.1.1).2, x.2.1, x.2.2)
instance (x : EncodedLTLTransitions.Context A × Pair × Pair) : Decidable (transition x) :=
  inferInstanceAs (Decidable (EncodedBreakpoints.step _))

omit [DecidableEq A] in
theorem stateCodes_primrec [Primcodable A] : Primrec (stateCodes (A := A)) :=
  pairs_primrec.comp (Primrec.list_length.comp states_primrec)

omit [DecidableEq A] in
theorem accepting_primrec [Primcodable A] : PrimrecRel (accepting (A := A)) :=
  Primrec.eq.comp (normalize_primrec.comp
    (Primrec.list_length.comp (states_primrec.comp Primrec.fst)) (Primrec.snd.comp Primrec.snd))
    (Primrec.const [])

theorem transition_primrec [Primcodable A] : PrimrecPred (transition (A := A)) :=
  EncodedBreakpoints.step_primrec.comp
    ((Primrec.list_length.comp (states_primrec.comp (Primrec.fst.comp Primrec.fst))).pair
      ((EncodedLTLTransitions.row_primrec.comp Primrec.fst).pair
        ((Primrec.snd.comp (EncodedLTLStates.compile_primrec.comp (Primrec.fst.comp Primrec.fst))).pair
          Primrec.snd)))

/-- The complete finite transition graph for one valuation. -/
def edges (ctx : EncodedLTLTransitions.Context A) : List (Pair × Pair) :=
  ((stateCodes ctx.1).product (stateCodes ctx.1)).filter
    (fun edge => decide (transition (ctx, edge)))

theorem edges_primrec [Primcodable A] : Primrec (edges (A := A)) := by
  have h : PrimrecRel (fun (ctx : EncodedLTLTransitions.Context A) (edge : Pair × Pair) =>
      transition (ctx, edge)) := transition_primrec
  exact h.swap.listFilter.comp
    (FiniteSearch.product_primrec.comp (stateCodes_primrec.comp Primrec.fst)
      (stateCodes_primrec.comp Primrec.fst)) Primrec.id

theorem mem_edges (ctx : EncodedLTLTransitions.Context A) (s t : Pair) :
    (s, t) ∈ edges ctx ↔ s ∈ stateCodes ctx.1 ∧ t ∈ stateCodes ctx.1 ∧ transition (ctx, s, t) := by
  have hp : (s, t) ∈ (stateCodes ctx.1).product (stateCodes ctx.1) ↔
      s ∈ stateCodes ctx.1 ∧ t ∈ stateCodes ctx.1 := List.mem_product
  simp only [edges, List.mem_filter, hp, decide_eq_true_eq, and_assoc]

def acceptingCodes (c : EncodedFiniteLTL.Code A) : List Pair :=
  (stateCodes c).filter (fun s => decide (accepting c s))

omit [DecidableEq A] in
theorem acceptingCodes_primrec [Primcodable A] : Primrec (acceptingCodes (A := A)) :=
  accepting_primrec.swap.listFilter.comp stateCodes_primrec Primrec.id

/-- A finite table compiler: state codes, initial code, accepting codes, and
the full edge list for each supplied valuation. -/
def compile (x : EncodedFiniteLTL.Code A × List (List A)) :=
  (stateCodes x.1, initial, acceptingCodes x.1,
    x.2.map (fun letter => (letter, edges (x.1, letter))))

theorem compile_primrec [Primcodable A] : Primrec (compile (A := A)) :=
  (stateCodes_primrec.comp Primrec.fst).pair ((Primrec.const initial).pair
    ((acceptingCodes_primrec.comp Primrec.fst).pair
      (Primrec.list_map Primrec.snd
        (Primrec.snd.pair (edges_primrec.comp
          ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))).to₂)))

noncomputable def decodeState (c : EncodedFiniteLTL.Code A) (s : Pair) :
    (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).State :=
  ⟨decode (states c).length s.1, decode (states c).length s.2⟩

theorem transition_correct (c : EncodedFiniteLTL.Code A) (letter : List A) (current next : Pair) :
    transition ((c, letter), current, next) ↔
      (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).step
        (decodeState c current) letter (decodeState c next) := by
  apply EncodedBreakpoints.Semantic.step_iff_buchiStep
    (EncodedLTLAutomaton.automaton c).initial (EncodedLTLAutomaton.automaton c).step
    (WeakComputable.recolor (EncodedLTLAutomaton.automaton c)).priority
    (EncodedLTLAutomaton.automaton c).stateFinite
  · exact EncodedLTLAutomaton.row_correct c letter
  · intro q
    rw [EncodedLTLAutomaton.priority_correct]
    change (if (EncodedLTLAutomaton.automaton c).priority q % 2 = 0 then 0 else 1) ≠ 0 ↔ _
    split_ifs <;> simp_all

theorem accepting_correct (c : EncodedFiniteLTL.Code A) (s : Pair) :
    accepting c s ↔ (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).accepting (decodeState c s) :=
  normalize_eq_nil_iff _ _

theorem stateCodes_complete (c : EncodedFiniteLTL.Code A)
    (q : (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).State) :
    ∃ s ∈ stateCodes c, decodeState c s = q := by
  obtain ⟨s, hs, he⟩ := pairs_complete (q.frontier, q.pending)
  refine ⟨s, hs, ?_⟩
  apply MiyanoHayashi.BuchiState.ext
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem initial_correct (c : EncodedFiniteLTL.Code A) :
    decodeState c initial = (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).initial := by
  apply MiyanoHayashi.BuchiState.ext
  · change decode (states c).length [0] =
      ({(EncodedLTLAutomaton.automaton c).initial} : Finset (Fin (states c).length))
    ext q
    simpa only [FiniteSubsets.mem_decode, List.mem_singleton, Finset.mem_singleton, Fin.ext_iff]
      using (iff_of_eq (congrArg (fun k => q.val = k) (EncodedLTLAutomaton.initial_zero c))).symm
  · change decode (states c).length [] = ∅
    ext q
    simp

theorem initial_mem_stateCodes (c : EncodedFiniteLTL.Code A) : initial ∈ stateCodes c := by
  have hn := (EncodedLTLAutomaton.automaton c).initial.isLt
  rw [EncodedLTLAutomaton.initial_zero] at hn
  exact List.mem_product.mpr
    ⟨List.mem_sublists'.mpr (List.singleton_sublist.mpr (List.mem_range.mpr hn)),
      List.mem_sublists'.mpr (List.nil_sublist _)⟩

/-- A finite Büchi automaton whose states and tests are the numeric codes above. -/
def buchi (c : EncodedFiniteLTL.Code A) : NondetBuchiAutomaton (List A) where
  State := {s : Pair // s ∈ stateCodes c}
  stateFinite := Fintype.ofFinset (stateCodes c).toFinset (fun _ => List.mem_toFinset)
  initial := ⟨initial, initial_mem_stateCodes c⟩
  step := fun s letter t => transition ((c, letter), s.val, t.val)
  accepting := fun s => accepting c s.val

/-- Numeric and semantic breakpoint runs recognize exactly the same language. -/
theorem buchi_accepts_iff (c : EncodedFiniteLTL.Code A) (word : OmegaWord (List A)) :
    (buchi c).Accepts word ↔
      (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).Accepts word := by
  constructor
  · rintro ⟨run, ha⟩
    let mapped : (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).RunFrom
        (WeakComputable.buchi (EncodedLTLAutomaton.automaton c)).initial word :=
      { path := fun t => decodeState c (run.path t).val
        initial_state := by rw [run.initial_state]; exact initial_correct c
        step_valid := fun t => (transition_correct c (word t) _ _).mp (run.step_valid t) }
    refine ⟨mapped, ?_⟩
    intro t
    obtain ⟨k, hk, ha⟩ := ha t
    exact ⟨k, hk, (accepting_correct c _).mp ha⟩
  · rintro ⟨run, ha⟩
    classical
    choose code hm hd using fun t => stateCodes_complete c (run.path t)
    let path (t : Nat) : (buchi c).State :=
      if t = 0 then (buchi c).initial else ⟨code t, hm t⟩
    have hpath (t : Nat) : decodeState c (path t).val = run.path t := by
      by_cases ht : t = 0
      · subst t
        simpa only [path, if_pos rfl, buchi, run.initial_state] using initial_correct c
      · simpa only [path, if_neg ht] using hd t
    let mapped : (buchi c).RunFrom (buchi c).initial word :=
      { path := path
        initial_state := by simp [path]
        step_valid := by
          intro t
          apply (transition_correct c (word t) _ _).mpr
          rw [hpath, hpath]
          exact run.step_valid t }
    refine ⟨mapped, ?_⟩
    intro t
    obtain ⟨k, hk, ha⟩ := ha t
    exact ⟨k, hk, (accepting_correct c _).mpr (hpath k ▸ ha)⟩

theorem accepts_iff (c : EncodedFiniteLTL.Code A) (word : OmegaWord (List A)) :
    (buchi c).Accepts word ↔ LTL.Satisfies EncodedLTLAutomaton.interp word (EncodedFiniteLTL.decode c) :=
  (buchi_accepts_iff c word).trans (EncodedLTLAutomaton.buchi_accepts_iff c word)

end DistributedSynthesis.EncodedLTLBreakpoints
