/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedThreadCompiler
import DistributedSynthesis.Library.Automata.UniversalThreadsComputable

/-! # Numeric universal-run determinization for finite resolution systems

The existing numeric bad-thread and Piterman compilers are reused unchanged.
The correctness interface is independent of distributed-system records.
-/
namespace DistributedSynthesis.EncodedUniversalThreads

namespace Buchi
open EncodedThreadBuchi

variable {L : Type*} (M : FiniteThreadSystem L)
  [Fintype M.Resolution] [DecidableEq M.State]
  (number : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (number q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ FiniteThreadSystem.Computable.priorityRange M)

def encode (s : FiniteThreadSystem.Computable.GuessState M) : State :=
  ((number s.1).val, s.2.map Subtype.val)

private theorem even_iff (p : Nat) : DetParityAutomaton.NatEven p ↔ p % 2 = 0 := by
  unfold DetParityAutomaton.NatEven
  constructor
  · rintro ⟨k, rfl⟩; omega
  · intro h; exact ⟨p / 2, by omega⟩

include hp hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem step_correct (ed : Edges) (a : L)
    (he : ∀ q r, ((number q).val, (number r).val) ∈ ed ↔
      ∃ i : M.Resolution, r = M.step q a i)
    (s t : FiniteThreadSystem.Computable.GuessState M) :
    step ((ps, ed), encode M number s, encode M number t) ↔
      (FiniteThreadSystem.Computable.buchi M).step s a t := by
  have hsome (tag : Option {p : Nat // p ∈ FiniteThreadSystem.Computable.priorityRange M})
      (p : {p : Nat // p ∈ FiniteThreadSystem.Computable.priorityRange M}) :
      tag.map Subtype.val = some p.val ↔ tag = some p := by
    cases tag with
    | none => simp
    | some t =>
      simp only [Option.map_some, Option.some.injEq]
      exact Subtype.val_injective.eq_iff
  have hex (P : Nat → Prop) : (∃ p ∈ ps, P p) ↔
      ∃ p : {p : Nat // p ∈ FiniteThreadSystem.Computable.priorityRange M}, P p.val := by
    constructor
    · rintro ⟨p, h, hp⟩; exact ⟨⟨p, (hr p).mp h⟩, hp⟩
    · rintro ⟨p, h⟩; exact ⟨p.val, (hr p.val).mpr p.property, h⟩
  simp only [step, encode, he, hp, hex, hsome, Option.map_eq_none_iff,
    FiniteThreadSystem.Computable.buchi, even_iff]

include hp hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem accepting_correct (s : FiniteThreadSystem.Computable.GuessState M) :
    accepting ps (encode M number s) ↔ (FiniteThreadSystem.Computable.buchi M).accepting s := by
  unfold accepting encode FiniteThreadSystem.Computable.buchi
  simp only [hp]
  constructor
  · rintro ⟨p, hmem, ht, he⟩
    obtain ⟨tag, htag, rfl⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨tag, htag, he⟩
  · rintro ⟨tag, htag, he⟩
    exact ⟨tag.val, (hr tag.val).mpr tag.property, by simp [htag], he⟩

include hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem states_complete (s : FiniteThreadSystem.Computable.GuessState M) :
    encode M number s ∈ states (Fintype.card M.State) ps := by
  apply List.mem_product.mpr
  refine ⟨List.mem_range.mpr (number s.1).isLt, ?_⟩
  cases h : s.2 with
  | none => simp [encode, h]
  | some p =>
    simp only [encode, h, Option.map_some, List.mem_cons, List.mem_map]
    exact Or.inr ⟨p.val, (hr p.val).mpr p.property, rfl⟩

omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem encode_injective : Function.Injective (encode M number) := by
  intro s t h
  exact Prod.ext (number.injective (Fin.ext (congrArg Prod.fst h)))
    (Option.map_injective Subtype.val_injective (congrArg Prod.snd h))

include hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem states_sound (c : State) (hc : c ∈ states (Fintype.card M.State) ps) :
    ∃ s : FiniteThreadSystem.Computable.GuessState M, encode M number s = c := by
  obtain ⟨hq, ht⟩ := List.mem_product.mp hc
  have hq' := List.mem_range.mp hq
  let q := number.symm ⟨c.1,hq'⟩
  cases h : c.2 with
  | none =>
    refine ⟨(q,none), ?_⟩
    simp only [encode, q, Equiv.apply_symm_apply, Option.map_none]
    exact Prod.ext rfl h.symm
  | some p =>
    have hp : p ∈ ps := by simpa only [h, List.mem_cons, Option.some_ne_none,
      List.mem_map, Option.some.injEq, exists_eq_right, false_or] using ht
    refine ⟨(q,some ⟨p,(hr p).mp hp⟩), ?_⟩
    simp only [encode, q, Equiv.apply_symm_apply, Option.map_some]
    exact Prod.ext rfl h.symm


end Buchi

namespace Numbering
open EncodedThreadBuchi EncodedThreadNumbering Buchi

variable {L : Type*} (M : FiniteThreadSystem L)
  [Fintype M.Resolution] [DecidableEq M.State]
  (baseNumber : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (baseNumber q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ FiniteThreadSystem.Computable.priorityRange M)

noncomputable def number : FiniteThreadSystem.Computable.GuessState M ≃
    Fin (Fintype.card (FiniteThreadSystem.Computable.GuessState M)) :=
  FiniteCodeNumbering.number (states (Fintype.card M.State) ps) (encode M baseNumber)
    (encode_injective M baseNumber) (states_complete M baseNumber ps hr)
    (states_sound M baseNumber ps hr)

omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem number_val (s : FiniteThreadSystem.Computable.GuessState M) :
    (number M baseNumber ps hr s).val = name (Fintype.card M.State,ps) (encode M baseNumber s) := rfl

include baseNumber hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem card_eq : Fintype.card (FiniteThreadSystem.Computable.GuessState M) =
    (codes (Fintype.card M.State,ps)).length :=
  FiniteCodeNumbering.card_eq _ (encode M baseNumber) (encode_injective M baseNumber)
    (states_complete M baseNumber ps hr) (states_sound M baseNumber ps hr)

include hp hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem edges_correct (es : Edges) (a : L)
    (he : ∀ q r, ((baseNumber q).val,(baseNumber r).val) ∈ es ↔
      ∃ i : M.Resolution, r = M.step q a i)
    (s t : FiniteThreadSystem.Computable.GuessState M) :
    ((number M baseNumber ps hr s).val,(number M baseNumber ps hr t).val) ∈
      edges (Fintype.card M.State,ps) es ↔ (FiniteThreadSystem.Computable.buchi M).step s a t := by
  simp only [EncodedThreadNumbering.edges,List.mem_map,number_val]
  constructor
  · rintro ⟨⟨u,v⟩,hm,heq⟩
    obtain ⟨hu,hv,hstep⟩ := (EncodedThreadBuchi.mem_edges _ _ u v).mp hm
    obtain ⟨hue,hve⟩ := Prod.mk.inj heq
    obtain rfl := FiniteCodeNumbering.name_injective _ hu (states_complete M baseNumber ps hr s) hue
    obtain rfl := FiniteCodeNumbering.name_injective _ hv (states_complete M baseNumber ps hr t) hve
    exact (step_correct M baseNumber ps hp hr es a he s t).mp hstep
  · intro h
    refine ⟨(encode M baseNumber s,encode M baseNumber t),?_,rfl⟩
    exact (EncodedThreadBuchi.mem_edges _ _ _ _).mpr
      ⟨states_complete M baseNumber ps hr s, states_complete M baseNumber ps hr t,
        (step_correct M baseNumber ps hp hr es a he s t).mpr h⟩

include hp hr in
omit [Fintype M.Resolution] [DecidableEq M.State] in
theorem accepting_correct (s : FiniteThreadSystem.Computable.GuessState M) :
    (number M baseNumber ps hr s).val ∈ accepting (Fintype.card M.State,ps) ↔
      (FiniteThreadSystem.Computable.buchi M).accepting s := by
  simp only [EncodedThreadNumbering.accepting,List.mem_map,number_val]
  constructor
  · rintro ⟨t,ht,he⟩
    obtain ⟨ht,hacc⟩ := List.mem_filter.mp ht
    obtain rfl := FiniteCodeNumbering.name_injective _ ht (states_complete M baseNumber ps hr s) he
    exact (Buchi.accepting_correct M baseNumber ps hp hr s).mp (of_decide_eq_true hacc)
  · intro h
    exact ⟨encode M baseNumber s,List.mem_filter.mpr ⟨states_complete M baseNumber ps hr s,
      decide_eq_true ((Buchi.accepting_correct M baseNumber ps hp hr s).mpr h)⟩,rfl⟩

end Numbering

open EncodedThreadBuchi EncodedThreadCompiler

private theorem cast_automaton_congr {k : Nat} (x y : EncodedPitermanCompiler.Input)
    (h : x = y) (hx : x.2.2.2.length = k) (hy : y.2.2.2.length = k) :
    (EncodedPitermanCompiler.automaton x).comap (Fin.cast hx.symm) =
      (EncodedPitermanCompiler.automaton y).comap (Fin.cast hy.symm) := by
  cases h
  rfl

variable {L : Type*} (M : FiniteThreadSystem L)
  [Fintype M.Resolution] [DecidableEq M.State]
  (baseNumber : M.State ≃ Fin (Fintype.card M.State)) (ps : List Nat)
  (hp : ∀ q, ps.getD (baseNumber q).val 0 = M.priority q)
  (hr : ∀ p, p ∈ ps ↔ p ∈ FiniteThreadSystem.Computable.priorityRange M)
  (es : List Edges) (letter : Fin es.length → L)
  (he : ∀ q (a : Fin es.length) r,
    ((baseNumber q).val,(baseNumber r).val) ∈ es[a.val]?.getD [] ↔
      ∃ i : M.Resolution, r = M.step q (letter a) i)

def sourceData : Input := (Fintype.card M.State,(baseNumber M.initial).val,ps,es)

def sourceBuchi : NondetBuchiAutomaton (Fin es.length) where
  State := FiniteThreadSystem.Computable.GuessState M
  stateFinite := inferInstance
  initial := (M.initial,none)
  step := fun q a r => (FiniteThreadSystem.Computable.buchi M).step q (letter a) r
  accepting := (FiniteThreadSystem.Computable.buchi M).accepting

local instance : DecidableEq (sourceBuchi M es letter).State :=
  inferInstanceAs (DecidableEq (FiniteThreadSystem.Computable.GuessState M))

include hp hr he in
theorem bad_accepts_iff (word : OmegaWord (Fin es.length)) :
    (badAutomaton (sourceData M baseNumber ps es)).Accepts word ↔
      (FiniteThreadSystem.Computable.buchi M).Accepts (OmegaWord.map letter word) := by
  let B := sourceBuchi M es letter
  let num := Numbering.number M baseNumber ps hr
  have hc : EncodedThreadNumbering.compile (sourceData M baseNumber ps es) =
      (Fintype.card B.State, (num B.initial).val,
        EncodedThreadNumbering.accepting (Fintype.card M.State,ps),
        es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps))) := by
    unfold EncodedThreadNumbering.compile sourceData
    rw [← Numbering.card_eq M baseNumber ps hr]
    rfl
  have hlen : (es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps))).length = es.length :=
    List.length_map _
  have hedge (q : B.State) (a : Fin es.length) (r : B.State) :
      ((num q).val,(num r).val) ∈
        (es.map (EncodedThreadNumbering.edges (Fintype.card M.State,ps)))[a.val]?.getD [] ↔ B.step q a r := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem a.isLt, Option.map_some, Option.getD_some]
    apply Numbering.edges_correct M baseNumber ps hp hr _ (letter a)
    intro q r
    simpa only [List.getElem?_eq_getElem a.isLt, Option.getD_some] using he q a r
  have hacc (q : B.State) : (num q).val ∈
      EncodedThreadNumbering.accepting (Fintype.card M.State,ps) ↔ B.accepting q :=
    Numbering.accepting_correct M baseNumber ps hp hr q
  have h := EncodedPitermanCompiler.accepts_iff B num
    (fun q a r => FiniteThreadSystem.Computable.stepDecidable M q (letter a) r)
    (FiniteThreadSystem.Computable.acceptingDecidable M) _ hlen _ hedge hacc word
  have hEq := cast_automaton_congr _ _ hc
    (EncodedThreadNumbering.alphabet_size (sourceData M baseNumber ps es)) hlen
  have hProp := congrArg (fun D : DetParityAutomaton (Fin es.length) => D.Accepts word) hEq
  refine (Iff.of_eq hProp).trans (h.trans ?_)
  constructor <;> rintro ⟨run,hrun⟩ <;>
    exact ⟨⟨run.path,run.initial_state,run.step_valid⟩,hrun⟩


include hp hr he in
/-- Numeric compilation checks every resolution sequence of the given system. -/
theorem accepts_iff (word : OmegaWord (Fin es.length)) :
    (EncodedThreadCompiler.automaton (sourceData M baseNumber ps es)).Accepts word ↔
      ∀ q : Nat → M.State, M.IsRun (OmegaWord.map letter word) q →
        NatSeqMinEvenParity (fun n => M.priority (q n)) := by
  rw [EncodedThreadCompiler.automaton,
    DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts,
    bad_accepts_iff M baseNumber ps hp hr es letter he,
    FiniteThreadSystem.Computable.buchi_eq, FiniteThreadSystem.violationBuchi_accepts_iff]
  constructor
  · intro hnot q hrun
    rcases natSeqMinEvenParity_or_minOddParity (fun n => M.priority (q n))
      (M.priority_range_finite q) with heven | hodd
    · exact heven
    · exact absurd ⟨q, hrun, hodd⟩ hnot
  · rintro hall ⟨q, hrun, hodd⟩
    exact not_natSeqMinEvenParity_and_natSeqMinOddParity _ ⟨hall q hrun, hodd⟩

end DistributedSynthesis.EncodedUniversalThreads
