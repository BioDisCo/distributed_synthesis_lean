/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedSupportTables
import DistributedSynthesis.Library.Automata.MiyanoHayashiComputable
import DistributedSynthesis.Library.Computability.FiniteSubsets

/-! # Numeric breakpoint transitions

States are pairs of canonical bounded subset lists. One simultaneous support
table determines both successor components; pending obligations reset exactly
when their decoded set is empty. The transition search is uniformly primitive
recursive in the state bound, transition row, priorities, and endpoint codes.
-/

namespace DistributedSynthesis.EncodedBreakpoints
open FiniteSubsets
open EncodedSupportTables

abbrev Input := Nat × Row × List Nat × Pair × Pair

def step (x : Input) : Prop :=
  ∃ table ∈ enumerateTables x.2.1 (normalize x.1 x.2.2.2.1.1),
    normalizePair x.1 (advance x.2.2.1 (normalize x.1 x.2.2.2.1.2) table) =
      normalizePair x.1 x.2.2.2.2

instance (x : Input) : Decidable (step x) := by unfold step; infer_instance

theorem step_primrec : PrimrecPred step := by
  have hn : Primrec (fun x : Input => x.1) := Primrec.fst
  have hr : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun x : Input => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun x : Input => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have ht : Primrec (fun x : Input => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hf := normalize_primrec.comp hn (Primrec.fst.comp hc)
  have ho := normalize_primrec.comp hn (Primrec.snd.comp hc)
  exact FiniteSearch.exists_mem (enumerateTables_primrec.comp hr hf)
    (Primrec.eq.comp
      (normalizePair_primrec.comp (hn.comp Primrec.fst)
        (advance_primrec.comp ((hp.comp Primrec.fst).pair
          ((ho.comp Primrec.fst).pair Primrec.snd))))
      ((normalizePair_primrec.comp hn ht).comp Primrec.fst))

/-- Distinct source tags make a list of simultaneous choices a function. -/
theorem choices_function {S : Type} [Inhabited S] (valid : Nat → S → Prop)
    (frontier : List Nat) (hn : frontier.Nodup) (selected : List (Nat × S)) :
    List.Forall₂ (fun entry q => entry.1 = q ∧ valid q entry.2) selected frontier ↔
      ∃ f : Nat → S, selected = frontier.map (fun q => (q, f q)) ∧
        ∀ q ∈ frontier, valid q (f q) := by
  induction frontier generalizing selected with
  | nil => simp
  | cons q qs ih =>
    obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
    constructor
    · intro h
      cases h with
      | @cons entry _ tail _ hhead htail =>
        obtain ⟨f, rfl, hf⟩ := (ih hnodup _).mp htail
        refine ⟨fun r => if r = q then entry.2 else f r, ?_, ?_⟩
        · simp only [List.map_cons, if_pos rfl]
          congr 1
          · exact Prod.ext hhead.1 rfl
          · apply List.map_congr_left
            intro r hr
            simp [show r ≠ q from fun he => hnot (he ▸ hr)]
        · intro r hr
          rcases List.mem_cons.mp hr with rfl | hr
          · simpa using hhead.2
          · simpa [show r ≠ q from fun he => hnot (he ▸ hr)] using hf r hr
    · rintro ⟨f, rfl, hf⟩
      exact List.Forall₂.cons ⟨rfl, hf q (by simp)⟩
        ((ih hnodup _).mpr ⟨f, rfl, fun r hr => hf r (by simp [hr])⟩)

def union {n : Nat} (frontier : List Nat) (f : Nat → Finset (Fin n)) : Finset (Fin n) :=
  frontier.toFinset.biUnion f

def pendingUnion {n : Nat} (frontier pending : List Nat)
    (f : Nat → Finset (Fin n)) : Finset (Fin n) :=
  (frontier.filter (fun q => decide (q ∈ pending))).toFinset.biUnion f

theorem decoded_successors {n : Nat} (table : Table) (frontier : List Nat)
    (f : Nat → Finset (Fin n))
    (he : decoded n table = frontier.map (fun q => (q, f q))) :
    decode n (successors table) = union frontier f := by
  ext q
  simp only [mem_decode, mem_successors, union, Finset.mem_biUnion, List.mem_toFinset]
  constructor
  · rintro ⟨entry, ht, hq⟩
    have : (entry.1, EncodedSupports.decodeSet n entry.2) ∈ decoded n table :=
      List.mem_map.mpr ⟨entry, ht, rfl⟩
    rw [he] at this
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq
    have hq' : q ∈ EncodedSupports.decodeSet n entry.2 := by simpa using hq
    exact ⟨r, hr, heq.2.symm ▸ hq'⟩
  · rintro ⟨r, hr, hq⟩
    have : (r, f r) ∈ decoded n table := he ▸ List.mem_map.mpr ⟨r, hr, rfl⟩
    obtain ⟨entry, ht, heq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq
    have hq' : q ∈ EncodedSupports.decodeSet n entry.2 := heq.2.symm ▸ hq
    exact ⟨entry, ht, by simpa using hq'⟩

theorem decoded_pendingSuccessors {n : Nat} (table : Table) (frontier pending : List Nat)
    (f : Nat → Finset (Fin n))
    (he : decoded n table = frontier.map (fun q => (q, f q))) :
    decode n (pendingSuccessors table pending) = pendingUnion frontier pending f := by
  ext q
  simp only [mem_decode, mem_pendingSuccessors, pendingUnion, Finset.mem_biUnion,
    List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨entry, ht, hp, hq⟩
    have : (entry.1, EncodedSupports.decodeSet n entry.2) ∈ decoded n table :=
      List.mem_map.mpr ⟨entry, ht, rfl⟩
    rw [he] at this
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq
    have hq' : q ∈ EncodedSupports.decodeSet n entry.2 := by simpa using hq
    exact ⟨r, ⟨hr, heq.1.symm ▸ hp⟩, heq.2.symm ▸ hq'⟩
  · rintro ⟨r, ⟨hr, hp⟩, hq⟩
    have : (r, f r) ∈ decoded n table := he ▸ List.mem_map.mpr ⟨r, hr, rfl⟩
    obtain ⟨entry, ht, heq⟩ := List.mem_map.mp this
    simp only [Prod.mk.injEq] at heq
    have hq' : q ∈ EncodedSupports.decodeSet n entry.2 := heq.2.symm ▸ hq
    exact ⟨entry, ht, heq.1.symm ▸ hp, by simpa using hq'⟩

def nextObligations {n : Nat} (priorities : List Nat) (frontier pending : List Nat)
    (f : Nat → Finset (Fin n)) : Finset (Fin n) :=
  (if pending = [] then union frontier f else pendingUnion frontier pending f).filter
    (fun q => priorities[q.val]?.getD 0 % 2 ≠ 0)

theorem decoded_nextPending {n : Nat} (priorities : List Nat) (table : Table)
    (frontier pending : List Nat) (f : Nat → Finset (Fin n))
    (he : decoded n table = frontier.map (fun q => (q, f q))) :
    decode n (nextPending priorities table pending) = nextObligations priorities frontier pending f := by
  have hs := decoded_successors table frontier f he
  have hp := decoded_pendingSuccessors table frontier pending f he
  ext q
  have hsq := Finset.ext_iff.mp hs q
  have hpq := Finset.ext_iff.mp hp q
  simp only [mem_decode] at hsq hpq
  simp only [mem_decode, mem_nextPending, nextObligations, Finset.mem_filter]
  split_ifs <;> simp_all

/-- Exact set semantics of the numeric search, with one choice function. -/
theorem step_iff_choices {n : Nat} (row : Row) (priorities : List Nat) (current next : Pair)
    (transition : Nat → PosBool (Fin n))
    (hc : ∀ q ∈ normalize n current.1,
      EncodedPositiveBoolean.decode (lookup row q) = (transition q).map Fin.val) :
    step (n, row, priorities, current, next) ↔
      ∃ f : Nat → Finset (Fin n),
        (∀ q ∈ normalize n current.1, EncodedSupports.Valid (transition q) (f q)) ∧
        decode n next.1 = union (normalize n current.1) f ∧
        decode n next.2 = nextObligations priorities (normalize n current.1)
          (normalize n current.2) f := by
  constructor
  · rintro ⟨table, ht, he⟩
    have hv := (tables_complete row (normalize n current.1) transition hc (decoded n table)).mp
      ⟨table, ht, rfl⟩
    obtain ⟨f, hf, hv⟩ := (choices_function (fun q s => EncodedSupports.Valid (transition q) s)
      _ (normalize_nodup _ _) _).mp hv
    have he' := (normalizePair_eq_iff _ _ _).mp he
    refine ⟨f, hv, ?_, ?_⟩
    · exact (congrArg Prod.fst he').symm.trans (decoded_successors _ _ _ hf)
    · exact (congrArg Prod.snd he').symm.trans (decoded_nextPending _ _ _ _ _ hf)
  · rintro ⟨f, hv, hs, hp⟩
    have hv' := (choices_function (fun q s => EncodedSupports.Valid (transition q) s)
      _ (normalize_nodup n current.1) _).mpr ⟨f, rfl, hv⟩
    obtain ⟨table, ht, he⟩ := (tables_complete row _ transition hc _).mpr hv'
    refine ⟨table, ht, (normalizePair_eq_iff _ _ _).mpr (Prod.ext ?_ ?_)⟩
    · exact (decoded_successors _ _ _ he).trans hs.symm
    · exact (decoded_nextPending _ _ _ _ _ he).trans hp.symm

open AlternatingParityAutomaton
namespace Semantic

/-- The finite carrier is explicit; its enumeration need not be a chosen default. -/
@[reducible] def automaton {n : Nat} {L : Type*} (initial : Fin n)
    (transition : Fin n → L → PosBool (Fin n)) (priority : Fin n → Nat)
    (finite : Fintype (Fin n)) : AlternatingParityAutomaton L where
  State := Fin n
  stateFinite := finite
  initial := initial
  step := transition
  priority := priority

variable {n : Nat} {L : Type*} (initial : Fin n)
  (transition : Fin n → L → PosBool (Fin n)) (priority : Fin n → Nat)
  (finite : Fintype (Fin n))

local notation "B" => automaton initial transition priority finite

def state (s : Pair) : MiyanoHayashi.BuchiState B := ⟨decode n s.1, decode n s.2⟩

def tableOfFunction (frontier : List Nat) (f : Nat → Finset (Fin n)) :
    MiyanoHayashi.Computable.Table B (decode n frontier) := fun q => f q.val.val

theorem successors_eq (frontier : List Nat) (f : Nat → Finset (Fin n)) :
    MiyanoHayashi.Computable.successors B (tableOfFunction initial transition priority finite frontier f) =
      union (normalize n frontier) f := by
  ext q
  simp only [MiyanoHayashi.Computable.successors, Finset.mem_biUnion,
    Finset.mem_attach, true_and, tableOfFunction, union, List.mem_toFinset, mem_normalize]
  constructor
  · rintro ⟨r, hq⟩
    exact ⟨r.val.val, ⟨r.val.isLt, (mem_decode _ _ _).mp r.property⟩, hq⟩
  · rintro ⟨r, ⟨hr, hm⟩, hq⟩
    exact ⟨⟨⟨r, hr⟩, (mem_decode _ _ _).mpr hm⟩, hq⟩

theorem pendingSuccessors_eq (frontier pending : List Nat) (f : Nat → Finset (Fin n)) :
    MiyanoHayashi.Computable.pendingSuccessors B
      (tableOfFunction initial transition priority finite frontier f) (decode n pending) =
      pendingUnion (normalize n frontier) (normalize n pending) f := by
  ext q
  simp only [MiyanoHayashi.Computable.pendingSuccessors, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_attach, true_and, tableOfFunction,
    pendingUnion, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, mem_normalize, mem_decode]
  constructor
  · rintro ⟨r, hp, hq⟩
    exact ⟨r.val.val, ⟨⟨r.val.isLt, (mem_decode _ _ _).mp r.property⟩,
      ⟨r.val.isLt, hp⟩⟩, hq⟩
  · rintro ⟨r, ⟨⟨hr, hm⟩, _, hp⟩, hq⟩
    exact ⟨⟨⟨r, hr⟩, (mem_decode _ _ _).mpr hm⟩, hp, hq⟩

theorem nextPending_eq (priorities : List Nat)
    (hp : ∀ q : Fin n, priority q ≠ 0 ↔ priorities[q.val]?.getD 0 % 2 ≠ 0)
    (frontier pending : List Nat) (f : Nat → Finset (Fin n)) :
    MiyanoHayashi.Computable.nextPending B
      (tableOfFunction initial transition priority finite frontier f) (decode n pending) =
      nextObligations priorities (normalize n frontier) (normalize n pending) f := by
  unfold MiyanoHayashi.Computable.nextPending nextObligations
  rw [successors_eq, pendingSuccessors_eq]
  simp only [normalize_eq_nil_iff]
  ext q
  simp only [Finset.mem_filter, hp]

def functionOfTable (frontier : List Nat)
    (table : MiyanoHayashi.Computable.Table B (decode n frontier)) (q : Nat) : Finset (Fin n) :=
  if h : q < n then
    if hm : (⟨q, h⟩ : Fin n) ∈ decode n frontier then table ⟨⟨q, h⟩, hm⟩ else ∅
  else ∅

theorem tableOfFunction_inverse (frontier : List Nat)
    (table : MiyanoHayashi.Computable.Table B (decode n frontier)) :
    tableOfFunction initial transition priority finite frontier
      (functionOfTable initial transition priority finite frontier table) = table := by
  funext q
  simp [tableOfFunction, functionOfTable, q.val.isLt, q.property]

def transitionAt (letter : L) (q : Nat) : PosBool (Fin n) :=
  if h : q < n then transition ⟨q, h⟩ letter else .falsum

theorem valid_iff (letter : L) (frontier : List Nat) (f : Nat → Finset (Fin n)) :
    MiyanoHayashi.Computable.Valid B letter
      (tableOfFunction initial transition priority finite frontier f) ↔
      ∀ q ∈ normalize n frontier, EncodedSupports.Valid (transitionAt transition letter q) (f q) := by
  constructor
  · intro hv q hq
    obtain ⟨hb, hm⟩ := (mem_normalize _ _ _).mp hq
    simpa only [transitionAt, dif_pos hb] using hv ⟨⟨q, hb⟩, (mem_decode _ _ _).mpr hm⟩
  · intro hv q
    simpa only [transitionAt, dif_pos q.val.isLt] using hv q.val.val
      ((mem_normalize _ _ _).mpr ⟨q.val.isLt, (mem_decode _ _ _).mp q.property⟩)

/-- The entire numeric transition relation, not just its separate updates,
agrees with the existing simultaneous-support construction. -/
theorem step_iff_tableStep (row : Row) (priorities : List Nat) (letter : L)
    (hc : ∀ q : Fin n, EncodedPositiveBoolean.decode (lookup row q.val) =
      (transition q letter).map Fin.val)
    (hp : ∀ q : Fin n, priority q ≠ 0 ↔ priorities[q.val]?.getD 0 % 2 ≠ 0)
    (current next : Pair) :
    step (n, row, priorities, current, next) ↔
      MiyanoHayashi.Computable.TableStep B (state initial transition priority finite current) letter
        (state initial transition priority finite next) := by
  have hc' : ∀ q ∈ normalize n current.1,
      EncodedPositiveBoolean.decode (lookup row q) =
        (transitionAt transition letter q).map Fin.val := by
    intro q hq
    have hb := ((mem_normalize _ _ _).mp hq).1
    simpa only [transitionAt, dif_pos hb] using hc ⟨q, hb⟩
  rw [step_iff_choices row priorities current next _ hc']
  constructor
  · rintro ⟨f, hv, hs, ho⟩
    refine ⟨tableOfFunction initial transition priority finite current.1 f,
      (valid_iff initial transition priority finite letter current.1 f).mpr hv, ?_, ?_⟩
    · exact hs.trans (successors_eq initial transition priority finite _ _).symm
    · exact ho.trans (nextPending_eq initial transition priority finite priorities hp _ _ _).symm
  · rintro ⟨table, hv, hs, ho⟩
    let f := functionOfTable initial transition priority finite current.1 table
    have he : tableOfFunction initial transition priority finite current.1 f = table :=
      tableOfFunction_inverse initial transition priority finite current.1 table
    refine ⟨f, (valid_iff initial transition priority finite letter current.1 f).mp (he.symm ▸ hv),
      ?_, ?_⟩
    · exact hs.trans (he ▸ successors_eq initial transition priority finite _ f)
    · exact ho.trans (he ▸ nextPending_eq initial transition priority finite priorities hp _ _ f)

theorem step_iff_buchiStep (row : Row) (priorities : List Nat) (letter : L)
    (hc : ∀ q : Fin n, EncodedPositiveBoolean.decode (lookup row q.val) =
      (transition q letter).map Fin.val)
    (hp : ∀ q : Fin n, priority q ≠ 0 ↔ priorities[q.val]?.getD 0 % 2 ≠ 0)
    (current next : Pair) :
    step (n, row, priorities, current, next) ↔
      MiyanoHayashi.buchiStep B (state initial transition priority finite current) letter
        (state initial transition priority finite next) :=
  (step_iff_tableStep initial transition priority finite row priorities letter hc hp current next).trans
    (MiyanoHayashi.Computable.step_iff B _ _ _).symm

end Semantic
end DistributedSynthesis.EncodedBreakpoints
