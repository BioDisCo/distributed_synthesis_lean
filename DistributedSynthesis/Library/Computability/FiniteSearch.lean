/- Project authors: see AUTHORS.md at the repository root. -/

import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Sections

/-! # Uniform bounded search on encoded parameters

The bound may depend on the input. These lemmas prove numeric primitive
recursiveness, not merely the existence of a Lean decision instance.
-/

namespace DistributedSynthesis.FiniteSearch

theorem tabulate_eq_ofFn {A : Type*} {n : Nat} (f : Nat → A) (g : Fin n → A)
    (h : ∀ q : Fin n, f q.val = g q) : (List.range n).map f = List.ofFn g := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simpa using h ⟨i, by simpa using hj⟩

/-- Minimum of a finite list, bounded above by an explicit default. -/
def minWith (fallback : Nat) (xs : List Nat) : Nat := xs.foldr min fallback

theorem minWith_primrec : Primrec₂ minWith :=
  Primrec.list_foldr Primrec.snd Primrec.fst
    (Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem le_minWith (k fallback : Nat) (xs : List Nat) :
    k ≤ minWith fallback xs ↔ k ≤ fallback ∧ ∀ r ∈ xs, k ≤ r := by
  induction xs <;> simp_all [minWith, le_min_iff, and_assoc, and_left_comm]

theorem minWith_le_default (fallback : Nat) (xs : List Nat) : minWith fallback xs ≤ fallback :=
  ((le_minWith _ _ _).mp le_rfl).1

theorem minWith_le_mem (fallback : Nat) (xs : List Nat) {r : Nat} (h : r ∈ xs) :
    minWith fallback xs ≤ r := ((le_minWith _ _ _).mp le_rfl).2 r h

/-- Uniform enumeration of a finite Cartesian product. -/
theorem product_primrec {A B : Type*} [Primcodable A] [Primcodable B] :
    Primrec₂ (List.product (α := A) (β := B)) := by
  exact Primrec.list_flatMap Primrec.fst
    (Primrec.list_map (Primrec.snd.comp Primrec.fst)
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂

/-- Exhaustive sublist enumeration, including the empty support. -/
theorem sublists_primrec {A : Type*} [Primcodable A] : Primrec (List.sublists' (α := A)) := by
  have hf : Primrec (fun xs : List A => xs.foldr
      (fun a tails => tails ++ tails.map (List.cons a)) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_append.comp (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.snd.comp Primrec.snd)
          (Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
            Primrec.snd).to₂)).to₂
  exact hf.of_eq (fun xs => by
    induction xs <;> simp_all [List.sublists'_cons, List.sublists'_nil])

/-- Enumerate simultaneous choices, one from each finite list. -/
theorem sections_primrec {A : Type*} [Primcodable A] : Primrec (List.sections (α := A)) := by
  have hf : Primrec (fun xs : List (List A) => xs.foldr
      (fun choices tails => tails.flatMap (fun tail => choices.map (fun a => a :: tail))) [[]]) :=
    Primrec.list_foldr Primrec.id (Primrec.const [[]])
      (Primrec.list_flatMap (Primrec.snd.comp Primrec.snd)
        (Primrec.list_map (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂).to₂).to₂
  exact hf.of_eq (fun xs => by induction xs <;> simp_all [List.sections])

variable {X : Type*} [Primcodable X]

/-- All fixed-length lists over an explicitly enumerated alphabet. -/
def words {A : Type*} (choices : List A) (n : Nat) : List (List A) :=
  ((List.range n).map (fun _ => choices)).sections

theorem words_primrec {A : Type*} [Primcodable A] : Primrec₂ (words (A := A)) :=
  sections_primrec.comp (Primrec.list_map (Primrec.list_range.comp Primrec.snd)
    (Primrec.fst.comp Primrec.fst).to₂)

theorem ofFn_mem_words {A : Type*} (choices : List A) {n : Nat} (f : Fin n → A)
    (h : ∀ q, f q ∈ choices) : List.ofFn f ∈ words choices n := by
  rw [words, List.mem_sections, List.forall₂_iff_get]
  refine ⟨by simp, ?_⟩
  intro i hi hj
  simpa using h ⟨i, by simpa using hi⟩

theorem exists_lt {bound : X → Nat} {p : X → Nat → Prop}
    (hb : Primrec bound) (hp : PrimrecRel p) :
    PrimrecPred (fun x => ∃ i < bound x, p x i) := by
  exact ((hp.swap.exists_mem_list).comp (Primrec.list_range.comp hb) Primrec.id).of_eq
    (by simp)

theorem forall_lt {bound : X → Nat} {p : X → Nat → Prop}
    (hb : Primrec bound) (hp : PrimrecRel p) :
    PrimrecPred (fun x => ∀ i < bound x, p x i) := by
  exact ((hp.swap.forall_mem_list).comp (Primrec.list_range.comp hb) Primrec.id).of_eq
    (by simp)

theorem exists_mem {A : Type*} [Primcodable A] {xs : X → List A} {p : X → A → Prop}
    (hx : Primrec xs) (hp : PrimrecRel p) :
    PrimrecPred (fun x => ∃ a ∈ xs x, p x a) :=
  hp.swap.exists_mem_list.comp hx Primrec.id

theorem forall_mem {A : Type*} [Primcodable A] {xs : X → List A} {p : X → A → Prop}
    (hx : Primrec xs) (hp : PrimrecRel p) :
    PrimrecPred (fun x => ∀ a ∈ xs x, p x a) :=
  hp.swap.forall_mem_list.comp hx Primrec.id

/-- Prepend each possible entry to each previously enumerated table. -/
def extend (alphabet : Nat) (tails : List (List Nat)) : List (List Nat) :=
  (List.range alphabet).flatMap fun a => tails.map (List.cons a)

/-- All length-`size` tables with entries below `alphabet`. -/
def tables (alphabet : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | size + 1 => extend alphabet (tables alphabet size)

theorem extend_primrec : Primrec₂ extend := by
  have hcons : Primrec₂ (fun (a : Nat) (tails : List (List Nat)) => tails.map (List.cons a)) :=
    Primrec.list_map Primrec.snd
      ((Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
  exact Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
    ((hcons.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂)

theorem tables_primrec : Primrec₂ tables := by
  have h := Primrec.nat_rec (Primrec.const ([[]] : List (List Nat)))
    ((extend_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).to₂)
  apply h.of_eq
  intro alphabet size
  induction size with
  | zero => rfl
  | succ size ih => simpa only [tables, Nat.rec_add_one] using congrArg (extend alphabet) ih

theorem mem_tables_iff (alphabet size : Nat) (xs : List Nat) :
    xs ∈ tables alphabet size ↔ xs.length = size ∧ ∀ x ∈ xs, x < alphabet := by
  induction size generalizing xs with
  | zero => cases xs <;> simp [tables]
  | succ size ih =>
    cases xs with
    | nil => simp [tables, extend]
    | cons x xs =>
      simp only [tables, extend, List.mem_flatMap, List.mem_range, List.mem_map,
        List.cons.injEq, List.length_cons, Nat.succ.injEq, List.forall_mem_cons]
      constructor
      · rintro ⟨a, ha, ys, hy, rfl, rfl⟩
        exact ⟨(ih ys).mp hy |>.1, ha, (ih ys).mp hy |>.2⟩
      · rintro ⟨hlen, hx, hxs⟩
        exact ⟨x, hx, xs, (ih xs).mpr ⟨hlen, hxs⟩, rfl, rfl⟩

/-- Every finite policy has a table in the numeric enumeration. -/
theorem ofFn_mem_tables {alphabet size : Nat} (policy : Fin size → Fin alphabet) :
    List.ofFn (fun q => (policy q).val) ∈ tables alphabet size := by
  rw [mem_tables_iff]
  refine ⟨List.length_ofFn, ?_⟩
  intro a ha
  obtain ⟨q, rfl⟩ := List.mem_ofFn.mp ha
  exact (policy q).isLt

/-- Decode a valid table into a policy, including empty-domain cases. -/
def policyOfTable {alphabet size : Nat} (xs : List Nat)
    (h : xs ∈ tables alphabet size) (q : Fin size) : Fin alphabet :=
  ⟨xs.getD q.val 0, by
    have hlen := (mem_tables_iff _ _ _).mp h |>.1
    have hq : q.val < xs.length := by simpa only [hlen] using q.isLt
    rw [List.getD_eq_getElem _ _ hq]
    exact ((mem_tables_iff _ _ _).mp h).2 _ (List.getElem_mem hq)⟩

theorem ofFn_policyOfTable {alphabet size : Nat} (xs : List Nat)
    (h : xs ∈ tables alphabet size) :
    List.ofFn (fun q => (policyOfTable xs h q).val) = xs := by
  apply List.ext_getElem
  · simpa using ((mem_tables_iff _ _ _).mp h).1.symm
  · intro i hi hj
    simp [policyOfTable, hj]

theorem mem_tables_iff_policy {alphabet size : Nat} (xs : List Nat) :
    xs ∈ tables alphabet size ↔
      ∃ policy : Fin size → Fin alphabet, List.ofFn (fun q => (policy q).val) = xs := by
  constructor
  · intro h
    exact ⟨policyOfTable xs h, ofFn_policyOfTable xs h⟩
  · rintro ⟨policy, rfl⟩
    exact ofFn_mem_tables policy

end DistributedSynthesis.FiniteSearch
