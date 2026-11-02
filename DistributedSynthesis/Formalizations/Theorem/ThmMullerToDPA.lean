/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Nodup
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators
import DistributedSynthesis.Formalizations.Theorem.ThmMullerCombinators

/-!
# Muller-to-DPA construction infrastructure

This file starts the constructive deterministic-Muller-to-parity backend.  The
full conversion uses a latest-appearance record (LAR): a permutation-like list
of all Muller states ordered by recency.  The declarations below provide the
finite-memory invariant and its refresh operation, which is the state update
used by the LAR parity construction.
-/

namespace DistributedSynthesis

universe u v

namespace DetMullerAutomaton

namespace LAR

variable {Alphabet : Type u}
variable (A : DetMullerAutomaton.{u, v} Alphabet)

/--
A latest-appearance record for a Muller automaton is a duplicate-free list
containing every Muller state.  The head is the most recently refreshed state.
-/
structure Record where
  order : List A.State
  nodup : order.Nodup
  complete : ∀ q : A.State, q ∈ order

attribute [simp] Record.nodup

/-- The set represented by a latest-appearance record is the full state set. -/
theorem Record.toFinset_eq_univ
    [DecidableEq A.State]
    (record : Record A) :
    record.order.toFinset = Finset.univ := by
  apply Finset.ext
  intro q
  constructor
  · intro _h
    simp
  · intro _h
    rw [List.mem_toFinset]
    exact record.complete q

/-- A latest-appearance record has exactly one entry for each Muller state. -/
theorem Record.length_eq_card
    (record : Record A) :
    record.order.length = Fintype.card A.State := by
  classical
  have hcard :
      record.order.toFinset.card = record.order.length :=
    List.toFinset_card_of_nodup record.nodup
  rw [← hcard, Record.toFinset_eq_univ]
  simp

/-- Encode a latest-appearance record as a fixed-length function. -/
def Record.code
    (record : Record A) :
    Fin (Fintype.card A.State) -> A.State :=
  fun i => record.order[i.1]'(by
    rw [Record.length_eq_card]
    exact i.2)

/-- The fixed-length code determines the latest-appearance record. -/
theorem Record.code_injective :
    Function.Injective (Record.code (A := A)) := by
  intro left right hcode
  have horders : left.order = right.order := by
    apply List.ext_getElem
    · rw [Record.length_eq_card (A := A) left,
        Record.length_eq_card (A := A) right]
    · intro i hleft _hright
      have hleftCard : i < Fintype.card A.State := by
        rw [← Record.length_eq_card (A := A) left]
        exact hleft
      have hcode_i := congrFun hcode ⟨i, hleftCard⟩
      simpa [Record.code] using hcode_i
  cases left
  cases right
  cases horders
  rfl

/-- Latest-appearance records form a finite memory space. -/
noncomputable instance Record.fintype : Fintype (Record A) := by
  classical
  exact Fintype.ofInjective (Record.code (A := A)) (Record.code_injective (A := A))

/-- The canonical initial latest-appearance record. -/
noncomputable def initialRecord : Record A := by
  classical
  exact
    { order := (Finset.univ : Finset A.State).toList
      nodup := Finset.nodup_toList _
      complete := by
        intro q
        rw [Finset.mem_toList]
        simp }

variable {A}

/--
Removing a state from a duplicate-free list removes all occurrences of that
state.  This is the key local fact behind LAR refresh.
-/
theorem not_mem_erase_self_of_nodup
    [DecidableEq A.State]
    (q : A.State)
    {order : List A.State}
    (horder : order.Nodup) :
    q ∉ order.erase q := by
  induction order with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.nodup_cons] at horder
      by_cases hhead : head = q
      · subst hhead
        rw [List.erase_cons_head]
        exact horder.1
      · rw [List.erase_cons_tail]
        · intro hmem
          rcases (List.mem_cons.mp hmem) with hsame | htail
          · exact hhead hsame.symm
          · exact ih horder.2 htail
        · simp [hhead]

/--
Refresh a latest-appearance record by moving `q` to the front while preserving
the relative order of all other states.
-/
noncomputable def Record.refresh
    (record : Record A)
    (q : A.State) :
    Record A := by
  classical
  exact
    { order := q :: record.order.erase q
      nodup := by
        rw [List.nodup_cons]
        exact
          ⟨not_mem_erase_self_of_nodup q record.nodup,
            record.nodup.erase q⟩
      complete := by
        intro r
        rw [List.mem_cons]
        by_cases hrq : r = q
        · exact Or.inl hrq
        · exact Or.inr ((List.mem_erase_of_ne hrq).mpr (record.complete r)) }

@[simp]
theorem Record.refresh_head
    (record : Record A)
    (q : A.State) :
    (record.refresh q).order.head? = some q := by
  classical
  rfl

@[simp]
theorem Record.refresh_complete
    (record : Record A)
    (q r : A.State) :
    r ∈ (record.refresh q).order := by
  classical
  exact (record.refresh q).complete r

/-- Refresh preserves the duplicate-free invariant. -/
theorem Record.refresh_nodup
    (record : Record A)
    (q : A.State) :
    (record.refresh q).order.Nodup := by
  classical
  exact (record.refresh q).nodup

/-- Refresh preserves the record length, hence the finite state-space size. -/
theorem Record.length_refresh
    (record : Record A)
    (q : A.State) :
    (record.refresh q).order.length = record.order.length := by
  classical
  rw [Record.length_eq_card, Record.length_eq_card]

/--
The LAR memory update induced by reading one letter from a Muller automaton
state.
-/
noncomputable def Record.step
    (record : Record A)
    (state : A.State)
    (letter : Alphabet) :
    Record A :=
  record.refresh (A.step state letter)

@[simp]
theorem Record.step_head
    (record : Record A)
    (state : A.State)
    (letter : Alphabet) :
    (record.step state letter).order.head? = some (A.step state letter) := by
  classical
  rfl

/--
The LAR event set generated when `q` is refreshed: these are exactly the states
that were at least as recent as `q` in the previous record.
-/
noncomputable def Record.hitSet
    (record : Record A)
    (q : A.State) :
    Finset A.State := by
  classical
  exact (record.order.take (record.order.idxOf q + 1)).toFinset

/--
List-level order predicate: `q` occurs no later than `r` when scanning from the
most recent end of a latest-appearance record.
-/
def beforeOrAt
    (q r : A.State) :
    List A.State -> Prop
  | [] => False
  | x :: xs => x = q ∨ (x ≠ r ∧ beforeOrAt q r xs)

theorem beforeOrAt_cons_self
    (q r : A.State)
    (xs : List A.State) :
    beforeOrAt (A := A) q r (q :: xs) := by
  exact Or.inl rfl

theorem beforeOrAt_cons_of_ne
    {q r x : A.State}
    {xs : List A.State}
    (hxr : x ≠ r)
    (h : beforeOrAt (A := A) q r xs) :
    beforeOrAt (A := A) q r (x :: xs) := by
  exact Or.inr ⟨hxr, h⟩

theorem mem_take_idx_succ_of_beforeOrAt
    [BEq A.State] [LawfulBEq A.State]
    (q r : A.State) :
    ∀ xs : List A.State,
      beforeOrAt (A := A) q r xs ->
        q ∈ xs.take (xs.idxOf r + 1)
  | [], h => False.elim h
  | x :: xs, h => by
      rcases h with hxq | ⟨hxr, htail⟩
      · subst hxq
        simp
      · have htailMem :=
          mem_take_idx_succ_of_beforeOrAt q r xs htail
        simp [List.idxOf_cons_ne _ hxr, htailMem]

theorem Record.mem_hitSet_of_beforeOrAt
    (record : Record A)
    {q r : A.State}
    (h : beforeOrAt (A := A) q r record.order) :
    q ∈ record.hitSet r := by
  classical
  rw [Record.hitSet, List.mem_toFinset]
  exact mem_take_idx_succ_of_beforeOrAt (A := A) q r record.order h

theorem beforeOrAt_of_mem_take_idx_succ
    [BEq A.State] [LawfulBEq A.State]
    (r : A.State) :
    ∀ xs : List A.State,
      r ∈ xs ->
        ∀ q : A.State,
          q ∈ xs.take (xs.idxOf r + 1) ->
            beforeOrAt (A := A) q r xs
  | [], hr, _q, _hq => False.elim (by simpa using hr)
  | x :: xs, hr, q, hq => by
      by_cases hxr : x = r
      · subst hxr
        simp at hq
        exact Or.inl hq.symm
      · rw [List.idxOf_cons_ne _ hxr] at hq
        simp at hq
        rcases hq with hq | hq
        · exact Or.inl hq.symm
        · exact Or.inr
            ⟨hxr, beforeOrAt_of_mem_take_idx_succ r xs
              (by
                rw [List.mem_cons] at hr
                rcases hr with hr | hr
                · exact False.elim (hxr hr.symm)
                · exact hr)
              q hq⟩

/-- If `q` occurs no later than `r` in a list, then `q` is before-or-at `r`. -/
theorem beforeOrAt_of_idxOf_le
    [BEq A.State] [LawfulBEq A.State]
    {q r : A.State} :
    ∀ xs : List A.State,
      q ∈ xs ->
        r ∈ xs ->
          xs.idxOf q ≤ xs.idxOf r ->
            beforeOrAt (A := A) q r xs
  | [], hq, _hr, _hle => False.elim (by simpa using hq)
  | x :: xs, hq, hr, hle => by
      by_cases hxq : x = q
      · subst hxq
        exact Or.inl rfl
      · have hxq' : x ≠ q := hxq
        by_cases hxr : x = r
        · subst hxr
          have hidxq : (x :: xs).idxOf q = xs.idxOf q + 1 := by
            rw [List.idxOf_cons_ne _ hxq']
          have hidxr : (x :: xs).idxOf x = 0 := by
            rw [List.idxOf_cons_self]
          rw [hidxq, hidxr] at hle
          omega
        · have hqtail : q ∈ xs := by
            rw [List.mem_cons] at hq
            rcases hq with hq | hq
            · exact False.elim (hxq hq.symm)
            · exact hq
          have hrtail : r ∈ xs := by
            rw [List.mem_cons] at hr
            rcases hr with hr | hr
            · exact False.elim (hxr hr.symm)
            · exact hr
          rw [List.idxOf_cons_ne _ hxq', List.idxOf_cons_ne _ hxr] at hle
          exact Or.inr
            ⟨hxr, beforeOrAt_of_idxOf_le (q := q) (r := r) xs hqtail hrtail (by omega)⟩

theorem Record.beforeOrAt_of_mem_hitSet
    (record : Record A)
    {q r : A.State}
    (h : q ∈ record.hitSet r) :
    beforeOrAt (A := A) q r record.order := by
  classical
  rw [Record.hitSet, List.mem_toFinset] at h
  exact beforeOrAt_of_mem_take_idx_succ (A := A)
    r record.order (record.complete r) q h

theorem beforeOrAt_erase_of_ne
    [DecidableEq A.State]
    {q r s : A.State}
    (hqs : q ≠ s) :
    ∀ xs : List A.State,
      beforeOrAt (A := A) q r xs ->
        beforeOrAt (A := A) q r (xs.erase s)
  | [], h => False.elim h
  | x :: xs, h => by
      by_cases hxs : x = s
      · subst hxs
        rw [List.erase_cons_head]
        rcases h with hxq | ⟨_hxr, htail⟩
        · exact False.elim (hqs hxq.symm)
        · exact htail
      · rw [List.erase_cons_tail (not_beq_of_ne hxs)]
        · rcases h with hxq | ⟨hxr, htail⟩
          · exact Or.inl hxq
          · exact Or.inr
              ⟨hxr, beforeOrAt_erase_of_ne hqs xs htail⟩

theorem beforeOrAt_of_beforeOrAt_erase_of_ne
    [DecidableEq A.State]
    {q r s : A.State}
    (hsr : s ≠ r) :
    ∀ xs : List A.State,
      beforeOrAt (A := A) q r (xs.erase s) ->
        beforeOrAt (A := A) q r xs
  | [], h => False.elim h
  | x :: xs, h => by
      by_cases hxs : x = s
      · subst hxs
        rw [List.erase_cons_head] at h
        exact Or.inr ⟨hsr, h⟩
      · rw [List.erase_cons_tail (not_beq_of_ne hxs)] at h
        rcases h with hxq | ⟨hxr, htail⟩
        · exact Or.inl hxq
        · exact Or.inr
            ⟨hxr, beforeOrAt_of_beforeOrAt_erase_of_ne hsr xs htail⟩

theorem Record.beforeOrAt_refresh_imp_eq_or_beforeOrAt
    (record : Record A)
    {q r s : A.State}
    (h : beforeOrAt (A := A) q r (record.refresh s).order) :
    q = s ∨ beforeOrAt (A := A) q r record.order := by
  classical
  rw [Record.refresh] at h
  rcases h with hqs | ⟨_hsr, htail⟩
  · exact Or.inl hqs.symm
  · exact Or.inr (beforeOrAt_of_beforeOrAt_erase_of_ne (A := A) _hsr record.order htail)

theorem Record.beforeOrAt_refresh_of_ne
    (record : Record A)
    {q r s : A.State}
    (h : beforeOrAt (A := A) q r record.order)
    (hsr : s ≠ r) :
    beforeOrAt (A := A) q r (record.refresh s).order := by
  classical
  rw [Record.refresh]
  by_cases hqs : q = s
  · subst hqs
    exact beforeOrAt_cons_self (A := A) q r (record.order.erase q)
  · exact beforeOrAt_cons_of_ne (A := A) hsr
      (beforeOrAt_erase_of_ne (A := A) hqs record.order h)

@[simp]
theorem Record.mem_hitSet_self
    (record : Record A)
    (q : A.State) :
    q ∈ record.hitSet q := by
  classical
  rw [Record.hitSet, List.mem_toFinset]
  exact (List.mem_take_iff_idxOf_lt (record.complete q)).mpr (Nat.lt_succ_self _)

theorem Record.mem_hitSet_imp_mem_record
    (record : Record A)
    (q r : A.State)
    (hr : r ∈ record.hitSet q) :
    r ∈ record.order := by
  classical
  rw [Record.hitSet, List.mem_toFinset] at hr
  exact List.mem_of_mem_take hr

/--
Every nonempty finite set of states has a least-recent member in a complete
record whose generated hit set contains the whole finite set.
-/
theorem Record.exists_hitSet_superset_finset
    (record : Record A)
    (S : Finset A.State)
    (hS : S.Nonempty) :
    ∃ r : A.State,
      r ∈ S ∧
        ∀ q : A.State, q ∈ S -> q ∈ record.hitSet r := by
  classical
  rcases Finset.exists_max_image S (fun q : A.State => record.order.idxOf q) hS with
    ⟨r, hrS, hrMax⟩
  refine ⟨r, hrS, ?_⟩
  intro q hqS
  exact Record.mem_hitSet_of_beforeOrAt (A := A) record
    (beforeOrAt_of_idxOf_le (A := A) record.order
      (record.complete q) (record.complete r) (hrMax q hqS))

/-- Hit sets are nonempty because they contain the refreshed state. -/
theorem Record.hitSet_nonempty
    (record : Record A)
    (q : A.State) :
    (record.hitSet q).Nonempty :=
  ⟨q, Record.mem_hitSet_self record q⟩

/-- A hit set can never contain more states than the Muller automaton. -/
theorem Record.hitSet_card_le
    (record : Record A)
    (q : A.State) :
    (record.hitSet q).card ≤ Fintype.card A.State := by
  classical
  calc
    (record.hitSet q).card ≤ Finset.univ.card := by
      exact Finset.card_le_card (by intro r _hr; simp)
    _ = Fintype.card A.State := by simp

/-- Immediately after refreshing `q`, the hit set of `q` itself is `{q}`. -/
@[simp]
theorem Record.refresh_hitSet_self
    (record : Record A)
    (q : A.State) :
    (record.refresh q).hitSet q = {q} := by
  classical
  ext r
  simp [Record.hitSet, Record.refresh]

/--
After refreshing `q`, the state `q` is in every hit set of the refreshed
record.
-/
theorem Record.mem_refresh_hitSet_refreshed
    (record : Record A)
    (q r : A.State) :
    q ∈ (record.refresh q).hitSet r := by
  classical
  simp [Record.hitSet, Record.refresh]

/-- Apply a finite block of LAR refreshes in chronological order. -/
noncomputable def Record.refreshList
    (record : Record A) :
    List A.State -> Record A
  | [] => record
  | q :: qs => (record.refresh q).refreshList qs

@[simp]
theorem Record.refreshList_nil
    (record : Record A) :
    record.refreshList [] = record := by
  rfl

@[simp]
theorem Record.refreshList_cons
    (record : Record A)
    (q : A.State)
    (qs : List A.State) :
    record.refreshList (q :: qs) = (record.refresh q).refreshList qs := by
  rfl

/-- Finite LAR refresh blocks compose by list append. -/
theorem Record.refreshList_append
    (record : Record A)
    (left right : List A.State) :
    record.refreshList (left ++ right) =
      (record.refreshList left).refreshList right := by
  classical
  induction left generalizing record with
  | nil =>
      rfl
  | cons q tail ih =>
      simp [Record.refreshList, ih]

/-- A singleton block is one refresh. -/
@[simp]
theorem Record.refreshList_singleton
    (record : Record A)
    (q : A.State) :
    record.refreshList [q] = record.refresh q := by
  rfl

/-- Appending one more element to a finite refresh block performs one more refresh. -/
theorem Record.refreshList_concat
    (record : Record A)
    (updates : List A.State)
    (q : A.State) :
    record.refreshList (updates ++ [q]) =
      (record.refreshList updates).refresh q := by
  classical
  rw [Record.refreshList_append]
  rfl

/--
The final state of a finite refresh block is at the head of the resulting LAR
record.
-/
theorem Record.refreshList_concat_head
    (record : Record A)
    (updates : List A.State)
    (q : A.State) :
    (record.refreshList (updates ++ [q])).order.head? = some q := by
  classical
  rw [Record.refreshList_concat]
  simp

/--
If a finite block contains no refresh of `r`, then a state that was already no
later than `r` in the record remains no later than `r` after the block.
-/
theorem Record.beforeOrAt_refreshList_of_not_mem
    (record : Record A)
    (updates : List A.State)
    {q r : A.State}
    (h : beforeOrAt (A := A) q r record.order)
    (hr : r ∉ updates) :
    beforeOrAt (A := A) q r (record.refreshList updates).order := by
  classical
  induction updates generalizing record with
  | nil =>
      simpa using h
  | cons s tail ih =>
      rw [List.mem_cons] at hr
      have hsr : s ≠ r := by
        intro hsr
        exact hr (Or.inl hsr.symm)
      have hrtail : r ∉ tail := by
        intro htail
        exact hr (Or.inr htail)
      exact ih (record.refresh s)
        (Record.beforeOrAt_refresh_of_ne (A := A) record h hsr)
        hrtail

/--
After a finite block that refreshes `q` and does not refresh `r`, the record
places `q` no later than `r`.
-/
theorem Record.beforeOrAt_refreshList_of_mem_of_not_mem
    (record : Record A)
    (updates : List A.State)
    {q r : A.State}
    (hq : q ∈ updates)
    (hr : r ∉ updates) :
    beforeOrAt (A := A) q r (record.refreshList updates).order := by
  classical
  induction updates generalizing record with
  | nil =>
      cases hq
  | cons s tail ih =>
      rw [List.mem_cons] at hq hr
      have hsr : s ≠ r := by
        intro hsr
        exact hr (Or.inl hsr.symm)
      have hrtail : r ∉ tail := by
        intro htail
        exact hr (Or.inr htail)
      rcases hq with hqs | hqtail
      · subst hqs
        exact Record.beforeOrAt_refreshList_of_not_mem
          (A := A) (record.refresh q) tail
          (beforeOrAt_cons_self (A := A) q r (record.order.erase q))
          hrtail
      · exact ih (record.refresh s) hqtail hrtail

/--
Consequently, the next refresh of `r` after such a block generates a hit set
that contains `q`.
-/
theorem Record.mem_refreshList_hitSet_of_mem_of_not_mem
    (record : Record A)
    (updates : List A.State)
    {q r : A.State}
    (hq : q ∈ updates)
    (hr : r ∉ updates) :
    q ∈ (record.refreshList updates).hitSet r := by
  classical
  exact Record.mem_hitSet_of_beforeOrAt (A := A)
    (record.refreshList updates)
    (Record.beforeOrAt_refreshList_of_mem_of_not_mem
      (A := A) record updates hq hr)

/--
Refreshing a list that does not contain target `r` preserves any existing
finite lower bound on the hit set of `r`.
-/
theorem Record.hitSet_superset_refreshList_of_not_mem
    (record : Record A)
    (updates : List A.State)
    (S : Finset A.State)
    {r : A.State}
    (hstart :
      ∀ q : A.State, q ∈ S -> q ∈ record.hitSet r)
    (hr : r ∉ updates) :
    ∀ q : A.State,
      q ∈ S ->
        q ∈ (record.refreshList updates).hitSet r := by
  intro q hqS
  exact Record.mem_hitSet_of_beforeOrAt (A := A)
    (record.refreshList updates)
    (Record.beforeOrAt_refreshList_of_not_mem
      (A := A) record updates
      (Record.beforeOrAt_of_mem_hitSet (A := A) record (hstart q hqS))
      hr)

/-- Refreshing by a state in `S` preserves the fact that the hit set for `r` is contained in `S`. -/
theorem Record.hitSet_subset_refresh_of_mem
    (record : Record A)
    (S : Finset A.State)
    {r s : A.State}
    (hr : r ∈ S)
    (hs : s ∈ S)
    (hsubset : ∀ q : A.State, q ∈ record.hitSet r -> q ∈ S) :
    ∀ q : A.State, q ∈ (record.refresh s).hitSet r -> q ∈ S := by
  classical
  intro q hq
  rcases Record.beforeOrAt_refresh_imp_eq_or_beforeOrAt
      (A := A) record
      (Record.beforeOrAt_of_mem_hitSet (A := A) (record.refresh s) hq) with
    hqs | hbefore
  · rw [hqs]
    exact hs
  · exact hsubset q (Record.mem_hitSet_of_beforeOrAt (A := A) record hbefore)

/-- A finite block of refreshes by states in `S` preserves the hit-set subset invariant. -/
theorem Record.hitSet_subset_refreshList_of_forall_mem
    (record : Record A)
    (S : Finset A.State)
    (updates : List A.State)
    {r : A.State}
    (hr : r ∈ S)
    (hupdates : ∀ q : A.State, q ∈ updates -> q ∈ S)
    (hsubset : ∀ q : A.State, q ∈ record.hitSet r -> q ∈ S) :
    ∀ q : A.State, q ∈ (record.refreshList updates).hitSet r -> q ∈ S := by
  classical
  induction updates generalizing record with
  | nil =>
      simpa using hsubset
  | cons s tail ih =>
      have hs : s ∈ S := hupdates s (by simp)
      have htail : ∀ q : A.State, q ∈ tail -> q ∈ S := by
        intro q hq
        exact hupdates q (by simp [hq])
      exact ih (record.refresh s) htail
        (Record.hitSet_subset_refresh_of_mem (A := A) record S hr hs hsubset)

theorem exists_append_cons_of_mem
    {q : A.State} :
    ∀ updates : List A.State,
      q ∈ updates ->
        ∃ pre : List A.State, ∃ suf : List A.State, updates = pre ++ q :: suf
  | [], h => False.elim (by simpa using h)
  | x :: xs, h => by
      rw [List.mem_cons] at h
      rcases h with hx | hxs
      · subst hx
        exact ⟨[], xs, rfl⟩
      · rcases exists_append_cons_of_mem xs hxs with
          ⟨pre, suf, hs⟩
        exact ⟨x :: pre, suf, by simp [hs]⟩

/--
If a finite refresh block contains `r` and all refreshed states lie in `S`, then
the final hit set for `r` is contained in `S`, independently of the starting
record.
-/
theorem Record.hitSet_subset_refreshList_of_target_mem_of_forall_mem
    (record : Record A)
    (S : Finset A.State)
    (updates : List A.State)
    {r : A.State}
    (hr : r ∈ updates)
    (hupdates : ∀ q : A.State, q ∈ updates -> q ∈ S) :
    ∀ q : A.State, q ∈ (record.refreshList updates).hitSet r -> q ∈ S := by
  classical
  rcases exists_append_cons_of_mem (A := A) updates hr with
    ⟨pre, suf, hsplit⟩
  subst hsplit
  rw [Record.refreshList_append]
  change
    ∀ q : A.State,
      q ∈ (((record.refreshList pre).refresh r).refreshList suf).hitSet r ->
        q ∈ S
  have hrS : r ∈ S := hupdates r (by simp)
  have hsuffix : ∀ q : A.State, q ∈ suf -> q ∈ S := by
    intro q hq
    exact hupdates q (by simp [hq])
  exact Record.hitSet_subset_refreshList_of_forall_mem
    (A := A) ((record.refreshList pre).refresh r) S suf
    hrS hsuffix
    (by
      intro q hq
      rw [Record.refresh_hitSet_self] at hq
      simp at hq
      rw [hq]
      exact hrS)

/-- State space of the LAR parity automaton before choosing priorities. -/
abbrev LARState (A : DetMullerAutomaton.{u, v} Alphabet) : Type v :=
  A.State × Record A

/--
Event-carrying LAR state space.  The third component records the LAR hit set of
the most recent transition, which is the information used by the standard
Muller-to-parity priority assignment.
-/
abbrev EventState (A : DetMullerAutomaton.{u, v} Alphabet) : Type v :=
  A.State × Record A × Finset A.State

/--
The LAR transition: follow the Muller transition in the first component and
refresh the latest-appearance record with the newly reached Muller state.
-/
noncomputable def step
    (state : LARState A)
    (letter : Alphabet) :
    LARState A :=
  let next := A.step state.1 letter
  (next, state.2.refresh next)

/--
The deterministic parity automaton skeleton induced by LAR memory.

The priority assignment is separated out: later correctness work will provide
the usual LAR priority function and prove that it recognizes the Muller
condition.
-/
noncomputable def automatonWithPriority
    (priority : LARState A -> Nat) :
    DetParityAutomaton Alphabet where
  State := LARState A
  stateFinite := inferInstance
  initial := (A.initial, initialRecord A)
  step := step (A := A)
  priority := priority

@[simp]
theorem automatonWithPriority_step_fst
    (priority : LARState A -> Nat)
    (state : LARState A)
    (letter : Alphabet) :
    ((automatonWithPriority (A := A) priority).step state letter).1 =
      A.step state.1 letter := by
  rfl

@[simp]
theorem automatonWithPriority_step_snd
    (priority : LARState A -> Nat)
    (state : LARState A)
    (letter : Alphabet) :
    ((automatonWithPriority (A := A) priority).step state letter).2 =
      state.2.refresh (A.step state.1 letter) := by
  rfl

/--
The LAR automaton's Muller-state component simulates the original Muller run
from the corresponding first component.
-/
theorem automatonWithPriority_runFrom_fst
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((automatonWithPriority (A := A) priority).runFrom state word n).1 =
      A.runFrom state.1 word n := by
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      change
        ((automatonWithPriority (A := A) priority).step
          ((automatonWithPriority (A := A) priority).runFrom state word n)
          (word n)).1 =
          A.step (A.runFrom state.1 word n) (word n)
      rw [automatonWithPriority_step_fst, ih]

/-- The LAR automaton's first component simulates the original initial run. -/
theorem automatonWithPriority_run_fst
    (priority : LARState A -> Nat)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((automatonWithPriority (A := A) priority).run word n).1 =
      A.run word n :=
  automatonWithPriority_runFrom_fst (A := A) priority
    (automatonWithPriority (A := A) priority).initial word n

/--
Infinite visits of Muller states are exactly preserved by the first projection
of the LAR run.
-/
theorem automatonWithPriority_stateSeen_fst_iff
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    (∀ n : Nat, ∃ k : Nat, n ≤ k ∧
        ((automatonWithPriority (A := A) priority).runFrom state word k).1 = q) ↔
      A.StateSeenInfinitelyOftenFrom state.1 word q := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hq⟩
    refine ⟨k, hk, ?_⟩
    simpa [automatonWithPriority_runFrom_fst (A := A) priority state word k] using hq
  · intro h n
    rcases h n with ⟨k, hk, hq⟩
    refine ⟨k, hk, ?_⟩
    simpa [automatonWithPriority_runFrom_fst (A := A) priority state word k] using hq

/-- The first projection of the LAR run has the same infinity set as the Muller run. -/
theorem automatonWithPriority_projectedInfStates_eq
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet) :
    { q : A.State | ∀ n : Nat, ∃ k : Nat, n ≤ k ∧
        ((automatonWithPriority (A := A) priority).runFrom state word k).1 = q } =
      A.InfStatesFrom state.1 word := by
  ext q
  exact automatonWithPriority_stateSeen_fst_iff (A := A) priority state word q

/--
After at least one transition, the head of the LAR record is the current
Muller state.
-/
theorem automatonWithPriority_runFrom_snd_head_succ
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (((automatonWithPriority (A := A) priority).runFrom state word (n + 1)).2).order.head? =
      some (A.runFrom state.1 word (n + 1)) := by
  change
    (((automatonWithPriority (A := A) priority).step
      ((automatonWithPriority (A := A) priority).runFrom state word n)
      (word n)).2).order.head? =
      some (A.step (A.runFrom state.1 word n) (word n))
  rw [automatonWithPriority_step_snd]
  simp [automatonWithPriority_runFrom_fst]

/--
For the initial run, every positive time has the current Muller state at the
head of the latest-appearance record.
-/
theorem automatonWithPriority_run_snd_head_succ
    (priority : LARState A -> Nat)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (((automatonWithPriority (A := A) priority).run word (n + 1)).2).order.head? =
      some (A.run word (n + 1)) :=
  automatonWithPriority_runFrom_snd_head_succ (A := A) priority
    (automatonWithPriority (A := A) priority).initial word n

/-- Every LAR record reached by the automaton still lists every Muller state. -/
theorem automatonWithPriority_runFrom_record_complete
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet)
    (n : Nat)
    (q : A.State) :
    q ∈ (((automatonWithPriority (A := A) priority).runFrom state word n).2).order :=
  (((automatonWithPriority (A := A) priority).runFrom state word n).2).complete q

/-- Every LAR record reached by the automaton remains duplicate-free. -/
theorem automatonWithPriority_runFrom_record_nodup
    (priority : LARState A -> Nat)
    (state : LARState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    (((automatonWithPriority (A := A) priority).runFrom state word n).2).order.Nodup :=
  (((automatonWithPriority (A := A) priority).runFrom state word n).2).nodup

/--
The event-carrying LAR transition: compute the next Muller state, remember the
hit set induced by the old record, and then refresh the record.
-/
noncomputable def eventStep
    (state : EventState A)
    (letter : Alphabet) :
    EventState A :=
  let next := A.step state.1 letter
  let hit := state.2.1.hitSet next
  (next, state.2.1.refresh next, hit)

/-- The event-carrying LAR automaton before fixing the concrete LAR priority. -/
noncomputable def eventAutomatonWithPriority
    (priority : EventState A -> Nat) :
    DetParityAutomaton Alphabet where
  State := EventState A
  stateFinite := by
    classical
    infer_instance
  initial := (A.initial, initialRecord A, ∅)
  step := eventStep (A := A)
  priority := priority

/--
Concrete LAR priority candidate.

The level is ordered by the size of the latest hit set: larger hit sets receive
smaller priorities.  At a fixed level, accepting Muller hit sets are even and
rejecting hit sets are odd.
-/
noncomputable def eventPriority
    (state : EventState A) :
    Nat := by
  classical
  let level := Fintype.card A.State - state.2.2.card
  exact
    if (state.2.2 : Set A.State) ∈ A.accepting then
      2 * level
    else
      2 * level + 1

/-- The concrete event-carrying LAR parity automaton candidate. -/
noncomputable def eventAutomaton :
    DetParityAutomaton Alphabet :=
  eventAutomatonWithPriority (A := A) (eventPriority (A := A))

/-- State-wise correctness target for the concrete LAR Muller-to-DPA automaton. -/
def eventAutomatonCorrectFrom
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    Prop :=
  (eventAutomaton (A := A)).AcceptsFrom state word ↔
    A.AcceptsFrom state.1 word

/-- Initial-state correctness target for the concrete LAR Muller-to-DPA automaton. -/
def eventAutomatonCorrect :
    Prop :=
  ∀ word : OmegaWord Alphabet,
    (eventAutomaton (A := A)).Accepts word ↔ A.Accepts word

/-- A hit set recurs infinitely often along the concrete LAR event automaton. -/
def EventHitSetSeenInfinitelyOftenFrom
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State) :
    Prop :=
  ∃ eventState : EventState A,
    (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
      state word eventState ∧
      eventState.2.2 = hitSet

/-- Some event state recurs infinitely often along every finite LAR event run. -/
theorem eventAutomaton_exists_eventStateSeenInfinitelyOftenFrom
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    ∃ eventState : EventState A,
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState :=
  (eventAutomaton (A := A)).toMuller.exists_stateSeenInfinitelyOftenFrom
    state word

/-- Some hit set recurs infinitely often along every finite LAR event run. -/
theorem eventAutomaton_exists_hitSetSeenInfinitelyOftenFrom
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    ∃ hitSet : Finset A.State,
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet := by
  rcases eventAutomaton_exists_eventStateSeenInfinitelyOftenFrom
      (A := A) state word with
    ⟨eventState, hstateSeen⟩
  exact ⟨eventState.2.2, eventState, hstateSeen, rfl⟩

/--
The recurring hit sets of a finite LAR event run have a cardinality-maximal
member.
-/
theorem eventAutomaton_exists_maximal_recurring_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    ∃ hitSet : Finset A.State,
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
        ∀ otherHitSet : Finset A.State,
          EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
            otherHitSet.card ≤ hitSet.card := by
  classical
  let seen : Set (Finset A.State) :=
    {hitSet | EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet}
  have hseenFinite : seen.Finite :=
    Set.finite_univ.subset (by intro hitSet _h; simp)
  have hseenNonempty : seen.Nonempty := by
    rcases eventAutomaton_exists_hitSetSeenInfinitelyOftenFrom
        (A := A) state word with
      ⟨hitSet, hhitSeen⟩
    exact ⟨hitSet, hhitSeen⟩
  rcases Set.exists_max_image seen Finset.card hseenFinite hseenNonempty with
    ⟨hitSet, hhitSeen, hmax⟩
  exact ⟨hitSet, hhitSeen, fun other hother => hmax other hother⟩

/--
State-wise correctness at the concrete initial event state gives the initial
language correctness theorem.
-/
theorem eventAutomaton_correct_of_initial_correctFrom
    (h :
      ∀ word : OmegaWord Alphabet,
        eventAutomatonCorrectFrom (A := A)
          (eventAutomaton (A := A)).initial word) :
    eventAutomatonCorrect (A := A) := by
  intro word
  exact h word

/--
Once the concrete LAR correctness theorem is proved, it packages directly as the
deterministic Muller-to-DPA compilation required by the LTL backend.
-/
noncomputable def eventAutomaton_toDPACompilation_of_correct
    (hcorrect : eventAutomatonCorrect (A := A)) :
    A.ToDPACompilation where
  dpa := eventAutomaton (A := A)
  correct := hcorrect

@[simp]
theorem eventPriority_of_accepting
    (state : EventState A)
    (hacc : (state.2.2 : Set A.State) ∈ A.accepting) :
    eventPriority (A := A) state =
      2 * (Fintype.card A.State - state.2.2.card) := by
  classical
  simp [eventPriority, hacc]

@[simp]
theorem eventPriority_of_rejecting
    (state : EventState A)
    (hrej : (state.2.2 : Set A.State) ∉ A.accepting) :
    eventPriority (A := A) state =
      2 * (Fintype.card A.State - state.2.2.card) + 1 := by
  classical
  simp [eventPriority, hrej]

theorem eventPriority_even_of_accepting
    (state : EventState A)
    (hacc : (state.2.2 : Set A.State) ∈ A.accepting) :
    DetParityAutomaton.NatEven (eventPriority (A := A) state) := by
  refine ⟨Fintype.card A.State - state.2.2.card, ?_⟩
  rw [eventPriority_of_accepting (A := A) state hacc]

theorem eventPriority_not_even_of_rejecting
    (state : EventState A)
    (hrej : (state.2.2 : Set A.State) ∉ A.accepting) :
    ¬ DetParityAutomaton.NatEven (eventPriority (A := A) state) := by
  intro h
  rw [eventPriority_of_rejecting (A := A) state hrej] at h
  exact DetParityAutomaton.natEven_add_one_not_even
    (2 * (Fintype.card A.State - state.2.2.card))
    ⟨Fintype.card A.State - state.2.2.card, rfl⟩ h

/-- The stored hit-set component of any event state is bounded by the Muller state space. -/
theorem EventState.hitSet_card_le
    (state : EventState A) :
    state.2.2.card ≤ Fintype.card A.State := by
  classical
  calc
    state.2.2.card ≤ (Finset.univ : Finset A.State).card := by
      exact Finset.card_le_card (by intro q _hq; simp)
    _ = Fintype.card A.State := by simp

/--
For an accepting event state, being no larger in priority than another event
state implies that its stored hit set has at least as large cardinality.
-/
theorem eventPriority_accepting_le_imp_card_le
    (state other : EventState A)
    (hacc : (state.2.2 : Set A.State) ∈ A.accepting)
    (hle :
      eventPriority (A := A) state ≤ eventPriority (A := A) other) :
    other.2.2.card ≤ state.2.2.card := by
  classical
  have hstateCard := EventState.hitSet_card_le (A := A) state
  have hotherCard := EventState.hitSet_card_le (A := A) other
  by_cases hotherAcc : (other.2.2 : Set A.State) ∈ A.accepting
  · rw [eventPriority_of_accepting (A := A) state hacc,
      eventPriority_of_accepting (A := A) other hotherAcc] at hle
    omega
  · rw [eventPriority_of_accepting (A := A) state hacc,
      eventPriority_of_rejecting (A := A) other hotherAcc] at hle
    omega

/--
For an accepting event state, cardinal maximality of its stored hit set implies
priority minimality among event states.
-/
theorem eventPriority_accepting_card_le_imp_priority_le
    (state other : EventState A)
    (hacc : (state.2.2 : Set A.State) ∈ A.accepting)
    (hcard : other.2.2.card ≤ state.2.2.card) :
    eventPriority (A := A) state ≤ eventPriority (A := A) other := by
  classical
  have hstateCard := EventState.hitSet_card_le (A := A) state
  have hotherCard := EventState.hitSet_card_le (A := A) other
  by_cases hotherAcc : (other.2.2 : Set A.State) ∈ A.accepting
  · rw [eventPriority_of_accepting (A := A) state hacc,
      eventPriority_of_accepting (A := A) other hotherAcc]
    omega
  · rw [eventPriority_of_accepting (A := A) state hacc,
      eventPriority_of_rejecting (A := A) other hotherAcc]
    omega

/-- The concrete LAR priority is even exactly on Muller-accepting hit sets. -/
theorem eventPriority_even_iff_accepting
    (state : EventState A) :
    DetParityAutomaton.NatEven (eventPriority (A := A) state) ↔
      (state.2.2 : Set A.State) ∈ A.accepting := by
  classical
  constructor
  · intro heven
    by_contra hrej
    exact eventPriority_not_even_of_rejecting (A := A) state hrej heven
  · intro hacc
    exact eventPriority_even_of_accepting (A := A) state hacc

@[simp]
theorem eventAutomaton_priority
    (state : EventState A) :
    (eventAutomaton (A := A)).priority state = eventPriority (A := A) state := by
  rfl

@[simp]
theorem eventAutomatonWithPriority_step_current
    (priority : EventState A -> Nat)
    (state : EventState A)
    (letter : Alphabet) :
    ((eventAutomatonWithPriority (A := A) priority).step state letter).1 =
      A.step state.1 letter := by
  rfl

@[simp]
theorem eventAutomatonWithPriority_step_record
    (priority : EventState A -> Nat)
    (state : EventState A)
    (letter : Alphabet) :
    ((eventAutomatonWithPriority (A := A) priority).step state letter).2.1 =
      state.2.1.refresh (A.step state.1 letter) := by
  rfl

@[simp]
theorem eventAutomatonWithPriority_step_hitSet
    (priority : EventState A -> Nat)
    (state : EventState A)
    (letter : Alphabet) :
    ((eventAutomatonWithPriority (A := A) priority).step state letter).2.2 =
      state.2.1.hitSet (A.step state.1 letter) := by
  rfl

/-- The event-carrying LAR automaton simulates the Muller run in its first component. -/
theorem eventAutomatonWithPriority_runFrom_current
    (priority : EventState A -> Nat)
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((eventAutomatonWithPriority (A := A) priority).runFrom state word n).1 =
      A.runFrom state.1 word n := by
  induction n generalizing state with
  | zero =>
      rfl
  | succ n ih =>
      change
        ((eventAutomatonWithPriority (A := A) priority).step
          ((eventAutomatonWithPriority (A := A) priority).runFrom state word n)
          (word n)).1 =
          A.step (A.runFrom state.1 word n) (word n)
      rw [eventAutomatonWithPriority_step_current, ih]

/-- The initial event-carrying LAR run simulates the Muller initial run. -/
theorem eventAutomatonWithPriority_run_current
    (priority : EventState A -> Nat)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((eventAutomatonWithPriority (A := A) priority).run word n).1 =
      A.run word n :=
  eventAutomatonWithPriority_runFrom_current (A := A) priority
    (eventAutomatonWithPriority (A := A) priority).initial word n

/-- The concrete event-carrying LAR automaton simulates the Muller run. -/
theorem eventAutomaton_runFrom_current
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((eventAutomaton (A := A)).runFrom state word n).1 =
      A.runFrom state.1 word n :=
  eventAutomatonWithPriority_runFrom_current (A := A)
    (eventPriority (A := A)) state word n

/--
The Muller states refreshed by the event LAR run during the next `len`
transitions after time `start`.
-/
noncomputable def eventRunStateBlock
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start : Nat) :
    Nat -> List A.State
  | 0 => []
  | len + 1 =>
      eventRunStateBlock state word start len ++
        [A.runFrom state.1 word (start + len + 1)]

@[simp]
theorem eventRunStateBlock_zero
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start : Nat) :
    eventRunStateBlock (A := A) state word start 0 = [] := by
  rfl

@[simp]
theorem eventRunStateBlock_succ
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat) :
    eventRunStateBlock (A := A) state word start (len + 1) =
      eventRunStateBlock (A := A) state word start len ++
        [A.runFrom state.1 word (start + len + 1)] := by
  rfl

theorem eventRunStateBlock_last_mem
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat) :
    A.runFrom state.1 word (start + len + 1) ∈
      eventRunStateBlock (A := A) state word start (len + 1) := by
  classical
  simp [eventRunStateBlock]

/--
Every positive offset inside the block contributes the Muller state reached at
that offset.
-/
theorem eventRunStateBlock_mem_of_pos_le
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len offset : Nat)
    (hpos : 0 < offset)
    (hle : offset ≤ len) :
    A.runFrom state.1 word (start + offset) ∈
      eventRunStateBlock (A := A) state word start len := by
  classical
  induction len with
  | zero =>
      omega
  | succ len ih =>
      by_cases hlast : offset = len + 1
      · subst hlast
        exact eventRunStateBlock_last_mem (A := A) state word start len
      · have hle' : offset ≤ len := by omega
        rw [eventRunStateBlock_succ]
        exact List.mem_append_left _
          (ih hle')

/--
If a Muller state is absent from every positive offset in a finite block, then
it is absent from the block list.
-/
theorem eventRunStateBlock_not_mem_of_forall_ne
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    (r : A.State)
    (hnone :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ≠ r) :
    r ∉ eventRunStateBlock (A := A) state word start len := by
  classical
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [eventRunStateBlock_succ, List.mem_append, List.mem_singleton]
      intro hmem
      rcases hmem with hmem | hlast
      · exact ih
          (by
            intro offset hpos hle
            exact hnone offset hpos (by omega))
          hmem
      · exact hnone (len + 1) (by omega) (by omega) hlast.symm

/-- If every positive offset in a run block is in `S`, then every block element is in `S`. -/
theorem eventRunStateBlock_forall_mem_of_forall_offsets
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    (S : Finset A.State)
    (hall :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ∈ S) :
    ∀ q : A.State,
      q ∈ eventRunStateBlock (A := A) state word start len -> q ∈ S := by
  classical
  induction len with
  | zero =>
      intro q hq
      simp at hq
  | succ len ih =>
      intro q hq
      rw [eventRunStateBlock_succ, List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact ih
          (by
            intro offset hpos hle
            exact hall offset hpos (by omega))
          q hq
      · rw [hq]
        exact hall (len + 1) (by omega) (by omega)

/--
The event LAR record after `len` more transitions is obtained by refreshing
the block of Muller states reached in those transitions.
-/
theorem eventAutomaton_runFrom_record_add
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat) :
    ((eventAutomaton (A := A)).runFrom state word (start + len)).2.1 =
      (((eventAutomaton (A := A)).runFrom state word start).2.1).refreshList
        (eventRunStateBlock (A := A) state word start len) := by
  classical
  induction len with
  | zero =>
      simp
  | succ len ih =>
      rw [eventRunStateBlock_succ, Record.refreshList_concat]
      have hsucc : start + (len + 1) = (start + len) + 1 := by omega
      rw [hsucc]
      simp only [eventAutomaton, DetParityAutomaton.runFrom,
        eventAutomatonWithPriority_step_record]
      have hih :
          ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
              state word (start + len)).2.1 =
            (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
              state word start).2.1).refreshList
                (eventRunStateBlock (A := A) state word start len) := by
        simpa [eventAutomaton] using ih
      rw [hih]
      congr 1
      rw [eventAutomatonWithPriority_runFrom_current]
      congr 1

/--
If `q` occurs in the next finite run block and `r` does not occur in that
block, then the record at the end of the block would generate a hit set for
`r` containing `q`.
-/
theorem eventAutomaton_mem_hitSet_of_seen_in_block_without_target
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    {q r : A.State}
    (hq :
      ∃ offset : Nat,
        0 < offset ∧
          offset ≤ len ∧
            A.runFrom state.1 word (start + offset) = q)
    (hr :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ≠ r) :
    q ∈
      (((eventAutomaton (A := A)).runFrom state word (start + len)).2.1).hitSet r := by
  classical
  rcases hq with ⟨offset, hpos, hle, hqeq⟩
  have hqmem :
      q ∈ eventRunStateBlock (A := A) state word start len := by
    rw [← hqeq]
    exact eventRunStateBlock_mem_of_pos_le (A := A)
      state word start len offset hpos hle
  have hrmem :
      r ∉ eventRunStateBlock (A := A) state word start len :=
    eventRunStateBlock_not_mem_of_forall_ne (A := A)
      state word start len r hr
  rw [eventAutomaton_runFrom_record_add]
  exact Record.mem_refreshList_hitSet_of_mem_of_not_mem
    (A := A)
    (((eventAutomaton (A := A)).runFrom state word start).2.1)
    (eventRunStateBlock (A := A) state word start len)
    hqmem hrmem

/--
If `q` is seen after `start`, `r` is not seen before the next transition, and
that next transition reaches `r`, then the generated hit set at the next time
contains `q`.
-/
theorem eventAutomaton_runFrom_hitSet_contains_of_seen_before_next_target
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    {q r : A.State}
    (hq :
      ∃ offset : Nat,
        0 < offset ∧
          offset ≤ len ∧
            A.runFrom state.1 word (start + offset) = q)
    (hr :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ≠ r)
    (hnext : A.runFrom state.1 word (start + len + 1) = r) :
    q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 := by
  classical
  have hmem :
      q ∈
        (((eventAutomaton (A := A)).runFrom state word (start + len)).2.1).hitSet r :=
    eventAutomaton_mem_hitSet_of_seen_in_block_without_target
      (A := A) state word start len hq hr
  have hsucc : start + len + 1 = (start + len) + 1 := by omega
  rw [hsucc]
  change
    q ∈
      (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
        ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
          state word (start + len))
        (word (start + len))).2.2)
  rw [eventAutomatonWithPriority_step_hitSet]
  rw [eventAutomatonWithPriority_runFrom_current]
  have hnextStep :
      A.step (A.runFrom state.1 word (start + len)) (word (start + len)) = r := by
    rw [hsucc] at hnext
    simpa [DetMullerAutomaton.runFrom] using hnext
  simpa [eventAutomaton, hnextStep] using hmem

/--
If a finite block has seen every Muller-infinity state except the next target
`r`, avoids `r`, and the following transition reaches `r`, then the generated
LAR hit set contains the whole Muller-infinity set.  The target state itself is
included because the just-refreshed state always belongs to its generated hit
set.
-/
theorem eventAutomaton_runFrom_generated_hitSet_contains_inf_of_seen_all_before_next_target
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    {r : A.State}
    (hseenAll :
      ∀ q : A.State,
        q ∈ A.infStateFinsetFrom state.1 word ->
          q ≠ r ->
          ∃ offset : Nat,
            0 < offset ∧
              offset ≤ len ∧
                A.runFrom state.1 word (start + offset) = q)
    (hr :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ≠ r)
    (hnext : A.runFrom state.1 word (start + len + 1) = r) :
    ∀ q : A.State,
      q ∈ A.infStateFinsetFrom state.1 word ->
        q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 := by
  intro q hq
  by_cases hqr : q = r
  · rw [hqr]
    rw [← hnext]
    have hsucc : start + len + 1 = (start + len) + 1 := by omega
    rw [hsucc]
    change
      A.runFrom state.1 word (start + len + 1) ∈
        (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
          ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
            state word (start + len))
          (word (start + len))).2.2)
    rw [eventAutomatonWithPriority_step_hitSet]
    rw [eventAutomatonWithPriority_runFrom_current]
    have hnextStep :
        A.step (A.runFrom state.1 word (start + len)) (word (start + len)) = r := by
      rw [← hsucc] at hnext
      simpa [DetMullerAutomaton.runFrom] using hnext
    simpa [hnextStep, hnext] using
      (Record.mem_hitSet_self
        (((eventAutomaton (A := A)).runFrom state word (start + len)).2.1)
        r)
  · exact eventAutomaton_runFrom_hitSet_contains_of_seen_before_next_target
      (A := A) state word start len (hseenAll q hq hqr) hr hnext

/--
Concrete event-run form of hit-set lower-bound preservation.  If the record at
`start` already has `S` inside the hit set for `r`, no state `r` is refreshed in
the following block, and the next transition reaches `r`, then the generated
hit set contains `S`.
-/
theorem eventAutomaton_runFrom_generated_hitSet_superset_of_block_avoids_target
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    (S : Finset A.State)
    {r : A.State}
    (hstart :
      ∀ q : A.State,
        q ∈ S ->
          q ∈ (((eventAutomaton (A := A)).runFrom state word start).2.1).hitSet r)
    (hr :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ≠ r)
    (hnext : A.runFrom state.1 word (start + len + 1) = r) :
    ∀ q : A.State,
      q ∈ S ->
        q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 := by
  classical
  intro q hqS
  have hrmem :
      r ∉ eventRunStateBlock (A := A) state word start len :=
    eventRunStateBlock_not_mem_of_forall_ne (A := A)
      state word start len r hr
  have hrecordSubset :
      q ∈
        ((((eventAutomaton (A := A)).runFrom state word start).2.1).refreshList
          (eventRunStateBlock (A := A) state word start len)).hitSet r :=
    Record.hitSet_superset_refreshList_of_not_mem
      (A := A)
      (((eventAutomaton (A := A)).runFrom state word start).2.1)
      (eventRunStateBlock (A := A) state word start len)
      S hstart hrmem q hqS
  have hsucc : start + len + 1 = (start + len) + 1 := by omega
  have hnextStep :
      A.step (A.runFrom state.1 word (start + len)) (word (start + len)) = r := by
    rw [hsucc] at hnext
    simpa [DetMullerAutomaton.runFrom] using hnext
  rw [hsucc]
  change
    q ∈
      (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
        ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
          state word (start + len))
        (word (start + len))).2.2)
  rw [eventAutomatonWithPriority_step_hitSet]
  rw [eventAutomatonWithPriority_runFrom_current]
  rw [hnextStep]
  have hrecordEq := eventAutomaton_runFrom_record_add
    (A := A) state word start len
  rwa [← hrecordEq] at hrecordSubset

/--
Subset preservation for generated hit sets along a concrete event run.

If all states refreshed in the next `len` transitions are in `S`, the next
target state `r` is in `S`, and the starting record's hit set for `r` is already
contained in `S`, then the hit set generated at the next `r` transition is
contained in `S`.
-/
theorem eventAutomaton_runFrom_generated_hitSet_subset_of_block_subset
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    (S : Finset A.State)
    {r : A.State}
    (hr : r ∈ S)
    (hall :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ∈ S)
    (hstart :
      ∀ q : A.State,
        q ∈ (((eventAutomaton (A := A)).runFrom state word start).2.1).hitSet r ->
          q ∈ S)
    (hnext : A.runFrom state.1 word (start + len + 1) = r) :
    ∀ q : A.State,
      q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 ->
        q ∈ S := by
  classical
  intro q hq
  have hblock :
      ∀ q : A.State,
        q ∈ eventRunStateBlock (A := A) state word start len -> q ∈ S :=
    eventRunStateBlock_forall_mem_of_forall_offsets
      (A := A) state word start len S hall
  have hrecordSubset :
      ∀ q : A.State,
        q ∈
            ((((eventAutomaton (A := A)).runFrom state word start).2.1).refreshList
              (eventRunStateBlock (A := A) state word start len)).hitSet r ->
          q ∈ S :=
    Record.hitSet_subset_refreshList_of_forall_mem
      (A := A)
      (((eventAutomaton (A := A)).runFrom state word start).2.1)
      S (eventRunStateBlock (A := A) state word start len)
      hr hblock hstart
  have hsucc : start + len + 1 = (start + len) + 1 := by omega
  have hnextStep :
      A.step (A.runFrom state.1 word (start + len)) (word (start + len)) = r := by
    rw [hsucc] at hnext
    simpa [DetMullerAutomaton.runFrom] using hnext
  rw [hsucc] at hq
  change
    q ∈
      (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
        ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
          state word (start + len))
        (word (start + len))).2.2) at hq
  rw [eventAutomatonWithPriority_step_hitSet] at hq
  rw [eventAutomatonWithPriority_runFrom_current] at hq
  rw [hnextStep] at hq
  have hrecordEq := eventAutomaton_runFrom_record_add
    (A := A) state word start len
  exact hrecordSubset q (by
    rwa [← hrecordEq])

/--
If the next finite run block contains `r`, every state in the block lies in
`S`, and the following transition also reaches `r`, then the generated hit set
at that following transition is contained in `S`, independently of records
before the block.
-/
theorem eventAutomaton_runFrom_generated_hitSet_subset_of_target_seen_in_block
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (start len : Nat)
    (S : Finset A.State)
    {r : A.State}
    (hrBlock :
      ∃ offset : Nat,
        0 < offset ∧
          offset ≤ len ∧
            A.runFrom state.1 word (start + offset) = r)
    (hall :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (start + offset) ∈ S)
    (hnext : A.runFrom state.1 word (start + len + 1) = r) :
    ∀ q : A.State,
      q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 ->
        q ∈ S := by
  classical
  rcases hrBlock with ⟨offset, hpos, hle, hoffset⟩
  have hrS : r ∈ S := by
    rw [← hoffset]
    exact hall offset hpos hle
  have hblockAll :
      ∀ q : A.State,
        q ∈ eventRunStateBlock (A := A) state word start len -> q ∈ S :=
    eventRunStateBlock_forall_mem_of_forall_offsets
      (A := A) state word start len S hall
  have hrBlockMem :
      r ∈ eventRunStateBlock (A := A) state word start len := by
    rw [← hoffset]
    exact eventRunStateBlock_mem_of_pos_le
      (A := A) state word start len offset hpos hle
  have hrecordSubset :
      ∀ q : A.State,
        q ∈
            ((((eventAutomaton (A := A)).runFrom state word start).2.1).refreshList
              (eventRunStateBlock (A := A) state word start len)).hitSet r ->
          q ∈ S :=
    Record.hitSet_subset_refreshList_of_target_mem_of_forall_mem
      (A := A)
      (((eventAutomaton (A := A)).runFrom state word start).2.1)
      S (eventRunStateBlock (A := A) state word start len)
      hrBlockMem hblockAll
  intro q hq
  have hsucc : start + len + 1 = (start + len) + 1 := by omega
  have hnextStep :
      A.step (A.runFrom state.1 word (start + len)) (word (start + len)) = r := by
    rw [hsucc] at hnext
    simpa [DetMullerAutomaton.runFrom] using hnext
  rw [hsucc] at hq
  change
    q ∈
      (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
        ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
          state word (start + len))
        (word (start + len))).2.2) at hq
  rw [eventAutomatonWithPriority_step_hitSet] at hq
  rw [eventAutomatonWithPriority_runFrom_current] at hq
  rw [hnextStep] at hq
  have hrecordEq := eventAutomaton_runFrom_record_add
    (A := A) state word start len
  exact hrecordSubset q (by
    rwa [← hrecordEq])

/--
After a finite flushing horizon, every generated LAR hit set is contained in
the Muller infinity set of the source run.

The proof first waits until no non-recurring Muller state appears again.  It
then waits long enough that every recurring state has appeared once inside the
post-flush block.  Any later transition to state `r` can therefore point back to
an earlier post-flush occurrence of the same `r`, so the generated LAR hit set
is contained in the recurring-state set.
-/
theorem eventAutomaton_generated_hitSet_subset_inf_after_horizon
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    ∃ start horizon : Nat,
      ∀ len : Nat,
        horizon ≤ len ->
          ∀ q : A.State,
            q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 ->
              q ∈ A.infStateFinsetFrom state.1 word := by
  classical
  let S := A.infStateFinsetFrom state.1 word
  rcases A.eventually_mem_infStateFinsetFrom state.1 word with ⟨base, hbase⟩
  rcases A.exists_horizon_seen_all_infStateFinsetFrom state.1 word (base + 1) with
    ⟨horizonTime, _hbaseHorizon, hseenAll⟩
  refine ⟨base, horizonTime + 1, ?_⟩
  intro len hlen q hq
  let r := A.runFrom state.1 word (base + len + 1)
  have hrS : r ∈ S := by
    exact hbase (base + len + 1) (by omega)
  rcases hseenAll r hrS with ⟨k, hkBase, hkHorizon, hkr⟩
  let offset := k - base
  have hoffsetPos : 0 < offset := by
    omega
  have hoffsetLe : offset ≤ len := by
    omega
  have hbaseOffset : base + offset = k := by
    omega
  have hrBlock :
      ∃ offset : Nat,
        0 < offset ∧
          offset ≤ len ∧
            A.runFrom state.1 word (base + offset) = r := by
    refine ⟨offset, hoffsetPos, hoffsetLe, ?_⟩
    simpa [hbaseOffset] using hkr
  have hall :
      ∀ offset : Nat,
        0 < offset ->
          offset ≤ len ->
            A.runFrom state.1 word (base + offset) ∈ S := by
    intro offset _hpos _hle
    exact hbase (base + offset) (by omega)
  exact
    eventAutomaton_runFrom_generated_hitSet_subset_of_target_seen_in_block
      (A := A) state word base len S hrBlock hall rfl q hq

/-- The concrete event-carrying LAR automaton simulates the Muller initial run. -/
theorem eventAutomaton_run_current
    (word : OmegaWord Alphabet)
    (n : Nat) :
    ((eventAutomaton (A := A)).run word n).1 =
      A.run word n :=
  eventAutomatonWithPriority_run_current (A := A)
    (eventPriority (A := A)) word n

/--
Infinite visits of Muller states are exactly preserved by the first projection
of the concrete event-carrying LAR run.
-/
theorem eventAutomaton_stateSeen_current_iff
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (q : A.State) :
    (∀ n : Nat, ∃ k : Nat, n ≤ k ∧
        ((eventAutomaton (A := A)).runFrom state word k).1 = q) ↔
      A.StateSeenInfinitelyOftenFrom state.1 word q := by
  constructor
  · intro h n
    rcases h n with ⟨k, hk, hq⟩
    refine ⟨k, hk, ?_⟩
    simpa [eventAutomaton_runFrom_current (A := A) state word k] using hq
  · intro h n
    rcases h n with ⟨k, hk, hq⟩
    refine ⟨k, hk, ?_⟩
    simpa [eventAutomaton_runFrom_current (A := A) state word k] using hq

/-- The concrete event automaton's projected infinity set is the Muller infinity set. -/
theorem eventAutomaton_projectedInfStates_eq
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    { q : A.State | ∀ n : Nat, ∃ k : Nat, n ≤ k ∧
        ((eventAutomaton (A := A)).runFrom state word k).1 = q } =
      A.InfStatesFrom state.1 word := by
  ext q
  exact eventAutomaton_stateSeen_current_iff (A := A) state word q

/-- The most recent hit set always contains the just-reached Muller state. -/
theorem eventAutomatonWithPriority_runFrom_hitSet_contains_current_succ
    (priority : EventState A -> Nat)
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.runFrom state.1 word (n + 1) ∈
      ((eventAutomatonWithPriority (A := A) priority).runFrom state word (n + 1)).2.2 := by
  change
    A.step (A.runFrom state.1 word n) (word n) ∈
      ((eventAutomatonWithPriority (A := A) priority).step
        ((eventAutomatonWithPriority (A := A) priority).runFrom state word n)
        (word n)).2.2
  rw [eventAutomatonWithPriority_step_hitSet]
  rw [eventAutomatonWithPriority_runFrom_current (A := A) priority state word n]
  exact Record.mem_hitSet_self _ _

/-- The concrete event automaton's most recent hit set contains the current Muller state. -/
theorem eventAutomaton_runFrom_hitSet_contains_current_succ
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    A.runFrom state.1 word (n + 1) ∈
      ((eventAutomaton (A := A)).runFrom state word (n + 1)).2.2 :=
  eventAutomatonWithPriority_runFrom_hitSet_contains_current_succ (A := A)
    (eventPriority (A := A)) state word n

/--
Along the concrete event automaton, evenness of the current priority is exactly
Muller-acceptance of the stored hit set.
-/
theorem eventAutomaton_priority_even_iff_hitSet_accepting
    (state : EventState A) :
    DetParityAutomaton.NatEven ((eventAutomaton (A := A)).priority state) ↔
      (state.2.2 : Set A.State) ∈ A.accepting := by
  rw [eventAutomaton_priority]
  exact eventPriority_even_iff_accepting (A := A) state

/--
The same parity characterization specialized to states reached during a run.
-/
theorem eventAutomaton_runFrom_priority_even_iff_hitSet_accepting
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (n : Nat) :
    DetParityAutomaton.NatEven
        ((eventAutomaton (A := A)).priority
          ((eventAutomaton (A := A)).runFrom state word n)) ↔
      (((eventAutomaton (A := A)).runFrom state word n).2.2 : Set A.State) ∈
        A.accepting :=
  eventAutomaton_priority_even_iff_hitSet_accepting (A := A)
    ((eventAutomaton (A := A)).runFrom state word n)

/--
For the concrete LAR automaton, a priority is seen infinitely often iff some
event state with that priority is seen infinitely often.
-/
theorem eventAutomaton_prioritySeen_iff_stateSeen
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (p : Nat) :
    (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom state word p ↔
      ∃ eventState : EventState A,
        (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
          state word eventState ∧
          eventPriority (A := A) eventState = p := by
  exact
    DetParityAutomaton.toMuller_prioritySeen_iff
      (eventAutomaton (A := A)) state word p

/--
Any even priority seen infinitely often by the concrete LAR automaton is
witnessed by an infinitely recurring event state whose stored hit set is
Muller-accepting.
-/
theorem eventAutomaton_exists_accepting_hitSet_of_even_prioritySeen
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (p : Nat)
    (hpEven : DetParityAutomaton.NatEven p)
    (hpSeen :
      (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom state word p) :
    ∃ eventState : EventState A,
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState ∧
        (eventState.2.2 : Set A.State) ∈ A.accepting ∧
          eventPriority (A := A) eventState = p := by
  rcases (eventAutomaton_prioritySeen_iff_stateSeen (A := A) state word p).mp hpSeen with
    ⟨eventState, hstateSeen, hpriority⟩
  refine ⟨eventState, hstateSeen, ?_, hpriority⟩
  have hevenState : DetParityAutomaton.NatEven (eventPriority (A := A) eventState) := by
    rwa [hpriority]
  exact (eventPriority_even_iff_accepting (A := A) eventState).mp hevenState

/--
Any rejecting event state recurring infinitely often contributes an infinitely
often odd priority.
-/
theorem eventAutomaton_prioritySeen_of_rejecting_stateSeen
    (state eventState : EventState A)
    (word : OmegaWord Alphabet)
    (hrej : (eventState.2.2 : Set A.State) ∉ A.accepting)
    (hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState) :
    (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom
      state word (eventPriority (A := A) eventState) ∧
      ¬ DetParityAutomaton.NatEven (eventPriority (A := A) eventState) := by
  constructor
  · exact (eventAutomaton_prioritySeen_iff_stateSeen (A := A)
      state word (eventPriority (A := A) eventState)).mpr
      ⟨eventState, hstateSeen, rfl⟩
  · exact eventPriority_not_even_of_rejecting (A := A) eventState hrej

/--
A rejecting recurring event state gives a concrete lower-priority obstruction
candidate: its priority is seen infinitely often and is odd.
-/
theorem eventAutomaton_rejecting_stateSeen_priority_odd
    (state eventState : EventState A)
    (word : OmegaWord Alphabet)
    (hrej : (eventState.2.2 : Set A.State) ∉ A.accepting)
    (hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState) :
    ∃ p : Nat,
      (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom state word p ∧
        ¬ DetParityAutomaton.NatEven p ∧
          p = eventPriority (A := A) eventState := by
  rcases eventAutomaton_prioritySeen_of_rejecting_stateSeen
      (A := A) state eventState word hrej hstateSeen with
    ⟨hpSeen, hpOdd⟩
  exact ⟨eventPriority (A := A) eventState, hpSeen, hpOdd, rfl⟩

/--
Unpack an accepting concrete LAR run into the recurring accepting hit set that
witnesses its minimal even priority.
-/
theorem eventAutomaton_acceptsFrom_exists_min_accepting_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ p : Nat,
      ∃ eventState : EventState A,
        DetParityAutomaton.NatEven p ∧
          (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom
            state word p ∧
            (∀ q : Nat,
              (eventAutomaton (A := A)).PrioritySeenInfinitelyOftenFrom
                state word q -> p ≤ q) ∧
              (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
                state word eventState ∧
                (eventState.2.2 : Set A.State) ∈ A.accepting ∧
                  eventPriority (A := A) eventState = p := by
  rcases hacc with ⟨p, hpEven, hpSeen, hpMin⟩
  rcases eventAutomaton_exists_accepting_hitSet_of_even_prioritySeen
      (A := A) state word p hpEven hpSeen with
    ⟨eventState, hstateSeen, hhitAccepting, hpriority⟩
  exact
    ⟨p, eventState, hpEven, hpSeen, hpMin, hstateSeen,
      hhitAccepting, hpriority⟩

/--
If an event state recurs infinitely often in the LAR automaton, then its Muller
state component recurs infinitely often in the source Muller automaton.
-/
theorem eventAutomaton_mullerStateSeen_of_eventStateSeen
    (state eventState : EventState A)
    (word : OmegaWord Alphabet)
    (hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState) :
    A.StateSeenInfinitelyOftenFrom state.1 word eventState.1 := by
  intro n
  rcases hstateSeen n with ⟨k, hk, hkevent⟩
  refine ⟨k, hk, ?_⟩
  have hrun :
      (eventAutomaton (A := A)).runFrom state word k = eventState := by
    simpa using hkevent
  have hcurrent :=
    eventAutomaton_runFrom_current (A := A) state word k
  rw [hrun] at hcurrent
  exact hcurrent.symm

/--
Any infinitely recurring event state has its current Muller component in its
stored hit set.  The proof uses a positive recurring occurrence.
-/
theorem eventAutomaton_eventState_current_mem_hitSet_of_stateSeen
    (state eventState : EventState A)
    (word : OmegaWord Alphabet)
    (hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState) :
    eventState.1 ∈ eventState.2.2 := by
  rcases hstateSeen 1 with ⟨k, hk, hkevent⟩
  cases k with
  | zero =>
      cases Nat.not_succ_le_zero 0 hk
  | succ k =>
      have hrun :
          (eventAutomaton (A := A)).runFrom state word (k + 1) = eventState := by
        simpa using hkevent
      have hmem :=
        eventAutomaton_runFrom_hitSet_contains_current_succ
          (A := A) state word k
      have hcurrent :=
        eventAutomaton_runFrom_current (A := A) state word (k + 1)
      rw [hrun] at hmem hcurrent
      simpa [hcurrent.symm] using hmem

/--
An accepting concrete LAR run exposes an accepting recurring hit set whose
current Muller component is genuinely in the source Muller infinity set and in
that hit set.
-/
theorem eventAutomaton_acceptsFrom_exists_accepting_hitSet_with_inf_current
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ eventState : EventState A,
      (eventState.2.2 : Set A.State) ∈ A.accepting ∧
        A.StateSeenInfinitelyOftenFrom state.1 word eventState.1 ∧
          eventState.1 ∈ eventState.2.2 := by
  rcases eventAutomaton_acceptsFrom_exists_min_accepting_hitSet
      (A := A) state word hacc with
    ⟨_p, eventState, _hpEven, _hpSeen, _hpMin,
      hstateSeen, hhitAccepting, _hpriority⟩
  exact
    ⟨eventState, hhitAccepting,
      eventAutomaton_mullerStateSeen_of_eventStateSeen
        (A := A) state eventState word hstateSeen,
      eventAutomaton_eventState_current_mem_hitSet_of_stateSeen
        (A := A) state eventState word hstateSeen⟩

/--
An accepting concrete LAR run has an accepting recurring event state whose
priority is minimal among all recurring event states.
-/
theorem eventAutomaton_acceptsFrom_exists_minimal_accepting_eventState
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ eventState : EventState A,
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState ∧
        (eventState.2.2 : Set A.State) ∈ A.accepting ∧
          ∀ other : EventState A,
            (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
              state word other ->
              eventPriority (A := A) eventState ≤
                eventPriority (A := A) other := by
  rcases eventAutomaton_acceptsFrom_exists_min_accepting_hitSet
      (A := A) state word hacc with
    ⟨p, eventState, _hpEven, _hpSeen, hpMin,
      hstateSeen, hhitAccepting, hpriority⟩
  refine ⟨eventState, hstateSeen, hhitAccepting, ?_⟩
  intro other hotherSeen
  rw [hpriority]
  exact hpMin (eventPriority (A := A) other)
    ((eventAutomaton_prioritySeen_iff_stateSeen (A := A)
      state word (eventPriority (A := A) other)).mpr
      ⟨other, hotherSeen, rfl⟩)

/--
The minimal accepting recurring event state supplied by an accepting LAR run
also projects to a Muller state occurring infinitely often in the source run.
-/
theorem eventAutomaton_acceptsFrom_exists_minimal_accepting_eventState_with_inf_current
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ eventState : EventState A,
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState ∧
        (eventState.2.2 : Set A.State) ∈ A.accepting ∧
          A.StateSeenInfinitelyOftenFrom state.1 word eventState.1 ∧
            eventState.1 ∈ eventState.2.2 ∧
              ∀ other : EventState A,
                (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
                  state word other ->
                  eventPriority (A := A) eventState ≤
                    eventPriority (A := A) other := by
  rcases eventAutomaton_acceptsFrom_exists_minimal_accepting_eventState
      (A := A) state word hacc with
    ⟨eventState, hstateSeen, hhitAccepting, hminimal⟩
  exact
    ⟨eventState, hstateSeen, hhitAccepting,
      eventAutomaton_mullerStateSeen_of_eventStateSeen
        (A := A) state eventState word hstateSeen,
      eventAutomaton_eventState_current_mem_hitSet_of_stateSeen
        (A := A) state eventState word hstateSeen,
      hminimal⟩

/--
The minimal accepting recurring event state supplied by an accepting LAR run has
a hit set of maximal cardinality among all recurring event states.
-/
theorem eventAutomaton_acceptsFrom_exists_maximal_accepting_hitSet_card
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ eventState : EventState A,
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState ∧
        (eventState.2.2 : Set A.State) ∈ A.accepting ∧
          ∀ other : EventState A,
            (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
              state word other ->
              other.2.2.card ≤ eventState.2.2.card := by
  rcases eventAutomaton_acceptsFrom_exists_minimal_accepting_eventState
      (A := A) state word hacc with
    ⟨eventState, hstateSeen, hhitAccepting, hminimal⟩
  refine ⟨eventState, hstateSeen, hhitAccepting, ?_⟩
  intro other hotherSeen
  exact eventPriority_accepting_le_imp_card_le
    (A := A) eventState other hhitAccepting (hminimal other hotherSeen)

/-- A recurring event state yields a recurring hit set. -/
theorem eventHitSetSeen_of_eventStateSeen
    (state eventState : EventState A)
    (word : OmegaWord Alphabet)
    (hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word eventState.2.2 :=
  ⟨eventState, hstateSeen, rfl⟩

/--
Every recurring hit set contains the current Muller component of a recurring
event state witnessing it.
-/
theorem eventHitSetSeen_exists_inf_member
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet) :
    ∃ q : A.State,
      A.StateSeenInfinitelyOftenFrom state.1 word q ∧ q ∈ hitSet := by
  rcases hhitSeen with ⟨eventState, hstateSeen, hhitEq⟩
  refine ⟨eventState.1, ?_, ?_⟩
  · exact eventAutomaton_mullerStateSeen_of_eventStateSeen
      (A := A) state eventState word hstateSeen
  · rw [← hhitEq]
    exact eventAutomaton_eventState_current_mem_hitSet_of_stateSeen
      (A := A) state eventState word hstateSeen

/-- Every recurring hit set is nonempty. -/
theorem eventHitSetSeen_nonempty
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet) :
    hitSet.Nonempty := by
  rcases eventHitSetSeen_exists_inf_member
      (A := A) state word hitSet hhitSeen with
    ⟨q, _hqInf, hqMem⟩
  exact ⟨q, hqMem⟩

/--
Every source Muller state that occurs infinitely often belongs to some
recurring LAR hit set.
-/
theorem eventAutomaton_exists_recurring_hitSet_of_mullerStateSeen
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (q : A.State)
    (hqSeen : A.StateSeenInfinitelyOftenFrom state.1 word q) :
    ∃ hitSet : Finset A.State,
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
        q ∈ hitSet := by
  classical
  let goodTimes : Set Nat :=
    {n | 0 < n ∧ A.runFrom state.1 word n = q}
  have hgoodFreq : ∃ᶠ n in Filter.atTop, n ∈ goodTimes := by
    rw [Filter.frequently_atTop]
    intro n
    rcases hqSeen (max n 1) with ⟨k, hk, hkq⟩
    refine ⟨k, ?_, ?_⟩
    · exact le_trans (Nat.le_max_left n 1) hk
    · exact ⟨lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_max_right n 1) hk), hkq⟩
  have hgoodInfinite : goodTimes.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite]
    exact hgoodFreq
  haveI : Infinite {n : Nat // n ∈ goodTimes} :=
    Set.Infinite.to_subtype hgoodInfinite
  obtain ⟨eventState, hfiber⟩ :=
    Finite.exists_infinite_fiber
      (fun n : {n : Nat // n ∈ goodTimes} =>
        (eventAutomaton (A := A)).runFrom state word n.1)
  let fiberSet : Set {n : Nat // n ∈ goodTimes} :=
    {n | (eventAutomaton (A := A)).runFrom state word n.1 = eventState}
  have hfiberSet : fiberSet.Infinite := by
    simpa [fiberSet, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hfiber)
  have hImageInf : (Subtype.val '' fiberSet).Infinite :=
    hfiberSet.image (fun x _ y _ hxy => Subtype.ext hxy)
  have hEventTimesInf :
      Set.Infinite
        {n : Nat | (eventAutomaton (A := A)).runFrom state word n = eventState} := by
    refine hImageInf.mono ?_
    intro n hn
    rcases hn with ⟨m, hm, rfl⟩
    exact hm
  have hfreqEvent :
      ∃ᶠ n in Filter.atTop,
        (eventAutomaton (A := A)).runFrom state word n = eventState := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hEventTimesInf
  have hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState := by
    rw [Filter.frequently_atTop] at hfreqEvent
    intro n
    rcases hfreqEvent n with ⟨k, hk, hkevent⟩
    exact ⟨k, hk, by simpa using hkevent⟩
  have hEventCurrent : eventState.1 = q := by
    have hfiberNonempty : fiberSet.Nonempty := hfiberSet.nonempty
    rcases hfiberNonempty with ⟨m, hm⟩
    have hmGood : m.1 ∈ goodTimes := m.2
    have hmRun : (eventAutomaton (A := A)).runFrom state word m.1 = eventState := hm
    have hmCurrent :=
      eventAutomaton_runFrom_current (A := A) state word m.1
    rw [hmRun] at hmCurrent
    exact hmCurrent.trans hmGood.2
  refine ⟨eventState.2.2, ⟨eventState, hstateSeen, rfl⟩, ?_⟩
  have hmem :=
    eventAutomaton_eventState_current_mem_hitSet_of_stateSeen
      (A := A) state eventState word hstateSeen
  simpa [hEventCurrent] using hmem

/--
If a hit set recurs, then it is generated infinitely often by actual positive
transitions of the event LAR automaton.  The returned index `k` names the
previous event state; the hit set at time `k + 1` is computed from that
previous record and the newly reached Muller state.
-/
theorem eventHitSetSeen_frequently_generated_from_previous_record
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k + 1 ∧
          ((eventAutomaton (A := A)).runFrom state word (k + 1)).2.2 =
            hitSet ∧
            (Record.hitSet
              (((eventAutomaton (A := A)).runFrom state word k).2.1)
              (A.runFrom state.1 word (k + 1))) = hitSet := by
  rcases hhitSeen with ⟨eventState, hstateSeen, hhitEq⟩
  intro n
  rcases hstateSeen (n + 1) with ⟨t, ht, htevent⟩
  cases t with
  | zero =>
      cases Nat.not_succ_le_zero n ht
  | succ k =>
      have hrun :
          (eventAutomaton (A := A)).runFrom state word (k + 1) =
            eventState := by
        simpa using htevent
      have htimeHit :
          ((eventAutomaton (A := A)).runFrom state word (k + 1)).2.2 =
            hitSet := by
        rw [hrun, hhitEq]
      have hgenerated :
          ((eventAutomaton (A := A)).runFrom state word (k + 1)).2.2 =
            (Record.hitSet
              (((eventAutomaton (A := A)).runFrom state word k).2.1)
              (A.runFrom state.1 word (k + 1))) := by
        change (
          (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).step
              ((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
                state word k)
              (word k)).2.2 =
            (Record.hitSet
              (((eventAutomatonWithPriority (A := A) (eventPriority (A := A))).runFrom
                state word k).2.1)
              (A.runFrom state.1 word (k + 1))))
        )
        rw [eventAutomatonWithPriority_step_hitSet]
        rw [eventAutomatonWithPriority_runFrom_current]
        rfl
      refine ⟨k, ?_, htimeHit, ?_⟩
      · omega
      · exact hgenerated.symm.trans htimeHit

/--
Every member of a recurring hit set is generated infinitely often from previous
records at real transition times.
-/
theorem eventHitSetSeen_member_frequently_generated_from_previous_record
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    {q : A.State}
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet)
    (hq : q ∈ hitSet) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k + 1 ∧
          q ∈ (Record.hitSet
            (((eventAutomaton (A := A)).runFrom state word k).2.1)
            (A.runFrom state.1 word (k + 1))) := by
  intro n
  rcases eventHitSetSeen_frequently_generated_from_previous_record
      (A := A) state word hitSet hhitSeen n with
    ⟨k, hk, _htimeHit, hgenerated⟩
  exact ⟨k, hk, by rwa [hgenerated]⟩

/--
If a hit set occurs arbitrarily late as the stored generated hit set, then it is
a recurring LAR hit set.  This is just finite pigeonhole over the full event
state at those occurrence times.
-/
theorem eventHitSetSeen_of_frequently_generated_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hfreq :
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧
            ((eventAutomaton (A := A)).runFrom state word k).2.2 = hitSet) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet := by
  classical
  let goodTimes : Set Nat :=
    {n | ((eventAutomaton (A := A)).runFrom state word n).2.2 = hitSet}
  have hgoodFreq : ∃ᶠ n in Filter.atTop, n ∈ goodTimes := by
    rw [Filter.frequently_atTop]
    intro n
    rcases hfreq n with ⟨k, hk, hkhit⟩
    exact ⟨k, hk, hkhit⟩
  have hgoodInfinite : goodTimes.Infinite := by
    rw [← Nat.frequently_atTop_iff_infinite]
    exact hgoodFreq
  haveI : Infinite {n : Nat // n ∈ goodTimes} :=
    Set.Infinite.to_subtype hgoodInfinite
  obtain ⟨eventState, hfiber⟩ :=
    Finite.exists_infinite_fiber
      (fun n : {n : Nat // n ∈ goodTimes} =>
        (eventAutomaton (A := A)).runFrom state word n.1)
  let fiberSet : Set {n : Nat // n ∈ goodTimes} :=
    {n | (eventAutomaton (A := A)).runFrom state word n.1 = eventState}
  have hfiberSet : fiberSet.Infinite := by
    simpa [fiberSet, Set.preimage, Set.mem_singleton_iff] using
      (Set.infinite_coe_iff.1 hfiber)
  have hImageInf : (Subtype.val '' fiberSet).Infinite :=
    hfiberSet.image (fun x _ y _ hxy => Subtype.ext hxy)
  have hEventTimesInf :
      Set.Infinite
        {n : Nat | (eventAutomaton (A := A)).runFrom state word n = eventState} := by
    refine hImageInf.mono ?_
    intro n hn
    rcases hn with ⟨m, hm, rfl⟩
    exact hm
  have hfreqEvent :
      ∃ᶠ n in Filter.atTop,
        (eventAutomaton (A := A)).runFrom state word n = eventState := by
    rw [Nat.frequently_atTop_iff_infinite]
    exact hEventTimesInf
  have hstateSeen :
      (eventAutomaton (A := A)).toMuller.StateSeenInfinitelyOftenFrom
        state word eventState := by
    rw [Filter.frequently_atTop] at hfreqEvent
    intro n
    rcases hfreqEvent n with ⟨k, hk, hkevent⟩
    exact ⟨k, hk, by simpa using hkevent⟩
  have hhit : eventState.2.2 = hitSet := by
    have hfiberNonempty : fiberSet.Nonempty := hfiberSet.nonempty
    rcases hfiberNonempty with ⟨m, hm⟩
    have hmGood : m.1 ∈ goodTimes := m.2
    have hmRun : (eventAutomaton (A := A)).runFrom state word m.1 = eventState := hm
    rw [← hmRun]
    exact hmGood
  exact ⟨eventState, hstateSeen, hhit⟩

/--
Every recurring LAR hit set is contained in the actual Muller infinity set.

This is the upper-bound half of LAR exactness: after the flushing horizon,
recurrence gives an occurrence of the same hit set at a generated transition,
and the flushing lemma bounds that generated set by the true infinity set.
-/
theorem eventHitSetSeen_subset_infStateFinsetFrom
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet) :
    ∀ q : A.State,
      q ∈ hitSet ->
        q ∈ A.infStateFinsetFrom state.1 word := by
  classical
  rcases eventAutomaton_generated_hitSet_subset_inf_after_horizon
      (A := A) state word with
    ⟨start, horizon, hsubsetGenerated⟩
  intro q hq
  rcases eventHitSetSeen_frequently_generated_from_previous_record
      (A := A) state word hitSet hhitSeen (start + horizon + 1) with
    ⟨k, hkLate, htimeHit, _hgenerated⟩
  let len := k - start
  have hstartLe : start ≤ k := by
    omega
  have hlenGe : horizon ≤ len := by
    omega
  have htime : start + len + 1 = k + 1 := by
    omega
  have hqGenerated :
      q ∈ ((eventAutomaton (A := A)).runFrom state word (start + len + 1)).2.2 := by
    rw [htime, htimeHit]
    exact hq
  exact hsubsetGenerated len hlenGe q hqGenerated

/-- Cardinal form of `eventHitSetSeen_subset_infStateFinsetFrom`. -/
theorem eventHitSetSeen_card_le_infStateFinsetFrom
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet) :
    hitSet.card ≤ (A.infStateFinsetFrom state.1 word).card := by
  exact Finset.card_le_card
    (eventHitSetSeen_subset_infStateFinsetFrom
      (A := A) state word hitSet hhitSeen)

/--
It is enough to find a recurring hit set containing all states in the semantic
Muller infinity set: the upper-bound theorem forces that hit set to be exactly
the infinity set.
-/
theorem infStateFinset_recurring_of_recurring_superset
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet)
    (hinfSubset :
      ∀ q : A.State,
        q ∈ A.infStateFinsetFrom state.1 word ->
          q ∈ hitSet) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word
      (A.infStateFinsetFrom state.1 word) := by
  have hhitSubset :
      ∀ q : A.State,
        q ∈ hitSet ->
          q ∈ A.infStateFinsetFrom state.1 word :=
    eventHitSetSeen_subset_infStateFinsetFrom
      (A := A) state word hitSet hhitSeen
  have hhitEq : hitSet = A.infStateFinsetFrom state.1 word := by
    exact Finset.Subset.antisymm hhitSubset hinfSubset
  rcases hhitSeen with ⟨eventState, hstateSeen, hstateHit⟩
  refine ⟨eventState, hstateSeen, ?_⟩
  rw [hstateHit, hhitEq]

/--
The concrete LAR run generates hit sets containing the whole semantic Muller
infinity set arbitrarily late.

At a late record, choose a least-recent member `r` of the infinity set; its
record hit set contains the whole infinity set.  Since `r` occurs infinitely
often, wait for its first later return.  No intervening refresh touches `r`, so
the lower bound is preserved until the return transition generates the next hit
set.
-/
theorem eventAutomaton_frequently_generated_hitSet_superset_infStateFinsetFrom
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    ∀ n : Nat,
      ∃ k : Nat,
        n ≤ k ∧
          ∀ q : A.State,
            q ∈ A.infStateFinsetFrom state.1 word ->
              q ∈ ((eventAutomaton (A := A)).runFrom state word k).2.2 := by
  classical
  intro n
  let S := A.infStateFinsetFrom state.1 word
  rcases Record.exists_hitSet_superset_finset
      (A := A)
      (((eventAutomaton (A := A)).runFrom state word n).2.1)
      S (A.infStateFinsetFrom_nonempty state.1 word) with
    ⟨r, hrS, hrecord⟩
  rcases A.infStateFinsetFrom_first_seen_after state.1 word hrS n with
    ⟨k, hnk, hkr, hfirst⟩
  let len := k - n - 1
  have htime : n + len + 1 = k := by
    omega
  refine ⟨k, by omega, ?_⟩
  rw [← htime]
  exact
    eventAutomaton_runFrom_generated_hitSet_superset_of_block_avoids_target
      (A := A) state word n len S hrecord
      (by
        intro offset hpos hle
        exact hfirst (n + offset) (by omega) (by omega))
      (by
        rw [htime]
        exact hkr)

/--
If arbitrarily late generated LAR hit sets contain every semantic
Muller-infinity state, then the semantic infinity set itself recurs.

The flushing lemma supplies the reverse inclusion for sufficiently late
generated hit sets, so these arbitrarily late supersets are in fact exact
occurrences of the infinity set.
-/
theorem infStateFinset_recurring_of_frequently_generated_superset
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hfreq :
      ∀ n : Nat,
        ∃ k : Nat,
          n ≤ k ∧
            ∀ q : A.State,
              q ∈ A.infStateFinsetFrom state.1 word ->
                q ∈ ((eventAutomaton (A := A)).runFrom state word k).2.2) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word
      (A.infStateFinsetFrom state.1 word) := by
  classical
  rcases eventAutomaton_generated_hitSet_subset_inf_after_horizon
      (A := A) state word with
    ⟨start, horizon, hsubsetGenerated⟩
  apply eventHitSetSeen_of_frequently_generated_hitSet
    (A := A) state word (A.infStateFinsetFrom state.1 word)
  intro n
  rcases hfreq (max n (start + horizon + 1)) with
    ⟨k, hkLate, hkSuperset⟩
  let len := k - start - 1
  have hkN : n ≤ k := by
    exact le_trans (Nat.le_max_left n (start + horizon + 1)) hkLate
  have hstartHorizon : start + horizon + 1 ≤ k := by
    exact le_trans (Nat.le_max_right n (start + horizon + 1)) hkLate
  have hlenGe : horizon ≤ len := by
    omega
  have htime : start + len + 1 = k := by
    omega
  have hsubset :
      ∀ q : A.State,
        q ∈ ((eventAutomaton (A := A)).runFrom state word k).2.2 ->
          q ∈ A.infStateFinsetFrom state.1 word := by
    intro q hq
    rw [← htime] at hq
    exact hsubsetGenerated len hlenGe q hq
  refine ⟨k, hkN, ?_⟩
  exact Finset.Subset.antisymm hsubset hkSuperset

/--
Arbitrarily late complete-return intervals force recurrence of the semantic
Muller infinity set.  A complete-return interval is a finite block that sees
every infinity-state, avoids the next target `r`, and then returns to `r`.
-/
theorem infStateFinset_recurring_of_frequently_complete_return
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hfreq :
      ∀ n : Nat,
        ∃ start len : Nat,
          ∃ r : A.State,
            n ≤ start + len + 1 ∧
              (∀ q : A.State,
                q ∈ A.infStateFinsetFrom state.1 word ->
                  q ≠ r ->
                    ∃ offset : Nat,
                      0 < offset ∧
                        offset ≤ len ∧
                          A.runFrom state.1 word (start + offset) = q) ∧
              (∀ offset : Nat,
                0 < offset ->
                  offset ≤ len ->
                    A.runFrom state.1 word (start + offset) ≠ r) ∧
              A.runFrom state.1 word (start + len + 1) = r) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word
      (A.infStateFinsetFrom state.1 word) := by
  apply infStateFinset_recurring_of_frequently_generated_superset
    (A := A) state word
  intro n
  rcases hfreq n with
    ⟨start, len, r, hlate, hseenAll, hrAvoid, hnext⟩
  refine ⟨start + len + 1, hlate, ?_⟩
  exact
    eventAutomaton_runFrom_generated_hitSet_contains_inf_of_seen_all_before_next_target
      (A := A) state word start len hseenAll hrAvoid hnext

/--
If the semantic Muller infinity set itself recurs as an LAR hit set, then any
cardinality-maximal recurring hit set is exactly that infinity set.
-/
theorem maximal_recurring_hitSet_eq_infStateFinsetFrom_of_inf_recurring
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet)
    (hmax :
      ∀ otherHitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
          otherHitSet.card ≤ hitSet.card)
    (hinfSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word
        (A.infStateFinsetFrom state.1 word)) :
    hitSet = A.infStateFinsetFrom state.1 word := by
  exact Finset.eq_of_subset_of_card_le
    (eventHitSetSeen_subset_infStateFinsetFrom
      (A := A) state word hitSet hhitSeen)
    (hmax (A.infStateFinsetFrom state.1 word) hinfSeen)

/--
Set-valued exactness of cardinality-maximal recurring hit sets, assuming the
semantic infinity set recurs as an LAR hit set.
-/
theorem maximal_recurring_hitSet_exact_of_inf_recurring
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hitSet : Finset A.State)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet)
    (hmax :
      ∀ otherHitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
          otherHitSet.card ≤ hitSet.card)
    (hinfSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word
        (A.infStateFinsetFrom state.1 word)) :
    (hitSet : Set A.State) = A.InfStatesFrom state.1 word := by
  rw [maximal_recurring_hitSet_eq_infStateFinsetFrom_of_inf_recurring
      (A := A) state word hitSet hhitSeen hmax hinfSeen]
  exact A.coe_infStateFinsetFrom state.1 word

/--
An accepting concrete LAR run has an accepting recurring hit set whose
cardinality is maximal among all recurring hit sets.
-/
theorem eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ hitSet : Finset A.State,
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
        (hitSet : Set A.State) ∈ A.accepting ∧
          ∀ otherHitSet : Finset A.State,
            EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
              otherHitSet.card ≤ hitSet.card := by
  rcases eventAutomaton_acceptsFrom_exists_maximal_accepting_hitSet_card
      (A := A) state word hacc with
    ⟨eventState, hstateSeen, hhitAccepting, hmaxCard⟩
  refine ⟨eventState.2.2, ⟨eventState, hstateSeen, rfl⟩, hhitAccepting, ?_⟩
  intro otherHitSet hotherHitSet
  rcases hotherHitSet with ⟨other, hotherSeen, hotherEq⟩
  rw [← hotherEq]
  exact hmaxCard other hotherSeen

/--
A recurring accepting hit set whose cardinality is maximal among all recurring
hit sets yields an accepting parity run.
-/
theorem eventAutomaton_acceptsFrom_of_exists_maximal_accepting_recurring_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hmax :
      ∃ hitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
          (hitSet : Set A.State) ∈ A.accepting ∧
            ∀ otherHitSet : Finset A.State,
              EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
                otherHitSet.card ≤ hitSet.card) :
    (eventAutomaton (A := A)).AcceptsFrom state word := by
  rcases hmax with ⟨hitSet, hhitSeen, hhitAcc, hmaxCard⟩
  rcases hhitSeen with ⟨eventState, hstateSeen, hhitEq⟩
  refine ⟨eventPriority (A := A) eventState, ?_, ?_, ?_⟩
  · exact
      (eventPriority_even_iff_accepting (A := A) eventState).mpr
        (by simpa [hhitEq] using hhitAcc)
  · exact
      (eventAutomaton_prioritySeen_iff_stateSeen (A := A)
        state word (eventPriority (A := A) eventState)).mpr
        ⟨eventState, hstateSeen, rfl⟩
  · intro q hqSeen
    rcases (eventAutomaton_prioritySeen_iff_stateSeen (A := A)
        state word q).mp hqSeen with
      ⟨other, hotherSeen, hotherPriority⟩
    rw [← hotherPriority]
    exact eventPriority_accepting_card_le_imp_priority_le
      (A := A) eventState other
      (by simpa [hhitEq] using hhitAcc)
      (by
        have hotherHitSeen :
            EventHitSetSeenInfinitelyOftenFrom (A := A)
              state word other.2.2 :=
          ⟨other, hotherSeen, rfl⟩
        have hcard := hmaxCard other.2.2 hotherHitSeen
        simpa [hhitEq] using hcard)

/--
The concrete LAR parity condition is equivalent to the existence of a
cardinality-maximal recurring accepting hit set.
-/
theorem eventAutomaton_acceptsFrom_iff_exists_maximal_accepting_recurring_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    (eventAutomaton (A := A)).AcceptsFrom state word ↔
      ∃ hitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
          (hitSet : Set A.State) ∈ A.accepting ∧
            ∀ otherHitSet : Finset A.State,
              EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
                otherHitSet.card ≤ hitSet.card := by
  constructor
  · exact eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet
      (A := A) state word
  · exact eventAutomaton_acceptsFrom_of_exists_maximal_accepting_recurring_hitSet
      (A := A) state word

/--
If the concrete finite Muller infinity set is a cardinality-maximal recurring
hit set, Muller acceptance implies acceptance of the LAR parity automaton.
-/
theorem eventAutomaton_acceptsFrom_of_infStateFinset_maximal_recurring
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hhitSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word
        (A.infStateFinsetFrom state.1 word))
    (hmax :
      ∀ otherHitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
          otherHitSet.card ≤ (A.infStateFinsetFrom state.1 word).card)
    (hacc : A.AcceptsFrom state.1 word) :
    (eventAutomaton (A := A)).AcceptsFrom state word := by
  exact eventAutomaton_acceptsFrom_of_exists_maximal_accepting_recurring_hitSet
    (A := A) state word
    ⟨A.infStateFinsetFrom state.1 word, hhitSeen,
      (A.acceptsFrom_iff_infStateFinsetFrom_accepting state.1 word).mp hacc,
      hmax⟩

/--
Full state-wise correctness follows once the LAR combinatorics prove that the
finite Muller infinity set is a maximal recurring hit set and that every
maximal recurring hit set denotes the same semantic infinity set.
-/
theorem eventAutomatonCorrectFrom_of_maximal_recurring_hitSet_exact
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hinfSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word
        (A.infStateFinsetFrom state.1 word))
    (hinfMax :
      ∀ otherHitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
          otherHitSet.card ≤ (A.infStateFinsetFrom state.1 word).card)
    (hexact :
      ∀ hitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ->
          (∀ otherHitSet : Finset A.State,
            EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
              otherHitSet.card ≤ hitSet.card) ->
            (hitSet : Set A.State) = A.InfStatesFrom state.1 word) :
    eventAutomatonCorrectFrom (A := A) state word := by
  constructor
  · intro hparity
    rcases eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet
        (A := A) state word hparity with
      ⟨hitSet, hhitSeen, hhitAcc, hmax⟩
    rw [DetMullerAutomaton.AcceptsFrom]
    rwa [← hexact hitSet hhitSeen hmax]
  · intro hmuller
    exact eventAutomaton_acceptsFrom_of_infStateFinset_maximal_recurring
      (A := A) state word hinfSeen hinfMax hmuller

/--
It is enough for full state-wise correctness to prove the core LAR exactness
claim: every cardinality-maximal recurring hit set is exactly the source Muller
infinity set.  Existence of a maximal recurring hit set is supplied by
finiteness.
-/
theorem eventAutomatonCorrectFrom_of_all_maximal_recurring_hitSet_exact
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hexact :
      ∀ hitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ->
          (∀ otherHitSet : Finset A.State,
            EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
              otherHitSet.card ≤ hitSet.card) ->
            (hitSet : Set A.State) = A.InfStatesFrom state.1 word) :
    eventAutomatonCorrectFrom (A := A) state word := by
  constructor
  · intro hparity
    rcases eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet
        (A := A) state word hparity with
      ⟨hitSet, hhitSeen, hhitAcc, hmax⟩
    rw [DetMullerAutomaton.AcceptsFrom]
    rwa [← hexact hitSet hhitSeen hmax]
  · intro hmuller
    rcases eventAutomaton_exists_maximal_recurring_hitSet
        (A := A) state word with
      ⟨hitSet, hhitSeen, hmax⟩
    have hhitAcc : (hitSet : Set A.State) ∈ A.accepting := by
      rw [hexact hitSet hhitSeen hmax]
      exact hmuller
    exact eventAutomaton_acceptsFrom_of_exists_maximal_accepting_recurring_hitSet
      (A := A) state word ⟨hitSet, hhitSeen, hhitAcc, hmax⟩

/--
State-wise LAR correctness follows from the remaining semantic LAR recurrence
claim that the true Muller infinity set recurs as a generated hit set.
-/
theorem eventAutomatonCorrectFrom_of_infStateFinset_recurring
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hinfSeen :
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word
        (A.infStateFinsetFrom state.1 word)) :
    eventAutomatonCorrectFrom (A := A) state word := by
  exact eventAutomatonCorrectFrom_of_all_maximal_recurring_hitSet_exact
    (A := A) state word
    (fun hitSet hhitSeen hmax =>
      maximal_recurring_hitSet_exact_of_inf_recurring
        (A := A) state word hitSet hhitSeen hmax hinfSeen)

/-- The semantic Muller infinity set recurs as a generated LAR hit set. -/
theorem eventAutomaton_infStateFinset_recurring
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    EventHitSetSeenInfinitelyOftenFrom (A := A) state word
      (A.infStateFinsetFrom state.1 word) := by
  exact infStateFinset_recurring_of_frequently_generated_superset
    (A := A) state word
    (eventAutomaton_frequently_generated_hitSet_superset_infStateFinsetFrom
      (A := A) state word)

/-- State-wise correctness of the concrete LAR Muller-to-DPA construction. -/
theorem eventAutomaton_correctFrom
    (state : EventState A)
    (word : OmegaWord Alphabet) :
    eventAutomatonCorrectFrom (A := A) state word := by
  exact eventAutomatonCorrectFrom_of_infStateFinset_recurring
    (A := A) state word
    (eventAutomaton_infStateFinset_recurring (A := A) state word)

/-- Initial-language correctness of the concrete LAR Muller-to-DPA construction. -/
theorem eventAutomaton_correct :
    eventAutomatonCorrect (A := A) :=
  eventAutomaton_correct_of_initial_correctFrom
    (A := A) (fun word => eventAutomaton_correctFrom (A := A)
      (eventAutomaton (A := A)).initial word)

/-- The unconditional deterministic Muller-to-DPA compilation supplied by LAR. -/
noncomputable def eventAutomaton_toDPACompilation :
    A.ToDPACompilation :=
  eventAutomaton_toDPACompilation_of_correct
    (A := A) (eventAutomaton_correct (A := A))

/--
If no accepting recurring hit set exists, the concrete LAR parity run rejects.
-/
theorem eventAutomaton_not_acceptsFrom_of_no_accepting_recurring_hitSet
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hno :
      ∀ hitSet : Finset A.State,
        EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ->
          (hitSet : Set A.State) ∉ A.accepting) :
    ¬ (eventAutomaton (A := A)).AcceptsFrom state word := by
  intro hacc
  rcases eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet
      (A := A) state word hacc with
    ⟨hitSet, hhitSeen, hhitAcc, _hmax⟩
  exact hno hitSet hhitSeen hhitAcc

/--
The maximal accepting recurring hit set extracted from an accepting LAR run
contains a source Muller state that occurs infinitely often.
-/
theorem eventAutomaton_acceptsFrom_exists_maximal_accepting_recurring_hitSet_with_inf_member
    (state : EventState A)
    (word : OmegaWord Alphabet)
    (hacc : (eventAutomaton (A := A)).AcceptsFrom state word) :
    ∃ hitSet : Finset A.State,
      EventHitSetSeenInfinitelyOftenFrom (A := A) state word hitSet ∧
        (hitSet : Set A.State) ∈ A.accepting ∧
          (∃ q : A.State,
            A.StateSeenInfinitelyOftenFrom state.1 word q ∧ q ∈ hitSet) ∧
            ∀ otherHitSet : Finset A.State,
              EventHitSetSeenInfinitelyOftenFrom (A := A) state word otherHitSet ->
                otherHitSet.card ≤ hitSet.card := by
  rcases eventAutomaton_acceptsFrom_exists_minimal_accepting_eventState_with_inf_current
      (A := A) state word hacc with
    ⟨eventState, hstateSeen, hhitAccepting, hcurrentInf, hcurrentMem, hminimal⟩
  refine
    ⟨eventState.2.2, ⟨eventState, hstateSeen, rfl⟩, hhitAccepting,
      ⟨eventState.1, hcurrentInf, hcurrentMem⟩, ?_⟩
  intro otherHitSet hotherHitSet
  rcases hotherHitSet with ⟨other, hotherSeen, hotherEq⟩
  rw [← hotherEq]
  exact eventPriority_accepting_le_imp_card_le
    (A := A) eventState other hhitAccepting (hminimal other hotherSeen)

end LAR

end DetMullerAutomaton

end DistributedSynthesis
