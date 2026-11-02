/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedSupports

/-! # Simultaneous numeric support choices

Each table entry records a source state and its chosen successor list. The
same table advances the whole frontier and the pending obligations. The
enumerator is complete for simultaneous finite supports, including an empty
frontier and transitions admitting the empty support.
-/

namespace DistributedSynthesis.EncodedSupportTables
open EncodedFiniteLTL EncodedSupports

abbrev Row := List (Code Nat)
abbrev Table := List (Nat × List Nat)

def lookup (row : Row) (q : Nat) : Code Nat := row[q]?.getD falsity

def choices (row : Row) (q : Nat) : List (Nat × List Nat) :=
  (enumerate (lookup row q)).map (fun xs => (q, xs))

def enumerateTables (row : Row) (frontier : List Nat) : List Table :=
  (frontier.map (choices row)).sections

theorem mem_choices (row : Row) (q : Nat) (entry : Nat × List Nat) :
    entry ∈ choices row q ↔ entry.1 = q ∧ entry.2 ∈ enumerate (lookup row q) := by
  rcases entry with ⟨r, xs⟩
  simp [choices, eq_comm, and_comm]

theorem mem_tables (row : Row) (frontier : List Nat) (table : Table) :
    table ∈ enumerateTables row frontier ↔
      List.Forall₂ (fun entry q => entry.1 = q ∧ entry.2 ∈ enumerate (lookup row q)) table frontier := by
  simp only [enumerateTables, List.mem_sections, List.forall₂_map_right_iff, mem_choices]

theorem table_length (row : Row) (frontier : List Nat) (table : Table)
    (h : table ∈ enumerateTables row frontier) : table.length = frontier.length :=
  ((mem_tables row frontier table).mp h).length_eq

/-- Forget list multiplicities, retaining the source tags. -/
def decoded (n : Nat) (table : Table) : List (Nat × Finset (Fin n)) :=
  table.map (fun entry => (entry.1, decodeSet n entry.2))

theorem tables_complete {n : Nat} (row : Row) (frontier : List Nat)
    (step : Nat → PosBool (Fin n))
    (hc : ∀ q ∈ frontier, EncodedPositiveBoolean.decode (lookup row q) = (step q).map Fin.val)
    (selected : List (Nat × Finset (Fin n))) :
    (∃ table ∈ enumerateTables row frontier, decoded n table = selected) ↔
      List.Forall₂ (fun entry q => entry.1 = q ∧ Valid (step q) entry.2) selected frontier := by
  induction frontier generalizing selected with
  | nil => simp [enumerateTables, decoded]
  | cons q frontier ih =>
    have htail : ∀ r ∈ frontier,
        EncodedPositiveBoolean.decode (lookup row r) = (step r).map Fin.val :=
      fun r hr => hc r (List.mem_cons_of_mem q hr)
    cases selected with
    | nil =>
      constructor
      · rintro ⟨table, ht, he⟩
        have hlen := table_length row (q :: frontier) table ht
        have hzero := congrArg List.length he
        simp [decoded] at hzero
        simp [hzero] at hlen
      · intro h
        cases h
    | cons entry selected =>
      constructor
      · rintro ⟨table, ht, he⟩
        have hrel := (mem_tables row (q :: frontier) table).mp ht
        cases hrel with
        | cons hhead hrest =>
          simp only [decoded, List.map_cons, List.cons.injEq] at he
          obtain ⟨he, htailEq⟩ := he
          refine List.Forall₂.cons ?_ ((ih htail selected).mp ⟨_, (mem_tables _ _ _).mpr hrest, htailEq⟩)
          cases he
          exact ⟨hhead.1, (enumerate_decodeSet_iff _ _ (hc q (by simp)) _).mp
            ⟨_, hhead.1 ▸ hhead.2, rfl⟩⟩
      · intro h
        cases h with
        | cons hhead hrest =>
          obtain ⟨xs, hxs, hxsEq⟩ := (enumerate_decodeSet_iff _ _ (hc q (by simp)) entry.2).mpr
            (hhead.1 ▸ hhead.2)
          obtain ⟨tail, htailMem, htailEq⟩ := (ih htail selected).mpr hrest
          refine ⟨(q, xs) :: tail, (mem_tables _ _ _).mpr
            (List.Forall₂.cons ⟨rfl, hxs⟩ ((mem_tables _ _ _).mp htailMem)), ?_⟩
          simp only [decoded, List.map_cons] at htailEq ⊢
          rw [hxsEq, htailEq]
          cases entry
          simp_all

def successors (table : Table) : List Nat := table.flatMap Prod.snd

def pendingSuccessors (table : Table) (pending : List Nat) : List Nat :=
  (table.filter (fun entry => decide (entry.1 ∈ pending))).flatMap Prod.snd

def nextPending (priorities : List Nat) (table : Table) (pending : List Nat) : List Nat :=
  (if pending = [] then successors table else pendingSuccessors table pending).filter
    (fun q => decide (priorities[q]?.getD 0 % 2 ≠ 0))

/-- Both components use the very same simultaneous support choice. -/
def advance (priorities : List Nat) (pending : List Nat) (table : Table) : List Nat × List Nat :=
  (successors table, nextPending priorities table pending)

theorem mem_successors (table : Table) (q : Nat) :
    q ∈ successors table ↔ ∃ entry ∈ table, q ∈ entry.2 := by
  simp [successors]

theorem mem_pendingSuccessors (table : Table) (pending : List Nat) (q : Nat) :
    q ∈ pendingSuccessors table pending ↔
      ∃ entry ∈ table, entry.1 ∈ pending ∧ q ∈ entry.2 := by
  simp only [pendingSuccessors, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
  aesop

theorem mem_nextPending (priorities : List Nat) (table : Table) (pending : List Nat) (q : Nat) :
    q ∈ nextPending priorities table pending ↔
      (if pending = [] then q ∈ successors table else q ∈ pendingSuccessors table pending) ∧
        priorities[q]?.getD 0 % 2 ≠ 0 := by
  unfold nextPending
  split_ifs <;> simp

section Computability

theorem lookup_primrec : Primrec₂ lookup :=
  Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst Primrec.snd) (Primrec.const falsity)

theorem choices_primrec : Primrec₂ choices :=
  Primrec.list_map (EncodedSupports.enumerate_primrec.comp lookup_primrec)
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

theorem enumerateTables_primrec : Primrec₂ enumerateTables :=
  FiniteSearch.sections_primrec.comp (Primrec.list_map Primrec.snd
    (choices_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

theorem successors_primrec : Primrec successors :=
  Primrec.list_flatMap Primrec.id (Primrec.snd.comp Primrec.snd).to₂

theorem pendingSuccessors_primrec : Primrec₂ pendingSuccessors := by
  have hm : PrimrecRel (fun (entry : Nat × List Nat) (pending : List Nat) => entry.1 ∈ pending) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).comp Primrec.snd (Primrec.fst.comp Primrec.fst)
  exact successors_primrec.comp hm.listFilter

theorem nextPending_primrec :
    Primrec (fun x : List Nat × Table × List Nat => nextPending x.1 x.2.1 x.2.2) := by
  have hraw : Primrec (fun x : List Nat × Table × List Nat =>
      if x.2.2 = [] then successors x.2.1 else pendingSuccessors x.2.1 x.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const []))
      (successors_primrec.comp (Primrec.fst.comp Primrec.snd))
      (pendingSuccessors_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  have hp : PrimrecRel (fun q (priorities : List Nat) => priorities[q]?.getD 0 % 2 ≠ 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.snd Primrec.fst) (Primrec.const 0))
      (Primrec.const 2)) (Primrec.const 0)).not
  exact hp.listFilter.comp hraw Primrec.fst

theorem advance_primrec :
    Primrec (fun x : List Nat × List Nat × Table => advance x.1 x.2.1 x.2.2) :=
  (successors_primrec.comp (Primrec.snd.comp Primrec.snd)).pair
    (nextPending_primrec.comp (Primrec.fst.pair
      ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd))))

end Computability
end DistributedSynthesis.EncodedSupportTables
