/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedParityTables
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteSubsets

/-! Uniform numeric latest-appearance-record compilation. The correctness
proof reuses the library's Muller-to-parity theorem. Acceptance families are
explicit lists of canonical finite-subset codes. -/
namespace Characterisation.EncodedMuller
open DistributedSynthesis

/-- Maximum state index, initial index, letter-major transition rows, and
accepting canonical subset codes. -/
abbrev Data := Nat × Nat × List (List Nat) × List (List Nat)
abbrev State := Nat × List Nat × List Nat
local instance : BEq State := instBEqOfDecidableEq

def size (d : Data) := d.1+1
def first (d : Data) := d.2.1
def rows (d : Data) := d.2.2.1
def accepting (d : Data) := d.2.2.2
def next (d : Data) (q a : Nat) := ((rows d).getD a []).getD q 0 % size d

def rawStates (d : Data) : List State := (List.range (size d)).product
  ((FiniteSearch.words (List.range (size d)) (size d)).product (FiniteSubsets.codes (size d)))
@[irreducible] def states (d : Data) := FiniteCodeNumbering.unique (rawStates d)
def name (d : Data) (s : State) := FiniteCodeNumbering.name (rawStates d) s

def step (d : Data) (s : State) (a : Nat) : State :=
  let q := next d s.1 a
  (q,q :: s.2.1.filter (fun r => decide (r ≠ q)),
    FiniteSubsets.normalize (size d) (s.2.1.take (s.2.1.idxOf q+1)))
def priority (d : Data) (s : State) :=
  if s.2.2 ∈ accepting d then 2*(size d-s.2.2.length) else 2*(size d-s.2.2.length)+1
def initial (d : Data) : State := (first d % size d,List.range (size d),[])
def transitions (d : Data) := (List.range (rows d).length).map
  (fun a => (states d).map (fun s => name d (step d s a)))
def compile (d : Data) : EncodedParityTables.Data :=
  ((states d).length-1,name d (initial d),(states d).map (priority d),transitions d)

theorem size_primrec : Primrec size := Primrec.succ.comp Primrec.fst
theorem first_primrec : Primrec first := Primrec.fst.comp Primrec.snd
theorem rows_primrec : Primrec rows := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem accepting_primrec : Primrec accepting := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem next_comp {X : Type*} [Primcodable X] {d : X → Data} {q a : X → Nat}
    (hd : Primrec d) (hq : Primrec q) (ha : Primrec a) :
    Primrec (fun x => next (d x) (q x) (a x)) :=
  Primrec.nat_mod.comp ((Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (rows_primrec.comp hd) ha) hq) (size_primrec.comp hd)
theorem rawStates_primrec : Primrec rawStates := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp size_primrec) (FiniteSearch.product_primrec.comp
    (FiniteSearch.words_primrec.comp (Primrec.list_range.comp size_primrec) size_primrec)
    (FiniteSubsets.codes_primrec.comp size_primrec))
theorem states_primrec : Primrec states := by
  unfold states
  exact FiniteCodeNumbering.unique_primrec.comp rawStates_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp
  (rawStates_primrec.comp Primrec.fst) Primrec.snd

theorem step_comp {X : Type*} [Primcodable X] {d : X → Data} {s : X → State} {a : X → Nat}
    (hd : Primrec d) (hs : Primrec s) (ha : Primrec a) :
    Primrec (fun x => step (d x) (s x) (a x)) := by
  have hq := next_comp hd (Primrec.fst.comp hs) ha
  have order := Primrec.fst.comp (Primrec.snd.comp hs)
  have filter : Primrec (fun x => (s x).2.1.filter (fun r => decide (r ≠ next (d x) (s x).1 (a x)))) :=
    (Primrec.eq.not.listFilter.comp order hq)
  exact hq.pair ((Primrec.list_cons.comp hq filter).pair
    (FiniteSubsets.normalize_primrec.comp (size_primrec.comp hd)
      (Primrec.list_take.comp (Primrec.succ.comp (Primrec.list_idxOf.comp hq order)) order)))
theorem priority_comp {X : Type*} [Primcodable X] {d : X → Data} {s : X → State}
    (hd : Primrec d) (hs : Primrec s) : Primrec (fun x => priority (d x) (s x)) := by
  have member : PrimrecRel (fun xs (ys : List (List Nat)) => xs ∈ ys) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap
  have hlevel := Primrec.nat_mul.comp (Primrec.const 2) (Primrec.nat_sub.comp (size_primrec.comp hd)
    (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp hs))))
  exact Primrec.ite (member.comp (Primrec.snd.comp (Primrec.snd.comp hs)) (accepting_primrec.comp hd))
    hlevel (Primrec.succ.comp hlevel)
theorem initial_primrec : Primrec initial :=
  (Primrec.nat_mod.comp first_primrec size_primrec).pair ((Primrec.list_range.comp size_primrec).pair (Primrec.const []))
theorem transitions_primrec : Primrec transitions := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.list_length.comp rows_primrec))
  change Primrec (fun x : Data × Nat => (states x.1).map (fun s => name x.1 (step x.1 s x.2)))
  apply Primrec.list_map (states_primrec.comp Primrec.fst)
  exact (name_primrec.comp (Primrec.fst.comp Primrec.fst)
    (step_comp (Primrec.fst.comp Primrec.fst) Primrec.snd (Primrec.snd.comp Primrec.fst))).to₂
theorem compile_primrec : Primrec compile :=
  (Primrec.nat_sub.comp (Primrec.list_length.comp states_primrec) (Primrec.const 1)).pair
    ((name_primrec.comp Primrec.id initial_primrec).pair
      ((Primrec.list_map states_primrec (priority_comp Primrec.fst Primrec.snd).to₂).pair transitions_primrec))

end Characterisation.EncodedMuller
