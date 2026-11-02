/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteFunctionCodes
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Computability.FiniteSetCodes

/-! Uniform code enumeration for numbered leader interfaces and handovers.
The context stores the maximum family width, annotation count, and maximum
priority. Matrices are separate for the two processes; function entries use
the existing finite-function table order. -/
namespace Characterisation.EncodedLeaderAlphabet
open DistributedSynthesis

abbrev Context := Nat × Nat × Nat
abbrev Header := Nat × List Nat × List Nat × List Nat
abbrev Outcome := Header × List Nat × List Nat
abbrev Move := Bool × List Nat

def width (c : Context) := c.1
def labels (c : Context) := c.2.1
def maxPriority (c : Context) := c.2.2

def headerTables (c : Context) (n : Nat) : List Header :=
  ((FiniteSearch.tables 2 (n*n)).product
    ((FiniteSearch.tables 2 (n*n)).product (FiniteSearch.tables (labels c) n))).map (fun data => (n,data))
def headers (c : Context) := (List.range (width c+1)).flatMap (headerTables c)
def outcomeTables (c : Context) (header : Header) : List Outcome :=
  ((FiniteSearch.tables (width c+1) header.1).product
    (FiniteSearch.tables (maxPriority c+1) header.1)).map (fun data => (header,data))
def rawOutcomes (c : Context) := (headers c).flatMap (outcomeTables c)
@[irreducible] def outcomes (c : Context) := FiniteCodeNumbering.unique (rawOutcomes c)
def outcomeName (c : Context) (outcome : Outcome) := FiniteCodeNumbering.name (rawOutcomes c) outcome

def rawMoves (c : Context) : List Move := [false,true].product (FiniteSetCodes.codes (outcomes c).length)
@[irreducible] def moves (c : Context) := FiniteCodeNumbering.unique (rawMoves c)
def moveName (c : Context) (move : Move) := FiniteCodeNumbering.name (rawMoves c) move
def offered (move : Move) (observation : Nat) := decide (observation ∈ move.2)

/-- Exact numeric predecessor/minimum relation. The old priority is irrelevant;
its slot identifies the parent, and each target retains its own phase minimum. -/
def HasEdge (outcome : Outcome) (old next : Nat × Nat) : Prop :=
  ∃ i < outcome.1.1,
    outcome.2.1.getD i 0 = old.1 ∧ next = (i,outcome.2.2.getD i 0)
instance (outcome : Outcome) (old next : Nat × Nat) : Decidable (HasEdge outcome old next) := by
  unfold HasEdge
  infer_instance

def edge (outcome : Outcome) (old next : Nat × Nat) := decide (HasEdge outcome old next)

theorem width_primrec : Primrec width := Primrec.fst
theorem labels_primrec : Primrec labels := Primrec.fst.comp Primrec.snd
theorem maxPriority_primrec : Primrec maxPriority := Primrec.snd.comp Primrec.snd

theorem headerTables_primrec : Primrec₂ headerTables := by
  apply Primrec.list_map
    (FiniteSearch.product_primrec.comp
      (FiniteSearch.tables_primrec.comp (Primrec.const 2) (Primrec.nat_mul.comp Primrec.snd Primrec.snd))
      (FiniteSearch.product_primrec.comp
        (FiniteSearch.tables_primrec.comp (Primrec.const 2) (Primrec.nat_mul.comp Primrec.snd Primrec.snd))
        (FiniteSearch.tables_primrec.comp (labels_primrec.comp Primrec.fst) Primrec.snd)))
  exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

theorem headers_primrec : Primrec headers :=
  Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp width_primrec)) headerTables_primrec

theorem outcomeTables_primrec : Primrec₂ outcomeTables :=
  Primrec.list_map (FiniteSearch.product_primrec.comp
    (FiniteSearch.tables_primrec.comp (Primrec.succ.comp (width_primrec.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd))
    (FiniteSearch.tables_primrec.comp (Primrec.succ.comp (maxPriority_primrec.comp Primrec.fst)) (Primrec.fst.comp Primrec.snd)))
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

theorem rawOutcomes_primrec : Primrec rawOutcomes := Primrec.list_flatMap headers_primrec outcomeTables_primrec
theorem outcomes_primrec : Primrec outcomes := by
  unfold outcomes
  exact FiniteCodeNumbering.unique_primrec.comp rawOutcomes_primrec
theorem outcomeName_primrec : Primrec₂ outcomeName :=
  FiniteCodeNumbering.name_primrec.comp (rawOutcomes_primrec.comp Primrec.fst) Primrec.snd
theorem rawMoves_primrec : Primrec rawMoves := FiniteSearch.product_primrec.comp (Primrec.const [false,true])
  (FiniteSetCodes.codes_primrec.comp (Primrec.list_length.comp outcomes_primrec))

theorem moves_primrec : Primrec moves := by
  unfold moves
  exact FiniteCodeNumbering.unique_primrec.comp rawMoves_primrec
theorem moveName_primrec : Primrec₂ moveName := FiniteCodeNumbering.name_primrec.comp
  (rawMoves_primrec.comp Primrec.fst) Primrec.snd

theorem offered_primrec : Primrec₂ offered := by
  have mem : PrimrecRel (fun (xs : List Nat) i => i ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact (mem.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).decide

theorem edge_primrec : Primrec (fun x : Outcome × (Nat × Nat) × (Nat × Nat) => edge x.1 x.2.1 x.2.2) := by
  apply PrimrecPred.decide
  apply FiniteSearch.exists_lt (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  apply PrimrecPred.and
  · exact Primrec.eq.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
      (Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  · exact Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.pair ((Primrec.list_getD 0).comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd))

end Characterisation.EncodedLeaderAlphabet
