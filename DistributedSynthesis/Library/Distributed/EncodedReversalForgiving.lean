/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedRoundObjectives
import DistributedSynthesis.Library.Automata.EncodedParityOperations

/-! # Numeric reversal-forgiving objective

Code zero is the accepting sink. Code `1 + last + 4*q` stores objective
state `q` and last graph (`0`: none, `1`: left, `2`: right, `3`: both).
The companion accepts a word immediately after a direct reversal.
-/
namespace DistributedSynthesis.EncodedReversalForgiving
open EncodedRoundObjectives EncodedNoDirect
abbrev Move := Data × Nat × LetterCode

def killed (last graph : Nat) : Prop := (last = 1 ∧ graph = 1) ∨ (last = 2 ∧ graph = 0)
instance (last graph : Nat) : Decidable (killed last graph) := by unfold killed; infer_instance
def next (x : Move) : Nat :=
  if x.2.1 = 0 ∨ killed ((x.2.1-1)%4) x.2.2.2.2.1.val then 0
  else 1 + (x.2.2.2.2.1.val+1) + 4*objectiveStep x.1 ((x.2.1-1)/4) x.2.2
def priority (d : Data) (q : Nat) : Nat :=
  if q = 0 then 0 else objectivePriority d ((q-1)/4)
def initial (d : Data) := 1 + 4*(EncodedParityTables.initial d.2 % stateCount d)
def row (d : Data) (a : LetterCode) :=
  (List.range (4*stateCount d+1)).map (fun q => next (d,q,a))
def tables (d : Data) : EncodedParityTables.Data :=
  (4*stateCount d,initial d,(List.range (4*stateCount d+1)).map (priority d),
    (letters d.1).map (row d))
def compile (d : Data) : Data := (d.1,tables d)

theorem killed_primrec : PrimrecRel killed :=
  ((Primrec.eq.comp Primrec.fst (Primrec.const 1)).and
    (Primrec.eq.comp Primrec.snd (Primrec.const 1))).or
  ((Primrec.eq.comp Primrec.fst (Primrec.const 2)).and
    (Primrec.eq.comp Primrec.snd (Primrec.const 0)))
theorem next_primrec : Primrec next := by
  have hq : Primrec (fun x : Move => x.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun x : Move => x.2.2) := Primrec.snd.comp Primrec.snd
  have hg : Primrec (fun x : Move => x.2.2.2.2.1.val) :=
    Primrec.fin_val.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha)))
  have ht := Primrec.nat_sub.comp hq (Primrec.const 1)
  exact Primrec.ite ((Primrec.eq.comp hq (Primrec.const 0)).or
    (killed_primrec.comp (Primrec.nat_mod.comp ht (Primrec.const 4)) hg)) (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.const 1) (Primrec.succ.comp hg))
      (Primrec.nat_mul.comp (Primrec.const 4)
        (objectiveStep_comp Primrec.fst (Primrec.nat_div.comp ht (Primrec.const 4)) ha)))
theorem priority_primrec : Primrec₂ priority :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (objectivePriority_primrec.comp Primrec.fst
      (Primrec.nat_div.comp (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)) (Primrec.const 4)))
theorem initial_primrec : Primrec initial :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 4)
    (Primrec.nat_mod.comp (EncodedParityTables.initial_primrec.comp Primrec.snd) stateCount_primrec))
theorem row_primrec : Primrec₂ row :=
  Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4) (stateCount_primrec.comp Primrec.fst)) (Primrec.const 1)))
    (next_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))).to₂
theorem tables_primrec : Primrec tables :=
  (Primrec.nat_mul.comp (Primrec.const 4) stateCount_primrec).pair
    (initial_primrec.pair
      ((Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 4) stateCount_primrec) (Primrec.const 1))) priority_primrec).pair
      (Primrec.list_map (letters_primrec.comp Primrec.fst) row_primrec)))
theorem compile_primrec : Primrec compile := Primrec.fst.pair tables_primrec

theorem next_lt (d : Data) (q : Nat) (a : LetterCode) : next (d,q,a) < 4*stateCount d+1 := by
  unfold next
  dsimp only
  split_ifs
  · omega
  · have hq : objectiveStep d ((q-1)/4) a < stateCount d := Nat.mod_lt _ (Nat.succ_pos _)
    have hg := a.2.2.1.isLt
    omega

theorem priority_getD (d : Data) (q : Fin (4*stateCount d+1)) :
    EncodedParityTables.priority (tables d) q.val = priority d q.val :=
  EncodedParityOperations.lookup_range _ q

theorem next_correct (d : Data) (q : Fin (4*stateCount d+1)) (a : Letter d) :
    objectiveStep (compile d) q.val (letterCode a) = next (d,q.val,letterCode a) := by
  have hm : letterCode a ∈ letters d.1 := (mem_letters_iff d.1 _).mpr ⟨a,rfl⟩
  have hi := List.idxOf_lt_length_of_mem hm
  have hr : ((letters d.1).map (row d)).getD ((letters d.1).idxOf (letterCode a)) [] = row d (letterCode a) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi)]
    simp only [List.getElem_map,List.getElem_idxOf]
  change (((letters d.1).map (row d)).getD ((letters d.1).idxOf (letterCode a)) []).getD q.val 0 %
    (4*stateCount d+1) = _
  rw [hr]
  unfold row
  rw [EncodedParityOperations.lookup_range (fun k => next (d,k,letterCode a)) q]
  exact Nat.mod_eq_of_lt (next_lt d q.val (letterCode a))
end DistributedSynthesis.EncodedReversalForgiving
