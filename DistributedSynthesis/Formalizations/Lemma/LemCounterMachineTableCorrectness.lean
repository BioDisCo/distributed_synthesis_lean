/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineFiniteTables

/-! # The finite-table predicates coincide with the checked LTL reduction -/
namespace DistributedSynthesis.CounterMachine.Compiler
open MM2 ResidueLTL
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def eraseLabel {Q : Type*} (l : Label Q) : Label Unit :=
  ⟨(),l.zero,l.carry,l.right⟩
def eraseOutput {Q : Type*} (o : Output Q) : Payload := ⟨eraseLabel o.base,o.residue⟩
def raw {n : Nat} (r : Letter (Fin (n+1))) : RawLetter :=
  ((r.graph,eraseOutput r.outputOne,eraseOutput r.outputTwo),r.outputOne.base.control.val,r.outputTwo.base.control.val)
theorem orientation_raw {n : Nat} (r : Letter (Fin (n+1))) : orientation (raw r).1 = oneLeft r := rfl
theorem leftControl_raw {n : Nat} (r : Letter (Fin (n+1))) :
    leftControl (raw r) = (leftLabel r).control.val := by
  unfold leftControl
  rw [orientation_raw]
  cases ht : oneLeft r <;> simp [leftLabel,ht,raw]
theorem rightControl_raw {n : Nat} (r : Letter (Fin (n+1))) :
    rightControl (raw r) = (rightLabel r).control.val := by
  unfold rightControl
  rw [orientation_raw]
  cases ht : oneLeft r <;> simp [rightLabel,ht,raw]
theorem leftLabel_unit {n : Nat} (r : Letter (Fin (n+1))) :
    leftLabel (unitLetter (raw r).1) = eraseLabel (leftLabel r) := by
  change (if oneLeft r then eraseLabel r.outputOne.base else eraseLabel r.outputTwo.base) = _
  cases ht : oneLeft r <;> simp [leftLabel,ht]
theorem rightLabel_unit {n : Nat} (r : Letter (Fin (n+1))) :
    rightLabel (unitLetter (raw r).1) = eraseLabel (rightLabel r) := by
  change (if oneLeft r then eraseLabel r.outputTwo.base else eraseLabel r.outputOne.base) = _
  cases ht : oneLeft r <;> simp [rightLabel,ht]
theorem leftPayload_zero {n : Nat} (r : Letter (Fin (n+1))) :
    (leftPayload (raw r).1).base.zero = (leftLabel r).zero := by
  unfold leftPayload
  rw [orientation_raw]
  cases ht : oneLeft r <;> simp [leftLabel,ht,raw,eraseOutput,eraseLabel]
theorem clamp_eq_address (P : Program) (i : Nat) : clamp P i = (address P i).val := by
  by_cases h : i ≤ P.length <;> simp [clamp,address,h]

theorem nextControl_correct (P : Program) (r : Letter (Fin (P.length+1))) :
    nextControl P (leftControl (raw r)) (raw r).1 =
      ((compile P).next (leftLabel r).control (leftLabel r).zero).val := by
  rw [leftControl_raw]
  unfold nextControl
  cases h : lookup P (leftLabel r).control.val with
  | none => simp [Machine.next,compile,h]
  | some ρ =>
    cases hz0 : (leftLabel r).zero 0 <;> cases hz1 : (leftLabel r).zero 1 <;> cases ρ <;>
      simp [Machine.next,compile,h,instruction,positive,kind,Instr.equivCode,leftPayload_zero,
        clamp_eq_address,hz0,hz1]

theorem initialTest_correct (P : Program) (r : Letter (Fin (P.length+1))) :
    initialTest P (raw r) = true ↔ initialCheck (compile P) r := by
  simp only [initialTest,Bool.and_eq_true,decide_eq_true_eq,leftControl_raw,initialStatic,
    initialCheck,leftLabel_unit,eraseLabel,unitMachine,compile,clamp_eq_address]
  change ((leftLabel r).control.val = (address P 1).val ∧
    (residues r = ScalingSafety.ResidueLTL.update (0,1) r.graph ∧ True ∧
      ∀ k, (leftLabel r).zero k = true)) ↔ _
  rw [Fin.val_inj]
  tauto

theorem localTest_correct (P : Program) (r : Letter (Fin (P.length+1))) :
    localTest P (raw r) = true ↔ localCheck (compile P) r := by
  simp only [localTest,Bool.and_eq_true,decide_eq_true_eq,leftControl_raw,rightControl_raw,
    localStatic,localCheck,leftLabel_unit,rightLabel_unit,eraseLabel,Fin.val_inj]
  cases h : lookup P (leftLabel r).control.val with
  | none => simp [unitMachine,compile,h]
  | some ρ =>
    cases ρ <;> simp [unitMachine,compile,h,kind,Instr.equivCode,Machine.op,instruction]

theorem pairTest_correct (P : Program) (a b : Letter (Fin (P.length+1))) :
    pairTest P (raw a,raw b) = true ↔ pairCheck (compile P) a b := by
  simp only [pairTest,Prod.fst,Prod.snd]
  rw [nextControl_correct]
  simp only [Bool.and_eq_true,decide_eq_true_eq,leftControl_raw,
    pairStatic,pairCheck,leftLabel_unit,eraseLabel,Fin.val_inj]
  change ((leftLabel b).control = (compile P).next (leftLabel a).control (leftLabel a).zero ∧
    (residues b = ScalingSafety.ResidueLTL.update (residues a) b.graph ∧ True ∧
      ∀ k, ((leftLabel b).right k).weight =
        ((leftLabel a).right k).child (ScalingSafety.digit (oneLeft a) b.graph))) ↔ _
  tauto

theorem raw_mem {n : Nat} (r : Letter (Fin (n+1))) : raw r ∈ letters n := by
  rw [mem_letters]
  exact ⟨by have := r.outputOne.base.control.isLt; exact Nat.le_of_lt_succ this,
    by have := r.outputTwo.base.control.isLt; exact Nat.le_of_lt_succ this⟩

end DistributedSynthesis.CounterMachine.Compiler
