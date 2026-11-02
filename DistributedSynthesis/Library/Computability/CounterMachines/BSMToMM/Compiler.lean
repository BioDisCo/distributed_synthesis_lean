/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Copyright Dominique Larchey-Wendling (LORIA -- CNRS).
Lean adaptation of the BSM-to-MM simulation in MM/mm_comp.v, revision
11c41e0637f0c5219ad1c4c92d11609b7e072c31. See ../README.md.
This port specializes source base to one and uses fixed-width blocks. It does
not append the upstream zeroifying postlude: ordinary halting is the target.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSMToMM.Encoding
import DistributedSynthesis.Library.Computability.CounterMachines.MM.StackMacros

namespace DistributedSynthesis.CounterMachine.BSMToMM
variable {n : Nat} (P : BSM.Program n)

def address (pc : Nat) : Nat := if 0 < pc ∧ pc ≤ P.length then 2+16*(pc-1) else 0

theorem valid_of_lookup {pc : Nat} {ρ : BSM.Instr n} (h : BSM.lookup P 1 pc = some ρ) :
    0 < pc ∧ pc ≤ P.length := by
  have hn : BSM.lookup P 1 pc ≠ none := by simp [h]
  have hb : ¬ (pc < 1 ∨ 1+P.length ≤ pc) := fun hbad => hn ((BSM.lookup_eq_none P 1 pc).mpr hbad)
  omega

theorem address_of_lookup {pc : Nat} {ρ : BSM.Instr n} (h : BSM.lookup P 1 pc = some ρ) :
    address P pc = 2+16*(pc-1) := by simp [address,valid_of_lookup P h]

theorem address_of_none {pc : Nat} (h : BSM.lookup P 1 pc = none) : address P pc = 0 := by
  have hn := (BSM.lookup_eq_none P 1 pc).mp h
  simp only [address]
  split_ifs <;> omega

def block (i pc : Nat) (ρ : BSM.Instr n) : MM.Program (2+n) :=
  match ρ.2 with
  | .inl false => MM.StackMacros.pushZero (frame ρ.1) i ++ [MM.dec tmp₁ (address P (pc+1))]
  | .inl true => MM.StackMacros.pushOne (frame ρ.1) i ++ [MM.dec tmp₁ (address P (pc+1))]
  | .inr (jf,je) => MM.StackMacros.pop (frame ρ.1) i (address P jf) (address P (pc+1)) (address P je)

theorem block_length (i pc : Nat) (ρ : BSM.Instr n) : (block P i pc ρ).length ≤ 16 := by
  rcases ρ with ⟨k,b | ⟨jf,je⟩⟩
  · cases b <;> simp [block,MM.StackMacros.pushZero,MM.StackMacros.pushOne,MM.Arithmetic.transfer,MM.Arithmetic.double]
  · simp [block,MM.StackMacros.pop,MM.Arithmetic.transfer,MM.Arithmetic.divide]

def codeAt (t : Nat) : MM.Instr (2+n) :=
  if t = 0 then MM.dec tmp₁ (address P 1) else
    match P[(t-1)/16]? with
    | none => MM.inc tmp₁
    | some ρ => (block P (2+16*((t-1)/16)) ((t-1)/16+1) ρ)[(t-1)%16]?.getD (MM.inc tmp₁)

def compile : MM.Program (2+n) := List.ofFn (fun t : Fin (1+16*P.length) => codeAt P t.val)

theorem lookup_compile (t : Nat) (ht : t < 1+16*P.length) :
    MM.lookup (compile P) 1 (1+t) = some (codeAt P t) := by
  simp [MM.lookup,compile,ht]

theorem block_placed (q : Fin P.length) :
    MM.Placed (compile P) 1 (2+16*q.val) (block P (2+16*q.val) (q.val+1) P[q.val]) := by
  intro j hj
  have hj16 : j < 16 := lt_of_lt_of_le hj (block_length P _ _ _)
  have ht : 1+16*q.val+j < 1+16*P.length := by omega
  have ha : 2+16*q.val+j = 1+(1+16*q.val+j) := by omega
  rw [ha,lookup_compile P _ ht]
  have hd : (1+16*q.val+j-1)/16 = q.val := by omega
  have hr : (1+16*q.val+j-1)%16 = j := by omega
  simp [codeAt,show 1+16*q.val+j ≠ 0 by omega,hd,hr,q.isLt,hj]

theorem placed_of_lookup {pc : Nat} {ρ : BSM.Instr n} (h : BSM.lookup P 1 pc = some ρ) :
    MM.Placed (compile P) 1 (address P pc) (block P (address P pc) pc ρ) := by
  have hv := valid_of_lookup P h
  let q : Fin P.length := ⟨pc-1,by omega⟩
  have hq : q.val+1 = pc := by dsimp [q]; omega
  have he : P[q.val] = ρ := by
    simpa [BSM.lookup,show 1 ≤ pc by omega,q,show pc-1 < P.length by omega] using h
  have hp := block_placed P q
  rw [he,hq] at hp
  simpa [address_of_lookup P h,q] using hp

def cfg (x : BSM.Cfg n) : MM.Cfg (2+n) := (address P x.1,state x.2)

theorem push_jump (i : Nat) (s : BSM.Stacks n) (j : Nat)
    (h : MM.lookup (compile P) 1 i = some (MM.dec tmp₁ j)) :
    MM.Reaches₁ (compile P) 1 (i,state s) (j,state s) := by
  apply MM.runSteps_reaches₁ _ _ 1 _ _ (by decide)
  simp [MM.runSteps,MM.step,MM.next,MM.dec,h]

theorem instruction_progress (pc : Nat) (s : BSM.Stacks n) (ρ : BSM.Instr n)
    (h : BSM.lookup P 1 pc = some ρ) :
    MM.Reaches₁ (compile P) 1 (cfg P (pc,s)) (cfg P (BSM.next ρ (pc,s))) := by
  have hp := placed_of_lookup P h
  rcases ρ with ⟨k,b | ⟨jf,je⟩⟩
  · cases b with
    | false =>
      have hp' : MM.Placed (compile P) 1 (address P pc)
          (MM.StackMacros.pushZero (frame k) (address P pc) ++ [MM.dec tmp₁ (address P (pc+1))]) := hp
      have ht := MM.StackMacros.pushZero_correct (frame k) _ _ _ hp'.left (state s) (MM.StackEncoding.encode (s k))
      rw [frame_start] at ht
      have he := frame_finish s k (false :: s k)
      simp only [MM.StackEncoding.encode_false] at he
      rw [he] at ht
      have hj : MM.lookup (compile P) 1 (address P pc+7) = some (MM.dec tmp₁ (address P (pc+1))) := by
        simpa [MM.StackMacros.pushZero,MM.Arithmetic.transfer,MM.Arithmetic.double] using hp'.right 0 (by simp)
      simpa [cfg,BSM.next] using ht.trans (push_jump P _ _ _ hj)
    | true =>
      have hp' : MM.Placed (compile P) 1 (address P pc)
          (MM.StackMacros.pushOne (frame k) (address P pc) ++ [MM.dec tmp₁ (address P (pc+1))]) := hp
      have ht := MM.StackMacros.pushOne_correct (frame k) _ _ _ hp'.left (state s) (MM.StackEncoding.encode (s k))
      rw [frame_start] at ht
      have he := frame_finish s k (true :: s k)
      simp only [MM.StackEncoding.encode_true] at he
      rw [he] at ht
      have hj : MM.lookup (compile P) 1 (address P pc+8) = some (MM.dec tmp₁ (address P (pc+1))) := by
        simpa [MM.StackMacros.pushOne,MM.StackMacros.pushZero,MM.Arithmetic.transfer,MM.Arithmetic.double] using hp'.right 0 (by simp)
      simpa [cfg,BSM.next] using ht.trans (push_jump P _ _ _ hj)
  · change MM.Placed _ _ _ (MM.StackMacros.pop (frame k) (address P pc)
      (address P jf) (address P (pc+1)) (address P je)) at hp
    cases hs : s k with
    | nil =>
      have ht := MM.StackMacros.pop_empty (frame k) _ _ _ _ _ _ hp (state s)
      have he : (frame k).regs (state s) 1 0 0 = state s := by simpa [hs] using frame_start s k
      rw [he] at ht
      simpa [cfg,BSM.next,hs] using ht
    | cons b l =>
      cases b with
      | false =>
        have ht := MM.StackMacros.pop_false (frame k) _ _ _ _ _ _ hp (state s)
          (MM.StackEncoding.encode l) (MM.StackEncoding.positive l)
        have he : (frame k).regs (state s) (2*MM.StackEncoding.encode l) 0 0 = state s := by
          simpa [hs] using frame_start s k
        rw [he,frame_finish] at ht
        simpa [cfg,BSM.next,hs] using ht
      | true =>
        have ht := MM.StackMacros.pop_true (frame k) _ _ _ _ _ _ hp (state s)
          (MM.StackEncoding.encode l) (MM.StackEncoding.positive l)
        have he : (frame k).regs (state s) (2*MM.StackEncoding.encode l+1) 0 0 = state s := by
          simpa [hs] using frame_start s k
        rw [he,frame_finish] at ht
        simpa [cfg,BSM.next,hs] using ht

theorem respects : StateTransition.Respects (BSM.step P 1) (MM.step (compile P) 1)
    (fun x y => cfg P x = y) := by
  apply StateTransition.fun_respects.mpr
  rintro ⟨pc,s⟩
  cases h : BSM.lookup P 1 pc with
  | none => simp [BSM.step,h,StateTransition.FRespects,cfg,address_of_none P h,MM.step,MM.lookup]
  | some ρ =>
    simpa [BSM.step,h,StateTransition.FRespects] using instruction_progress P pc s ρ h

theorem halts_iff (x : BSM.Cfg n) :
    MM.Terminates (compile P) 1 (cfg P x) ↔ BSM.Terminates P 1 x :=
  StateTransition.tr_eval_dom (respects P) rfl

theorem compile_correct (s : BSM.Stacks n) :
    MM.Halts (compile P,state s) ↔ BSM.Halts (1,P,s) := by
  have hh : MM.lookup (compile P) 1 1 = some (MM.dec tmp₁ (address P 1)) := by
    simpa [codeAt] using lookup_compile P 0 (by omega)
  have hr := push_jump P 1 s (address P 1) hh
  have he := StateTransition.reaches_eval hr.to_reflTransGen
  change (StateTransition.eval (MM.step (compile P) 1) (1,state s)).Dom ↔ _
  rw [he]
  exact halts_iff P (1,s)

end DistributedSynthesis.CounterMachine.BSMToMM
