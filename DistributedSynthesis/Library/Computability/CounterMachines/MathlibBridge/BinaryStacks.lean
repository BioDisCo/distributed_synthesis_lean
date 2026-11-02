/-
Lean development: the paper authors listed in AUTHORS.md at the repository root.
The Mathlib credits below refer to reused upstream definitions and proofs.
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0; see ../LICENSE-APACHE-2.0.

Binary-alphabet compiler for Mario Carneiro's Mathlib TM2 semantics.
This compiler is an addition of this project, not a port of Rocq's BSM.
-/
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-! # Two-bit stack encoding with exact statement simulation

Every source symbol is represented by two consecutive bits, first bit at the
top. Source push therefore pushes the second bit before the first. Source pop
removes both bits. Source peek pops the first bit, peeks at the second, and
restores the first bit; on an empty stack it restores nothing. A single optional
bit is added to the local store, and is cleared before every source continuation.

The simulation is generic in the stack index, source alphabet, control labels,
and local store. Its sole encoding hypothesis is a left inverse on symbols.
Exact statement correspondence applies to encoded stacks; malformed bit stacks
are deliberately outside this invariant. One whole source TM2 step corresponds
to one whole target TM2 step, since each executes a finite structured statement.
-/
namespace DistributedSynthesis.CounterMachine.MathlibBridge.BinaryStacks
open Turing

variable {K Γ Λ σ : Type}

structure Codec (Γ : Type*) where
  encode : Γ → Bool × Bool
  decode : Bool → Bool → Γ
  decode_encode : ∀ a, decode (encode a).1 (encode a).2 = a

namespace Codec
variable (C : Codec Γ)

def word : List Γ → List Bool
  | [] => []
  | a :: l => (C.encode a).1 :: (C.encode a).2 :: word l

@[simp] theorem word_nil : C.word [] = [] := rfl
@[simp] theorem word_cons (a : Γ) (l : List Γ) :
    C.word (a :: l) = (C.encode a).1 :: (C.encode a).2 :: C.word l := rfl

theorem word_length (l : List Γ) : (C.word l).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih,Nat.mul_add,Nat.add_assoc]

def read (a b : Option Bool) : Option Γ :=
  a.bind fun x => b.map (C.decode x)

@[simp] theorem read_none (b : Option Bool) : C.read none b = none := rfl
@[simp] theorem read_encode (a : Γ) :
    C.read (some (C.encode a).1) (some (C.encode a).2) = some a := by
  simp [read,C.decode_encode]

end Codec

variable (C : Codec Γ) [DecidableEq K]

abbrev Store (σ : Type*) := σ × Option Bool
abbrev SourceStmt := TM2.Stmt (fun _ : K => Γ) Λ σ
abbrev TargetStmt := TM2.Stmt (fun _ : K => Bool) Λ (Store σ)

def clear (q : TargetStmt (K := K) (Λ := Λ) (σ := σ)) :
    TargetStmt (K := K) (Λ := Λ) (σ := σ) :=
  .load (fun v => (v.1,none)) q

def stmt : SourceStmt (K := K) (Γ := Γ) (Λ := Λ) (σ := σ) →
    TargetStmt (K := K) (Λ := Λ) (σ := σ)
  | .push k f q =>
    .push k (fun v => (C.encode (f v.1)).2)
      (.push k (fun v => (C.encode (f v.1)).1) (stmt q))
  | .peek k f q =>
    .pop k (fun v a => (v.1,a))
      (.peek k (fun v b => (f v.1 (C.read v.2 b),v.2))
        (.branch (fun v => v.2.isSome)
          (.push k (fun v => v.2.getD false) (clear (stmt q)))
          (clear (stmt q))))
  | .pop k f q =>
    .pop k (fun v a => (v.1,a))
      (.pop k (fun v b => (f v.1 (C.read v.2 b),none)) (stmt q))
  | .load f q => .load (fun v => (f v.1,none)) (stmt q)
  | .branch f q r => .branch (fun v => f v.1) (stmt q) (stmt r)
  | .goto f => .goto (fun v => f v.1)
  | .halt => .halt

def stacks (s : K → List Γ) : K → List Bool := fun k => C.word (s k)

omit [DecidableEq K] in
@[simp] theorem stacks_apply (s : K → List Γ) (k : K) : stacks C s k = C.word (s k) := rfl

theorem stacks_update (s : K → List Γ) (k : K) (l : List Γ) :
    stacks C (Function.update s k l) = Function.update (stacks C s) k (C.word l) := by
  funext j
  by_cases h : j = k
  · subst j; simp [stacks]
  · simp [stacks,h]

def cfg (x : TM2.Cfg (fun _ : K => Γ) Λ σ) : TM2.Cfg (fun _ : K => Bool) Λ (Store σ) :=
  ⟨x.l,(x.var,none),stacks C x.stk⟩

theorem stepAux_correct (q : SourceStmt (K := K) (Γ := Γ) (Λ := Λ) (σ := σ))
    (v : σ) (s : K → List Γ) :
    TM2.stepAux (stmt C q) (v,none) (stacks C s) = cfg C (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
    simpa [stmt,TM2.stepAux,stacks_update] using
      ih v (Function.update s k (f v :: s k))
  | peek k f q ih =>
    cases hs : s k with
    | nil =>
      have hu : Function.update (stacks C s) k [] = stacks C s :=
        Function.update_eq_self_iff.mpr (by simp [hs])
      simpa [stmt,TM2.stepAux,clear,hs,hu] using ih (f v none) s
    | cons a l =>
      have hu : Function.update (stacks C s) k
          ((C.encode a).1 :: (C.encode a).2 :: C.word l) = stacks C s :=
        Function.update_eq_self_iff.mpr (by simp [hs])
      simpa [stmt,TM2.stepAux,clear,hs,hu] using
        ih (f v (some a)) s
  | pop k f q ih =>
    cases hs : s k with
    | nil =>
      simpa [stmt,TM2.stepAux,stacks_update,stacks,hs,Function.update_eq_self] using
        ih (f v none) (Function.update s k [])
    | cons a l =>
      simpa [stmt,TM2.stepAux,stacks_update,stacks,hs,C.decode_encode] using
        ih (f v (some a)) (Function.update s k l)
  | load f q ih => exact ih (f v) s
  | branch f q r ihq ihr =>
    cases h : f v <;> simp [stmt,TM2.stepAux,h,ihq,ihr]
  | goto f => rfl
  | halt => rfl

def machine (M : Λ → SourceStmt (K := K) (Γ := Γ) (Λ := Λ) (σ := σ)) :
    Λ → TargetStmt (K := K) (Λ := Λ) (σ := σ) :=
  fun q => stmt C (M q)

theorem step_correct (M : Λ → SourceStmt (K := K) (Γ := Γ) (σ := σ))
    (x : TM2.Cfg (fun _ : K => Γ) Λ σ) :
    TM2.step (machine C M) (cfg C x) = (TM2.step M x).map (cfg C) := by
  rcases x with ⟨q,v,s⟩
  cases q with
  | none => rfl
  | some q => exact congrArg some (stepAux_correct C (M q) v s)

theorem respects (M : Λ → SourceStmt (K := K) (Γ := Γ) (σ := σ)) :
    StateTransition.Respects (TM2.step M) (TM2.step (machine C M))
      (fun x y => cfg C x = y) := by
  apply StateTransition.fun_respects.mpr
  intro x
  have he := step_correct C M x
  cases h : TM2.step M x with
  | none => simpa [h,StateTransition.FRespects] using he
  | some y =>
    apply Relation.TransGen.single
    simpa [h] using he

theorem eval_eq (M : Λ → SourceStmt (K := K) (Γ := Γ) (σ := σ))
    (x : TM2.Cfg (fun _ : K => Γ) Λ σ) :
    StateTransition.eval (TM2.step (machine C M)) (cfg C x) =
      (StateTransition.eval (TM2.step M) x).map (cfg C) :=
  StateTransition.tr_eval' _ _ _ (respects C M) x

theorem halts_iff (M : Λ → SourceStmt (K := K) (Γ := Γ) (σ := σ))
    (x : TM2.Cfg (fun _ : K => Γ) Λ σ) :
    (StateTransition.eval (TM2.step (machine C M)) (cfg C x)).Dom ↔
      (StateTransition.eval (TM2.step M) x).Dom :=
  StateTransition.tr_eval_dom (respects C M) rfl

end DistributedSynthesis.CounterMachine.MathlibBridge.BinaryStacks
