/-
Lean development: the paper authors listed in AUTHORS.md at the repository root.
The Mathlib credits below refer to reused upstream definitions and proofs.
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0; see ../LICENSE-APACHE-2.0.

This module builds on Mario Carneiro's TM2 semantics and finite-support API
in Mathlib.Computability.TuringMachine.StackTuringMachine (Apache-2.0).
-/
import Mathlib.Computability.TuringMachine.StackTuringMachine

/-! # Restricting a stack machine to its finite control support

The stack alphabet and local-store type are unchanged. A supported label is
replaced by its subtype in the given finite set. An arbitrary fixed supported
label makes the translation total on unsupported jumps; the support hypothesis
proves that this fallback is never taken. One-step and halting correspondence
hold for every configuration of the restricted machine, not just reachable ones.
-/
namespace DistributedSynthesis.CounterMachine.MathlibBridge.FiniteControl
open Turing

variable {K Λ σ : Type*} {Γ : K → Type*} [DecidableEq K] [DecidableEq Λ]
variable (S : Finset Λ) (q₀ : S)

def restrictLabel (q : Λ) : S := if h : q ∈ S then ⟨q,h⟩ else q₀

@[simp] theorem restrictLabel_val {q : Λ} (h : q ∈ S) :
    (restrictLabel S q₀ q).val = q := by simp [restrictLabel,h]

def restrictStmt : TM2.Stmt Γ Λ σ → TM2.Stmt Γ S σ
  | .push k f q => .push k f (restrictStmt q)
  | .peek k f q => .peek k f (restrictStmt q)
  | .pop k f q => .pop k f (restrictStmt q)
  | .load f q => .load f (restrictStmt q)
  | .branch f q r => .branch f (restrictStmt q) (restrictStmt r)
  | .goto f => .goto (fun v => restrictLabel S q₀ (f v))
  | .halt => .halt

def liftCfg (x : TM2.Cfg Γ S σ) : TM2.Cfg Γ Λ σ :=
  ⟨x.l.map Subtype.val,x.var,x.stk⟩

theorem lift_stepAux (q : TM2.Stmt Γ Λ σ) (hq : TM2.SupportsStmt S q)
    (v : σ) (stk : ∀ k, List (Γ k)) :
    liftCfg S (TM2.stepAux (restrictStmt S q₀ q) v stk) = TM2.stepAux q v stk := by
  induction q generalizing v stk with
  | push k f q ih => exact ih hq _ _
  | peek k f q ih => exact ih hq _ _
  | pop k f q ih => exact ih hq _ _
  | load f q ih => exact ih hq _ _
  | branch f q r ihq ihr =>
    cases hv : f v <;> simp [restrictStmt,TM2.stepAux,hv,ihq hq.1,ihr hq.2]
  | goto f => simp [restrictStmt,TM2.stepAux,liftCfg,restrictLabel_val S q₀ (hq v)]
  | halt => rfl

def machine (M : Λ → TM2.Stmt Γ Λ σ) : S → TM2.Stmt Γ S σ :=
  fun q => restrictStmt S q₀ (M q.val)

theorem lift_step (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) (x : TM2.Cfg Γ S σ) :
    (TM2.step (machine S q₀ M) x).map (liftCfg S) = TM2.step M (liftCfg S x) := by
  rcases x with ⟨q,v,stk⟩
  cases q with
  | none => rfl
  | some q =>
    simp only [TM2.step,Option.map_some,liftCfg,machine]
    exact congrArg some (lift_stepAux S q₀ (M q.val) (hM _ q.property) v stk)

theorem respects (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) :
    StateTransition.Respects (TM2.step (machine S q₀ M)) (TM2.step M)
      (fun x y => liftCfg S x = y) := by
  apply StateTransition.fun_respects.mpr
  intro x
  have he := lift_step S q₀ M hM x
  cases h : TM2.step (machine S q₀ M) x with
  | none => simpa [h,StateTransition.FRespects] using he.symm
  | some y =>
    change StateTransition.Reaches₁ (TM2.step M) (liftCfg S x) (liftCfg S y)
    apply Relation.TransGen.single
    simpa [h] using he.symm

theorem eval_eq (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) (x : TM2.Cfg Γ S σ) :
    StateTransition.eval (TM2.step M) (liftCfg S x) =
      (StateTransition.eval (TM2.step (machine S q₀ M)) x).map (liftCfg S) :=
  StateTransition.tr_eval' _ _ _ (respects S q₀ M hM) x

theorem halts_iff (M : Λ → TM2.Stmt Γ Λ σ)
    (hM : ∀ q ∈ S, TM2.SupportsStmt S (M q)) (x : TM2.Cfg Γ S σ) :
    (StateTransition.eval (TM2.step (machine S q₀ M)) x).Dom ↔
      (StateTransition.eval (TM2.step M) (liftCfg S x)).Dom :=
  (StateTransition.tr_eval_dom (respects S q₀ M hM) rfl).symm

end DistributedSynthesis.CounterMachine.MathlibBridge.FiniteControl
