/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Finite control-graph compiler using the project's BSM control macros.
The target semantics are adapted from Dominique Larchey-Wendling's BSM.v.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSMMacros

/-! # Whole-program layout for finite binary-stack control graphs

Each node occupies seven instruction slots. A two-instruction entry block jumps
to the chosen initial node; address zero is reserved for halting. Short blocks
are padded with unreachable instructions. All placement hypotheses are proved
from the layout. Every graph step takes a positive number of BSM steps, so the
deterministic simulation reflects termination as well as preserving it.
-/
namespace DistributedSynthesis.CounterMachine.BSMGraph
open BSM

inductive Op (n m : Nat)
  | jump (q : Option (Fin m))
  | push (k : Fin n) (b : Bool) (q : Option (Fin m))
  | pop (k : Fin n) (q : Option Bool → Option (Fin m))
  | peek (k : Fin n) (q : Option Bool → Option (Fin m))

abbrev Cfg (n m : Nat) := Option (Fin m) × BSM.Stacks n

def next {n m : Nat} (op : Op n m) (s : BSM.Stacks n) : Cfg n m :=
  match op with
  | .jump q => (q,s)
  | .push k b q => (q,Function.update s k (b :: s k))
  | .pop k q => (q (s k).head?,Function.update s k (s k).tail)
  | .peek k q => (q (s k).head?,s)

def step {n m : Nat} (M : Fin m → Op n m) : Cfg n m → Option (Cfg n m)
  | (none,_) => none
  | (some q,s) => some (next (M q) s)

def address {m : Nat} : Option (Fin m) → Nat
  | none => 0
  | some q => 3 + 7*q.val

def block {n m : Nat} (scratch : Fin n) (i : Nat) : Op n m → BSM.Program n
  | .jump q => BSM.jump scratch (address q)
  | .push k b q => BSM.pushTo k b (address q)
  | .pop k q => BSM.popTo k (address (q (some true))) (address (q (some false))) (address (q none))
  | .peek k q => BSM.peek k i (address (q (some true))) (address (q (some false))) (address (q none))

theorem block_length {n m : Nat} (scratch : Fin n) (i : Nat) (op : Op n m) :
    (block scratch i op).length ≤ 7 := by
  cases op <;> simp [block,BSM.jump,BSM.pushTo,BSM.popTo,BSM.peek]

def codeAt {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (t : Nat) : BSM.Instr n :=
  if t < 2 then (BSM.jump scratch (address (some entry)))[t]?.getD (BSM.push scratch false)
  else if h : (t-2)/7 < m then
    let q : Fin m := ⟨(t-2)/7,h⟩
    (block scratch (address (some q)) (M q))[(t-2)%7]?.getD (BSM.push scratch false)
  else BSM.push scratch false

def compile {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m) : BSM.Program n :=
  List.ofFn (fun t : Fin (2+7*m) => codeAt scratch entry M t.val)

theorem lookup_compile {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (t : Nat) (ht : t < 2+7*m) :
    BSM.lookup (compile scratch entry M) 1 (1+t) = some (codeAt scratch entry M t) := by
  simp [BSM.lookup,compile,ht]

theorem block_placed {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (q : Fin m) : BSM.Placed (compile scratch entry M) 1 (address (some q))
      (block scratch (address (some q)) (M q)) := by
  intro j hj
  have hj7 : j < 7 := lt_of_lt_of_le hj (block_length scratch _ _)
  have ht : 2+7*q.val+j < 2+7*m := by omega
  have ha : address (some q)+j = 1+(2+7*q.val+j) := by simp [address]; omega
  rw [ha,lookup_compile scratch entry M _ ht]
  have hd : (2+7*q.val+j-2)/7 = q.val := by omega
  have hr : (2+7*q.val+j-2)%7 = j := by omega
  simp only [codeAt,show ¬ (2+7*q.val+j < 2) by omega,if_false,hd,hr,dif_pos q.isLt]
  simp [hj]

theorem entry_placed {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m) :
    BSM.Placed (compile scratch entry M) 1 1 (BSM.jump scratch (address (some entry))) := by
  intro j hj
  have hj2 : j < 2 := by simpa [BSM.jump] using hj
  rw [lookup_compile scratch entry M j (by omega)]
  simp [codeAt,hj2,hj]

def cfg {n m : Nat} (x : Cfg n m) : BSM.Cfg n := (address x.1,x.2)

theorem block_progress {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (q : Fin m) (s : BSM.Stacks n) :
    BSM.Reaches₁ (compile scratch entry M) 1 (cfg (some q,s)) (cfg (next (M q) s)) := by
  have hp := block_placed scratch entry M q
  cases ho : M q with
  | jump r => exact BSM.jump_progress _ _ _ _ _ _ (by simpa [ho,block] using hp)
  | push k b r =>
    exact BSM.runSteps_reaches₁ _ _ 3 _ _ (by decide)
      (BSM.pushTo_correct _ _ _ _ _ _ _ (by simpa [ho,block] using hp))
  | peek k f =>
    have h := BSM.peek_progress _ _ _ _ _ _ _ s (by simpa [ho,block] using hp)
    cases hs : s k with
    | nil => simpa [cfg,next,hs,BSM.peekTarget] using h
    | cons b l => cases b <;> simpa [cfg,next,hs,BSM.peekTarget] using h
  | pop k f =>
    have h : BSM.Placed (compile scratch entry M) 1 (address (some q))
        (BSM.popTo k (address (f (some true))) (address (f (some false))) (address (f none))) :=
      by simpa [ho,block] using hp
    cases hs : s k with
    | nil =>
      have hu : Function.update s k [] = s := Function.update_eq_self_iff.mpr hs.symm
      exact BSM.runSteps_reaches₁ _ _ 1 _ _ (by decide)
        (by simpa [cfg,next,hs,hu] using BSM.popTo_empty _ _ _ _ _ _ k s hs h)
    | cons b l =>
      cases b with
      | false =>
        exact BSM.runSteps_reaches₁ _ _ 1 _ _ (by decide)
          (by simpa [cfg,next,hs] using BSM.popTo_false _ _ _ _ _ _ k s l hs h)
      | true =>
        exact BSM.runSteps_reaches₁ _ _ 3 _ _ (by decide)
          (by simpa [cfg,next,hs] using BSM.popTo_true _ _ _ _ _ _ k s l hs h)

theorem respects {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m) :
    StateTransition.Respects (step M) (BSM.step (compile scratch entry M) 1)
      (fun x y => cfg x = y) := by
  apply StateTransition.fun_respects.mpr
  rintro ⟨q,s⟩
  cases q with
  | none => simp [step,StateTransition.FRespects,cfg,address,BSM.step,BSM.lookup]
  | some q => exact block_progress scratch entry M q s

theorem halts_iff {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (x : Cfg n m) :
    BSM.Terminates (compile scratch entry M) 1 (cfg x) ↔ (StateTransition.eval (step M) x).Dom :=
  StateTransition.tr_eval_dom (respects scratch entry M) rfl

theorem initial_halts_iff {n m : Nat} (scratch : Fin n) (entry : Fin m) (M : Fin m → Op n m)
    (s : BSM.Stacks n) :
    BSM.Halts (1,compile scratch entry M,s) ↔
      (StateTransition.eval (step M) (some entry,s)).Dom := by
  have hr := BSM.jump_progress _ _ _ _ _ s (entry_placed scratch entry M)
  have he := StateTransition.reaches_eval hr.to_reflTransGen
  change (StateTransition.eval (BSM.step (compile scratch entry M) 1) (1,s)).Dom ↔ _
  rw [he]
  exact halts_iff scratch entry M (some entry,s)

end DistributedSynthesis.CounterMachine.BSMGraph
