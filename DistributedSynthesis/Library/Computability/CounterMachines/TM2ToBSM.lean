/-
Lean adaptation and development: the paper authors listed in AUTHORS.md
at the repository root. The credits below refer to upstream formalizations,
not authorship of this Lean implementation; see the CounterMachines README.md.
-/

/-
SPDX-License-Identifier: MPL-2.0
Whole-program compiler from Mario Carneiro's Mathlib TM2 semantics to the
project's Lean adaptation of Dominique Larchey-Wendling's Rocq BSM semantics.
The control extraction and composition proofs are additions of this project.
See README.md and LICENSE-MPL-2.0 in this directory.
-/
import DistributedSynthesis.Library.Computability.CounterMachines.BSMGraph
import Mathlib.Computability.TuringMachine.StackTuringMachine
import Mathlib.Data.Fintype.EquivFin

/-! # Finite-store elimination and structured-control compilation

A control node is a supported substatement together with a local-store value.
All such nodes form a finite type. Loads and Boolean branches are resolved in
that node; only stack reads branch at runtime. Statement induction proves a
strict simulation of every TM2 step. Composing with the BSM graph layout yields
halting equivalence for the actual instruction list, with no layout hypothesis.

The enumeration is chosen for each fixed finite source machine. This module
does not assert primitive recursiveness of a uniform syntax compiler. The
undecidability application uses one fixed machine and separately certifies its
varying-input encoding.
-/
namespace DistributedSynthesis.CounterMachine.TM2ToBSM
open Turing

variable {K Λ σ : Type} [DecidableEq K] [Fintype Λ] [Fintype σ]
abbrev Stmt := TM2.Stmt (fun _ : K => Bool) Λ σ
variable (M : Λ → Stmt (K := K) (Λ := Λ) (σ := σ))

open scoped Classical in
noncomputable def statements : Finset (Stmt (K := K) (Λ := Λ) (σ := σ)) :=
  Finset.univ.biUnion (fun l => TM2.stmts₁ (M l))

omit [DecidableEq K] [Fintype σ] in
theorem root_mem (l : Λ) : M l ∈ statements M := by
  classical
  exact Finset.mem_biUnion.mpr ⟨l,Finset.mem_univ _,TM2.stmts₁_self⟩

omit [DecidableEq K] [Fintype σ] in
theorem sub_mem {q r : Stmt (K := K) (Λ := Λ) (σ := σ)}
    (hq : q ∈ statements M) (hr : r ∈ TM2.stmts₁ q) : r ∈ statements M := by
  classical
  obtain ⟨l,hl,hql⟩ := Finset.mem_biUnion.mp hq
  exact Finset.mem_biUnion.mpr ⟨l,hl,TM2.stmts₁_trans hql hr⟩

abbrev Node := (statements M) × σ
noncomputable def index (q : Stmt (K := K) (Λ := Λ) (σ := σ))
    (hq : q ∈ statements M) (v : σ) : Fin (Fintype.card (Node M)) :=
  Fintype.equivFin (Node M) (⟨q,hq⟩,v)

variable {n : Nat} (e : K ≃ Fin n)

def mapStacks (s : K → List Bool) : BSM.Stacks n := fun k => s (e.symm k)

theorem mapStacks_update (s : K → List Bool) (k : K) (l : List Bool) :
    mapStacks e (Function.update s k l) = Function.update (mapStacks e s) (e k) l := by
  funext j
  by_cases h : j = e k
  · subst j
    change Function.update s k l (e.symm (e k)) = Function.update (mapStacks e s) (e k) l (e k)
    rw [e.symm_apply_apply,Function.update_self,Function.update_self]
  · have h' : e.symm j ≠ k := by intro he; apply h; rw [← he]; simp
    simp [mapStacks,h,h']

noncomputable def opOf : (q : Stmt (K := K) (Λ := Λ) (σ := σ)) →
    q ∈ statements M → σ → BSMGraph.Op n (Fintype.card (Node M))
  | .push k f q,h,v => .push (e k) (f v) (some (index M q
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) v))
  | .peek k f q,h,v => .peek (e k) (fun a => some (index M q
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) (f v a)))
  | .pop k f q,h,v => .pop (e k) (fun a => some (index M q
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) (f v a)))
  | .load f q,h,v => .jump (some (index M q
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) (f v)))
  | .branch f q r,h,v => bif f v then .jump (some (index M q
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) v))
      else .jump (some (index M r
      (sub_mem M h (by simp [TM2.stmts₁,TM2.stmts₁_self])) v))
  | .goto f,_,v => .jump (some (index M (M (f v)) (root_mem M (f v)) v))
  | .halt,_,_ => .jump none

noncomputable def graph (i : Fin (Fintype.card (Node M))) : BSMGraph.Op n (Fintype.card (Node M)) :=
  let p := (Fintype.equivFin (Node M)).symm i
  opOf M e p.1.val p.1.property p.2

omit [DecidableEq K] in
theorem graph_index (q : Stmt (K := K) (Λ := Λ) (σ := σ)) (hq : q ∈ statements M) (v : σ) :
    graph M e (index M q hq v) = opOf M e q hq v := by simp [graph,index]

noncomputable def cfg (x : TM2.Cfg (fun _ : K => Bool) Λ σ) : BSMGraph.Cfg n (Fintype.card (Node M)) :=
  (x.l.map (fun l => index M (M l) (root_mem M l) x.var),mapStacks e x.stk)

omit [DecidableEq K] in
theorem node_step (q : Stmt (K := K) (Λ := Λ) (σ := σ)) (hq : q ∈ statements M)
    (v : σ) (s : K → List Bool) :
    BSMGraph.next (opOf M e q hq v) (mapStacks e s) ∈
      BSMGraph.step (graph M e) (some (index M q hq v),mapStacks e s) := by
  simp [BSMGraph.step,graph_index]

theorem statement_progress (q : Stmt (K := K) (Λ := Λ) (σ := σ)) (hq : q ∈ statements M)
    (v : σ) (s : K → List Bool) :
    StateTransition.Reaches₁ (BSMGraph.step (graph M e))
      (some (index M q hq v),mapStacks e s) (cfg M e (TM2.stepAux q v s)) := by
  induction q generalizing v s with
  | push k f q ih =>
    apply Relation.TransGen.head (r := fun x y => y ∈ BSMGraph.step (graph M e) x) (node_step M e _ hq v s)
    simpa [opOf,BSMGraph.next,mapStacks_update,mapStacks] using
      ih (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self])) v
        (Function.update s k (f v :: s k))
  | peek k f q ih =>
    apply Relation.TransGen.head (r := fun x y => y ∈ BSMGraph.step (graph M e) x) (node_step M e _ hq v s)
    simpa [opOf,BSMGraph.next,mapStacks] using
      ih (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self])) (f v (s k).head?) s
  | pop k f q ih =>
    apply Relation.TransGen.head (r := fun x y => y ∈ BSMGraph.step (graph M e) x) (node_step M e _ hq v s)
    simpa [opOf,BSMGraph.next,mapStacks_update,mapStacks] using
      ih (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self]))
        (f v (s k).head?) (Function.update s k (s k).tail)
  | load f q ih =>
    apply Relation.TransGen.head (r := fun x y => y ∈ BSMGraph.step (graph M e) x) (node_step M e _ hq v s)
    exact ih (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self])) (f v) s
  | branch f q r ihq ihr =>
    apply Relation.TransGen.head (r := fun x y => y ∈ BSMGraph.step (graph M e) x) (node_step M e _ hq v s)
    cases hf : f v with
    | false =>
      simpa [opOf,TM2.stepAux,BSMGraph.next,hf] using
        ihr (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self])) v s
    | true =>
      simpa [opOf,TM2.stepAux,BSMGraph.next,hf] using
        ihq (sub_mem M hq (by simp [TM2.stmts₁,TM2.stmts₁_self])) v s
  | goto f => exact Relation.TransGen.single (node_step M e _ hq v s)
  | halt => exact Relation.TransGen.single (node_step M e _ hq v s)

theorem respects : StateTransition.Respects (TM2.step M) (BSMGraph.step (graph M e))
    (fun x y => cfg M e x = y) := by
  apply StateTransition.fun_respects.mpr
  rintro ⟨q,v,s⟩
  cases q with
  | none => rfl
  | some q => exact statement_progress M e (M q) (root_mem M q) v s

theorem graph_halts_iff (x : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    (StateTransition.eval (BSMGraph.step (graph M e)) (cfg M e x)).Dom ↔
      (StateTransition.eval (TM2.step M) x).Dom :=
  StateTransition.tr_eval_dom (respects M e) rfl

noncomputable def compile (scratch : Fin n) (entry : Λ) (v : σ) : BSM.Program n :=
  BSMGraph.compile scratch (index M (M entry) (root_mem M entry) v) (graph M e)

theorem compile_correct (scratch : Fin n) (entry : Λ) (v : σ) (s : K → List Bool) :
    BSM.Halts (1,compile M e scratch entry v,mapStacks e s) ↔
      (StateTransition.eval (TM2.step M) ⟨some entry,v,s⟩).Dom :=
  (BSMGraph.initial_halts_iff scratch _ (graph M e) (mapStacks e s)).trans
    (graph_halts_iff M e ⟨some entry,v,s⟩)

end DistributedSynthesis.CounterMachine.TM2ToBSM
