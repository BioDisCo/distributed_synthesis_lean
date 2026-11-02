/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericOperations

/-! # Primitive-recursive postfix evaluation of MSO constructions

Instructions carry the finite variable context. Codes contain only natural
numbers and finite lists. Evaluation is total, including malformed codes;
correctness below is used for the well-scoped codes produced from formulas.
-/
namespace DistributedSynthesis.MSO.Tree.NumericProgram
open NumericValuations EncodedProjectedTree

abbrev Instruction := Nat × Shape × Nat × Nat × Nat × List Nat × List Nat
abbrev Code := List Instruction

def operation (b : Nat) (t : Instruction) (p q : Data) : Data :=
  if t.1 < 8 then NumericOperations.atom b t.2.1 t.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1
  else if t.1 = 8 then NumericOperations.neg b t.2.1 q
  else if t.1 = 9 then NumericOperations.conj b t.2.1 p q
  else if t.1 = 10 then NumericOperations.rename b t.2.1 (t.2.1.1,t.2.2.1,t.2.2.2.1)
    t.2.2.2.2.2.1 t.2.2.2.2.2.2 q
  else NumericOperations.project b t.2.1 (t.2.1.1,t.2.2.1,t.2.2.2.1)
    t.2.2.2.2.2.1 t.2.2.2.2.2.2 q

def arity (t : Instruction) : Nat := if t.1 < 8 then 0 else if t.1 = 9 then 2 else 1

def step (b : Nat) (s : List Data) (t : Instruction) : List Data :=
  operation b t (s.getD 1 default) (s.getD 0 default) :: s.drop (arity t)
def run (b : Nat) (code : Code) (stack : List Data) : List Data := code.foldl (step b) stack

def compile (b : Nat) (code : Code) : Data := (run b code []).getD 0 default

@[fun_prop] theorem operation_primrec : Primrec (fun x : Nat × Instruction × Data × Data =>
    operation x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold operation
  apply Primrec.ite (by fun_prop) (by fun_prop)
  apply Primrec.ite (by fun_prop) (by fun_prop)
  apply Primrec.ite (by fun_prop) (by fun_prop)
  apply Primrec.ite <;> fun_prop
@[fun_prop] theorem arity_primrec : Primrec arity := by
  unfold arity
  apply Primrec.ite (by fun_prop) (by fun_prop)
  apply Primrec.ite <;> fun_prop
@[fun_prop] theorem step_primrec : Primrec (fun x : Nat × List Data × Instruction => step x.1 x.2.1 x.2.2) := by
  unfold step
  apply Primrec.list_cons.comp (by fun_prop)
  exact Primrec.list_drop.comp (by fun_prop) (by fun_prop)

theorem run_primrec : Primrec (fun x : Nat × Code × List Data => run x.1 x.2.1 x.2.2) := by
  unfold run
  exact Primrec.list_foldl (show Primrec (fun x : Nat × Code × List Data => x.2.1) by fun_prop)
    (show Primrec (fun x : Nat × Code × List Data => x.2.2) by fun_prop)
    ((step_primrec.comp (show Primrec (fun x : (Nat × Code × List Data) × List Data × Instruction =>
      (x.1.1,x.2.1,x.2.2)) by fun_prop)).to₂)

theorem compile_primrec : Primrec₂ compile := by
  have h : Primrec (fun x : Nat × Code => run x.1 x.2 []) :=
    run_primrec.comp (g := fun x : Nat × Code => (x.1,x.2,([] : List Data)))
      (Primrec.fst.pair (Primrec.snd.pair (Primrec.const ([] : List Data))))
  exact (Primrec.list_getD (default : Data)).comp h (Primrec.const 0)

structure Program (b : Nat) where
  code : Code
  data : Data
  computes : ∀ stack, run b code stack = data :: stack

namespace Program
variable {b : Nat}

theorem compile_eq (p : Program b) : compile b p.code = p.data := by
  simp only [compile, p.computes, List.getD_cons_zero]

def atom (s : Shape) (k i j d : Nat) (hk : k < 8) : Program b where
  code := [(k,s,i,j,d,[],[])]
  data := NumericOperations.atom b s k i j d
  computes stack := by simp [run, step, operation, arity, hk]

def neg (s : Shape) (p : Program b) : Program b where
  code := p.code ++ [(8,s,0,0,0,[],[])]
  data := NumericOperations.neg b s p.data
  computes stack := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (step b) stack p.code = p.data :: stack from p.computes stack]
    rfl

def conj (s : Shape) (p q : Program b) : Program b where
  code := p.code ++ q.code ++ [(9,s,0,0,0,[],[])]
  data := NumericOperations.conj b s p.data q.data
  computes stack := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (step b) stack p.code = p.data :: stack from p.computes stack]
    rw [show List.foldl (step b) (p.data :: stack) q.code = q.data :: p.data :: stack from q.computes _]
    rfl

def rename (s : Shape) (n m : Nat) (f g : List Nat) (p : Program b) : Program b where
  code := p.code ++ [(10,s,n,m,0,f,g)]
  data := NumericOperations.rename b s (s.1,n,m) f g p.data
  computes stack := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (step b) stack p.code = p.data :: stack from p.computes stack]
    rfl

def project (s : Shape) (n m : Nat) (f g : List Nat) (p : Program b) : Program b where
  code := p.code ++ [(11,s,n,m,0,f,g)]
  data := NumericOperations.project b s (s.1,n,m) f g p.data
  computes stack := by
    simp only [run, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [show List.foldl (step b) stack p.code = p.data :: stack from p.computes stack]
    rfl

end Program
end DistributedSynthesis.MSO.Tree.NumericProgram
