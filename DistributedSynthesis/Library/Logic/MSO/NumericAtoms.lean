/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NumericValuations
import DistributedSynthesis.Library.Automata.EncodedRunTreeEnumeration

/-! # Primitive-recursive atomic MSO automata

The instruction tags are false, membership, equality, label, root, directed
successor, child, and singleton. All use two Boolean control states. The local
atoms reset this otherwise redundant state to false at every transition.
-/
namespace DistributedSynthesis.MSO.Tree.NumericAtoms
open NumericValuations

abbrev Input := Nat × Shape × Nat × Nat × Nat × Nat

def branches (x : Input) := x.1
def shape (x : Input) := x.2.1
def tag (x : Input) := x.2.2.1
def first (x : Input) := x.2.2.2.1
def second (x : Input) := x.2.2.2.2.1
def third (x : Input) := x.2.2.2.2.2

def zeroVector (b : Nat) : List Nat := (List.range b).map (fun _ => 0)
def edgeVector (b marked direction : Nat) : List Nat :=
  (List.range b).map (fun i => if marked = 1 ∧ i = direction then 1 else 0)

def localCondition (x : Input) (a : Nat) : Prop :=
  if tag x = 1 then node (shape x) a (first x) = 1 → set (shape x) a (second x) = 1
  else if tag x = 2 then node (shape x) a (first x) = node (shape x) a (second x)
  else if tag x = 3 then node (shape x) a (first x) = 1 → base (shape x) a = second x
  else False
instance (x : Input) (a : Nat) : Decidable (localCondition x a) := by unfold localCondition; infer_instance

def condition (x : Input) (q a : Nat) (v : List Nat) : Prop :=
  if tag x < 4 then localCondition x a ∧ v = zeroVector (branches x)
  else if tag x = 4 then (q = 1 → node (shape x) a (first x) = 1) ∧ v = zeroVector (branches x)
  else if tag x = 5 then node (shape x) a (second x) = q ∧
    v = edgeVector (branches x) (node (shape x) a (first x)) (third x)
  else if tag x = 6 then node (shape x) a (second x) = q ∧
    (if node (shape x) a (first x) = 1 then
      ∃ d < branches x, v = edgeVector (branches x) 1 d else v = zeroVector (branches x))
  else if tag x = 7 then
    (if q = 1 then
      if node (shape x) a (first x) = 1 then v = zeroVector (branches x)
      else ∃ d < branches x, v = edgeVector (branches x) 1 d
    else node (shape x) a (first x) = 0 ∧ v = zeroVector (branches x))
  else False
instance (x : Input) (q a : Nat) (v : List Nat) : Decidable (condition x q a v) := by
  unfold condition
  infer_instance

def initial (x : Input) : Nat := if tag x = 4 ∨ tag x = 7 then 1 else 0

def rawData (x : Input) : EncodedRunTree.Input :=
  (branches x, count (shape x) - 1, 1, initial x, if tag x = 7 then [0,1] else [0,0],
    EncodedRunTree.enumerate (branches x) 2 (count (shape x)) (condition x))

def compile (x : Input) : EncodedProjectedTree.Data := EncodedRunTree.compile (rawData x)

@[fun_prop] theorem branches_primrec : Primrec branches := Primrec.fst
@[fun_prop] theorem shape_primrec : Primrec shape := by unfold shape; fun_prop
@[fun_prop] theorem tag_primrec : Primrec tag := by unfold tag; fun_prop
@[fun_prop] theorem first_primrec : Primrec first := by unfold first; fun_prop
@[fun_prop] theorem second_primrec : Primrec second := by unfold second; fun_prop
@[fun_prop] theorem third_primrec : Primrec third := by unfold third; fun_prop
@[fun_prop] theorem zeroVector_primrec : Primrec zeroVector := by unfold zeroVector; fun_prop
@[fun_prop] theorem edgeVector_primrec :
    Primrec (fun x : Nat × Nat × Nat => edgeVector x.1 x.2.1 x.2.2) := by
  unfold edgeVector
  apply PrimrecFunProp.map (by fun_prop)
  apply Primrec.ite <;> fun_prop

private theorem implies_primrec {X : Type*} [Primcodable X] {p q : X → Prop}
    (hp : PrimrecPred p) (hq : PrimrecPred q) : PrimrecPred (fun x => p x → q x) :=
  (hp.not.or hq).of_eq (fun _ => by tauto)
attribute [local fun_prop] implies_primrec

@[fun_prop] theorem localCondition_primrec : PrimrecPred (fun x : Input × Nat => localCondition x.1 x.2) := by
  unfold localCondition
  apply PrimrecFunProp.predicate_ite <;> try fun_prop
  apply PrimrecFunProp.predicate_ite <;> try fun_prop
  apply PrimrecFunProp.predicate_ite <;> try fun_prop
  exact PrimrecFunProp.predicate_const False

@[fun_prop] theorem condition_primrec :
    PrimrecPred (fun x : Input × Nat × Nat × List Nat => condition x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold condition
  repeat' first | apply PrimrecFunProp.predicate_ite | apply PrimrecPred.and | exact PrimrecFunProp.predicate_const False | fun_prop

@[fun_prop] theorem initial_primrec : Primrec initial := by
  unfold initial
  apply Primrec.ite <;> fun_prop

@[fun_prop] theorem rawData_primrec : Primrec rawData := by
  unfold rawData
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (Primrec.const 1)
  apply Primrec.pair initial_primrec
  apply Primrec.pair
  · apply Primrec.ite <;> fun_prop
  · apply EncodedRunTree.enumerate_primrec <;> fun_prop

theorem compile_primrec : Primrec compile := EncodedRunTree.compile_primrec.comp rawData_primrec

end DistributedSynthesis.MSO.Tree.NumericAtoms
