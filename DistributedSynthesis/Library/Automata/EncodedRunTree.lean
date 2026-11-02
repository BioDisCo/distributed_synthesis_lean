/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedProjectedTree
import DistributedSynthesis.Library.Automata.EncodedWordTree
import DistributedSynthesis.Library.Computability.FiniteFunctionCoding

/-! # Compiling explicit nondeterministic tree-transition tables

The input fields are direction count, maximum letter index, maximum state
index, initial index, priorities, and allowed transition triples. A triple is
`(source, letter, successor-vector)`, using the existing finite-function coding.
Compilation records transition choices in node labels and preserves a rejecting
flag after any illegal choice.
-/
namespace DistributedSynthesis.EncodedRunTree

abbrev Transition := Nat × Nat × List Nat
abbrev Input := Nat × Nat × Nat × Nat × List Nat × List Transition

def branches (x : Input) := x.1
def alphabet (x : Input) := x.2.1 + 1
def states (x : Input) := x.2.2.1 + 1
def initial (x : Input) := x.2.2.2.1
def priorities (x : Input) := x.2.2.2.2.1
def transitions (x : Input) := x.2.2.2.2.2
def vectors (x : Input) := FiniteFunctionCoding.codes (branches x) (states x)
def choices (x : Input) := alphabet x * (vectors x).length

def valid (x : Input) (q a : Nat) (v : List Nat) : Prop := (q, a, v) ∈ transitions x
instance (x : Input) (q a : Nat) (v : List Nat) : Decidable (valid x q a v) := by
  unfold valid
  infer_instance

def rawStep (x : Input) (s l b : Nat) : Nat :=
  let v := (vectors x).getD (l % (vectors x).length) []
  2 * v.getD b 0 + if s % 2 = 1 ∧ valid x (s / 2) (l / (vectors x).length) v then 1 else 0

def rawPriority (x : Input) (s : Nat) : Nat :=
  if s % 2 = 1 then (priorities x).getD (s / 2) 0 else 1

def wordData (x : Input) : EncodedParityTables.Data :=
  (2 * states x - 1, 2 * (initial x % states x) + 1,
    (List.range (2 * states x)).map (rawPriority x),
    (List.range (choices x * branches x)).map (fun l =>
      (List.range (2 * states x)).map (fun s => rawStep x s (l / branches x) (l % branches x))))

def compile (x : Input) : EncodedProjectedTree.Data :=
  (x.2.1, EncodedWordTree.compile (branches x, choices x, wordData x),
    (List.range (choices x)).map (fun l => l / (vectors x).length))

@[fun_prop] theorem branches_primrec : Primrec branches := Primrec.fst
@[fun_prop] theorem alphabet_primrec : Primrec alphabet := by unfold alphabet; fun_prop
@[fun_prop] theorem states_primrec : Primrec states := by unfold states; fun_prop
@[fun_prop] theorem initial_primrec : Primrec initial := by unfold initial; fun_prop
@[fun_prop] theorem priorities_primrec : Primrec priorities := by unfold priorities; fun_prop
@[fun_prop] theorem transitions_primrec : Primrec transitions := by unfold transitions; fun_prop
@[fun_prop] theorem vectors_primrec : Primrec vectors :=
  FiniteFunctionCoding.codes_primrec.comp branches_primrec states_primrec
@[fun_prop] theorem choices_primrec : Primrec choices := by unfold choices; fun_prop

@[fun_prop] theorem valid_primrec :
    PrimrecPred (fun x : Input × Nat × Nat × List Nat => valid x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hm : PrimrecRel (fun (xs : List Transition) v => v ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact hm.comp (transitions_primrec.comp Primrec.fst) Primrec.snd

@[fun_prop] theorem rawStep_primrec :
    Primrec (fun x : Input × Nat × Nat × Nat => rawStep x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold rawStep
  apply Primrec.nat_add.comp
  · fun_prop
  · apply Primrec.ite <;> fun_prop

@[fun_prop] theorem rawPriority_primrec : Primrec (fun x : Input × Nat => rawPriority x.1 x.2) := by
  unfold rawPriority
  apply Primrec.ite <;> fun_prop

@[fun_prop] theorem wordData_primrec : Primrec wordData := by unfold wordData; fun_prop

theorem compile_primrec : Primrec compile := by
  unfold compile
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair
  · apply EncodedWordTree.compile_primrec.comp
    fun_prop
  · fun_prop

end DistributedSynthesis.EncodedRunTree
