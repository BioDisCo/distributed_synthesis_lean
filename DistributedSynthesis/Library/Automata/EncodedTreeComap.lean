/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedRunTreeCorrect
import DistributedSynthesis.Library.Automata.EncodedRunTreeEnumeration
import DistributedSynthesis.Library.Automata.EncodedTreeComplementCorrect
import DistributedSynthesis.Library.Automata.EncodedTreeProjection

/-! # Primitive-recursive inverse letter maps for numeric tree automata

The complete finite transition relation is tabulated with the new letter map,
then passed to the existing transition-choice encoding. Missing entries of the
map are zero and indices are reduced modulo the old public alphabet size.
-/
namespace DistributedSynthesis.EncodedTreeComap
open EncodedProjectedTree

abbrev Input := Data × Nat × List Nat

def rawData (x : Input) : EncodedRunTree.Input :=
  (EncodedTreeNonemptiness.branches (monitorData x.1), x.2.1, (monitorData x.1).1,
    EncodedTreeNonemptiness.initial (monitorData x.1), EncodedTreeNonemptiness.priorities (monitorData x.1),
    EncodedRunTree.enumerate (EncodedTreeComplement.branches x.1) (EncodedTreeComplement.states x.1)
      (x.2.1 + 1) (fun q a v => EncodedTreeComplement.legal x.1 q
        (x.2.2.getD a 0 % alphabetSize x.1) v))

def compile (x : Input) : Data := EncodedRunTree.compile (rawData x)

attribute [local fun_prop] monitorData_primrec alphabetSize_primrec
  EncodedTreeNonemptiness.initial_primrec EncodedTreeNonemptiness.priorities_primrec
  EncodedTreeNonemptiness.branches_primrec

@[fun_prop] theorem rawData_primrec : Primrec rawData := by
  unfold rawData
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair (by fun_prop)
  apply EncodedRunTree.enumerate_primrec <;> fun_prop

theorem compile_primrec : Primrec compile := EncodedRunTree.compile_primrec.comp rawData_primrec

def letterMap (x : Input) (a : Fin (x.2.1 + 1)) : Fin (alphabetSize x.1) :=
  ⟨x.2.2.getD a.val 0 % alphabetSize x.1, Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem delta_iff (x : Input) (q : (automaton x.1).State) (a : Fin (x.2.1 + 1))
    (v : Fin (EncodedTreeNonemptiness.branches (monitorData x.1)) → (automaton x.1).State) :
    (EncodedRunTree.source (rawData x)).delta q a v ↔ (automaton x.1).delta q (letterMap x a) v := by
  change (q.val, a.val, FiniteFunctionCoding.encode v) ∈
    EncodedRunTree.enumerate (EncodedTreeComplement.branches x.1) (EncodedTreeComplement.states x.1)
      (x.2.1 + 1) (fun q a v => EncodedTreeComplement.legal x.1 q
        (x.2.2.getD a 0 % alphabetSize x.1) v) ↔ _
  rw [EncodedRunTree.mem_enumerate]
  have hv : FiniteFunctionCoding.encode v ∈ FiniteFunctionCoding.codes
      (EncodedTreeComplement.branches x.1) (EncodedTreeComplement.states x.1) :=
    (FiniteCodeNumbering.mem_unique _ _).mpr (FiniteSearch.ofFn_mem_tables v)
  have hq : q.val < EncodedTreeComplement.states x.1 := q.isLt
  simp only [hq, a.isLt, hv, true_and]
  exact EncodedTreeComplement.legal_correct x.1 q (letterMap x a) v

variable (x : Input) [Inhabited (Fin (EncodedTreeNonemptiness.branches (monitorData x.1)))]

/-- The same tree is read through the supplied finite letter map. -/
theorem compile_correct (tree : LabeledTree
    (Fin (EncodedTreeNonemptiness.branches (monitorData x.1))) (Fin (x.2.1 + 1))) :
    (automaton (compile x)).acceptsTree tree ↔ (automaton x.1).acceptsTree (letterMap x ∘ tree) := by
  letI : Inhabited (EncodedRunTree.Direction (rawData x)) :=
    inferInstanceAs (Inhabited (Fin (EncodedTreeNonemptiness.branches (monitorData x.1))))
  have h := RunParityTreeAutomaton.acceptsTree_iff_of_equiv
    ((automaton x.1).comap (letterMap x)) (EncodedRunTree.source (rawData x)) (Equiv.refl _)
    rfl (fun _ => rfl) (fun q a v => delta_iff x q a v) tree
  exact (EncodedRunTree.compile_correct (rawData x) tree).trans h

end DistributedSynthesis.EncodedTreeComap
