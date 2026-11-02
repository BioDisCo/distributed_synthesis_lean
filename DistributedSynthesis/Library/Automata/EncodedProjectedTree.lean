/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeNonemptiness
import DistributedSynthesis.Library.Automata.TreeProjection

/-! # Numeric presentations of nondeterministic parity tree automata

A presentation consists of a deterministic tree monitor and a letter projection.
The monitor's letters include the nondeterministic transition choice. Projection
makes this choice existential, once per node and shared by all successors.

The public alphabet has `alphabetMax + 1` letters. Missing entries of the
projection table default to zero and are reduced modulo this positive size.
Nonemptiness is exactly the existing primitive-recursive monitor test. No
strategy, correctness certificate, or emptiness oracle is part of the input.
-/

namespace DistributedSynthesis.EncodedProjectedTree

abbrev Data := Nat × EncodedTreeNonemptiness.Data × List Nat

def alphabetSize (d : Data) : Nat := d.1 + 1
def monitorData (d : Data) : EncodedTreeNonemptiness.Data := d.2.1
def projection (d : Data) : List Nat := d.2.2

def letter (d : Data) (a : Fin (EncodedTreeNonemptiness.labels (monitorData d))) :
    Fin (alphabetSize d) :=
  ⟨(projection d).getD a.val 0 % alphabetSize d, Nat.mod_lt _ (Nat.succ_pos _)⟩

def automaton (d : Data) :
    RunParityTreeAutomaton (Fin (EncodedTreeNonemptiness.branches (monitorData d)))
      (Fin (alphabetSize d)) :=
  (EncodedTreeNonemptiness.monitor (monitorData d)).toRunAutomaton.project (letter d)

def solve (d : Data) : Bool := EncodedTreeNonemptiness.solve (monitorData d)

theorem alphabetSize_primrec : Primrec alphabetSize := Primrec.succ.comp Primrec.fst
theorem monitorData_primrec : Primrec monitorData := Primrec.fst.comp Primrec.snd
theorem projection_primrec : Primrec projection := Primrec.snd.comp Primrec.snd
theorem solve_primrec : Primrec solve :=
  EncodedTreeNonemptiness.solve_primrec.comp monitorData_primrec

theorem accepts_iff (d : Data) (tree : LabeledTree _ _) :
    (automaton d).acceptsTree tree ↔
      ∃ annotated, letter d ∘ annotated = tree ∧
        (EncodedTreeNonemptiness.monitor (monitorData d)).toRunAutomaton.acceptsTree annotated :=
  RunParityTreeAutomaton.project_acceptsTree_iff _ _ _

theorem solve_correct (d : Data) :
    solve d = true ↔ ∃ tree, (automaton d).acceptsTree tree := by
  rw [solve, EncodedTreeNonemptiness.solve_correct]
  constructor
  · rintro ⟨tree, htree⟩
    exact ⟨letter d ∘ tree, (accepts_iff d _).mpr ⟨tree, rfl, htree⟩⟩
  · rintro ⟨tree, htree⟩
    obtain ⟨annotated, _, ha⟩ := (accepts_iff d tree).mp htree
    exact ⟨annotated, ha⟩

theorem nonempty_computable :
    ComputablePred (fun d : Data => ∃ tree, (automaton d).acceptsTree tree) :=
  (Primrec.eq.comp solve_primrec (Primrec.const true)).computablePred.of_eq solve_correct

end DistributedSynthesis.EncodedProjectedTree
