/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeShape
import DistributedSynthesis.Library.Automata.EncodedTreeWord
import DistributedSynthesis.Library.Automata.EncodedParityProductCorrect

/-! # Numeric conjunction of projected parity tree monitors

A node chooses one compatible pair of annotated letters. The existing numeric
parity product checks both component paths. The public letter is the shared
projection of the two choices; the branch direction is shared as well.
-/
namespace DistributedSynthesis.EncodedTreeIntersection
open EncodedProjectedTree
open Characterisation

abbrev Input := Nat × Nat × Data × Data

def left (x : Input) : Data := EncodedTreeShape.resize x.1 x.2.1 x.2.2.1
def right (x : Input) : Data := EncodedTreeShape.resize x.1 x.2.1 x.2.2.2
def output (d : Data) (i : Nat) : Nat := (projection d).getD i 0 % alphabetSize d

def pairs (x : Input) : List (Nat × Nat) :=
  ((List.range (EncodedTreeNonemptiness.labels (monitorData (left x)))).product
    (List.range (EncodedTreeNonemptiness.labels (monitorData (right x))))).filter
      (fun p => decide (output (left x) p.1 = output (right x) p.2))

def productData (x : Input) : EncodedParityProduct.Data :=
  (EncodedTreeWord.compile (monitorData (left x)), EncodedTreeWord.compile (monitorData (right x)),
    (List.range ((pairs x).length * x.1)).map (fun i =>
      let p := (pairs x).getD (i / x.1) (0, 0)
      (p.1 * x.1 + i % x.1, p.2 * x.1 + i % x.1)))

def compile (x : Input) : Data :=
  (x.2.1, EncodedWordTree.compile (x.1, (pairs x).length,
      EncodedParityProduct.conjunction (productData x)),
    (pairs x).map (fun p => output (left x) p.1))

attribute [local fun_prop] alphabetSize_primrec monitorData_primrec projection_primrec
  EncodedTreeNonemptiness.labels_primrec

@[fun_prop] theorem left_primrec : Primrec left := by unfold left; fun_prop
@[fun_prop] theorem right_primrec : Primrec right := by unfold right; fun_prop
@[fun_prop] theorem output_primrec : Primrec (fun x : Data × Nat => output x.1 x.2) := by
  unfold output; fun_prop
@[fun_prop] theorem product_primrec :
    Primrec (fun x : List Nat × List Nat => x.1.product x.2) := FiniteSearch.product_primrec
@[fun_prop] theorem pairs_primrec : Primrec pairs := by unfold pairs; fun_prop

@[fun_prop] theorem productData_primrec : Primrec productData := by
  unfold productData
  apply Primrec.pair (EncodedTreeWord.compile_primrec.comp (by fun_prop))
  apply Primrec.pair (EncodedTreeWord.compile_primrec.comp (by fun_prop))
  fun_prop

theorem compile_primrec : Primrec compile := by
  unfold compile
  apply Primrec.pair (by fun_prop)
  apply Primrec.pair
  · apply EncodedWordTree.compile_primrec.comp
    exact Primrec.fst.pair ((Primrec.list_length.comp pairs_primrec).pair
      (EncodedParityProduct.conjunction_primrec.comp productData_primrec))
  · fun_prop

end DistributedSynthesis.EncodedTreeIntersection
