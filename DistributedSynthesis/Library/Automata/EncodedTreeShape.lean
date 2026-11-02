/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedProjectedTree
import DistributedSynthesis.Library.Computability.PrimrecFunProp

/-! # Explicit alphabets for numeric tree-automaton operations

Binary operations interpret both operands at the same direction and public
letter alphabets. Keeping these dimensions explicit also gives total meanings
to malformed input codes, without adding proof fields to numeric input.
-/
namespace DistributedSynthesis.EncodedTreeShape
open EncodedProjectedTree

def resize (b a : Nat) (d : Data) : Data :=
  (a, ((monitorData d).1, EncodedTreeNonemptiness.labels (monitorData d), b,
    EncodedTreeNonemptiness.transitions (monitorData d),
    EncodedTreeNonemptiness.priorities (monitorData d),
    EncodedTreeNonemptiness.initial (monitorData d)), projection d)

attribute [local fun_prop] monitorData_primrec projection_primrec
  EncodedTreeNonemptiness.labels_primrec EncodedTreeNonemptiness.transitions_primrec
  EncodedTreeNonemptiness.priorities_primrec EncodedTreeNonemptiness.initial_primrec

@[fun_prop] theorem resize_primrec :
    Primrec (fun x : Nat × Nat × Data => resize x.1 x.2.1 x.2.2) := by
  unfold resize
  fun_prop

@[simp] theorem resize_self (d : Data) :
    resize (EncodedTreeNonemptiness.branches (monitorData d)) d.1 d = d := rfl

@[simp] theorem resize_resize (b a b' a' : Nat) (d : Data) :
    resize b a (resize b' a' d) = resize b a d := rfl

abbrev Accepts (b a : Nat) (d : Data) (tree : LabeledTree (Fin b) (Fin (a + 1))) : Prop :=
  (automaton (resize b a d)).acceptsTree tree

end DistributedSynthesis.EncodedTreeShape
