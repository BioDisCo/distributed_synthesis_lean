/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedProjectedTree
import DistributedSynthesis.Library.Computability.PrimrecFunProp

/-! # Primitive-recursive letter projection for numeric tree automata -/
namespace DistributedSynthesis.EncodedTreeProjection
open EncodedProjectedTree

abbrev Input := Data × Nat × List Nat

def compile (x : Input) : Data :=
  (x.2.1, monitorData x.1,
    (List.range (EncodedTreeNonemptiness.labels (monitorData x.1))).map
      (fun l => x.2.2.getD ((projection x.1).getD l 0 % alphabetSize x.1) 0))

attribute [local fun_prop] monitorData_primrec projection_primrec alphabetSize_primrec
  EncodedTreeNonemptiness.labels_primrec

theorem compile_primrec : Primrec compile := by
  unfold compile
  fun_prop

def letterMap (n : Nat) (xs : List Nat) {k : Nat} (a : Fin k) : Fin (n + 1) :=
  ⟨xs.getD a.val 0 % (n + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem letter_eq (x : Input) (a : Fin (EncodedTreeNonemptiness.labels (monitorData x.1))) :
    letter (compile x) a = letterMap x.2.1 x.2.2 (letter x.1 a) := by
  apply Fin.ext
  change ((List.range _).map _).getD a.val 0 % _ = _
  rw [List.getD_eq_getElem _ _ (by simpa using a.isLt)]
  simp only [List.getElem_map, List.getElem_range]
  rfl

theorem accepts_iff (x : Input) (tree : LabeledTree _ _) :
    (automaton (compile x)).acceptsTree tree ↔
      ∃ original, letterMap x.2.1 x.2.2 ∘ original = tree ∧
        (automaton x.1).acceptsTree original := by
  rw [EncodedProjectedTree.accepts_iff]
  constructor
  · rintro ⟨annotated, labels, accepts⟩
    refine ⟨letter x.1 ∘ annotated, ?_,
      (EncodedProjectedTree.accepts_iff x.1 _).mpr ⟨annotated, rfl, accepts⟩⟩
    exact (funext (fun node => (letter_eq x (annotated node)).symm)).trans labels
  · rintro ⟨original, labels, accepts⟩
    obtain ⟨annotated, hannotated, accepts⟩ :=
      (EncodedProjectedTree.accepts_iff x.1 original).mp accepts
    refine ⟨annotated, ?_, accepts⟩
    funext node
    exact (letter_eq x (annotated node)).trans
      ((congrArg (letterMap x.2.1 x.2.2) (congrFun hannotated node)).trans (congrFun labels node))

end DistributedSynthesis.EncodedTreeProjection
