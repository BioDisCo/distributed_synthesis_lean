/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Logic.MSO.NodeQuantification
import DistributedSynthesis.Library.Logic.MSO.TreeAtoms

/-! # Recognition of predicates on encoded valuations

This is a proof interface for constructing automata, not a claim that arbitrary
semantic predicates are recognizable. The frontend uses it for structural
induction on the existing Mathlib first-order syntax.
-/
namespace DistributedSynthesis.MSO.Tree

variable {Branch Alphabet : Type*} {n m k l : Nat}

abbrev ValuationPredicate (Branch Alphabet : Type*) (n m : Nat) :=
  LabeledTree Branch Alphabet → (Fin n → TreeNode Branch) →
    (Fin m → Set (TreeNode Branch)) → Prop

def Recognizable (P : ValuationPredicate Branch Alphabet n m) : Prop :=
  ∃ A : RunParityTreeAutomaton.{_, _, 0} Branch (ValuationLabel Alphabet n m),
    ∀ tree nodes sets, A.acceptsTree (encode tree nodes sets) ↔ P tree nodes sets

/-- Inverse renaming of marker coordinates. -/
def renameMarkers (f : Fin n → Fin k) (g : Fin m → Fin l)
    (a : ValuationLabel Alphabet k l) : ValuationLabel Alphabet n m :=
  (a.1, a.2.1 ∘ f, a.2.2 ∘ g)

@[simp] theorem renameMarkers_encode (f : Fin n → Fin k) (g : Fin m → Fin l)
    (tree : LabeledTree Branch Alphabet) (nodes : Fin k → TreeNode Branch)
    (sets : Fin l → Set (TreeNode Branch)) :
    renameMarkers f g ∘ encode tree nodes sets = encode tree (nodes ∘ f) (sets ∘ g) := rfl

namespace Recognizable
variable {P Q : ValuationPredicate Branch Alphabet n m}

theorem congr (h : Recognizable P)
    (same : ∀ tree nodes sets, P tree nodes sets ↔ Q tree nodes sets) : Recognizable Q := by
  obtain ⟨A, correct⟩ := h
  exact ⟨A, fun tree nodes sets => (correct tree nodes sets).trans (same tree nodes sets)⟩

theorem rename (h : Recognizable P) (f : Fin n → Fin k) (g : Fin m → Fin l) :
    Recognizable (fun tree nodes sets => P tree (nodes ∘ f) (sets ∘ g)) := by
  obtain ⟨A, correct⟩ := h
  refine ⟨A.comap (renameMarkers f g), fun tree nodes sets => ?_⟩
  rw [RunParityTreeAutomaton.comap_acceptsTree_iff, renameMarkers_encode]
  exact correct tree _ _

theorem falsum : Recognizable (Branch := Branch) (Alphabet := Alphabet)
    (n := n) (m := m) (fun _ _ _ => False) :=
  ⟨falseAutomaton, falseAutomaton_correct⟩

variable [Fintype Branch] [Nonempty Branch] [Fintype Alphabet]

theorem neg (h : Recognizable P) : Recognizable (fun tree nodes sets => ¬ P tree nodes sets) := by
  obtain ⟨A, correct⟩ := h
  exact ⟨TreeComplement.automaton A, fun tree nodes sets =>
    (TreeComplement.accepts_iff A _).trans (not_congr (correct tree nodes sets))⟩

omit [Nonempty Branch] [Fintype Alphabet] in
theorem conj (hP : Recognizable P) (hQ : Recognizable Q) :
    Recognizable (fun tree nodes sets => P tree nodes sets ∧ Q tree nodes sets) := by
  obtain ⟨A, hA⟩ := hP
  obtain ⟨B, hB⟩ := hQ
  exact ⟨TreeBoolean.inter A B, fun tree nodes sets =>
    (TreeBoolean.inter_accepts_iff A B _).trans (and_congr (hA tree nodes sets) (hB tree nodes sets))⟩

theorem impl (hP : Recognizable P) (hQ : Recognizable Q) :
    Recognizable (fun tree nodes sets => P tree nodes sets → Q tree nodes sets) := by
  exact (hP.conj hQ.neg).neg.congr (fun _ _ _ => by tauto)

omit [Fintype Alphabet] in
theorem existsNode {P : ValuationPredicate Branch Alphabet (n+1) m} (h : Recognizable P) :
    Recognizable (fun tree nodes sets => ∃ x, P tree (Fin.snoc nodes x) sets) := by
  obtain ⟨A, correct⟩ := h
  exact ⟨exNodeAutomaton A, fun tree nodes sets =>
    (exNodeAutomaton_accepts_iff A tree nodes sets).trans
      (exists_congr (fun x => correct tree (Fin.snoc nodes x) sets))⟩

theorem forallNode {P : ValuationPredicate Branch Alphabet (n+1) m} (h : Recognizable P) :
    Recognizable (fun tree nodes sets => ∀ x, P tree (Fin.snoc nodes x) sets) := by
  exact h.neg.existsNode.neg.congr (fun _ _ _ => by simp)

omit [Fintype Branch] [Nonempty Branch] [Fintype Alphabet] in
theorem existsSet {P : ValuationPredicate Branch Alphabet n (m+1)} (h : Recognizable P) :
    Recognizable (fun tree nodes sets => ∃ X, P tree nodes (Fin.snoc sets X)) := by
  obtain ⟨A, correct⟩ := h
  refine ⟨A.project dropSet, fun tree nodes sets => ?_⟩
  rw [RunParityTreeAutomaton.project_acceptsTree_iff]
  constructor
  · rintro ⟨lifted, labels, accepts⟩
    obtain ⟨X, rfl⟩ := (dropSet_eq_encode_iff tree nodes sets lifted).mp labels
    exact ⟨X, (correct tree nodes (Fin.snoc sets X)).mp accepts⟩
  · rintro ⟨X, satisfies⟩
    exact ⟨encode tree nodes (Fin.snoc sets X), dropSet_encode tree nodes sets X,
      (correct tree nodes (Fin.snoc sets X)).mpr satisfies⟩

theorem forallSet {P : ValuationPredicate Branch Alphabet n (m+1)} (h : Recognizable P) :
    Recognizable (fun tree nodes sets => ∀ X, P tree nodes (Fin.snoc sets X)) := by
  exact h.neg.existsSet.neg.congr (fun _ _ _ => by simp)

end Recognizable
end DistributedSynthesis.MSO.Tree
