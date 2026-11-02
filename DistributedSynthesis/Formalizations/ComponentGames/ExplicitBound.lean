/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ComponentRoots
import Mathlib.Computability.DFA

/- An explicit bound, uniform in the input recognizer. This is a prefix-hole
bound, not a definition of consensus or a claim about consensus algorithms. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation

variable {α Q : Type*} [Fintype Q]

/-- Delete loops from a finite run, retaining its initial and final states. -/
theorem short_word_same_state (M : Recognizer α Q) (q : Q) (w : List α) :
    ∃ v : List α, v.length < Fintype.card Q ∧ M.evalFrom q v = M.evalFrom q w := by
  classical
  let automaton : DFA α Q := ⟨M.step, M.start, M.accept⟩
  induction hw : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    by_cases small : w.length < Fintype.card Q
    · exact ⟨w, small, rfl⟩
    · obtain ⟨r,a,b,c,eq,_,nonempty,ha,_,hc⟩ :=
        automaton.evalFrom_split (Nat.le_of_not_gt small) (rfl : automaton.evalFrom q w = _)
      have eval : M.evalFrom q (a ++ c) = M.evalFrom q w := by
        change automaton.evalFrom q (a ++ c) = automaton.evalFrom q w
        rw [DFA.evalFrom_of_append, ha, hc]
      have smaller : (a ++ c).length < n := by
        have pos : 0 < b.length := List.length_pos_iff.mpr nonempty
        rw [← hw, eq]
        simp only [List.length_append]
        omega
      obtain ⟨v,hv,he⟩ := ih (a ++ c).length smaller (a ++ c) rfl
      exact ⟨v,hv,he.trans eval⟩

theorem prefix_holes_short (M : Recognizer α Q) (P : List α → Prop)
    (recognizes : ∀ w, P w ↔ M.eval w ∈ M.accept)
    (holes : HasPrefixHoles P) :
    ∀ h, P h → ∃ u, u.length < Fintype.card Q ∧ ¬ P (h ++ u) := by
  intro h hh
  obtain ⟨u,hu⟩ := holes h hh
  obtain ⟨v,hv,eq⟩ := short_word_same_state M (M.eval h) u
  refine ⟨v,hv,?_⟩
  intro live
  apply hu
  apply (recognizes _).mpr
  have := (recognizes _).mp live
  change M.evalFrom (M.eval h) v = M.evalFrom (M.eval h) u at eq
  change M.evalFrom M.start (h ++ v) ∈ M.accept at this
  rw [Recognizer.evalFrom_of_append] at this
  change M.evalFrom (M.eval h) v ∈ M.accept at this
  rw [eq] at this
  simpa only [Recognizer.eval, Recognizer.evalFrom_of_append] using this

/-- The explicit positive block length is just the number of states. -/
theorem prefix_holes_exact_card [Nonempty α]
    (M : Recognizer α Q) (P : List α → Prop)
    (recognizes : ∀ w, P w ↔ M.eval w ∈ M.accept)
    (closed : PrefixClosed P) (holes : HasPrefixHoles P) :
    0 < Fintype.card Q ∧
      ∀ h, ∃ u : List α, u.length = Fintype.card Q ∧ ¬ P (h ++ u) := by
  classical
  letI : Nonempty Q := ⟨M.start⟩
  let a : α := Classical.choice inferInstance
  refine ⟨Fintype.card_pos, fun h => ?_⟩
  by_cases live : P h
  · obtain ⟨u,short,missing⟩ := prefix_holes_short M P recognizes holes h live
    refine ⟨u ++ List.replicate (Fintype.card Q - u.length) a, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]; omega
    · simpa only [List.append_assoc] using
        rejected_append P closed missing (List.replicate (Fintype.card Q - u.length) a)
  · exact ⟨List.replicate (Fintype.card Q) a, by simp, rejected_append P closed live _⟩

/-- Common roots at the explicit, uniform block length, for arbitrary private
input alphabets and arbitrary connected subfamilies. -/
theorem explicit_common_roots (A : Set (Nat → Graph))
    (M : DetParityAutomaton Graph) (recognizes : ∀ x, x ∈ A ↔ M.Accepts x)
    (holes : GeometricHoles A) :
    0 < Fintype.card M.State ∧ ∀ (I₁ I₂ : Type),
      PeriodicBlocks.CommonBlockRoots (I₁:=I₁) (I₂:=I₂)
        (LivePrefix A) (Fintype.card M.State) := by
  classical
  letI : Nonempty Graph := ⟨.both⟩
  obtain ⟨positive,exactHoles⟩ := prefix_holes_exact_card
    (prefixRecognizer M) (LivePrefix A) (prefixRecognizer_correct M A recognizes)
    (livePrefix_closed A) (geometric_holes_imply_prefix_holes A holes)
  refine ⟨positive,?_⟩
  intro I₁ I₂ R anchor alive root suffix lengths connected
  by_cases nonempty : Nonempty R
  · let i : R := Classical.choice nonempty
    have lengthEq := connected_same_depth (LivePrefix A)
      (inputConnected_projects (LivePrefix A) (connected i))
    simp only [History.graphSequence,List.length_map,List.length_append,lengths] at lengthEq
    obtain ⟨p,common⟩ := exact_holes_common_view (LivePrefix A) _ exactHoles anchor
      (by omega) alive
    refine ⟨p,?_⟩
    apply PeriodicBlocks.common_roots_of_common_lag root suffix _ lengths p
    intro j k
    exact (common _ (connected j)).symm.trans (common _ (connected k))
  · exact ⟨.one,fun i => False.elim (nonempty ⟨i⟩)⟩

end Characterisation.ComponentGames

