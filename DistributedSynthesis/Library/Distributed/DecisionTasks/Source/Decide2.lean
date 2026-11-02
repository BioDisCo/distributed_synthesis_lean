/- Extracted from consensusLTL/lean/ConsensusLTL/Decide2.lean.
Only decision-task dependencies are retained; see ../SOURCE.md. -/

import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Back
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.ColAut
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Colouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.TaskColouring
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Konig
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Views
import DistributedSynthesis.Library.Distributed.DecisionTasks.Source.Model

-- Preserve the source section contexts on Lean 4.30.
set_option linter.unusedSectionVars false

namespace DistributedSynthesis.DecisionTasks.Source

open ColAut

variable {AdvQ : Type} [Fintype AdvQ] [DecidableEq AdvQ]

variable {V O : Type} [Fintype V] [DecidableEq V] [Fintype O] [DecidableEq O]

/-- The spec for a task at a fixed input assignment: no constraint on a muted process's colour, and
the pair of current colours must eventually be one the task allows. -/
def taskSpec (T : Task Bool V O) [∀ I o, Decidable (T.allows I o)] (I : Bool → V) : Spec O where
  deafOk _ _ := true
  rel a b := decide (T.allows I fun p => if p then b else a)

/-- **A task colouring is a family of labelling problems, one per input assignment, together with
the root constraint.**  The components used by distinct assignments are disjoint, so nothing else
couples them. -/
theorem taskColouring_iff_family {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}
    [∀ I o, Decidable (T.allows I o)] {C : Bool → V → V → Base → O} :
    TaskColouring adv T C ↔
      (∀ p x y y', C p x y none = C p x y' none) ∧
      ∀ I : Bool → V,
        GenColouring (taskSpec T I) adv (fun p => colFor C I p none) (colFor C I) := by
  rw [taskColouring_annotated_form]
  constructor
  · rintro ⟨hi, ht, ha⟩
    refine ⟨hi, fun I => ⟨fun _ => rfl, fun _ _ _ _ => rfl, fun σ hσ p => ?_, fun σ hσ => ?_⟩⟩
    · rcases ht σ hσ I p with ⟨i, c, hh, hc, hall⟩ | ⟨N, c, hsil, hc, hev⟩
      · exact Or.inl ⟨i, hh, by rw [hc]; exact hall⟩
      · exact Or.inr ⟨N, hsil, by rw [hc]; exact hev⟩
    · obtain ⟨n₀, h⟩ := ha σ hσ I
      refine ⟨n₀, fun n hn => ?_⟩
      have hfun : (fun p => if p = true then colFor C I W (base W σ n)
          else colFor C I U (base U σ n)) = fun p => colFor C I p (base p σ n) := by
        funext p; cases p <;> rfl
      show decide (T.allows I fun p => if p = true then colFor C I W (base W σ n)
        else colFor C I U (base U σ n)) = true
      rw [decide_eq_true_eq, hfun]
      exact h n hn
  · rintro ⟨hi, hf⟩
    refine ⟨hi, fun σ hσ I p => ?_, fun σ hσ I => ?_⟩
    · rcases (hf I).term σ hσ p with ⟨i, hh, hall⟩ | ⟨N, hsil, hev⟩
      · exact Or.inl ⟨i, _, hh, rfl, hall⟩
      · exact Or.inr ⟨N, _, hsil, rfl, hev⟩
    · obtain ⟨n₀, h⟩ := (hf I).rel σ hσ
      refine ⟨n₀, fun n hn => ?_⟩
      have hd : decide (T.allows I fun p => if p = true then colFor C I W (base W σ n)
          else colFor C I U (base U σ n)) = true := h n hn
      have hfun : (fun p => if p = true then colFor C I W (base W σ n)
          else colFor C I U (base U σ n)) = fun p => colFor C I p (base p σ n) := by
        funext p; cases p <;> rfl
      rw [hfun] at hd
      exact of_decide_eq_true hd

open Classical in
/-- **The family splits.**  A task colouring exists exactly when there is one assignment of root
colours, depending only on a process and its own input, at which every instance is solvable. -/
theorem exists_taskColouring_iff {adv : Set (ℕ → Event Bool)} {T : Task Bool V O}
    [∀ I o, Decidable (T.allows I o)] [Nonempty V] :
    (∃ C, TaskColouring adv T C) ↔
      ∃ rt : Bool → V → O, ∀ I : Bool → V,
        ∃ D, GenColouring (taskSpec T I) adv (fun p => rt p (I p)) D := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨hi, hf⟩ := taskColouring_iff_family.mp hC
    refine ⟨fun p x => C p x (Classical.arbitrary V) none, fun I => ⟨colFor C I, ?_⟩⟩
    have hroot : (fun p => colFor C I p none)
        = fun p => C p (I p) (Classical.arbitrary V) none := by
      funext p
      exact hi p (I p) (I (!p)) (Classical.arbitrary V)
    rw [← hroot]
    exact hf I
  · rintro ⟨rt, hrt⟩
    choose D hD using hrt
    refine ⟨fun p x y => D (inp p x y) p, taskColouring_iff_family.mpr ⟨?_, ?_⟩⟩
    · intro p x y y'
      have h1 := (hD (inp p x y)).root p
      have h2 := (hD (inp p x y')).root p
      rw [h1, h2, inp_self, inp_self]
    · intro I
      have hcol : colFor (fun p x y => D (inp p x y) p) I = D I := by
        funext p b
        show D (inp p (I p) (I (!p))) p b = D I p b
        rw [inp_eq]
      rw [hcol]
      have hroot : (fun p => D I p none) = fun p => rt p (I p) := funext (hD I).root
      rw [hroot]
      exact hD I

/-- The family, read by the automaton. -/
theorem exists_taskColouring_iff_aut (A : Adv AdvQ) (T : Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] [Nonempty V] :
    (∃ C, TaskColouring (advOf A) T C) ↔
      ∃ rt : Bool → V → O, ∀ I : Bool → V,
        AutSolvableAt (taskSpec T I) A (fun p => rt p (I p)) :=
  exists_taskColouring_iff.trans
    (exists_congr fun rt => forall_congr' fun I => (autSolvableAt_iff _ _ _).symm)

/-- **The labelling problem for a finite task is decidable.** -/
def decidableTaskColouringAdv (A : Adv AdvQ) (T : Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] [Nonempty V] :
    Decidable (∃ C, TaskColouring (advOf A) T C) :=
  decidable_of_iff _ (exists_taskColouring_iff_aut A T).symm

/-- **Every finite decision task for two processes is decidable** against an ω-regular adversary,
by an algorithm and with no appeal to Rabin's theorem. -/
def decidableSolvesTaskAdv (A : Adv AdvQ) (T : Task Bool V O)
    [∀ I o, Decidable (T.allows I o)] [Nonempty V] [Nonempty O] :
    Decidable (∃ (St : Type) (A' : Algorithm Bool V St) (out : Bool → St → Option O),
      A'.SolvesTask out T (advOf A)) :=
  letI := decidableTaskColouringAdv A T
  decidable_of_iff _ (solvesTask_iff_taskColouring (V := V) (O := O)).symm

end DistributedSynthesis.DecisionTasks.Source
