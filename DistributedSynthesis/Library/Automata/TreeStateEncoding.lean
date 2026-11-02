/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeProjection

/-! # State numberings preserve parity-tree languages -/
namespace DistributedSynthesis.RunParityTreeAutomaton

variable {Branch Alphabet : Type*}
variable (A B : RunParityTreeAutomaton Branch Alphabet) (e : A.State ≃ B.State)
variable (initial : e A.initial = B.initial)
variable (priority : ∀ q, B.priority (e q) = A.priority q)
variable (transition : ∀ q a next, B.delta (e q) a (e ∘ next) ↔ A.delta q a next)

include initial priority transition in
theorem acceptsTree_iff_of_equiv (tree : LabeledTree Branch Alphabet) :
    B.acceptsTree tree ↔ A.acceptsTree tree := by
  constructor
  · rintro ⟨run, ⟨hinit, hstep⟩, hparity⟩
    refine ⟨e.symm ∘ run, ⟨?_, ?_⟩, ?_⟩
    · change e.symm (run []) = A.initial
      rw [hinit, ← initial, Equiv.symm_apply_apply]
    · intro node
      apply (transition (e.symm (run node)) (tree node) (fun b => e.symm (run (node ++ [b])))).mp
      simpa only [Function.comp_def, Equiv.apply_symm_apply] using hstep node
    · intro branch
      have h := hparity branch
      have heq : (fun n => B.priority (run (branchNode branch n))) =
          (fun n => A.priority (e.symm (run (branchNode branch n)))) := by
        funext n
        exact (congrArg B.priority (e.apply_symm_apply _)).symm.trans (priority _)
      exact heq ▸ h
  · rintro ⟨run, ⟨hinit, hstep⟩, hparity⟩
    refine ⟨e ∘ run, ⟨?_, ?_⟩, ?_⟩
    · exact (congrArg e hinit).trans initial
    · intro node
      exact (transition (run node) (tree node) (fun b => run (node ++ [b]))).mpr (hstep node)
    · intro branch
      simpa only [Function.comp_apply, priority] using hparity branch

end DistributedSynthesis.RunParityTreeAutomaton
