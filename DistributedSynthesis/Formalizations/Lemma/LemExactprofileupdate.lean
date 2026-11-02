/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefProfiles

/-!
# Exactness of locally uniform profile update
-/

namespace DistributedSynthesis

universe u v w x y

/--
Lemma `lem:exactprofileupdate`, soundness direction: a locally uniform action
updates every represented counterfactual history by the displayed transition.
-/
theorem exact_profile_update_sound
    {Hist : Type u} {View₁ : Type v} {View₂ : Type w}
    {State : Type x} {Out₁ : Type y} {Out₂ : Type y}
    (problem : ExactProfileUpdateProblem Hist View₁ View₂ State Out₁ Out₂)
    (action : LocallyUniformAction View₁ View₂ Out₁ Out₂)
    (h : Hist) :
    exactProfileUpdate problem action h =
      problem.transition h (action.act₁ (problem.view₁ h)) (action.act₂ (problem.view₂ h)) := by
  rfl

/--
Completeness direction: every pair of local-view output functions is already a
locally uniform action on the represented finite counterfactual set.
-/
theorem exact_profile_update_complete
    {View₁ : Type v} {View₂ : Type w} {Out₁ : Type y} {Out₂ : Type y}
    (act₁ : View₁ -> Out₁)
    (act₂ : View₂ -> Out₂) :
    Nonempty (LocallyUniformAction View₁ View₂ Out₁ Out₂) := by
  exact ⟨{ act₁ := act₁, act₂ := act₂ }⟩

end DistributedSynthesis
