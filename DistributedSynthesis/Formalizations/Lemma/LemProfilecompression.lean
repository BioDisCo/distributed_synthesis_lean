/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Definition.DefProfiles

/-!
# Finite profile compression
-/

namespace DistributedSynthesis

universe u v

/--
Lemma `lem:profilecompression`: deterministic future behavior under closed
graph uncertainty is represented by the finite set of possible current states,
with the displayed one-step update.
-/
theorem finite_profile_compression
    {State : Type u} {Alphabet : Type v}
    [Fintype State]
    (delta : State -> Alphabet -> State)
    (letterOfGraph : Graph -> Alphabet)
    (profile : AutomatonGraphProfile State) :
    Nonempty (Fintype State) ∧
      (AutomatonGraphProfile.step delta letterOfGraph profile).possible =
        { state' | ∃ state graph, state ∈ profile.possible ∧
          state' = delta state (letterOfGraph graph) } := by
  exact ⟨⟨inferInstance⟩, rfl⟩

end DistributedSynthesis
