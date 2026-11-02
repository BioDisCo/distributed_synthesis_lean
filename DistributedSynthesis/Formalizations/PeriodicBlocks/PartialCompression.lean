/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockScenarios

/-! Compression when only some source roots reach the chosen component.
Repeated roots are allowed, as needed to store a smaller family in a fixed
number of slots. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

theorem finite_retraction {T : Type} [Finite T] [Nonempty T] (B : Nat)
    (bound : Nat.card T ≤ B+1) :
    ∃ keep : BlockSlots B → T, ∃ encode : T → BlockSlots B, ∀ t, keep (encode t) = t := by
  classical
  letI := Fintype.ofFinite T
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := T) (β := BlockSlots B)
    (by simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using bound)
  exact ⟨Function.invFun e, e, Function.leftInverse_invFun e.injective⟩

theorem partial_representative_views {I₁ I₂ R G Q W O Z : Type} {Rank : Type*}
    [LinearOrder Rank] [WellFoundedLT Rank]
    (key : R → BlockType G Q W O Z) (rank : R → Rank)
    (root : R → EnvHistory I₁ I₂)
    (rootEqual : ∀ i j, root i = root j → key i = key j)
    (leader : Proc)
    (common : ∀ i j, (∃ z, (key i).suffixes z = true) → (∃ z, (key j).suffixes z = true) →
      currentView leader (root i) = currentView leader (root j))
    (i j : R) (a b : Z) (insideI : (key i).suffixes a = true) (insideJ : (key j).suffixes b = true)
    (u v : EnvHistory I₁ I₂) (lengths : List.length u = List.length v)
    (p : Proc) (same : currentView p (root i++u) = currentView p (root j++v)) :
    currentView p (root (representative key rank i)++u) =
      currentView p (root (representative key rank j)++v) := by
  apply append_preserves_views _ _ _ _ _ u v lengths p same
  intro q eq
  by_cases isLeader : q = leader
  · subst q
    exact common _ _ ⟨a,(representative_suffixes key rank i a).trans insideI⟩
      ⟨b,(representative_suffixes key rank j b).trans insideJ⟩
  · have leaders := common i j ⟨a,insideI⟩ ⟨b,insideJ⟩
    have sameRoot : root i = root j := by
      cases q <;> cases leader
      · exact False.elim (isLeader rfl)
      · exact joint_env_history _ _ eq leaders
      · exact joint_env_history _ _ leaders eq
      · exact False.elim (isLeader rfl)
    rw [representative_eq key rank (rootEqual i j sameRoot)]

/-- The exact rank-minimal fold can be encoded in a fixed slot set. The
remaining slots are filled by repeated retained endpoints. -/
theorem retained_response {R G Q W O Z : Type} {Rank : Type*}
    [LinearOrder Rank] [WellFoundedLT Rank]
    [Finite G] [Finite Q] [Finite W] [Finite O] [Finite Z]
    (key : R → BlockType G Q W O Z) (rank : R → Rank) (B : Nat)
    (bound : Nat.card (BlockType G Q W O Z) * Nat.card Z ≤ B+1)
    (existsEndpoint : ∃ i z, (key i).suffixes z = true) :
    ∃ keep : BlockSlots B → R × Z, ∃ fold : R × Z → BlockSlots B,
      (∀ j, (key (keep j).1).suffixes (keep j).2 = true) ∧
      ∀ i z, (key i).suffixes z = true → keep (fold (i,z)) = (representative key rank i,z) := by
  classical
  obtain ⟨finite,size⟩ := retained_endpoint_bound key rank
  letI := finite
  haveI : Nonempty (RetainedEndpoints key rank) := by
    obtain ⟨i,z,inside⟩ := existsEndpoint
    exact ⟨foldEndpoint key rank i z inside⟩
  obtain ⟨keep,encode,inverse⟩ := finite_retraction B (size.trans bound)
  let fold (x : R × Z) : BlockSlots B :=
    if inside : (key x.1).suffixes x.2 = true then encode (foldEndpoint key rank x.1 x.2 inside) else 0
  refine ⟨fun j => (keep j).val, fold, fun j => (keep j).property.1, ?_⟩
  intro i z inside
  simp only [fold, dif_pos inside, inverse, foldEndpoint]

end
end Characterisation.PeriodicBlocks
