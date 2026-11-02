/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.Compression

/-! Retained endpoints have a bounded exact observation interface. The fold
itself is a function of each process's view. This does not claim that the
original input-dependent component has bounded cardinality. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

def RetainedEndpoints {R G Q W O Z Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
    (typeOf : R → BlockType G Q W O Z) (rank : R → Rank) :=
  {x : R × Z // (typeOf x.1).suffixes x.2 = true ∧ representative typeOf rank x.1 = x.1}

theorem retained_endpoint_bound {R G Q W O Z Rank : Type*}
    [LinearOrder Rank] [WellFoundedLT Rank]
    [Finite G] [Finite Q] [Finite W] [Finite O] [Finite Z]
    (typeOf : R → BlockType G Q W O Z) (rank : R → Rank) :
    Finite (RetainedEndpoints typeOf rank) ∧
      Nat.card (RetainedEndpoints typeOf rank) ≤ Nat.card (BlockType G Q W O Z) * Nat.card Z := by
  obtain ⟨finite, bound⟩ := endpoint_bound (Z := Z) typeOf rank
  letI := finite
  let embed : RetainedEndpoints typeOf rank →
      {x : R × Z // representative typeOf rank x.1 = x.1} :=
    fun x => ⟨x.val, x.property.2⟩
  have injective : Function.Injective embed := by
    intro x y eq
    apply Subtype.ext
    exact congrArg (fun x : {x : R × Z // representative typeOf rank x.1 = x.1} => x.val) eq
  exact ⟨Finite.of_injective embed injective,
    le_trans (Nat.card_le_card_of_injective embed injective) bound⟩

/-- Every original endpoint in the component folds to a retained endpoint
of that same component. -/
def foldEndpoint {R G Q W O Z Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
    (typeOf : R → BlockType G Q W O Z) (rank : R → Rank)
    (i : R) (z : Z) (inside : (typeOf i).suffixes z = true) : RetainedEndpoints typeOf rank :=
  ⟨(representative typeOf rank i, z),
    (representative_suffixes typeOf rank i z).trans inside,
    representative_idempotent typeOf rank i⟩

/-- Renumbering the retained endpoints gives exactly their two local-view
relations and annotations, in a fixed finite domain. -/
theorem retained_finite_interface {I₁ I₂ R G Q W O Z Rank Label : Type*}
    [LinearOrder Rank] [WellFoundedLT Rank]
    [Finite G] [Finite Q] [Finite W] [Finite O] [Finite Z]
    (typeOf : R → BlockType G Q W O Z) (rank : R → Rank)
    (root : R → EnvHistory I₁ I₂) (suffix : Z → EnvHistory I₁ I₂)
    (label : RetainedEndpoints typeOf rank → Label) :
    ∃ summary : SwitchInterface Label (Nat.card (BlockType G Q W O Z) * Nat.card Z),
      ∃ e : Fin summary.1.val ≃ RetainedEndpoints typeOf rank,
        RepresentsInputShape (fun i => root (e i).val.1 ++ suffix (e i).val.2) summary.2.1 ∧
        ∀ i, summary.2.2 i = label (e i) := by
  obtain ⟨finite, bound⟩ := retained_endpoint_bound typeOf rank
  letI := finite
  exact finite_switch_interface _ bound (fun x => root x.val.1 ++ suffix x.val.2) label

/-- Each process can apply the semantic fold to its own view. No root index
or information from the other process is supplied as an extra observation. -/
theorem representative_local_maps {I₁ I₂ R G Q W O Z Rank : Type*}
    [LinearOrder Rank] [WellFoundedLT Rank]
    (typeOf : R → BlockType G Q W O Z) (rank : R → Rank)
    (root : R → EnvHistory I₁ I₂) (injective : Function.Injective root)
    (leader : Proc) (common : ∀ i j, currentView leader (root i) = currentView leader (root j))
    (D : Nat) (suffix : Z → EnvHistory I₁ I₂) (lengths : ∀ z, List.length (suffix z) = D) :
    ∃ localMap : (p : Proc) → View I₁ I₂ p → View I₁ I₂ p,
      ∀ p i z, localMap p (currentView p (root i ++ suffix z)) =
        currentView p (root (representative typeOf rank i) ++ suffix z) := by
  let oldView p (x : R × Z) := currentView p (root x.1 ++ suffix x.2)
  let newView p (x : R × Z) := currentView p (root (representative typeOf rank x.1) ++ suffix x.2)
  refine ⟨fun p => Function.extend (oldView p) (newView p) (fun _ => .empty p), ?_⟩
  intro p i z
  apply Function.FactorsThrough.extend_apply (f := oldView p) (g := newView p) (a := (i,z))
  intro x y eq
  exact representative_views typeOf rank root injective leader common x.1 y.1
    (suffix x.2) (suffix y.2) ((lengths x.2).trans (lengths y.2).symm) p eq

end
end Characterisation.PeriodicBlocks
