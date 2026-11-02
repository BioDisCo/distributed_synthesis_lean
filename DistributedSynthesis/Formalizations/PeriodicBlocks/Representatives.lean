/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.ViewFolding
import Mathlib.Order.WellFounded
import Mathlib.SetTheory.Cardinal.Finite

/-! One representative per finite block type, selected by a proof-side rank.
The selection is noncomputable. It is used for completeness, not as the
algorithm that constructs the finite game. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis

section Selection
variable {R T Rank : Type*} [LinearOrder Rank] [WellFoundedLT Rank]
variable (key : R → T) (rank : R → Rank)

/-- Choose a root of least rank among roots with the same block type. -/
noncomputable def representative (i : R) : R :=
  Function.argminOn rank {j | key j = key i} ⟨i, rfl⟩

theorem representative_key (i : R) : key (representative key rank i) = key i :=
  Function.argminOn_mem rank {j | key j = key i} ⟨i, rfl⟩

theorem representative_rank (i : R) : rank (representative key rank i) ≤ rank i :=
  Function.argminOn_le rank {j | key j = key i} (a := i) rfl

theorem representative_eq {i j : R} (same : key i = key j) :
    representative key rank i = representative key rank j := by
  unfold representative
  congr 1
  rw [same]

theorem representative_idempotent (i : R) :
    representative key rank (representative key rank i) = representative key rank i :=
  representative_eq key rank (representative_key key rank i)

/-- The number of retained roots is bounded by the number of block types,
independently of the number of original roots. -/
theorem representative_bound [Finite T] :
    Finite {i : R // representative key rank i = i} ∧
      Nat.card {i : R // representative key rank i = i} ≤ Nat.card T := by
  let code : {i : R // representative key rank i = i} → T := fun i => key i.val
  have inj : Function.Injective code := by
    intro i j same
    apply Subtype.ext
    exact i.property.symm.trans ((representative_eq key rank same).trans j.property)
  exact ⟨Finite.of_injective code inj, Nat.card_le_card_of_injective code inj⟩

/-- A retained endpoint consists of a retained root and an unchanged suffix. -/
theorem endpoint_bound {Z : Type*} [Finite T] [Finite Z] :
    Finite {x : R × Z // representative key rank x.1 = x.1} ∧
      Nat.card {x : R × Z // representative key rank x.1 = x.1} ≤
        Nat.card T * Nat.card Z := by
  let code : {x : R × Z // representative key rank x.1 = x.1} → T × Z :=
    fun x => (key x.val.1, x.val.2)
  have inj : Function.Injective code := by
    intro x y same
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.symm.trans
        ((representative_eq key rank (congrArg Prod.fst same)).trans y.property)
    · exact congrArg (fun x : T × Z => x.2) same
  refine ⟨Finite.of_injective code inj, ?_⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_injective code inj

end Selection

/-- The complete finite data used to group roots for one ending component.
`W` indexes all nonempty prefixes of a block and `Z` its full-length suffixes.
The rule includes the joint output at every prefix, not just the endpoint. -/
structure BlockType (G Q W O Z : Type*) where
  graphState : G
  objectiveState : Q
  rule : W → O
  suffixes : Z → Bool

instance {G Q W O Z : Type*}
    [Fintype G] [Fintype Q] [Fintype W] [Fintype O] [Fintype Z]
    [DecidableEq W] [DecidableEq Z] :
    Fintype (BlockType G Q W O Z) :=
  Fintype.ofEquiv (G × Q × (W → O) × (Z → Bool))
    { toFun := fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
      invFun := fun t => (t.graphState, t.objectiveState, t.rule, t.suffixes)
      left_inv := by intro t; rfl
      right_inv := by intro t; cases t; rfl }

instance {G Q W O Z : Type*}
    [DecidableEq G] [DecidableEq Q] [Fintype W] [DecidableEq O] [Fintype Z] :
    DecidableEq (BlockType G Q W O Z) := by
  intro a b
  apply decidable_of_iff
    ((a.graphState, a.objectiveState, a.rule, a.suffixes) =
      (b.graphState, b.objectiveState, b.rule, b.suffixes))
  cases a; cases b
  simp only [Prod.mk.injEq, BlockType.mk.injEq]

instance {G Q W O Z : Type*} [Finite G] [Finite Q] [Finite W] [Finite O] [Finite Z] :
    Finite (BlockType G Q W O Z) := by
  let encode : BlockType G Q W O Z → G × Q × (W → O) × (Z → Bool) :=
    fun t => (t.graphState, t.objectiveState, t.rule, t.suffixes)
  apply Finite.of_injective encode
  intro a b same
  cases a; cases b
  simpa [encode] using same

section Block
variable {I₁ I₂ R G Q W O Z Rank : Type*}
variable [LinearOrder Rank] [WellFoundedLT Rank]
variable (typeOf : R → BlockType G Q W O Z) (rank : R → Rank)

/-- Including the suffix set in the type makes replacement stay within the
chosen ending component, rather than merely within the live prefix language. -/
theorem representative_suffixes (i : R) (z : Z) :
    (typeOf (representative typeOf rank i)).suffixes z = (typeOf i).suffixes z :=
  congrArg (fun t => t.suffixes z) (representative_key typeOf rank i)

/-- Initial objective states and the entire block rule survive replacement. -/
theorem representative_rule (i : R) :
    (typeOf (representative typeOf rank i)).objectiveState = (typeOf i).objectiveState ∧
    (typeOf (representative typeOf rank i)).rule = (typeOf i).rule := by
  rw [representative_key typeOf rank i]
  exact ⟨rfl, rfl⟩

/-- Folding roots in a common-view family preserves equality of local views
at every round of the block, for arbitrary pairs of equal-length suffixes. -/
theorem representative_views
    (root : R → EnvHistory I₁ I₂) (injective : Function.Injective root)
    (leader : Proc) (common : ∀ i j, currentView leader (root i) = currentView leader (root j))
    (i j : R) (u v : EnvHistory I₁ I₂) (lengths : List.length u = List.length v)
    (p : Proc) (same : currentView p (root i ++ u) = currentView p (root j ++ v)) :
    currentView p (root (representative typeOf rank i) ++ u) =
      currentView p (root (representative typeOf rank j) ++ v) :=
  append_preserves_views _ _ _ _
    (fun q eq => common_view_root_map root injective leader common
      (representative typeOf rank) q i j eq) u v lengths p same

end Block
end Characterisation.PeriodicBlocks
