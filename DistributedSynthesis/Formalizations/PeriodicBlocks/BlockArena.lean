/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.CompressionTheorem
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingComponents
import DistributedSynthesis.Library.Distributed.LeaderPhases.SupportedPublicTree

/-! The finite moves of the periodic-block game. A move specifies the output
policy and, for each possible ending component, a view-preserving map into a
bounded family of retained endpoints. All guards are finite checks. -/

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxSynthPendingDepth 16

abbrev BlockSlots (B : Nat) := Fin (B+1)

structure BlockBoundary (G Q : Type) (B : Nat) where
  shape : InputShape (BlockSlots B)
  graph : BlockSlots B → G
  objective : BlockSlots B → Q
  deriving Fintype, DecidableEq

abbrev BlockEnd (I₁ I₂ : Type) (B D : Nat) := ClosingLayer (BlockSlots B) I₁ I₂ D
abbrev ComponentMask (I₁ I₂ : Type) (B D : Nat) := BlockEnd I₁ I₂ B D → Bool

/-- `keep` lists the target family, allowing duplicate entries. `fold` maps
every possible endpoint to a target slot. Only endpoints in the selected
component impose obligations. -/
structure BlockResponse (I₁ I₂ : Type) (B D : Nat) where
  keep : BlockSlots B → BlockEnd I₁ I₂ B D
  fold : BlockEnd I₁ I₂ B D → BlockSlots B

structure BlockMove (I₁ I₂ O₁ O₂ G Q : Type) (B D : Nat) where
  source : BlockBoundary G Q B
  policy : ClosingPolicy (BlockSlots B) I₁ I₂ O₁ O₂ D
  response : ComponentMask I₁ I₂ B D → BlockResponse I₁ I₂ B D

structure BlockOutcome (I₁ I₂ G Q : Type) (B D : Nat) where
  component : ComponentMask I₁ I₂ B D
  target : BlockBoundary G Q B

section Instances
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
instance : Fintype (BlockResponse I₁ I₂ B D) :=
  Fintype.ofEquiv ((BlockSlots B → BlockEnd I₁ I₂ B D) × (BlockEnd I₁ I₂ B D → BlockSlots B))
    { toFun := fun t => ⟨t.1,t.2⟩
      invFun := fun t => (t.keep,t.fold)
      left_inv := fun _ => rfl
      right_inv := by intro t; cases t; rfl }
instance : DecidableEq (BlockResponse I₁ I₂ B D) := by
  intro a b
  apply decidable_of_iff ((a.keep,a.fold) = (b.keep,b.fold))
  cases a; cases b
  simp only [Prod.mk.injEq, BlockResponse.mk.injEq]
variable [Fintype O₁] [Fintype O₂] [Fintype G] [Fintype Q]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq G] [DecidableEq Q]
instance : Fintype (BlockMove I₁ I₂ O₁ O₂ G Q B D) :=
  Fintype.ofEquiv (BlockBoundary G Q B × ClosingPolicy (BlockSlots B) I₁ I₂ O₁ O₂ D ×
      (ComponentMask I₁ I₂ B D → BlockResponse I₁ I₂ B D))
    { toFun := fun t => ⟨t.1,t.2.1,t.2.2⟩
      invFun := fun t => (t.source,t.policy,t.response)
      left_inv := fun _ => rfl
      right_inv := by intro t; cases t; rfl }
instance : DecidableEq (BlockMove I₁ I₂ O₁ O₂ G Q B D) := by
  intro a b
  letI : DecidableEq (ClosingPolicy (BlockSlots B) I₁ I₂ O₁ O₂ D) := by
    unfold ClosingPolicy
    infer_instance
  apply decidable_of_iff ((a.source,a.policy,a.response) = (b.source,b.policy,b.response))
  cases a; cases b
  simp only [Prod.mk.injEq, BlockMove.mk.injEq]
instance : Fintype (BlockOutcome I₁ I₂ G Q B D) :=
  Fintype.ofEquiv (ComponentMask I₁ I₂ B D × BlockBoundary G Q B)
    { toFun := fun t => ⟨t.1,t.2⟩
      invFun := fun t => (t.component,t.target)
      left_inv := fun _ => rfl
      right_inv := by intro t; cases t; rfl }
instance : DecidableEq (BlockOutcome I₁ I₂ G Q B D) := by
  intro a b
  apply decidable_of_iff ((a.component,a.target) = (b.component,b.target))
  cases a; cases b
  simp only [Prod.mk.injEq, BlockOutcome.mk.injEq]
end Instances

section Computation
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D : Nat}
variable [Fintype I₁] [Fintype I₂]
variable [DecidableEq I₁] [DecidableEq I₂]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)

def blockEndShape (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    InputShape (BlockEnd I₁ I₂ B D) := closingLayerShape move.source.shape D

def blockEndGraph (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    BlockEnd I₁ I₂ B D → G :=
  closingLayerLabels (fun q e _ => M.step q e.2.2) move.source.graph move.policy D (Nat.le_refl _)

def blockEndObjective (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    BlockEnd I₁ I₂ B D → Q :=
  closingLayerLabels step move.source.objective move.policy D (Nat.le_refl _)

def blockEndLive (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    BlockEnd I₁ I₂ B D → Bool := fun e => decide (blockEndGraph M move e ∈ M.accept)

def blockComponent (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (e : BlockEnd I₁ I₂ B D) : ComponentMask I₁ I₂ B D :=
  closingComponentMask (blockEndShape move) (blockEndLive M move) e

def blockTarget (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (mask : ComponentMask I₁ I₂ B D) : BlockBoundary G Q B :=
  let keep := (move.response mask).keep
  ⟨restrictInputShape (blockEndShape move) keep,
    blockEndGraph M move ∘ keep, blockEndObjective step move ∘ keep⟩

def ResponseChecks (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (mask : ComponentMask I₁ I₂ B D) (response : BlockResponse I₁ I₂ B D) : Prop :=
  (∀ j, mask (response.keep j) = true) ∧
  (∀ p e f, mask e = true → mask f = true → blockEndShape move p e f = true →
    blockEndShape move p (response.keep (response.fold e)) (response.keep (response.fold f)) = true) ∧
  (∀ e, mask e = true → blockEndGraph M move (response.keep (response.fold e)) = blockEndGraph M move e ∧
    blockEndObjective step move (response.keep (response.fold e)) = blockEndObjective step move e)

def ResponseValid (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (mask : ComponentMask I₁ I₂ B D) : Prop :=
  ResponseChecks M step move mask (move.response mask)

def BlockMoveValid (boundary : BlockBoundary G Q B)
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) : Prop :=
  move.source = boundary ∧ ClosingPolicyCoherent move.source.shape move.policy ∧
    ∀ e, blockEndLive M move e = true → ResponseValid M step move (blockComponent M move e)

instance responseValid_decidable [DecidableEq G] [DecidableEq Q]
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) (mask : ComponentMask I₁ I₂ B D) :
    Decidable (ResponseValid M step move mask) := by
  unfold ResponseValid ResponseChecks
  infer_instance

instance blockMoveValid_decidable [DecidableEq G] [DecidableEq Q]
    [DecidableEq O₁] [DecidableEq O₂]
    (boundary : BlockBoundary G Q B) (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) :
    Decidable (BlockMoveValid M step boundary move) := by
  unfold BlockMoveValid
  infer_instance

def blockOffers [DecidableEq G] [DecidableEq Q]
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (outcome : BlockOutcome I₁ I₂ G Q B D) : Bool :=
  decide (outcome.target = blockTarget M step move outcome.component ∧
    ∃ e, blockEndLive M move e = true ∧ outcome.component = blockComponent M move e)

def actualBlockOutcome (move : BlockMove I₁ I₂ O₁ O₂ G Q B D)
    (e : BlockEnd I₁ I₂ B D) : BlockOutcome I₁ I₂ G Q B D :=
  let mask := blockComponent M move e
  ⟨mask, blockTarget M step move mask⟩

theorem actualBlockOutcome_offered [DecidableEq G] [DecidableEq Q]
    (move : BlockMove I₁ I₂ O₁ O₂ G Q B D) (e : BlockEnd I₁ I₂ B D)
    (live : blockEndLive M move e = true) :
    blockOffers M step move (actualBlockOutcome M step move e) = true := by
  simp only [blockOffers, decide_eq_true_eq, actualBlockOutcome]
  exact ⟨True.intro, e, live, rfl⟩

end Computation
end Characterisation.PeriodicBlocks
