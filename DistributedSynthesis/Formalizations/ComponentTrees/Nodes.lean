/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.ComponentSteps

/-! Node and step semantics for `main.tex`, `def:tree-component-tree`.
These local definitions do not assert the global bounded-representation or
MSO theorem. Every reduction satisfying the manuscript's conditions is
allowed, including reductions not constructed from endpoint tables.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {I₁ I₂ O₁ O₂ Q G : Type} {D : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]

namespace Reduction
variable (P : Position I₁ I₂ Q D) (r : Reduction P.past P.state)

def imageHistories : Finset (EnvHistory I₁ I₂) :=
  (Finset.univ.image r.map.edge).image Subtype.val

theorem imageHistories_subset : r.imageHistories P ⊆ P.histories := by
  intro h hh
  obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hh
  exact e.property

def imagePosition : Position I₁ I₂ Q D where
  phase := P.phase
  histories := r.imageHistories P
  nonempty := by
    obtain ⟨h, hh⟩ := P.nonempty
    exact ⟨(r.map.edge ⟨h, hh⟩).val, Finset.mem_image.mpr
      ⟨r.map.edge ⟨h, hh⟩, Finset.mem_image.mpr ⟨⟨h, hh⟩, Finset.mem_univ _, rfl⟩, rfl⟩⟩
  lengths := fun h hh => P.lengths h (r.imageHistories_subset P hh)
  state := fun h => P.state ⟨h.val, r.imageHistories_subset P h.property⟩

def imageInclusion : (r.imagePosition P).Root → P.Root :=
  fun h => ⟨h.val, r.imageHistories_subset P h.property⟩

def imageProjection (e : P.Root) : (r.imagePosition P).Root :=
  ⟨(r.map.edge e).val, Finset.mem_image.mpr
    ⟨r.map.edge e, Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, rfl⟩⟩

theorem imageProjection_fixed (e : (r.imagePosition P).Root) :
    r.imageProjection P (r.imageInclusion P e) = e := by
  obtain ⟨f, hf, eq⟩ := Finset.mem_image.mp e.property
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hf
  have incl : r.imageInclusion P e = r.map.edge g := Subtype.ext eq.symm
  apply Subtype.ext
  change (r.map.edge (r.imageInclusion P e)).val = e.val
  rw [incl, r.idempotent]
  exact eq

def imageMap : ViewComplexMap P.past (r.imagePosition P).past :=
  ViewComplexMap.ofEdge (r.imageProjection P) (fun p e f same => r.map.preserves_views p e f same)

theorem imagePosition_card : (r.imagePosition P).histories.card = (Finset.univ.image r.map.edge).card :=
  Finset.card_image_of_injective _ Subtype.val_injective

theorem imageProjection_state (e : P.Root) :
    (r.imagePosition P).state (r.imageProjection P e) = P.state e := r.states e

/-- The unique initial edge forces every root reduction to be the identity. -/
theorem initial_map_identity (q : Q)
    (r : Reduction (Position.initial (I₁ := I₁) (I₂ := I₂) (D := D) q).past
      (Position.initial (D := D) q).state) :
    r.map = ViewComplexMap.identity (Position.initial (D := D) q).past := by
  apply ViewComplexMap.ext
  funext e
  apply Subtype.ext
  exact (Finset.mem_singleton.mp (r.map.edge e).property).trans
    (Finset.mem_singleton.mp e.property).symm

variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G)

/-- Reducing preserves all position conditions, including state reachability.
Reachability uses each retained history's own original witness. -/
theorem imagePosition_valid (P : Position I₁ I₂ B.State D) (r : Reduction P.past P.state)
    (valid : PositionValid B M P) : PositionValid B M (r.imagePosition P) := by
  refine ⟨fun h => valid.1 (r.imageInclusion P h), ?_, fun h => valid.2.2 (r.imageInclusion P h)⟩
  intro h k
  rw [← r.imageProjection_fixed P h, ← r.imageProjection_fixed P k]
  exact Relation.ReflTransGen.lift (r.imageProjection P) (fun e f edge => by
    obtain ⟨p, same⟩ := edge
    exact ⟨p, r.map.preserves_views p e f same⟩)
    (valid.2.1 (r.imageInclusion P h) (r.imageInclusion P k))

end Reduction

variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- Exactly the local node data in the current compressed-tree definition.
The bound is imposed on r(K), not on K. -/
structure CompressedNode (bound : Nat) where
  position : Position I₁ I₂ B.State D
  valid : PositionValid B M position
  reduction : Reduction position.past position.state
  small : (reduction.imagePosition position).histories.card ≤ bound
  rule : ClosingPolicy (reduction.imagePosition position).Root I₁ I₂ O₁ O₂ D
  distributed : ClosingPolicyCoherent (reduction.imagePosition position).shape rule

namespace CompressedNode
variable {B M} {bound : Nat} (N : CompressedNode B M bound)

def extensionMove : Move I₁ I₂ O₁ O₂ B.State D :=
  ⟨N.reduction.imagePosition N.position, N.rule, id⟩

/-- The children are the full connected components of the reduced source's
live extensions. The child's own reduction is applied only at its next step. -/
def Successor (P : Position I₁ I₂ B.State D) : Prop :=
  ∃ C : Finset N.extensionMove.source.End,
    IsComponent M N.extensionMove C ∧
    P.phase = N.position.phase + 1 ∧
    P.histories = C.image N.extensionMove.source.history ∧
    ∀ (h : P.Root) (e : C), h.val = N.extensionMove.source.history e.val →
      P.state h = blockSuccessor B N.extensionMove.source.state N.rule e.val

theorem successor_exists (C : Finset N.extensionMove.source.End)
    (component : IsComponent M N.extensionMove C) :
    ∃ P, N.Successor P ∧ PositionValid B M P := by
  obtain ⟨P, phase, histories, valid, states⟩ := component_position M B N.extensionMove C
    (N.reduction.imagePosition_valid B M N.position N.valid) component
  exact ⟨P, ⟨C, component, phase, histories, states⟩, valid⟩

theorem successor_bound (P : Position I₁ I₂ B.State D) (step : N.Successor P) :
    P.histories.card ≤ bound * Nat.card (RoundRecord I₁ I₂ Graph Unit Unit) ^ D := by
  obtain ⟨C, component, _, histories, _⟩ := step
  rw [histories]
  exact component_position_bound M N.extensionMove C component bound N.small

/-- The exact edge equation in `eq:tree-compatible-run`. -/
def CompatibleStep (P : Position I₁ I₂ B.State D) (e : N.position.Root) (f : P.Root)
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D) : Prop :=
  f.val = (N.reduction.map.edge e).val ++ u.val

/-- A compatible step carries the actual block successor state, with the
original state preserved through the source reduction. -/
theorem compatible_step_state (P : Position I₁ I₂ B.State D) (next : N.Successor P)
    (e : N.position.Root) (f : P.Root)
    (u : BlockWord (RoundRecord I₁ I₂ Graph Unit Unit) D)
    (step : N.CompatibleStep P e f u) :
    P.state f = B.step (N.position.state e)
      (ruleBlock N.rule (wordScenario (N.reduction.imageProjection N.position e) u)) := by
  obtain ⟨C, _, _, histories, states⟩ := next
  have inside : f.val ∈ C.image N.extensionMove.source.history := by rw [← histories]; exact f.property
  obtain ⟨s, hs, eq⟩ := Finset.mem_image.mp inside
  have scenario : s = wordScenario (N.reduction.imageProjection N.position e) u :=
    N.extensionMove.source.history_injective (eq.trans
      (step.trans (wordScenario_history N.extensionMove.source.past (N.reduction.imageProjection N.position e) u).symm))
  rw [states f ⟨s, hs⟩ eq.symm]
  change blockSuccessor B N.extensionMove.source.state N.rule s = _
  rw [scenario]
  unfold blockSuccessor
  apply congrArg (fun q => B.step q (ruleBlock N.rule _))
  exact (congrArg N.extensionMove.source.state
    (wordScenario_root (I₁ := I₁) (I₂ := I₂) (N.reduction.imageProjection N.position e) u)).trans
    (N.reduction.imageProjection_state N.position e)

/-- Reverse-proof local simulation: first compose with r, then copy the
rule from r(K). There is no target-child fold in this block. -/
theorem copied_rule {H : Type} (past : H → EnvHistory I₁ I₂)
    (T : ViewComplexMap past N.position.past) (state : H → B.State)
    (states : ∀ h, state h = N.position.state (T.edge h)) :
    ClosingPolicyCoherent (extractInputShape past)
      (restrictClosingPolicy (N.reduction.imageProjection N.position ∘ T.edge) N.rule) ∧
    ∀ s : ClosingLayer H I₁ I₂ D,
      blockSuccessor B state
        (restrictClosingPolicy (N.reduction.imageProjection N.position ∘ T.edge) N.rule) s =
      blockSuccessor B N.extensionMove.source.state N.rule
        (mapClosingLayer (N.reduction.imageProjection N.position ∘ T.edge) D s) := by
  let composed := (N.reduction.imageMap N.position).comp T
  exact copied_block_rule past N.extensionMove.source.past composed.edge
    composed.preserves_views B state N.extensionMove.source.state
    (fun h => (states h).trans (N.reduction.imageProjection_state N.position (T.edge h)).symm)
    N.rule N.distributed

end CompressedNode
end
end Characterisation.ComponentTrees
