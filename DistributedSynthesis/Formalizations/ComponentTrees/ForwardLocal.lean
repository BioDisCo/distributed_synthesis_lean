/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.TreeCoverage

/-! Subset and state-label invariants in the forward tree construction.
Restrict the original rule to the reduction image. A full compressed child
is contained in a full original child, with exactly its original labels.
-/
namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D bound : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]

/-- Literal inclusion of histories, with their original states. -/
structure PositionInclusion (P R : Position I₁ I₂ B.State D) where
  histories : P.histories ⊆ R.histories
  phase : P.phase = R.phase
  states : ∀ h : P.Root, P.state h = R.state ⟨h.val, histories h.property⟩

namespace PositionInclusion
variable {B M} {P R S : Position I₁ I₂ B.State D}
def edge (i : PositionInclusion B P R) (h : P.Root) : R.Root := ⟨h.val, i.histories h.property⟩
def map (i : PositionInclusion B P R) : ViewComplexMap P.past R.past :=
  ViewComplexMap.ofEdge i.edge (fun _ _ _ same => same)
def identity (P : Position I₁ I₂ B.State D) : PositionInclusion B P P := ⟨fun _ h => h, rfl, fun _ => rfl⟩
def castTarget (i : PositionInclusion B P R) (eq : R = S) : PositionInclusion B P S := eq ▸ i
end PositionInclusion

variable (U : UncompressedNode B M) (P : Position I₁ I₂ B.State D)
variable (valid : PositionValid B M P) (r : Reduction P.past P.state)
variable (small : (r.imagePosition P).histories.card ≤ bound) (inc : PositionInclusion B P U.position)

def imageInclusion : PositionInclusion B (r.imagePosition P) U.position where
  histories := fun _ h => inc.histories (r.imageHistories_subset P h)
  phase := inc.phase
  states h := inc.states (r.imageInclusion P h)

def restrictNode : CompressedNode B M bound where
  position := P
  valid := valid
  reduction := r
  small := small
  rule := restrictClosingPolicy (imageInclusion B M U P r inc).edge U.rule
  distributed := simulation_rule_coherent (r.imagePosition P).past U.position.past
    (imageInclusion B M U P r inc).edge (fun _ _ _ same => same) U.rule U.distributed

/-- The endpoint map is literal inclusion, including the full D-letter suffix. -/
theorem inclusion_endpoint_history (e : (r.imagePosition P).End) :
    U.position.history (mapClosingLayer (imageInclusion B M U P r inc).edge D e) =
      (r.imagePosition P).history e := by
  rw [Position.history, ← closingLayerHistory_map]
  rfl

theorem inclusion_endpoint_state (e : (r.imagePosition P).End) :
    blockSuccessor B (r.imagePosition P).state (restrictNode B M U P valid r small inc).rule e =
      blockSuccessor B U.position.state U.rule (mapClosingLayer (imageInclusion B M U P r inc).edge D e) :=
  (copied_block_rule (r.imagePosition P).past U.position.past (imageInclusion B M U P r inc).edge
    (fun _ _ _ same => same) B (r.imagePosition P).state U.position.state
    (imageInclusion B M U P r inc).states U.rule U.distributed).2 e

omit U P valid r small inc in
/-- A view-preserving endpoint map sends a connected live component into
one target component. This allows several source components per target. -/
theorem component_image (m t : Move I₁ I₂ O₁ O₂ B.State D)
    (C : Finset m.source.End) (component : IsComponent M m C)
    (F : m.source.End → t.source.End)
    (alive : ∀ e ∈ C, extensionLive M t (F e) = true)
    (views : ∀ p e f, currentView p (m.source.history e) = currentView p (m.source.history f) →
      currentView p (t.source.history (F e)) = currentView p (t.source.history (F f))) :
    ∃ L : Finset t.source.End, IsComponent M t L ∧ ∀ e ∈ C, F e ∈ L := by
  obtain ⟨a, ha⟩ := component_nonempty M m C component
  let graph := closingObservationGraph (closingLayerShape t.source.shape D) (extensionLive M t)
  have mapEdge (e f : C)
      (same : ∃ p, currentView p (m.source.history e.val) = currentView p (m.source.history f.val)) :
      graph.Reachable (F e.val) (F f.val) := by
    by_cases eq : F e.val = F f.val
    · rw [eq]
    apply SimpleGraph.Adj.reachable
    refine ⟨eq, alive e.val e.property, alive f.val f.property, ?_⟩
    obtain ⟨p, same⟩ := same
    exact ⟨p, Or.inl ((closingLayerShape_exact t.source.past _
      (extractInputShape_exact t.source.past) D p _ _).mpr (views p e.val f.val same))⟩
  have reach (e : C) : graph.Reachable (F a) (F e.val) := by
    have path := component_connected M m C component ⟨a, ha⟩ e
    induction path with
    | refl => exact SimpleGraph.Reachable.refl _
    | @tail b c _ edge ih => exact ih.trans (mapEdge b c edge)
  let L := Finset.univ.filter (fun e => closingComponentMask
    (closingLayerShape t.source.shape D) (extensionLive M t) (F a) e = true)
  refine ⟨L, ⟨F a, alive a ha, fun e => by simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]⟩, ?_⟩
  intro e he
  simp only [L, Finset.mem_filter, Finset.mem_univ, true_and,
    closingComponentMask, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨alive e he, reach ⟨e, he⟩⟩

/-- The subset/state invariant propagates to every full compressed child. -/
theorem inclusion_next (R : Position I₁ I₂ B.State D)
    (next : (restrictNode B M U P valid r small inc).Successor R) :
    ∃ S, U.Successor S ∧ Nonempty (PositionInclusion B R S) := by
  let N := restrictNode B M U P valid r small inc
  let F : (r.imagePosition P).End → U.position.End := mapClosingLayer (imageInclusion B M U P r inc).edge D
  obtain ⟨C, component, phase, histories, labels⟩ := next
  have equalHist e : U.move.source.history (F e) = N.extensionMove.source.history e :=
    inclusion_endpoint_history B M U P r inc e
  obtain ⟨L, target, inside⟩ := component_image B M N.extensionMove U.move C component F
    (by
      intro e he
      change extensionLive M ⟨U.position, U.rule, id⟩ (F e) = true
      rw [extensionLive_identity]
      exact decide_eq_true (by
        change M.eval (History.graphSequence (U.move.source.history (F e))) ∈ M.accept
        rw [equalHist]
        exact component_alive M N.extensionMove C component ⟨e, he⟩))
    (by intro p e f same; rw [equalHist, equalHist]; exact same)
  obtain ⟨S, targetPhase, targetHistories, _, targetLabels⟩ := component_position M B U.move L U.valid target
  have subset : R.histories ⊆ S.histories := by
    rw [histories, targetHistories]
    intro h hh
    obtain ⟨e, he, eq⟩ := Finset.mem_image.mp hh
    exact Finset.mem_image.mpr ⟨F e, inside e he, (equalHist e).trans eq⟩
  refine ⟨S, ⟨L, target, targetPhase, targetHistories, targetLabels⟩, ⟨⟨subset, ?_, ?_⟩⟩⟩
  · rw [phase, targetPhase]
    exact congrArg (· + 1) inc.phase
  · intro h
    have mem : h.val ∈ C.image N.extensionMove.source.history := by rw [← histories]; exact h.property
    obtain ⟨e, he, eq⟩ := Finset.mem_image.mp mem
    rw [labels h ⟨e, he⟩ eq.symm,
      targetLabels ⟨h.val, subset h.property⟩ ⟨F e, inside e he⟩ ((equalHist e).trans eq).symm]
    exact inclusion_endpoint_state B M U P valid r small inc e

end
end Characterisation.ComponentTrees
