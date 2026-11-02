/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.PullFiniteNode
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableIsomorphisms

/-! Reconstruct one entire concrete child from its finite numbering.
The map is a finite bijection preserving all vertices and block states.
-/
namespace Characterisation.ComponentTrees.FiniteDecode
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentTrees.FiniteTransport
open Characterisation.ComponentGames Characterisation.ComponentGames.HistoryGame
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
open scoped Characterisation.ComponentGames.FiniteEnumeration
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {I₁ I₂ O₁ O₂ G : Type} {D capacity : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable [Fintype O₁] [Fintype O₂] [DecidableEq O₁] [DecidableEq O₂]
variable (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
variable [DecidableEq B.State]
variable (M : Recognizer Graph G) [DecidablePred (· ∈ M.accept)]
variable (live : B.State → Bool)
variable (liveCorrect : ∀ h q, StateReachable B h q →
  (live q = true ↔ M.eval (History.graphSequence h) ∈ M.accept))
variable (P : Position I₁ I₂ B.State D) (valid : PositionValid B M P)
variable {bound : Nat}
variable (m : FiniteAlphabet.Move (capacity:=capacity) B)
variable (e : Representation.Iso (FinitePositions.historyData P) m.source.2)
variable (checks : FinitePositions.ReductionChecks m.source.2 bound m.replacement)
variable (c : FiniteAlphabet.Child B m)
variable (correct : FiniteAlphabet.ChildCorrect B live m c)

local notation "r" => pullReduction B P m e checks
local notation "out" => pullRule B P m e

include liveCorrect valid in
theorem component_back_pull (K : Finset m.End) (component : FiniteAlphabet.Component B live m K) :
    IsComponent M (FullExtensions.full B P r out) (K.image (mapClosingLayer e.toEquiv.symm D)) := by
  apply (component_back B M live liveCorrect P valid r out m.source e K ?_).1
  change FiniteAlphabet.Component B live
    ⟨m.source,Representation.policy e.toEquiv (Representation.policy e.toEquiv.symm m.rule),
      Representation.replacement e.toEquiv (Representation.replacement e.toEquiv.symm m.replacement)⟩ K
  have pol := Representation.policy_inverse e.toEquiv.symm m.rule
  have rep := Representation.replacement_inverse e.toEquiv.symm m.replacement
  simp only [Equiv.symm_symm] at pol rep
  rw [pol,rep]
  exact component

def childComponent : Finset P.End :=
  (FiniteAlphabet.childEdges B m c).image (mapClosingLayer e.toEquiv.symm D)

include liveCorrect valid correct in
theorem childComponent_correct : IsComponent M (FullExtensions.full B P r out)
    (childComponent B P m e c) :=
  component_back_pull B M live liveCorrect P valid m e checks _ correct.2.1

def childPosition : Position I₁ I₂ B.State D :=
  ExecutableReverse.componentPosition B M (FullExtensions.full B P r out) (childComponent B P m e c)
    (childComponent_correct B M live liveCorrect P valid m e checks c correct)

theorem childPosition_next : ComponentSuccessor B M (FullExtensions.full B P r out)
    (childPosition B M live liveCorrect P valid m e checks c correct) :=
  ExecutableReverse.componentPosition_successor B M _ _ _

def childHistory (k : c.1.Root) : EnvHistory I₁ I₂ := P.history (mapClosingLayer e.toEquiv.symm D (c.2 k))

theorem childEndpoint_mem (k : c.1.Root) :
    mapClosingLayer e.toEquiv.symm D (c.2 k) ∈ childComponent B P m e c :=
  Finset.mem_image.mpr ⟨c.2 k,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩,rfl⟩

def childRoot (k : c.1.Root) : (childPosition B M live liveCorrect P valid m e checks c correct).Root :=
  ⟨childHistory B P m e c k, Finset.mem_image.mpr ⟨_,childEndpoint_mem B P m e c k,rfl⟩⟩

theorem childRoot_bijective : Function.Bijective (childRoot B M live liveCorrect P valid m e checks c correct) := by
  constructor
  · intro k l eq
    apply correct.1
    apply (Representation.layerEquiv e.toEquiv.symm D).injective
    exact P.history_injective (congrArg Subtype.val eq)
  · intro h
    obtain ⟨s,mem,hs⟩ := Finset.mem_image.mp h.property
    obtain ⟨t,inside,ts⟩ := Finset.mem_image.mp mem
    obtain ⟨k,_,kt⟩ := Finset.mem_image.mp inside
    refine ⟨k,Subtype.ext ?_⟩
    change P.history (mapClosingLayer e.toEquiv.symm D (c.2 k)) = h.val
    rw [kt,ts]
    exact hs

def childEquiv : c.1.Root ≃ (childPosition B M live liveCorrect P valid m e checks c correct).Root :=
  ExecutableHistories.finiteEquiv _ (childRoot_bijective B M live liveCorrect P valid m e checks c correct)

theorem childEquiv_history (k : c.1.Root) :
    (childEquiv B M live liveCorrect P valid m e checks c correct k).val = childHistory B P m e c k := rfl

/-- This is the isomorphism used for the recursive next node, not merely
a state-preserving injection into part of that node. -/
def childIso : Representation.Iso
    (FinitePositions.historyData (childPosition B M live liveCorrect P valid m e checks c correct)) c.1.2 := by
  let f := childEquiv B M live liveCorrect P valid m e checks c correct
  apply Representation.Iso.symm
  refine { toEquiv := f, graph_same := fun _ => rfl, shape_same := ?_, state_same := ?_ }
  · intro p k l
    have eq := Representation.layerShape_map e.toEquiv P.shape m.source.2.shape (root_shapes B P m.source e) D p
      (mapClosingLayer e.toEquiv.symm D (c.2 k)) (mapClosingLayer e.toEquiv.symm D (c.2 l))
    simp only [Representation.mapLayer_inverse'] at eq
    rw [correct.2.2.1 p k l]
    change _ = closingLayerShape m.source.2.shape D p (c.2 k) (c.2 l)
    rw [eq]
    apply Bool.eq_iff_iff.mpr
    simp only [FinitePositions.historyData,ExecutableHistories.shape_eq]
    rw [extractInputShape_exact]
    exact (closingLayerShape_exact P.past P.shape (extractInputShape_exact P.past) D p _ _).symm
  · intro k
    have state := ExecutableReverse.componentPosition_states B M (FullExtensions.full B P r out)
      (childComponent B P m e c) (childComponent_correct B M live liveCorrect P valid m e checks c correct)
      (f k) ⟨_,childEndpoint_mem B P m e c k⟩ rfl
    have mapped := FinitePositions.blockSuccessor_transport B (FinitePositions.historyData P) m.source.2 e out
      (mapClosingLayer e.toEquiv.symm D (c.2 k))
    rw [Representation.mapLayer_inverse'] at mapped
    have rule : Representation.policy e.toEquiv out = m.rule := by
      funext n s
      exact congrArg (m.rule n) (Representation.mapLayer_inverse' e.toEquiv _ s)
    rw [rule] at mapped
    exact state.trans (mapped.symm.trans (correct.2.2.2 k).symm)

/-- Every numbered child edge has its exact concrete history. -/
theorem childIso_history (k : c.1.Root) :
    ((childIso B M live liveCorrect P valid m e checks c correct).toEquiv.symm k).val =
      P.history (mapClosingLayer e.toEquiv.symm D (c.2 k)) := rfl

end Characterisation.ComponentTrees.FiniteDecode
