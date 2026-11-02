/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentTrees.Nodes
import DistributedSynthesis.Formalizations.ComponentGames.ExecutableHistories

/-! Finite position data and exact reduction/transition transport for the
MSO encoding. Reuses the existing finite representation and isomorphism types.
The graph-recognizer coordinate is already in the block state, so its separate
slot in the reused representation is Unit.
-/
namespace Characterisation.ComponentTrees.FinitePositions
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames
open scoped Characterisation.ComponentGames.Representation DistributedSynthesis.FiniteOrders
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {H J I₁ I₂ O₁ O₂ Q : Type} {D : Nat}

abbrev Position (Q : Type) (bound : Nat) := Representation.Position Unit Q bound

def historyData [DecidableEq I₁] [DecidableEq I₂]
    (P : HistoryGame.Position I₁ I₂ Q D) : Representation.Data P.Root Unit Q :=
  ⟨ExecutableHistories.shape P.past, fun _ => (), P.state⟩

/-- Exactly owner-preservation, idempotence, state preservation, and the
image bound. No endpoint-table choice or intermediate-state test is added. -/
def ReductionChecks [Fintype H] [DecidableEq H]
    (a : Representation.Data H Unit Q) (bound : Nat) (r : H → H) : Prop :=
  (∀ p h k, a.shape p h k = true → a.shape p (r h) (r k) = true) ∧
  (∀ h, r (r h) = r h) ∧ (∀ h, a.state (r h) = a.state h) ∧
  (Finset.univ.image r).card ≤ bound

instance reductionChecksDecidable [Fintype H] [DecidableEq H] [DecidableEq Q]
    (a : Representation.Data H Unit Q) (bound : Nat) (r : H → H) :
    Decidable (ReductionChecks a bound r) := by
  unfold ReductionChecks
  infer_instance

theorem reductionChecks_transport [Fintype H] [Fintype J] [DecidableEq H] [DecidableEq J]
    (a : Representation.Data H Unit Q) (b : Representation.Data J Unit Q)
    (e : Representation.Iso a b) (bound : Nat) (r : H → H) :
    ReductionChecks b bound (Representation.replacement e.toEquiv r) ↔ ReductionChecks a bound r := by
  constructor
  · rintro ⟨views,idem,states,small⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro p h k same
      have mapped := views p (e.toEquiv h) (e.toEquiv k) (by simpa only [e.shape_same] using same)
      simpa only [Representation.replacement_apply,e.shape_same] using mapped
    · intro h
      apply e.toEquiv.injective
      simpa only [Representation.replacement_apply] using idem (e.toEquiv h)
    · intro h
      simpa only [Representation.replacement_apply,e.state_same] using states (e.toEquiv h)
    · simpa only [Representation.replacement_image_card] using small
  · rintro ⟨views,idem,states,small⟩
    refine ⟨?_,?_,?_,?_⟩
    · intro p j k same
      obtain ⟨h,rfl⟩ := e.toEquiv.surjective j
      obtain ⟨l,rfl⟩ := e.toEquiv.surjective k
      simpa only [Representation.replacement_apply,e.shape_same] using
        views p h l (by simpa only [e.shape_same] using same)
    · intro j
      obtain ⟨h,rfl⟩ := e.toEquiv.surjective j
      simp only [Representation.replacement_apply,idem]
    · intro j
      obtain ⟨h,rfl⟩ := e.toEquiv.surjective j
      simpa only [Representation.replacement_apply,e.state_same] using states h
    · simpa only [Representation.replacement_image_card] using small

/-- The finite tests characterize all reductions of a concrete position. -/
theorem reductionChecks_history [DecidableEq I₁] [DecidableEq I₂]
    (P : HistoryGame.Position I₁ I₂ Q D) (bound : Nat) (r : P.Root → P.Root) :
    ReductionChecks (historyData P) bound r ↔
      ∃ reduction : Reduction P.past P.state, reduction.map.edge = r ∧
        (Finset.univ.image reduction.map.edge).card ≤ bound := by
  classical
  simp only [ReductionChecks,historyData,ExecutableHistories.shape_eq]
  constructor
  · rintro ⟨views,idem,states,small⟩
    let reduction : Reduction P.past P.state := {
      map := ViewComplexMap.ofEdge r (by
        intro p h k same
        exact (extractInputShape_exact P.past p (r h) (r k)).mp
          (views p h k ((extractInputShape_exact P.past p h k).mpr same)))
      idempotent := idem
      states := states }
    exact ⟨reduction,rfl,small⟩
  · rintro ⟨reduction,rfl,small⟩
    refine ⟨?_,reduction.idempotent,reduction.states,small⟩
    intro p h k same
    exact (extractInputShape_exact P.past p _ _).mpr
      (reduction.map.preserves_views p h k ((extractInputShape_exact P.past p h k).mp same))

variable [DecidableEq I₁] [DecidableEq I₂]

theorem ruleBlock_transport (e : H ≃ J) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (s : ClosingLayer H I₁ I₂ D) :
    ruleBlock (Representation.policy e out) (mapClosingLayer e D s) = ruleBlock out s := by
  apply Subtype.ext
  exact (closingLayerTrace_restrict e.symm out D (Nat.le_refl _) _).trans
    (congrArg (closingLayerTrace out D (Nat.le_refl _)) (Representation.mapLayer_inverse e D s))

theorem blockSuccessor_transport
    (B : DetParityAutomaton (BlockWord (ContinuationLetter I₁ I₂ O₁ O₂) D))
    (a : Representation.Data H Unit B.State) (b : Representation.Data J Unit B.State)
    (e : Representation.Iso a b) (out : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (s : ClosingLayer H I₁ I₂ D) :
    blockSuccessor B b.state (Representation.policy e.toEquiv out) (mapClosingLayer e.toEquiv D s) =
      blockSuccessor B a.state out s := by
  simp only [blockSuccessor,closingLayerRoot_map,e.state_same,ruleBlock_transport]

local instance [LinearOrder I₁] [LinearOrder I₂] :
    LinearOrder (RoundRecord I₁ I₂ Graph Unit Unit) :=
  LinearOrder.lift' (envRecordEquiv I₁ I₂).symm (envRecordEquiv I₁ I₂).symm.injective

/-- Finite numbering retains the exact view relations and block-state
labels. This includes every concrete position within the edge bound. -/
def encode [LinearOrder I₁] [LinearOrder I₂] {bound : Nat}
    (P : HistoryGame.Position I₁ I₂ Q D) (small : P.histories.card ≤ bound) : Position Q bound :=
  Representation.pack P.histories small (historyData P)

def encodeIso [LinearOrder I₁] [LinearOrder I₂] {bound : Nat}
    (P : HistoryGame.Position I₁ I₂ Q D) (small : P.histories.card ≤ bound) :
    Representation.Iso (historyData P) (encode P small).2 :=
  Representation.packIso P.histories small (historyData P)

end Characterisation.ComponentTrees.FinitePositions
