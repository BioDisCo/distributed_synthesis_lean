/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedClosingCompleteness

/-! An actual pair of consecutive leader boundaries determines its closing
window and a collected complete successor. The caller supplies neither a
scenario witness nor a scheduled-window hypothesis. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {B C K : Nat}
variable [Fintype H] [DecidableEq H] [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (h : EnvHistory I₁ I₂) (live : P (History.graphSequence h))
variable (a : Nat) (phase : ConsecutiveLeaderBoundaries P d h a)
variable (e : H ≃ InputHistoryComponent P (h.take a))
variable (shape : InputShape H)
variable (rep : RepresentsInputShape (boundaryPhaseSources P d h a ∘ e) shape)
variable (active : H → Bool)
variable (activity : SourceActivityOnLive P d a (phaseClosingCut d h a)
  (boundaryPhaseSources P d h a ∘ e) active)
variable (source : H → GraphRootState GQ d K)
variable (sourceExact : ∀ i, GraphRootRep P M
  (History.graphSequence ((boundaryPhaseSources P d h a ∘ e) i)) (source i))
variable (graphBounded : ∀ g, P g → Finite (HistoryComponent P g) ∧ Nat.card (HistoryComponent P g) ≤ K)
variable (small : ∀ k : EnvHistory I₁ I₂, P (History.graphSequence k) → leaderBoundary P d k = true →
  Nat.card (InputHistoryComponent P k) ≤ B)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ (d+1))
variable (coherent : ClosingPolicyCoherent shape expected)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

include closed recognizes recent live phase rep activity sourceExact graphBounded small coherent in
/-- Every physical handover is represented, together with its entire
component, in the finite collector of its canonical closing window. -/
theorem numbered_actual_handover_offer :
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1)),
      n.val+1 = List.length h-phaseClosingCut d h a ∧
      closingLayerHistory ((boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val) (n.val+1) root = h ∧
      move.2.1 = restrictClosingPolicy Subtype.val expected ∧
      ClosingOfferRealizes P ((boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      certificateHandover (slot ∘ Subtype.val) minimum move ∈
        graphClosingOffers M source active shape (decide (List.length (boundaryPhaseWord d h a) = 0))
          step initial expected slot minimum := by
  let u := h.take a
  let word := boundaryPhaseWord d h a
  let past := boundaryPhaseSources P d h a ∘ e
  let L := phaseClosingCut d h a
  have bounds := phaseClosingCut_bounds P d h a phase
  have lenU : List.length u = a := by
    simp only [u,List.length_take,min_eq_left (Nat.le_of_lt phase.start_lt)]
  have lenWord : List.length word = L-a := by
    simp only [word,boundaryPhaseWord,List.length_drop,List.length_take,min_eq_left (Nat.le_of_lt bounds.2.1),L]
  have total : List.length u + List.length word = L := by rw [lenU,lenWord]; dsimp [L]; omega
  have depth : ∀ i, List.length (past i) = L := fun i => boundaryPhaseSources_depth P d h a phase (e i)
  let n : Fin (d+1) := ⟨List.length h-L-1,by dsimp [L]; omega⟩
  have age : n.val+1 = List.length h-L := by dsimp [n,L]; omega
  have rootSlot : ∃ i, (e i).val = u := by
    obtain ⟨i,eq⟩ := e.surjective ⟨u,Relation.ReflTransGen.refl⟩
    exact ⟨i,congrArg Subtype.val eq⟩
  obtain ⟨i,sourceI⟩ := rootSlot
  have prefixI : past i = h.take L := by
    change (e i).val ++ word = h.take L
    rw [sourceI]
    have split := List.take_append_drop a (h.take L)
    rw [List.take_take,min_eq_left bounds.1] at split
    exact split
  obtain ⟨raw,rawHistory⟩ := closingLayer_contains_append past i (n.val+1) (h.drop L)
    (by simp only [History.length,List.length_drop]; exact age.symm)
  rw [prefixI,List.take_append_drop] at rawHistory
  have sourceHistory := closingLayerHistory_take_source past L depth (n.val+1) raw
  rw [rawHistory] at sourceHistory
  have sourceLive : P (History.graphSequence (past (closingLayerRoot (n.val+1) raw))) := by
    rw [← sourceHistory]
    exact live_history_take P closed h live L
  have alive : active (closingLayerRoot (n.val+1) raw) = true := by
    apply (activity _ sourceLive).mpr
    intro m lo hi
    change leaderBoundary P d ((past (closingLayerRoot (n.val+1) raw)).take m) = false
    rw [← sourceHistory,List.take_take,min_eq_left hi]
    exact phase.no_boundary m lo (by omega)
  obtain ⟨root,rootEq⟩ := activeClosingLayer_preimage active (n.val+1) raw alive
  have actual : closingLayerHistory (past ∘ Subtype.val) (n.val+1) root = h := by
    rw [closingLayerHistory_map,rootEq,rawHistory]
  have scheduled : closingWindowScheduled (decide (List.length word = 0)) (d+1) (n.val+1) = true := by
    have isInitial : (List.length word = 0) ↔ L = a := by rw [lenWord]; dsimp [L]; omega
    rw [age]
    simpa only [isInitial] using
      (closingWindowScheduled_iff a L (List.length h) (d+1) bounds.1 bounds.2.1 bounds.2.2).mpr rfl
  have active' : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
      (carriedBoundarySources P u word ∘ e) active := by
    rw [total,lenU]
    exact activity
  have phase' : ConsecutiveLeaderBoundaries P d
      (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root)
      (List.length u) := by
    change ConsecutiveLeaderBoundaries P d (closingLayerHistory (past ∘ Subtype.val) (n.val+1) root) (List.length u)
    rw [actual,lenU]
    exact phase
  obtain ⟨move,policy,realizes,offered⟩ := numbered_graphClosingOffers_complete M P closed recognizes d recent
    u word e (live_history_take P closed h live a) phase.start_boundary shape rep active active' source sourceExact
    graphBounded small step initial expected coherent slot minimum n root scheduled
    (by change P (History.graphSequence (closingLayerHistory (past ∘ Subtype.val) (n.val+1) root)); rwa [actual]) phase'
  exact ⟨n,root,move,age,actual,policy,realizes,offered⟩

end
end Characterisation
