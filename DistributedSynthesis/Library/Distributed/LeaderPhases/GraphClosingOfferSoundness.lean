/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphClosingOffers
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingOfferRealization
import DistributedSynthesis.Library.Distributed.LeaderPhases.NumberedBoundaryCoverage

/-! Discharge target coverage for every collected graph-coupled offer using
the canonical closing schedule and the actual current active source family. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {B C K : Nat}
variable [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (e : H ≃ InputHistoryComponent P u) (liveU : P (History.graphSequence u))
variable (startU : leaderBoundary P d u = true)
variable [Fintype H] [DecidableEq H]
variable (shape : InputShape H)
variable (rep : RepresentsInputShape (carriedBoundarySources P u word ∘ e) shape)
variable (active : H → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word ∘ e) active)
variable (source : H → GraphRootState GQ d K)
variable (sourceExact : ∀ h, GraphRootRep P M
  (History.graphSequence ((carriedBoundarySources P u word ∘ e) h)) (source h))
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ (d+1))
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

include closed recognizes recent liveU startU rep activity sourceExact in
/-- Every offered handover has one complete realization from the current
carried family. All retained histories end the same phase, have the checked
labels and observation shape, and extend their actual predecessor roots. -/
theorem numbered_graphClosingOffers_live_realizes (outcome : LeaderHandover Q B C)
    (member : outcome ∈ graphClosingOffers M source active shape (decide (List.length word = 0))
      step initial expected slot minimum) :
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1)),
      certificateHandover (slot ∘ Subtype.val) minimum move = outcome ∧
      ClosingOfferRealizes P ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      P (History.graphSequence (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) root)) ∧
      ∀ i, ConsecutiveLeaderBoundaries P d
        (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) (move.2.2.1 i))
        (List.length u) := by
  obtain ⟨table,graphChecked,offered⟩ := (mem_graphClosingOffers_iff M source active shape _ step initial expected slot minimum outcome).mp member
  obtain ⟨n,root,move,accepted,equality⟩ := (mem_scheduledClosingOffers_iff _ _ _ _ _ _ _ _ _ outcome).mp offered
  have checked := (mem_scheduledClosingCertificates_iff _ _ _ _ _ _ _ n root move).mp accepted
  let f : ActiveClosingRoots active → H := Subtype.val
  let past := carriedBoundarySources P u word ∘ e
  let boundary := closingGraphBoundaryTable M table
  let live := closingGraphLiveTable table
  have liveExact := closingGraphLiveTable_exact M P closed recognizes past source sourceExact table graphChecked
  have flags := closingGraphFlags_exact_on_live M P closed recognizes past source sourceExact table graphChecked
  have restrictedLive : ∀ m s, restrictClosingFlags f live m s = true ↔
      P (History.graphSequence (closingLayerHistory (past ∘ f) m.val s)) := by
    intro m s
    simpa only [restrictClosingFlags,closingLayerHistory_map] using liveExact m (mapClosingLayer f m.val s)
  have liveRoot := (closingLiveTable_exact P (past ∘ f) (restrictClosingFlags f live)
    restrictedLive (n.val+1) (by omega) root).mp checked.1.2.1
  have flagEq : closingFlagAt (restrictClosingFlags f boundary) =
      fun m s => closingFlagAt boundary m (mapClosingLayer f m s) := by
    funext m s
    exact closingFlagAt_restrict f boundary m s
  have exit := checked.1.2.2.1
  rw [flagEq] at exit
  have covers := numbered_scheduled_active_coverage P closed d recent u word e liveU startU active activity
    (closingFlagAt boundary) flags n checked.1.1 root liveRoot exit
  have realization := scheduledClosingCertificate_realizes P (past ∘ f)
    (((carriedBoundarySources_injective P u word).comp e.injective).comp Subtype.val_injective)
    (restrictInputShape shape f) (restrictInputShape_exact past shape rep f)
    (List.length u + List.length word) (fun h => carriedBoundarySources_depth P u word (e (f h)))
    (decide (List.length word = 0)) (restrictClosingFlags f boundary) (restrictClosingFlags f live)
    restrictedLive step (initial ∘ f) (restrictClosingPolicy f expected) n root move accepted covers
  have oldLive : P (History.graphSequence (closingLayerHistory past (n.val+1)
      (mapClosingLayer f (n.val+1) root))) := by
    simpa only [closingLayerHistory_map] using liveRoot
  have oldExit : closingFirstExit (closingFlagAt boundary) (n.val+1)
      (mapClosingLayer f (n.val+1) root) = true := by
    simpa only [closingFirstExit_restrict] using checked.1.2.2.1
  have oldPhase := numbered_live_first_exit_phase P closed d recent u word e liveU startU active activity
    (closingFlagAt boundary) flags n _ oldLive (activeClosingLayer_root_alive active (n.val+1) root) oldExit
  have phase : ConsecutiveLeaderBoundaries P d (closingLayerHistory (past ∘ f) (n.val+1) root) (List.length u) := by
    simpa only [past,closingLayerHistory_map] using oldPhase
  refine ⟨n,root,move,equality,realization,liveRoot,?_⟩
  intro i
  apply consecutiveLeaderBoundaries_component P closed d recent liveRoot _ (List.length u) phase
  exact (realization.2.1 _).mpr ⟨i,rfl⟩

include closed recognizes recent liveU startU rep activity sourceExact in
theorem numbered_graphClosingOffers_realizes (outcome : LeaderHandover Q B C)
    (member : outcome ∈ graphClosingOffers M source active shape (decide (List.length word = 0))
      step initial expected slot minimum) :
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1)),
      certificateHandover (slot ∘ Subtype.val) minimum move = outcome ∧
      ClosingOfferRealizes P ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      ∀ i, ConsecutiveLeaderBoundaries P d
        (closingLayerHistory ((carriedBoundarySources P u word ∘ e) ∘ Subtype.val) (n.val+1) (move.2.2.1 i))
        (List.length u) := by
  obtain ⟨n,root,move,equality,realization,_,phases⟩ :=
    numbered_graphClosingOffers_live_realizes M P closed recognizes d recent u word e liveU startU
      shape rep active activity source sourceExact step initial expected slot minimum outcome member
  exact ⟨n,root,move,equality,realization,phases⟩

end

section
variable {I₁ I₂ O₁ O₂ Q GQ : Type} {B C K : Nat}
variable [Fintype GQ] [DecidableEq GQ] [Fintype Q] [DecidableEq Q]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable [Nonempty O₁] [Nonempty O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (P : List Graph → Prop) (closed : PrefixClosed P)
variable (recognizes : ∀ g, P g ↔ M.eval g ∈ M.accept) (d : Nat)
variable (recent : ∀ g, P g → ∃ p, RecentOther P d g p)
variable (u word : EnvHistory I₁ I₂) (liveU : P (History.graphSequence u))
variable (startU : leaderBoundary P d u = true)
variable [Fintype (InputHistoryComponent P u)] [DecidableEq (InputHistoryComponent P u)]
variable (shape : InputShape (InputHistoryComponent P u))
variable (rep : RepresentsInputShape (carriedBoundarySources P u word) shape)
variable (active : InputHistoryComponent P u → Bool)
variable (activity : SourceActivityOnLive P d (List.length u) (List.length u + List.length word)
  (carriedBoundarySources P u word) active)
variable (source : InputHistoryComponent P u → GraphRootState GQ d K)
variable (sourceExact : ∀ h, GraphRootRep P M
  (History.graphSequence (carriedBoundarySources P u word h)) (source h))
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
variable (initial : InputHistoryComponent P u → Q)
variable (expected : ClosingPolicy (InputHistoryComponent P u) I₁ I₂ O₁ O₂ (d+1))
variable (slot : InputHistoryComponent P u → Fin (B+1)) (minimum : Q → Fin (C+1))

include closed recognizes recent liveU startU rep activity sourceExact in
/-- Every offered handover has one complete realization from the current
carried family. All retained histories end the same phase, have the checked
labels and observation shape, and extend their actual predecessor roots. -/
theorem graphClosingOffers_realizes (outcome : LeaderHandover Q B C)
    (member : outcome ∈ graphClosingOffers M source active shape (decide (List.length word = 0))
      step initial expected slot minimum) :
    ∃ (n : Fin (d+1)) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
      (move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B (d+1) (n.val+1)),
      certificateHandover (slot ∘ Subtype.val) minimum move = outcome ∧
      ClosingOfferRealizes P (carriedBoundarySources P u word ∘ Subtype.val)
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected) (by omega) root move ∧
      ∀ i, ConsecutiveLeaderBoundaries P d
        (closingLayerHistory (carriedBoundarySources P u word ∘ Subtype.val) (n.val+1) (move.2.2.1 i))
        (List.length u) := by
  simpa only [Function.comp_def,Equiv.refl_apply] using
    numbered_graphClosingOffers_realizes M P closed recognizes d recent u word
      (Equiv.refl (InputHistoryComponent P u)) liveU startU shape rep active activity source sourceExact
      step initial expected slot minimum outcome member

end
end Characterisation
