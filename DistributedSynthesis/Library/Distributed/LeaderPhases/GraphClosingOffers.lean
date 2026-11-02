/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledClosingOffers
import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphCoupledBundles

/-! A finite collector computed from the current graph bank, activity bits,
labels, and carried policy. It enumerates checked graph scans and all their
checked closing certificates; no scan or certificate need be guessed by a
local process as an additional output annotation. -/
namespace Characterisation
open DistributedSynthesis

section Collector
variable {H I₁ I₂ O₁ O₂ Q GQ : Type} {B C d K D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q] [Fintype GQ]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (source : H → GraphRootState GQ d K) (active : H → Bool)
variable (shape : InputShape H) (initialWindow : Bool)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

def graphClosingOffers : Finset (LeaderHandover Q B C) :=
  (Finset.univ.filter fun table : ClosingGraphTable H I₁ I₂ GQ d K D =>
    checkClosingGraphTable M source table = true).biUnion fun table =>
      scheduledClosingOffers (restrictInputShape shape (Subtype.val : ActiveClosingRoots active → H))
        initialWindow (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table))
        (restrictClosingFlags Subtype.val (closingGraphLiveTable table))
        step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected)
        (slot ∘ Subtype.val) minimum

theorem mem_graphClosingOffers_iff (outcome : LeaderHandover Q B C) :
    outcome ∈ graphClosingOffers M source active shape initialWindow step initial expected slot minimum ↔
      ∃ table : ClosingGraphTable H I₁ I₂ GQ d K D,
        checkClosingGraphTable M source table = true ∧
        outcome ∈ scheduledClosingOffers
          (restrictInputShape shape (Subtype.val : ActiveClosingRoots active → H))
          initialWindow (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table))
          (restrictClosingFlags Subtype.val (closingGraphLiveTable table))
          step (initial ∘ Subtype.val) (restrictClosingPolicy Subtype.val expected)
          (slot ∘ Subtype.val) minimum := by
  simp only [graphClosingOffers, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Any demanded certificate in any checked graph-coupled bundle belongs
to the collector. Thus enumeration includes all such witnesses. -/
theorem graphClosingOffers_of_bundle
    (table : ClosingGraphTable H I₁ I₂ GQ d K D)
    (graphChecked : checkClosingGraphTable M source table = true)
    (bundle : FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B D)
    (checked : checkScheduledExitBundle (restrictInputShape shape Subtype.val) initialWindow
      (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table))
      (restrictClosingFlags Subtype.val (closingGraphLiveTable table))
      step (initial ∘ Subtype.val) (fun _ => True) (restrictClosingPolicy Subtype.val expected) bundle = true)
    (n : Fin D) (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ (n.val+1))
    (scheduled : closingWindowScheduled initialWindow D (n.val+1) = true)
    (alive : closingFlagAt (restrictClosingFlags Subtype.val (closingGraphLiveTable table)) (n.val+1) root = true)
    (exit : closingFirstExit
      (closingFlagAt (restrictClosingFlags Subtype.val (closingGraphBoundaryTable M table))) (n.val+1) root = true) :
    certificateHandover (slot ∘ Subtype.val) minimum (bundle.2 n root) ∈
      graphClosingOffers M source active shape initialWindow step initial expected slot minimum := by
  apply (mem_graphClosingOffers_iff M source active shape initialWindow step initial expected slot minimum _).mpr
  exact ⟨table,graphChecked,scheduledClosingOffers_of_bundle _ _ _ _ _ _ _ _ _ bundle checked n root scheduled alive exit⟩

end Collector
end Characterisation
