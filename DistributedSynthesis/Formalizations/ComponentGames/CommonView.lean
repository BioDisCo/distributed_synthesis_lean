/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CommonPastView
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds

/- Exact-depth geometric ingredient of Lemma 4.5. The existing proof chooses
a possibly larger window; this file keeps the manuscript's SAME D.
The consensus premise is discharged separately in ConsensusHoles.lean. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation FullViewPath PaddingProjection
set_option maxHeartbeats 1200000

private theorem incident_bounds {h : List Graph} {v : Vertex} (hv : Incident h v) :
    pathIndex h ≤ PaddingProjection.coordinate v ∧ PaddingProjection.coordinate v ≤ pathIndex h + 1 := by
  rcases hv with rfl | rfl
  · exact (actual_process_index_bounds h).1
  · exact (actual_process_index_bounds h).2

theorem exact_holes_unique_blind_view (P : List Graph → Prop) (D : Nat)
    (holes : ∀ h, ∃ u, u.length = D ∧ ¬ P (h ++ u))
    (h k : List Graph) (deep : D ≤ h.length) (live : P h)
    (conn : Connected P h k) (v w : Vertex) (hv : Incident h v) (hw : Incident k w)
    (bv : BlindFor D v) (bw : BlindFor D w) : v = w := by
  have liveK : P k := by
    rcases Relation.ReflTransGen.cases_tail conn with rfl | ⟨_,_,step⟩
    · exact live
    · exact step.2.1
  have depth := connected_same_depth P conn
  have notLess : ∀ (a b : List Graph) (x y : Vertex),
      D ≤ a.length → P a → Connected P a b → Incident a x → Incident b y →
      BlindFor D x → BlindFor D y → ¬ PaddingProjection.coordinate x < PaddingProjection.coordinate y := by
    intro a b x y deepA liveA connected ix iy bx byy lt
    have ax := incident_bounds ix
    have byb := incident_bounds iy
    have sameDepth := connected_same_depth P connected
    obtain ⟨i, ci⟩ := blindFor_coordinate_divisible D x bx
    obtain ⟨j, cj⟩ := blindFor_coordinate_divisible D y byy
    have positive : 0 < 3^D := by positivity
    have ij : i < j := by nlinarith
    have upper : PaddingProjection.coordinate y ≤ 3^a.length := by
      have bbound := pathIndex_lt b
      rw [← sameDepth] at bbound
      omega
    have fits : (i+1) * 3^D ≤ 3^((a.length-D)+D) := by
      rw [Nat.sub_add_cancel deepA]
      nlinarith
    obtain ⟨z,lo,hi,missing⟩ := aligned_holes_of_exact_prefix_holes P D (a.length-D) holes i fits
    apply missing
    rw [Nat.sub_add_cancel deepA]
    apply connected_interval_live P a.length rfl liveA connected z
    · nlinarith
    · nlinarith
  have eq : PaddingProjection.coordinate v = PaddingProjection.coordinate w := by
    have a := notLess h k v w deep live conn hv hw bv bw
    have b := notLess k h w v (by omega) liveK (connected_symm P conn) hw hv bw bv
    omega
  exact coordinate_injective (t := h.length) ⟨h,rfl,hv⟩ ⟨k,depth.symm,hw⟩ eq

theorem exact_holes_recent_receiver (P : List Graph → Prop) (D : Nat)
    (holes : ∀ h, ∃ u, u.length = D ∧ ¬ P (h ++ u))
    (h : List Graph) (deep : D ≤ h.length) (live : P h) :
    ∃ p : Proc, RecentOther P D h p := by
  classical
  letI : Decidable (∃ k v, Connected P h k ∧ Incident k v ∧ BlindFor D v) :=
    Classical.propDecidable _
  by_cases someBlind : ∃ k v, Connected P h k ∧ Incident k v ∧ BlindFor D v
  · obtain ⟨k,v,hk,hv,bv⟩ := someBlind
    refine ⟨viewOwner v, ?_⟩
    intro j w hj hw different bw
    have liveK : P k := by
      rcases Relation.ReflTransGen.cases_tail hk with rfl | ⟨_,_,step⟩
      · exact live
      · exact step.2.1
    have eq := exact_holes_unique_blind_view P D holes k j
      (by rw [← connected_same_depth P hk]; exact deep) liveK
      ((connected_symm P hk).trans hj) v w hv hw bv bw
    exact different (congrArg viewOwner eq.symm)
  · refine ⟨.one, ?_⟩
    intro k v hk hv _ bv
    exact someBlind ⟨k,v,hk,hv,bv⟩

-- Applies to arbitrary connected input-history families, not only to full
-- components, with unrestricted private inputs and the exact window D.
theorem exact_holes_common_view {I₁ I₂ : Type} (P : List Graph → Prop) (D : Nat)
    (holes : ∀ h, ∃ u, u.length = D ∧ ¬ P (h ++ u))
    (h : EnvHistory I₁ I₂) (deep : D ≤ List.length h)
    (live : P (History.graphSequence h)) :
    ∃ p, ∀ k, InputConnected P h k →
      lagView D (currentView p h) = lagView D (currentView p k) := by
  obtain ⟨p,recent⟩ := exact_holes_recent_receiver P D holes (History.graphSequence h)
    (by simpa [History.graphSequence] using deep) live
  exact ⟨p,fun k conn => selected_lag_component P D p recent conn⟩

end Characterisation.ComponentGames
