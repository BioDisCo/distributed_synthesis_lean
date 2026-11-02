/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.RowCharacterization
import DistributedSynthesis.Library.Distributed.GraphAdversaries.ViewComponents
import DistributedSynthesis.Library.Distributed.PaddingProjection

/-! Connecting reflected indices to actual local views and their connected
components. The coordinates below are the repository's local-view functions. -/

namespace Characterisation

open DistributedSynthesis DistributedSynthesis.FullViewPath

theorem actual_endpoint_indices (h : List Graph) :
    PaddingProjection.coordinate (left (evaluate h)) = pathIndex h ∧
      PaddingProjection.coordinate (right (evaluate h)) = pathIndex h + 1 := by
  induction h using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl⟩
  | append_singleton h g ih =>
    rw [at_append, pathIndex_append]
    by_cases hp : pathIndex h % 2 = 0
    · have ht : (evaluate h).oneLeft = true := by simp [orientation_agrees, hp]
      cases g <;>
        simp [PaddingProjection.coordinate, PaddingProjection.vertexProject,
          PaddingProjection.project, left, right, advance, advanceViews, ht,
          indexStep, graphDigit, Proc.other, hp] at ih ⊢ <;> simp [ih.1, ih.2] <;> omega
    · have ht : (evaluate h).oneLeft = false := by simp [orientation_agrees, hp]
      cases g <;>
        simp [PaddingProjection.coordinate, PaddingProjection.vertexProject,
          PaddingProjection.project, left, right, advance, advanceViews, ht,
          indexStep, graphDigit, Proc.other, hp] at ih ⊢ <;> simp [ih.1, ih.2] <;> omega

theorem actual_process_index_bounds (h : List Graph) :
    (pathIndex h ≤ PaddingProjection.project (fun _ => true) (evaluate h).one ∧
      PaddingProjection.project (fun _ => true) (evaluate h).one ≤ pathIndex h + 1) ∧
    (pathIndex h ≤ PaddingProjection.project (fun _ => true) (evaluate h).two ∧
      PaddingProjection.project (fun _ => true) (evaluate h).two ≤ pathIndex h + 1) := by
  have endpoints := actual_endpoint_indices h
  cases ht : (evaluate h).oneLeft <;>
    simp [PaddingProjection.coordinate, PaddingProjection.vertexProject, left, right, ht]
      at endpoints <;> omega

theorem adjacent_index_bounds {h k : List Graph} (adjacent : Adjacent h k) :
    pathIndex h ≤ pathIndex k + 1 ∧ pathIndex k ≤ pathIndex h + 1 := by
  have hb := actual_process_index_bounds h
  have kb := actual_process_index_bounds k
  rcases adjacent with eqOne | eqTwo
  · have eq := congrArg (PaddingProjection.project (fun _ => true)) eqOne
    omega
  · have eq := congrArg (PaddingProjection.project (fun _ => true)) eqTwo
    omega

theorem adjacent_same_depth {h k : List Graph} (adjacent : Adjacent h k) :
    h.length = k.length := by
  have hd := at_depth h
  have kd := at_depth k
  rcases adjacent with eqOne | eqTwo
  · have eq := congrArg depth eqOne
    omega
  · have eq := congrArg depth eqTwo
    omega

theorem connected_same_depth (P : List Graph → Prop) {h k : List Graph}
    (connected : Connected P h k) : h.length = k.length := by
  induction connected with
  | refl => rfl
  | tail _ step ih => exact ih.trans (adjacent_same_depth step.2.2)

theorem connected_interval_live (P : List Graph → Prop) (t : Nat)
    {h k : List Graph} (hlen : h.length = t) (live : P h)
    (connected : Connected P h k) :
    ∀ j, pathIndex h ≤ j → j ≤ pathIndex k → LiveIndex P t j := by
  induction connected with
  | refl =>
    intro j lo hi
    exact ⟨h, hlen, by omega, live⟩
  | @tail a b conn step ih =>
    intro j lo hi
    by_cases before : j ≤ pathIndex a
    · exact ih j lo before
    · have jump := adjacent_index_bounds step.2.2
      have jEq : pathIndex b = j := by omega
      have bLen : b.length = t :=
        ((connected_same_depth P conn).trans (adjacent_same_depth step.2.2)).symm.trans hlen
      exact ⟨b, bLen, jEq, step.2.1⟩

theorem connected_symm (P : List Graph → Prop) {h k : List Graph}
    (connected : Connected P h k) : Connected P k h := by
  apply Relation.ReflTransGen.symmetric _ connected
  intro u v step
  refine ⟨step.2.1, step.1, ?_⟩
  exact step.2.2.elim (fun eq => Or.inl eq.symm) (fun eq => Or.inr eq.symm)

theorem bounded_rows_bound_connected_distance (P : List Graph → Prop)
    (bounded : BoundedRowIntervals P) :
    ∃ K, ∀ h k, P h → Connected P h k →
      pathIndex k < pathIndex h + K ∧ pathIndex h < pathIndex k + K := by
  obtain ⟨K, bound⟩ := bounded
  refine ⟨K, fun h k live connected => ?_⟩
  have kLen := connected_same_depth P connected
  have kLive : P k := by
    rcases Relation.ReflTransGen.cases_tail connected with rfl | ⟨_, _, step⟩
    · exact live
    · exact step.2.1
  have oneDirection : ∀ u v, P u → Connected P u v → pathIndex u ≤ pathIndex v →
      pathIndex v < pathIndex u + K := by
    intro u v liveU conn uv
    have vBound : pathIndex v + 1 ≤ 3 ^ u.length := by
      have vl := connected_same_depth P conn
      rw [vl]
      exact pathIndex_lt v
    have lenBound := bound u.length (pathIndex u) (pathIndex v + 1) (by omega) vBound
      (fun j lo hi => connected_interval_live P u.length rfl liveU conn j lo (by omega))
    omega
  rcases le_total (pathIndex h) (pathIndex k) with hk | kh
  · have forward := oneDirection h k live connected hk
    constructor <;> omega
  · have backward := oneDirection k h kLive (connected_symm P connected) kh
    constructor <;> omega

def HistoryComponent (P : List Graph → Prop) (h : List Graph) :=
  {k : List Graph // Connected P h k}

def BoundedViewComponents (P : List Graph → Prop) : Prop :=
  ∃ K, ∀ h, P h → Finite (HistoryComponent P h) ∧ Nat.card (HistoryComponent P h) ≤ K

theorem bounded_rows_imply_bounded_components (P : List Graph → Prop)
    (bounded : BoundedRowIntervals P) : BoundedViewComponents P := by
  obtain ⟨K, distance⟩ := bounded_rows_bound_connected_distance P bounded
  refine ⟨2 * K + 1, fun h live => ?_⟩
  let f : HistoryComponent P h → Fin (2 * K + 1) := fun k =>
    ⟨pathIndex k.val + K - pathIndex h, by
      have near := distance h k.val live k.property
      omega⟩
  have injective : Function.Injective f := by
    intro u v eq
    have offsets := congrArg Fin.val eq
    change pathIndex u.val + K - pathIndex h = pathIndex v.val + K - pathIndex h at offsets
    have uNear := distance h u.val live u.property
    have vNear := distance h v.val live v.property
    have indices : pathIndex u.val = pathIndex v.val := by omega
    apply Subtype.ext
    exact pathIndex_injective _ _
      ((connected_same_depth P u.property).symm.trans (connected_same_depth P v.property)) indices
  have finite : Finite (HistoryComponent P h) := Finite.of_injective f injective
  exact ⟨finite, by simpa using Nat.card_le_card_of_injective f injective⟩

theorem adjacent_of_consecutive_indices (h k : List Graph)
    (sameDepth : h.length = k.length) (next : pathIndex h + 1 = pathIndex k) : Adjacent h k := by
  have hr : PaddingProjection.Reachable h.length (right (evaluate h)) := by
    refine ⟨h, rfl, ?_⟩
    cases ht : (evaluate h).oneLeft <;> simp [right, ht]
  have kl : PaddingProjection.Reachable h.length (left (evaluate k)) := by
    refine ⟨k, sameDepth.symm, ?_⟩
    cases kt : (evaluate k).oneLeft <;> simp [left, kt]
  have eq : right (evaluate h) = left (evaluate k) :=
    PaddingProjection.coordinate_injective hr kl
      (by rw [(actual_endpoint_indices h).2, (actual_endpoint_indices k).1, next])
  cases ht : (evaluate h).oneLeft <;> cases kt : (evaluate k).oneLeft <;>
    simp [left, right, ht, kt] at eq
  · exact Or.inl eq
  · exact Or.inr eq

theorem connected_of_live_interval (P : List Graph → Prop) (h k : List Graph)
    (sameDepth : h.length = k.length) (ordered : pathIndex h ≤ pathIndex k)
    (_liveH : P h) (liveK : P k)
    (allLive : ∀ j, pathIndex h ≤ j → j ≤ pathIndex k → LiveIndex P h.length j) :
    Connected P h k := by
  suffices ∀ d k, k.length = h.length → pathIndex k = pathIndex h + d → P k →
      (∀ j, pathIndex h ≤ j → j ≤ pathIndex k → LiveIndex P h.length j) →
      Connected P h k by
    exact this (pathIndex k - pathIndex h) k sameDepth.symm (by omega) liveK allLive
  intro d
  induction d with
  | zero =>
    intro k depthEq indexEq _ _
    have eq : k = h := pathIndex_injective k h depthEq (by simpa using indexEq)
    subst k
    exact Relation.ReflTransGen.refl
  | succ d ih =>
    intro k depthEq indexEq liveK allLive
    obtain ⟨w, wlen, windex, liveW⟩ := allLive (pathIndex h + d) (by omega) (by omega)
    have previousConn := ih w wlen windex liveW (fun j lo hi => allLive j lo (by omega))
    exact previousConn.tail ⟨liveW, liveK,
      adjacent_of_consecutive_indices w k (wlen.trans depthEq.symm) (by omega)⟩

theorem bounded_components_imply_bounded_rows (P : List Graph → Prop)
    (bounded : BoundedViewComponents P) : BoundedRowIntervals P := by
  classical
  obtain ⟨K, bound⟩ := bounded
  refine ⟨K + 1, fun t a b hab _ allLive => ?_⟩
  by_cases empty : b = a
  · omega
  have strict : a < b := by omega
  obtain ⟨h, hlen, hindex, liveH⟩ := allLive a le_rfl strict
  have choices : ∀ j : Fin (b - a), ∃ w : List Graph,
      w.length = t ∧ pathIndex w = a + j.val ∧ P w := by
    intro j
    exact allLive (a + j.val) (by omega) (by omega)
  choose chosen chosenSpec using choices
  let f : Fin (b - a) → HistoryComponent P h := fun j =>
    ⟨chosen j, connected_of_live_interval P h (chosen j)
      (hlen.trans (chosenSpec j).1.symm) (by rw [hindex, (chosenSpec j).2.1]; omega)
      liveH (chosenSpec j).2.2 (by
        intro i lo hi
        rw [hlen]
        exact allLive i (by omega) (by have := (chosenSpec j).2.1; omega))⟩
  have injective : Function.Injective f := by
    intro i j eq
    have histories := congrArg Subtype.val eq
    change chosen i = chosen j at histories
    have indices := congrArg pathIndex histories
    rw [(chosenSpec i).2.1, (chosenSpec j).2.1] at indices
    apply Fin.ext
    omega
  obtain ⟨finite, cardBound⟩ := bound h liveH
  letI : Finite (HistoryComponent P h) := finite
  have size := Nat.card_le_card_of_injective f injective
  simp only [Nat.card_fin] at size
  omega

/-- Exact correspondence between bounded surviving path intervals and
bounded components of the actual local-view incidence graph. -/
theorem bounded_components_iff_bounded_rows (P : List Graph → Prop) :
    BoundedViewComponents P ↔ BoundedRowIntervals P :=
  ⟨bounded_components_imply_bounded_rows P, bounded_rows_imply_bounded_components P⟩

/-- Completed geometric characterization of bounded uncertainty components.
The remaining synthesis conjecture must still connect this condition to an
effective realizability decision procedure. -/
theorem omegaRegular_holes_iff_bounded_components (A : Set (Nat → Graph))
    (regular : OmegaRegular A) :
    GeometricHoles A ↔ BoundedViewComponents (LivePrefix A) :=
  (omegaRegular_holes_iff_bounded_rows A regular).trans
    (bounded_components_iff_bounded_rows _).symm

end Characterisation
