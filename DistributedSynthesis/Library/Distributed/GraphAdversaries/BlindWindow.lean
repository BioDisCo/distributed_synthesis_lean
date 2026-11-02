/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.InputProjection

/-! A graph component with bounded width has at most one local-view shape
whose last sufficiently many rounds contain no reception. -/
namespace Characterisation
open DistributedSynthesis FullViewPath PaddingProjection

def Incident (h : List Graph) (v : Vertex) : Prop :=
  v = .inl (evaluate h).one ∨ v = .inr (evaluate h).two

/-- The last `d` rounds are all nonreceiving rounds. -/
def BlindFor (d : Nat) (v : Vertex) : Prop := ∃ u, blind^[d] u = v

theorem coordinate_blind (v : Vertex) : PaddingProjection.coordinate (blind v) = 3 * PaddingProjection.coordinate v := by
  cases v <;> rfl

theorem coordinate_blind_iterate (d : Nat) (v : Vertex) :
    PaddingProjection.coordinate (blind^[d] v) = 3^d * PaddingProjection.coordinate v := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Function.iterate_succ_apply', coordinate_blind, ih, pow_succ]
    ring

theorem blindFor_coordinate_divisible (d : Nat) (v : Vertex) (hv : BlindFor d v) :
    3^d ∣ PaddingProjection.coordinate v := by
  obtain ⟨u, rfl⟩ := hv
  exact ⟨PaddingProjection.coordinate u, coordinate_blind_iterate d u⟩

private theorem incident_bounds {h : List Graph} {v : Vertex} (hv : Incident h v) :
    pathIndex h ≤ PaddingProjection.coordinate v ∧ PaddingProjection.coordinate v ≤ pathIndex h + 1 := by
  rcases hv with rfl | rfl
  · exact (actual_process_index_bounds h).1
  · exact (actual_process_index_bounds h).2

private theorem close_multiples_equal (B a b : Nat) (ha : B ∣ a) (hb : B ∣ b)
    (ab : a < b + B) (ba : b < a + B) : a = b := by
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  have positive : 0 < B := by nlinarith
  have eq : i = j := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with lt | gt
    · have : i + 1 ≤ j := lt
      have := Nat.mul_le_mul_left B this
      nlinarith
    · have : j + 1 ≤ i := gt
      have := Nat.mul_le_mul_left B this
      nlinarith
  rw [eq]

/-- For a uniform graph-component bound, a uniform window suffices to ensure
that two incident views without reception throughout the window are identical.
This concerns graph-only view shapes, not equality of their private inputs. -/
theorem bounded_components_unique_blind_view (P : List Graph → Prop)
    (bounded : BoundedViewComponents P) :
    ∃ d, ∀ h k v w, P h → Connected P h k → Incident h v → Incident k w →
      BlindFor d v → BlindFor d w → v = w := by
  obtain ⟨K, dist⟩ := bounded_rows_bound_connected_distance P
    ((bounded_components_iff_bounded_rows P).mp bounded)
  refine ⟨K+1, ?_⟩
  intro h k v w hh conn hv hw bv bw
  have hd := dist h k hh conn
  have vb := incident_bounds hv
  have wb := incident_bounds hw
  have power : K+1 < 3^(K+1) := Nat.lt_pow_self (by decide)
  have coordEq : PaddingProjection.coordinate v = PaddingProjection.coordinate w := close_multiples_equal _ _ _
    (blindFor_coordinate_divisible _ _ bv) (blindFor_coordinate_divisible _ _ bw)
    (by omega) (by omega)
  apply coordinate_injective (t := h.length) _ _ coordEq
  · exact ⟨h, rfl, hv⟩
  · exact ⟨k, (connected_same_depth P conn).symm, hw⟩

theorem holes_unique_blind_view (A : Set (Nat → Graph)) (regular : OmegaRegular A)
    (holes : GeometricHoles A) :
    ∃ d, ∀ h k v w, LivePrefix A h → Connected (LivePrefix A) h k →
      Incident h v → Incident k w → BlindFor d v → BlindFor d w → v = w :=
  bounded_components_unique_blind_view _
    ((omegaRegular_holes_iff_bounded_components A regular).mp holes)

def viewOwner : Vertex → Proc
  | .inl _ => .one
  | .inr _ => .two

/-- Each live component has a process such that every view of the other
process receives within the uniform window at depths at least that window.
The process may vary by component. -/
theorem holes_component_recent_receiver (A : Set (Nat → Graph))
    (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d, ∀ h, LivePrefix A h → ∃ p : Proc,
      ∀ k v, Connected (LivePrefix A) h k → Incident k v → viewOwner v ≠ p →
        ¬ BlindFor d v := by
  classical
  obtain ⟨d, unique⟩ := holes_unique_blind_view A regular holes
  refine ⟨d, ?_⟩
  intro h hh
  by_cases someBlind : ∃ k v, Connected (LivePrefix A) h k ∧ Incident k v ∧ BlindFor d v
  · obtain ⟨k,v,hk,hv,bv⟩ := someBlind
    refine ⟨viewOwner v, ?_⟩
    intro j w hj hw different bw
    have liveK : LivePrefix A k := by
      rcases Relation.ReflTransGen.cases_tail hk with rfl | ⟨_,_,step⟩
      · exact hh
      · exact step.2.1
    have conn : Connected (LivePrefix A) k j := (connected_symm _ hk).trans hj
    have eq := unique k j v w liveK conn hv hw bv bw
    exact different (congrArg viewOwner eq.symm)
  · refine ⟨.one, ?_⟩
    intro k v hk hv _ bv
    exact someBlind ⟨k,v,hk,hv,bv⟩

end Characterisation
