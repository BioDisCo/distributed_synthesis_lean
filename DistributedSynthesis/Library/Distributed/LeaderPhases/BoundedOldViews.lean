/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CommonPastView

/-! Uniformly many old coordinator views join the bounded recent pieces.
Each is determined by one common past view and at most d fresh inputs. -/
namespace Characterisation
open DistributedSynthesis

def lastViewInputs {I₁ I₂ : Type*} {p : Proc} : Nat → View I₁ I₂ p → List (PSum I₁ I₂)
  | 0,_ => []
  | _+1,.empty _ => []
  | d+1,.noRecv v i => lastViewInputs d v ++ [i]
  | d+1,.recv v i _ _ => lastViewInputs d v ++ [i]

theorem lastViewInputs_length_le {I₁ I₂ : Type*} {p : Proc} (d : Nat) (v : View I₁ I₂ p) :
    (lastViewInputs d v).length ≤ d := by
  induction d generalizing v with
  | zero => simp [lastViewInputs]
  | succ d ih =>
    cases v <;> simp only [lastViewInputs, List.length_append, List.length_singleton,
      List.length_nil]
    · omega
    · exact Nat.add_le_add_right (ih _) 1
    · exact Nat.add_le_add_right (ih _) 1

/-- When all d final rounds are nonreceiving, their own inputs and the
view before them reconstruct the entire current view. -/
theorem old_view_reconstruct {I₁ I₂ : Type*} {p : Proc} (d : Nat) (v : View I₁ I₂ p)
    (old : d ≤ silentAge v) :
    (lastViewInputs d v).foldl View.noRecv (lagView d v) = v := by
  induction d generalizing v with
  | zero => rfl
  | succ d ih =>
    cases v with
    | empty => simp [silentAge] at old
    | recv => simp [silentAge] at old
    | noRecv v i =>
      have age : d ≤ silentAge v := by simp only [silentAge] at old; omega
      simpa [lastViewInputs, lagView, View.nonFringe, NonFringeView.previousView,
        List.foldl_append] using congrArg (fun w => View.noRecv w i) (ih v age)

/-- Fixing the past view bounds all possible old extensions by a finite
input array. This theorem also covers syntactic views not occurring in runs. -/
theorem finite_old_extensions {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (p : Proc) (d : Nat) (base : View I₁ I₂ p) :
    Finite {v : View I₁ I₂ p // d ≤ silentAge v ∧ lagView d v = base} ∧
      Nat.card {v : View I₁ I₂ p // d ≤ silentAge v ∧ lagView d v = base} ≤
        Nat.card (Fin d → Option (PSum I₁ I₂)) := by
  let key : {v : View I₁ I₂ p // d ≤ silentAge v ∧ lagView d v = base} →
      (Fin d → Option (PSum I₁ I₂)) := fun v i => (lastViewInputs d v.val)[i.val]?
  have inj : Function.Injective key := by
    intro a b eq
    have words : lastViewInputs d a.val = lastViewInputs d b.val := by
      apply List.ext_getElem?
      intro i
      by_cases inside : i < d
      · exact congrFun eq ⟨i,inside⟩
      · have ha := lastViewInputs_length_le d a.val
        have hb := lastViewInputs_length_le d b.val
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    apply Subtype.ext
    have ra := old_view_reconstruct d a.val a.property.1
    have rb := old_view_reconstruct d b.val b.property.1
    rw [a.property.2] at ra
    rw [b.property.2, ← words] at rb
    exact ra.symm.trans rb
  exact ⟨Finite.of_injective key inj, Nat.card_le_card_of_injective key inj⟩

def OldCoordinatorViews {I₁ I₂ : Type*} (P : List Graph → Prop) (d : Nat)
    (h : EnvHistory I₁ I₂) (p : Proc) :=
  {v : View I₁ I₂ p // ∃ k, InputConnected P h k ∧ currentView p k = v ∧ d ≤ silentAge v}

/-- Even if the full input-history component is unbounded, its old
coordinator views form a uniformly bounded set. -/
theorem bounded_old_coordinator_views {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (p : Proc)
    (recent : RecentOther P d (History.graphSequence h) p) :
    Finite (OldCoordinatorViews P d h p) ∧
      Nat.card (OldCoordinatorViews P d h p) ≤ Nat.card (Fin d → Option (PSum I₁ I₂)) := by
  let base := lagView d (currentView p h)
  let f : OldCoordinatorViews P d h p →
      {v : View I₁ I₂ p // d ≤ silentAge v ∧ lagView d v = base} := fun v => ⟨v.val, by
    obtain ⟨k,conn,eq,age⟩ := v.property
    refine ⟨age,?_⟩
    rw [← eq]
    exact (selected_lag_component P d p recent conn).symm⟩
  have inj : Function.Injective f := by
    intro a b eq
    apply Subtype.ext
    exact congrArg (fun z : {v : View I₁ I₂ p // d ≤ silentAge v ∧ lagView d v = base} => z.val) eq
  have bound := finite_old_extensions p d base
  letI := bound.1
  exact ⟨Finite.of_injective f inj,(Nat.card_le_card_of_injective f inj).trans bound.2⟩

/-- A whole component consists of uniformly bounded recent pieces. All
links between pieces use one of uniformly many old views of one coordinator.
Neither the number of pieces nor their multiplicities is bounded here. -/
theorem holes_finite_piece_decomposition {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B C, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      ∃ p : Proc,
        (Finite (OldCoordinatorViews (LivePrefix A) d h p) ∧
          Nat.card (OldCoordinatorViews (LivePrefix A) d h p) ≤ C) ∧
        ∀ k, InputConnected (LivePrefix A) h k →
          (Finite (RecentPiece (LivePrefix A) d k) ∧
            Nat.card (RecentPiece (LivePrefix A) d k) ≤ B) ∧
          ∀ l, InputAdjacent k l → RecentAdjacent d k l ∨
            (currentView p k = currentView p l ∧ d ≤ silentAge (currentView p k)) := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  obtain ⟨K,bound⟩ := (omegaRegular_holes_iff_bounded_components A regular).mp holes
  let C := Nat.card (Fin d → Option (PSum I₁ I₂))
  refine ⟨d,K*C^2,C,?_⟩
  intro h live
  obtain ⟨p,hp⟩ := recent _ live
  refine ⟨p,bounded_old_coordinator_views _ d h p hp,?_⟩
  intro k conn
  have liveK : LivePrefix A (History.graphSequence k) := by
    rcases Relation.ReflTransGen.cases_tail conn with rfl | ⟨_,_,step⟩
    · exact live
    · exact step.2.1
  have hpK := (recentOther_component_invariant (LivePrefix A) d
    (inputConnected_projects _ conn) p).mp hp
  have piece := finite_recent_piece (LivePrefix A) ⟨K,bound⟩ d k liveK
  refine ⟨⟨piece.1,piece.2.trans (Nat.mul_le_mul_right _ (bound _ liveK).2)⟩,?_⟩
  intro l adj
  exact adjacent_recent_or_coordinator _ d k l p hpK adj

end Characterisation
