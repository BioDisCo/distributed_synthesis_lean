/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.ActualHandoverOffers

/-! The actual history in a complete successor certificate has the actual
preceding source slot as parent. This connects complete component coverage
to the finite game's hidden predecessor relation, without guessing a parent. -/
namespace Characterisation
open DistributedSynthesis

theorem actual_handover_parent_edge
    {H I₁ I₂ O₁ O₂ Q : Type} {B C D n : Nat}
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (a : Nat)
    (before : a ≤ List.length h) (e : H ≃ InputHistoryComponent P (h.take a))
    (active : H → Bool)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (initial : ActiveClosingRoots active → Q)
    (expected : ClosingPolicy (ActiveClosingRoots active) I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n)
    (move : ClosingBoundaryCertificate (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B D n)
    (actual : closingLayerHistory ((boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val) n root = h)
    (realizes : ClosingOfferRealizes P ((boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val)
      step initial expected bound root move)
    (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1)) (oldMinimum : Fin (C+1)) :
    let outcome := certificateHandover (slot ∘ Subtype.val) minimum move
    ∃ i : Fin move.1.val,
      closingLayerHistory ((boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val) n (move.2.2.1 i) = h ∧
      HandoverEdge (slot (e.symm ⟨h.take a,Relation.ReflTransGen.refl⟩),oldMinimum) outcome ()
        (handoverSlot outcome i,minimum (move.2.2.2.2 i)) := by
  let past : ActiveClosingRoots active → EnvHistory I₁ I₂ :=
    (boundaryPhaseSources P d h a ∘ e) ∘ Subtype.val
  obtain ⟨i,target⟩ := (realizes.2.1 h).mp (by rw [actual]; exact Relation.ReflTransGen.refl)
  let parent := (closingLayerRoot n (move.2.2.1 i)).val
  have parentPrefix : (e parent).val.IsPrefix h := by
    have result := closingCertificate_parent_prefix
      (fun s : ActiveClosingRoots active => (e s.val).val) past
      (fun _ => ⟨boundaryPhaseWord d h a,rfl⟩) move i
    rwa [target] at result
  have depth : List.length (e parent).val = a := by
    simpa only [List.length_take,min_eq_left before] using (inputConnected_length P (e parent).property).symm
  have oldHistory : (e parent).val = h.take a := by
    obtain ⟨suffix,joined⟩ := parentPrefix
    calc
      (e parent).val = ((e parent).val ++ suffix).take (List.length (e parent).val) := by rw [List.take_left]
      _ = ((e parent).val ++ suffix).take a := congrArg (fun j => ((e parent).val ++ suffix).take j) depth
      _ = h.take a := congrArg (List.take a) joined
  have oldIndex : parent = e.symm ⟨h.take a,Relation.ReflTransGen.refl⟩ := by
    apply e.injective
    apply Subtype.ext
    simpa only [Equiv.apply_symm_apply] using oldHistory
  refine ⟨i,target,?_⟩
  apply (certificateHandover_edge (slot ∘ Subtype.val) minimum move _ _).mpr
  exact ⟨i,congrArg slot oldIndex,rfl⟩

end Characterisation
