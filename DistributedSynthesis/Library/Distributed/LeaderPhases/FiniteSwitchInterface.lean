/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteInputInterface

/-! One fixed finite set represents the observation matrices and finite
annotations of all switch components, independently of their depth. No
sufficiency for an unbounded phase or parity objective is asserted here. -/
namespace Characterisation
open DistributedSynthesis

abbrev SwitchInterface (Q : Type*) (B : Nat) :=
  Σ n : Fin (B+1), InputShape (Fin n.val) × (Fin n.val → Q)

instance switchInterface_finite {Q : Type*} [Finite Q] (B : Nat) :
    Finite (SwitchInterface Q B) := by
  unfold SwitchInterface InputShape
  infer_instance

/-- Renumbering a bounded history family gives an exact finite observation
interface, retaining each history's annotation in its own slot. -/
theorem finite_switch_interface {H I₁ I₂ Q : Type*} [Finite H]
    (B : Nat) (bound : Nat.card H ≤ B)
    (past : H → EnvHistory I₁ I₂) (label : H → Q) :
    ∃ summary : SwitchInterface Q B, ∃ e : Fin summary.1.val ≃ H,
      RepresentsInputShape (past ∘ e) summary.2.1 ∧
      ∀ i, summary.2.2 i = label (e i) := by
  classical
  letI := Fintype.ofFinite H
  have bound' : Fintype.card H < B+1 := by
    rw [Nat.card_eq_fintype_card] at bound
    omega
  let n : Fin (B+1) := ⟨Fintype.card H,bound'⟩
  let e : Fin n.val ≃ H := (Fintype.equivFin H).symm
  refine ⟨⟨n,extractInputShape (past ∘ e),label ∘ e⟩,e,?_,?_⟩
  · exact extractInputShape_exact (past ∘ e)
  · intro i
    rfl

/-- Under the graph-only holes hypothesis, every owner switch has a
representation in the same finite interface type (for fixed finite Q).
Annotations may include adversary states, objective states, and priorities. -/
theorem holes_finite_switch_interfaces {I₁ I₂ Q : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A)
    (label : EnvHistory I₁ I₂ → Q) :
    ∃ d B, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      componentLeader (LivePrefix A) d (History.graphSequence h.dropLast) ≠
        componentLeader (LivePrefix A) d (History.graphSequence h) →
      ∃ summary : SwitchInterface Q B,
      ∃ e : Fin summary.1.val ≃ InputHistoryComponent (LivePrefix A) h,
        RepresentsInputShape (fun i => (e i).val) summary.2.1 ∧
        ∀ i, summary.2.2 i = label (e i).val := by
  obtain ⟨d,B,bound⟩ := holes_uniformly_bounded_switch_components (I₁:=I₁) (I₂:=I₂)
    A regular holes
  refine ⟨d,B,?_⟩
  intro h live changed
  obtain ⟨finite,size⟩ := bound h live changed
  letI : Finite (InputHistoryComponent (LivePrefix A) h) := finite
  exact finite_switch_interface B size (fun k => k.val) (fun k => label k.val)

end Characterisation
