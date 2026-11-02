/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.ComponentBounds
import DistributedSynthesis.Library.Distributed.Execution

/-! A local-consistency criterion for assembling outputs into actual strategies.
This is a strategy correspondence, not yet a finite-game construction. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

/-- Output assignments to live histories must agree whenever a process has
exactly the same local view. No condition relates distinct components. -/
def LocallyConsistent {O₁ O₂ : Type*} (P : List Graph → Prop)
    (out : List Graph → O₁ × O₂) : Prop :=
  (∀ h k, P h → P k → (evaluate h).one = (evaluate k).one → (out h).1 = (out k).1) ∧
  (∀ h k, P h → P k → (evaluate h).two = (evaluate k).two → (out h).2 = (out k).2)

private theorem chooseLocal {V O : Type*} [Nonempty O] (P : List Graph → Prop) (view : List Graph → V)
    (value : List Graph → O)
    (coherent : ∀ h k, P h → P k → view h = view k → value h = value k) :
    ∃ f : V → O, ∀ h, P h → f (view h) = value h := by
  classical
  let f (v : V) : O := if hv : ∃ h, P h ∧ view h = v then value hv.choose
    else Classical.choice inferInstance
  refine ⟨f, ?_⟩
  intro h hh
  have hv : ∃ k, P k ∧ view k = view h := ⟨h, hh, rfl⟩
  simp only [f, dif_pos hv]
  exact coherent _ h hv.choose_spec.1 hh hv.choose_spec.2

/-- Every locally consistent assignment on live histories is implemented by
one pair of local strategies. Arbitrary outputs suffice on unreachable views. -/
theorem locallyConsistent_iff_strategy {O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂]
    (P : List Graph → Prop) (out : List Graph → O₁ × O₂) :
    LocallyConsistent P out ↔
      ∃ σ : StrategyPair Unit Unit O₁ O₂, ∀ h, P h →
        σ.one (evaluate h).one = (out h).1 ∧ σ.two (evaluate h).two = (out h).2 := by
  classical
  constructor
  · intro consistent
    obtain ⟨f, hf⟩ := chooseLocal P (fun h => (evaluate h).one) (fun h => (out h).1) consistent.1
    obtain ⟨g, hg⟩ := chooseLocal P (fun h => (evaluate h).two) (fun h => (out h).2) consistent.2
    exact ⟨⟨f,g⟩, fun h hh => ⟨hf h hh, hg h hh⟩⟩
  · rintro ⟨σ, hs⟩
    constructor
    · intro h k hh hk eq
      rw [← (hs h hh).1, ← (hs k hk).1, eq]
    · intro h k hh hk eq
      rw [← (hs h hh).2, ← (hs k hk).2, eq]

/-- Consistency checks may be performed separately inside each component.
A shared local view itself witnesses that two live histories are connected. -/
theorem locallyConsistent_iff_componentwise {O₁ O₂ : Type*}
    (P : List Graph → Prop) (out : List Graph → O₁ × O₂) :
    LocallyConsistent P out ↔
      (∀ h k, P h → P k → Connected P h k →
        (evaluate h).one = (evaluate k).one → (out h).1 = (out k).1) ∧
      (∀ h k, P h → P k → Connected P h k →
        (evaluate h).two = (evaluate k).two → (out h).2 = (out k).2) := by
  constructor
  · intro hc
    exact ⟨fun h k hh hk _ eq => hc.1 h k hh hk eq,
      fun h k hh hk _ eq => hc.2 h k hh hk eq⟩
  · intro hc
    exact ⟨fun h k hh hk eq => hc.1 h k hh hk
        (Relation.ReflTransGen.single ⟨hh,hk,Or.inl eq⟩) eq,
      fun h k hh hk eq => hc.2 h k hh hk
        (Relation.ReflTransGen.single ⟨hh,hk,Or.inr eq⟩) eq⟩

/-- A bounded component admits only finitely many output assignments, before
or after imposing the local-consistency constraints. -/
theorem finite_component_output_assignments {O₁ O₂ : Type*} [Finite O₁] [Finite O₂]
    (P : List Graph → Prop) (bounded : BoundedViewComponents P)
    (h : List Graph) (hh : P h) : Finite (HistoryComponent P h → O₁ × O₂) := by
  obtain ⟨K, hb⟩ := bounded
  letI : Finite (HistoryComponent P h) := (hb h hh).1
  infer_instance

end Characterisation
