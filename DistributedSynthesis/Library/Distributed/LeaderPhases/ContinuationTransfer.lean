/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingTransitionCompiler

/-! An observation matrix determines the entire continuation problem, not
only bounded windows. The same strategy is transported simultaneously at
every root and every future depth. Physical rounds remain explicit. -/
namespace Characterisation
open DistributedSynthesis

/-- All future prescriptions, indexed by their exact number of rounds. -/
abbrev ContinuationPolicy (H I₁ I₂ O₁ O₂ : Type) :=
  (n : Nat) → ClosingLayer H I₁ I₂ (n+1) → O₁ × O₂

def ContinuationCoherent {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂] (shape : InputShape H)
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) : Prop :=
  ∀ n, ShapeCoherent (closingLayerShape (I₁:=I₁) (I₂:=I₂) shape (n+1)) (out n)

/-- One local strategy implements the infinite family of tables. Equality
of views forces equality of physical depths, so no independent choices at
different depths are being identified. -/
theorem continuation_coherent_iff_local {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) :
    ContinuationCoherent shape out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ n s,
      σ.one (currentView .one (closingLayerHistory past (n+1) s)) = (out n s).1 ∧
      σ.two (currentView .two (closingLayerHistory past (n+1) s)) = (out n s).2 := by
  have timeEq : ∀ (n m : Nat) s t,
      InputAdjacent (closingLayerHistory past (n+1) s)
        (closingLayerHistory past (m+1) t) → n = m := by
    intro n m s t adj
    have len := adjacent_same_depth (inputAdjacent_projects adj)
    have lengths : List.length (closingLayerHistory past (n+1) s) =
        List.length (closingLayerHistory past (m+1) t) := by
      simpa [History.graphSequence] using len
    rw [closingLayerHistory_length past L depth,
      closingLayerHistory_length past L depth] at lengths
    omega
  constructor
  · intro coherent
    apply (tables_compatible_iff_local
      (fun n s => closingLayerHistory past (n+1) s) out).mp
    constructor
    · intro n m s t eq
      obtain rfl := timeEq n m s t (Or.inl eq)
      exact (coherent n).1 s t ((closingLayerShape_exact past shape rep _ .one s t).mpr eq)
    · intro n m s t eq
      obtain rfl := timeEq n m s t (Or.inr eq)
      exact (coherent n).2 s t ((closingLayerShape_exact past shape rep _ .two s t).mpr eq)
  · rintro ⟨σ,correct⟩ n
    exact (shapeCoherent_iff_local _ _ (closingLayerShape_exact past shape rep _) (out n)).mpr
      ⟨σ,correct n⟩

def strategyContinuationPolicy {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂) :
    ContinuationPolicy H I₁ I₂ O₁ O₂ :=
  fun n s => (σ.one (currentView .one (closingLayerHistory past (n+1) s)),
    σ.two (currentView .two (closingLayerHistory past (n+1) s)))

theorem strategyContinuationPolicy_coherent {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (rep : RepresentsInputShape past shape) :
    ContinuationCoherent shape (strategyContinuationPolicy σ past) := by
  intro n
  constructor
  · intro s t eq
    exact congrArg σ.one ((closingLayerShape_exact past shape rep _ .one s t).mp eq)
  · intro s t eq
    exact congrArg σ.two ((closingLayerShape_exact past shape rep _ .two s t).mp eq)

/-- Every strategy on one realization of a shape has an exact continuation
on any other realization. This is one strategy for all roots, all graph
alternatives, all private inputs and all future depths, in either direction.
The two initial depths may differ; the new strategy knows its own depth. -/
theorem continuation_strategy_transfer {H I₁ I₂ O₁ O₂ : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past other : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (otherRep : RepresentsInputShape other shape)
    (L : Nat) (otherDepth : ∀ h, List.length (other h) = L)
    (σ : StrategyPair I₁ I₂ O₁ O₂) :
    ∃ τ : StrategyPair I₁ I₂ O₁ O₂,
      strategyContinuationPolicy τ other = strategyContinuationPolicy σ past := by
  obtain ⟨τ,correct⟩ := (continuation_coherent_iff_local other shape otherRep L otherDepth
    (strategyContinuationPolicy σ past)).mp
      (strategyContinuationPolicy_coherent σ past shape rep)
  refine ⟨τ,?_⟩
  funext n s
  exact Prod.ext (correct n s).1 (correct n s).2

end Characterisation
