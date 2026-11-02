/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingOfferRealization
import DistributedSynthesis.Library.Distributed.LeaderPhases.PhaseOfferMinima

/-! Replayed closing labels retain priority minima accumulated before the
closing window. The collector therefore need not reset progress at the cut. -/
namespace Characterisation
open DistributedSynthesis

def closingMinimumStep {Q J I₁ I₂ O₁ O₂ : Type} {C : Nat}
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (priority : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → J → Fin (C+1))
    (state : Q × (J → Fin (C+1))) (input : I₁ × I₂ × Graph) (output : O₁ × O₂) :
    Q × (J → Fin (C+1)) :=
  phaseMinimumStep (fun q letter => step q letter.1 letter.2)
    (fun q letter => priority q letter.1 letter.2) state (input,output)

/-- The advertised minimum is the minimum of the incoming phase minimum
and every priority in the actual closing trace, including its last output. -/
theorem closingOffer_minima_exact {H Q J I₁ I₂ O₁ O₂ : Type} {B C D n : Nat}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (priority : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → J → Fin (C+1))
    (initial : H → Q × (J → Fin (C+1)))
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ (Q × (J → Fin (C+1))) B D n)
    (realizes : ClosingOfferRealizes P past (closingMinimumStep step priority) initial expected bound root move)
    (i : Fin move.1.val) (j : J) :
    (move.2.2.2.2 i).2 j = min ((initial (closingLayerRoot n (move.2.2.1 i))).2 j)
      (phaseWordMinima (fun q letter => step q letter.1 letter.2)
        (fun q letter => priority q letter.1 letter.2)
        (initial (closingLayerRoot n (move.2.2.1 i))).1
        (closingLayerTrace expected n bound (move.2.2.1 i)) j) := by
  have replay := realizes.2.2.2.1 i
  simp only [closingMinimumStep] at replay
  rw [phaseMinimumRun_accumulator] at replay
  exact congrArg (fun state => state.2 j) replay

/-- If the incoming labels were accumulated from the preceding leader
boundary, the certificate contains the minimum of that whole phase, not
merely the bounded closing window. Prefix traces may have arbitrary length. -/
theorem closingOffer_minima_from_phase_start {H Q J I₁ I₂ O₁ O₂ : Type} {B C D n : Nat}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q)
    (priority : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → J → Fin (C+1))
    (start : H → Q)
    (prefixTrace : H → List ((I₁ × I₂ × Graph) × (O₁ × O₂)))
    (initial : H → Q × (J → Fin (C+1)))
    (incoming : ∀ h, initial h = (prefixTrace h).foldl
      (fun q letter => closingMinimumStep step priority q letter.1 letter.2)
      (start h,fun _ => Fin.last C))
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ (Q × (J → Fin (C+1))) B D n)
    (realizes : ClosingOfferRealizes P past (closingMinimumStep step priority) initial expected bound root move)
    (i : Fin move.1.val) (j : J) :
    (move.2.2.2.2 i).2 j =
      phaseWordMinima (fun q letter => step q letter.1 letter.2)
        (fun q letter => priority q letter.1 letter.2)
        (start (closingLayerRoot n (move.2.2.1 i)))
        (prefixTrace (closingLayerRoot n (move.2.2.1 i)) ++
          closingLayerTrace expected n bound (move.2.2.1 i)) j := by
  have replay := realizes.2.2.2.1 i
  rw [incoming, ← List.foldl_append] at replay
  simp only [closingMinimumStep] at replay
  rw [phaseMinimumRun_exact] at replay
  exact congrArg (fun state => state.2 j) replay

end Characterisation
