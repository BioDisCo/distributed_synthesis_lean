/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.CoordinatorResponses

/-! Compatibility across communicated tables. The table index is not an
additional observation: entries from different tables must agree whenever
an actual process has the same view. -/
namespace Characterisation
open DistributedSynthesis

/-- Scenarios may belong to different phases, windows, or coordinator
choices. Compatibility is imposed across the entire family. -/
def TablesCompatible {J I₁ I₂ O₁ O₂ : Type*} {S : J → Type*}
    (hist : (j : J) → S j → EnvHistory I₁ I₂)
    (out : (j : J) → S j → O₁ × O₂) : Prop :=
  (∀ j k s t, currentView .one (hist j s) = currentView .one (hist k t) →
    (out j s).1 = (out k t).1) ∧
  (∀ j k s t, currentView .two (hist j s) = currentView .two (hist k t) →
    (out j s).2 = (out k t).2)

/-- An arbitrary, possibly infinite family of instructions has a single
local implementation exactly when it agrees on equal observations, including
observations arising under different table indices. -/
theorem tables_compatible_iff_local {J I₁ I₂ O₁ O₂ : Type*}
    [Nonempty O₁] [Nonempty O₂] {S : J → Type*}
    (hist : (j : J) → S j → EnvHistory I₁ I₂)
    (out : (j : J) → S j → O₁ × O₂) :
    TablesCompatible hist out ↔ ∃ σ : StrategyPair I₁ I₂ O₁ O₂, ∀ j s,
      σ.one (currentView .one (hist j s)) = (out j s).1 ∧
      σ.two (currentView .two (hist j s)) = (out j s).2 := by
  constructor
  · intro h
    obtain ⟨one, hOne⟩ := factor_local_response
      (fun x : Sigma S => currentView .one (hist x.1 x.2))
      (fun x : Sigma S => (out x.1 x.2).1)
      (fun x y eq => h.1 x.1 y.1 x.2 y.2 eq)
    obtain ⟨two, hTwo⟩ := factor_local_response
      (fun x : Sigma S => currentView .two (hist x.1 x.2))
      (fun x : Sigma S => (out x.1 x.2).2)
      (fun x y eq => h.2 x.1 y.1 x.2 y.2 eq)
    exact ⟨⟨one,two⟩, fun j s => ⟨hOne ⟨j,s⟩,hTwo ⟨j,s⟩⟩⟩
  · rintro ⟨σ,h⟩
    constructor
    · intro j k s t eq
      rw [← (h j s).1, ← (h k t).1, eq]
    · intro j k s t eq
      rw [← (h j s).2, ← (h k t).2, eq]

/-- If both processes can recover the table index from their actual view,
within-table consistency suffices. This hypothesis must be proved for the
chosen communication schedule, rather than giving processes the index. -/
theorem compatible_of_observable_index {J I₁ I₂ O₁ O₂ : Type*} {S : J → Type*}
    (hist : (j : J) → S j → EnvHistory I₁ I₂)
    (out : (j : J) → S j → O₁ × O₂)
    (oneIndex : View I₁ I₂ .one → J) (twoIndex : View I₁ I₂ .two → J)
    (oneRecovers : ∀ j s, oneIndex (currentView .one (hist j s)) = j)
    (twoRecovers : ∀ j s, twoIndex (currentView .two (hist j s)) = j)
    (oneCoherent : ∀ j s t, currentView .one (hist j s) = currentView .one (hist j t) →
      (out j s).1 = (out j t).1)
    (twoCoherent : ∀ j s t, currentView .two (hist j s) = currentView .two (hist j t) →
      (out j s).2 = (out j t).2) : TablesCompatible hist out := by
  constructor
  · intro j k s t eq
    have same : j = k := by rw [← oneRecovers j s, ← oneRecovers k t, eq]
    subst k
    exact oneCoherent j s t eq
  · intro j k s t eq
    have same : j = k := by rw [← twoRecovers j s, ← twoRecovers k t, eq]
    subst k
    exact twoCoherent j s t eq

end Characterisation
