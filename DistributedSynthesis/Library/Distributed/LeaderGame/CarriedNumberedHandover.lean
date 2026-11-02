/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.CarriedLeaderMachine

/-! The numbered certificate and the recursively carried state use the same
incoming state and every physical round. A target enumeration is obtained
from the certificate itself; no fresh matching of observation rows is used. -/
namespace Characterisation
open DistributedSynthesis

theorem closingOffer_exact_enumeration {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (out : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n)
    (realizes : ClosingOfferRealizes P past step initial out bound root move) :
    ∃ e : Fin move.1.val ≃ InputHistoryComponent P (closingLayerHistory past n root),
      ∀ i, (e i).val = closingLayerHistory past n (move.2.2.1 i) := by
  let f : Fin move.1.val → InputHistoryComponent P (closingLayerHistory past n root) :=
    fun i => ⟨closingLayerHistory past n (move.2.2.1 i),(realizes.2.1 _).mpr ⟨i,rfl⟩⟩
  have injective : Function.Injective f := fun i j same => realizes.1 (congrArg Subtype.val same)
  have surjective : Function.Surjective f := by
    intro k
    obtain ⟨i,same⟩ := (realizes.2.1 k.val).mp k.property
    exact ⟨i,Subtype.ext same⟩
  exact ⟨Equiv.ofBijective f ⟨injective,surjective⟩,fun _ => rfl⟩

section
variable {Data GQ I₁ I₂ O₁ O₂ : Type} {d K C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable (rank : objective.State → Fin (C+1))
variable (decode : LeaderPhaseOrigin I₁ I₂ → CarriedLeaderState Data objective.State I₁ I₂ →
  StrategyPair I₁ I₂ O₁ O₂)
variable (update : CarriedLeaderState Data objective.State I₁ I₂ → LeaderPhaseOrigin I₁ I₂ →
  LeaderPhaseOrigin I₁ I₂ → (EnvHistory I₁ I₂ → objective.State) → (EnvHistory I₁ I₂ → Nat) → Data)

/-- The finite annotation agrees with the actual recursive update, including
the entire phase minimum. The public-data updater is irrelevant to these
two fields and cannot reset the incoming objective state. -/
theorem leaderAnnotation_matches_carried_advance
    (state : CarriedLeaderState Data objective.State I₁ I₂)
    (old target : LeaderPhaseOrigin I₁ I₂)
    (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective)
    (root word : EnvHistory I₁ I₂) (depth : List.length root = old.1)
    (incoming : q.1.2 = state.label root) (nonempty : word ≠ []) :
    let next := carriedLeaderAdvance (fun s input output => objective.step s (input,output))
      (fun s => (rank s).val) decode update state old target
    let value := strategyContinuationLabel (decode old state) (leaderAnnotationStep M objective rank)
      (resetLeaderMinimum objective q) root word
    value.1.2 = next.label (root++word) ∧ (value.2 ()).val = next.minimum (root++word) := by
  have takeRoot : (root++word).take old.1 = root := by rw [← depth,List.take_left]
  have dropRoot : (root++word).drop old.1 = word := by rw [← depth,List.drop_left]
  have length : List.length (root++word)-old.1-1 = List.length word-1 := by
    rw [List.length_append,depth,Nat.add_sub_cancel_left]
  dsimp only [carriedLeaderAdvance]
  constructor
  · rw [leaderAnnotation_objective,takeRoot,dropRoot,incoming]
  · rw [leaderAnnotation_minimum M objective rank (decode old state) q root word nonempty,
      takeRoot,dropRoot,length,incoming]

end
end Characterisation
