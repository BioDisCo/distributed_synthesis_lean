/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledClosingOffers
import DistributedSynthesis.Library.Distributed.LeaderPhases.HandoverHistoryLifting

/-! A collected certificate represents one complete successor family of
the current concrete source family. All its labels are replayed from the
same carried policy and all predecessor links are literal history prefixes. -/
namespace Characterisation
open DistributedSynthesis

/-- Semantic conclusion for a certificate. The target histories are fixed
by its retained scenarios, rather than selected independently per property. -/
def ClosingOfferRealizes {H I₁ I₂ O₁ O₂ Q : Type} {B D n : Nat}
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂)
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D) (bound : n ≤ D)
    (root : ClosingLayer H I₁ I₂ n)
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n) : Prop :=
  Function.Injective (closingLayerHistory past n ∘ move.2.2.1) ∧
  (∀ k, InputConnected P (closingLayerHistory past n root) k ↔
    ∃ i, closingLayerHistory past n (move.2.2.1 i) = k) ∧
  RepresentsInputShape (closingLayerHistory past n ∘ move.2.2.1) move.2.2.2.1 ∧
  (∀ i, move.2.2.2.2 i =
    (closingLayerTrace expected n bound (move.2.2.1 i)).foldl
      (fun q letter => step q letter.1 letter.2) (initial (closingLayerRoot n (move.2.2.1 i)))) ∧
  (∀ i, (past (closingLayerRoot n (move.2.2.1 i))).IsPrefix
    (closingLayerHistory past n (move.2.2.1 i)))

section
variable {H I₁ I₂ O₁ O₂ Q : Type} {B D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q] [Nonempty O₁] [Nonempty O₂]

theorem scheduledClosingCertificate_realizes
    (P : List Graph → Prop) (past : H → EnvHistory I₁ I₂) (injective : Function.Injective past)
    (shape : InputShape H) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L)
    (initialWindow : Bool) (boundary live : ClosingFlagTable H I₁ I₂ D)
    (liveExact : ∀ m s, live m s = true ↔ P (History.graphSequence (closingLayerHistory past m.val s)))
    (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
    (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
    (n : Fin D) (root : ClosingLayer H I₁ I₂ (n.val+1))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1))
    (member : ⟨n,root,move⟩ ∈ scheduledClosingCertificates shape initialWindow boundary live step initial expected)
    (covers : ∀ k, InputConnected P (closingLayerHistory past (n.val+1) root) k →
      ∃ s, closingLayerHistory past (n.val+1) s = k) :
    ClosingOfferRealizes P past step initial expected (show n.val+1 ≤ D by omega) root move := by
  have checked := (mem_scheduledClosingCertificates_iff shape initialWindow boundary live step initial expected n root move).mp member
  have exactLive := closingLiveTable_exact P past live liveExact (n.val+1) (by omega)
  have correct := (checkClosingBoundaryCertificate_correct_of_target_coverage P past injective shape rep L depth
    step initial (show n.val+1 ≤ D by omega) (closingFlagAt live (n.val+1)) exactLive root
    ((exactLive root).mp checked.1.2.1) covers (fun _ => True) move).mp checked.2
  refine ⟨correct.2.1,correct.2.2,correct.1.2.1.1,?_,?_⟩
  · intro i
    simpa only [checked.1.2.2.2] using correct.1.2.1.2 i
  · exact closingCertificate_parent_prefix past past (fun _ => ⟨[],by simp⟩) move

end
end Characterisation
