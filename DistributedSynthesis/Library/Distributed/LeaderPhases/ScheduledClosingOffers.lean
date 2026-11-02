/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderHandoverProgress

/-! Collect all checked certificates for scheduled live first exits of a
fixed carried policy. The controller does not choose a subset of exits or
provide independently guessed target entries. -/
namespace Characterisation
open DistributedSynthesis

abbrev ScheduledClosingCandidate (H I₁ I₂ O₁ O₂ Q : Type) (B D : Nat) :=
  Σ n : Fin D, ClosingLayer H I₁ I₂ (n.val+1) ×
    ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1)

section
variable {H I₁ I₂ O₁ O₂ Q : Type} {B C D : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]

instance scheduledClosingCandidate_fintype :
    Fintype (ScheduledClosingCandidate H I₁ I₂ O₁ O₂ Q B D) := by
  unfold ScheduledClosingCandidate
  infer_instance

variable (shape : InputShape H) (initialWindow : Bool)
variable (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)

def checkScheduledClosingCandidate
    (candidate : ScheduledClosingCandidate H I₁ I₂ O₁ O₂ Q B D) : Bool :=
  let n := candidate.1
  let root := candidate.2.1
  let move := candidate.2.2
  decide (closingWindowScheduled initialWindow D (n.val+1) = true ∧
    closingFlagAt live (n.val+1) root = true ∧
    closingFirstExit (closingFlagAt boundary) (n.val+1) root = true ∧
    move.2.1 = expected) &&
  checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
    (closingFlagAt live (n.val+1)) root (fun _ => True) move

def scheduledClosingCertificates : Finset (ScheduledClosingCandidate H I₁ I₂ O₁ O₂ Q B D) :=
  Finset.univ.filter fun candidate =>
    checkScheduledClosingCandidate shape initialWindow boundary live step initial expected candidate = true

theorem mem_scheduledClosingCertificates_iff
    (n : Fin D) (root : ClosingLayer H I₁ I₂ (n.val+1))
    (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1)) :
    ⟨n,root,move⟩ ∈ scheduledClosingCertificates shape initialWindow boundary live step initial expected ↔
      (closingWindowScheduled initialWindow D (n.val+1) = true ∧
        closingFlagAt live (n.val+1) root = true ∧
        closingFirstExit (closingFlagAt boundary) (n.val+1) root = true ∧
        move.2.1 = expected) ∧
      checkClosingBoundaryCertificate shape step initial (show n.val+1 ≤ D by omega)
        (closingFlagAt live (n.val+1)) root (fun _ => True) move = true := by
  simp only [scheduledClosingCertificates, Finset.mem_filter, Finset.mem_univ, true_and,
    checkScheduledClosingCandidate, Bool.and_eq_true, decide_eq_true_eq]

variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

/-- Preserve whole certificates when passing to the public outcome alphabet.
Different legal numberings are all included. -/
def scheduledClosingOffers : Finset (LeaderHandover Q B C) :=
  (scheduledClosingCertificates shape initialWindow boundary live step initial expected).image
    (fun candidate => certificateHandover slot minimum candidate.2.2)

theorem mem_scheduledClosingOffers_iff (outcome : LeaderHandover Q B C) :
    outcome ∈ scheduledClosingOffers shape initialWindow boundary live step initial expected slot minimum ↔
      ∃ (n : Fin D) (root : ClosingLayer H I₁ I₂ (n.val+1))
        (move : ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D (n.val+1)),
        ⟨n,root,move⟩ ∈ scheduledClosingCertificates shape initialWindow boundary live step initial expected ∧
        certificateHandover slot minimum move = outcome := by
  simp only [scheduledClosingOffers, Finset.mem_image]
  constructor
  · rintro ⟨⟨n,root,move⟩,member,equality⟩
    exact ⟨n,root,move,member,equality⟩
  · rintro ⟨n,root,move,member,equality⟩
    exact ⟨⟨n,root,move⟩,member,equality⟩

/-- Every demanded exit in a checked bundle is offered, using exactly that
bundle's common policy and its complete target certificate. -/
theorem scheduledClosingOffers_of_bundle
    (bundle : FirstExitBundle H I₁ I₂ O₁ O₂ Q B D)
    (checked : checkScheduledExitBundle shape initialWindow boundary live step initial
      (fun _ => True) expected bundle = true)
    (n : Fin D) (root : ClosingLayer H I₁ I₂ (n.val+1))
    (scheduled : closingWindowScheduled initialWindow D (n.val+1) = true)
    (alive : closingFlagAt live (n.val+1) root = true)
    (exit : closingFirstExit (closingFlagAt boundary) (n.val+1) root = true) :
    certificateHandover slot minimum (bundle.2 n root) ∈
      scheduledClosingOffers shape initialWindow boundary live step initial expected slot minimum := by
  have correct := (checkScheduledExitBundle_correct shape initialWindow boundary live step initial
    (fun _ => True) expected bundle).mp checked
  have each := correct.2.2 n root scheduled alive exit
  apply (mem_scheduledClosingOffers_iff shape initialWindow boundary live step initial expected slot minimum _).mpr
  refine ⟨n,root,bundle.2 n root,?_,rfl⟩
  exact (mem_scheduledClosingCertificates_iff shape initialWindow boundary live step initial expected n root _).mpr
    ⟨⟨scheduled,alive,exit,each.1.trans correct.1⟩,each.2⟩

end
end Characterisation
