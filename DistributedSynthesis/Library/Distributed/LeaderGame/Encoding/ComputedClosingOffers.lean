/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ScheduledClosingOffers

/-! Eliminate guessed policies and target annotations from the collector.
The carried policy is fixed; a target is computed from its selected complete
component. All legal target numberings remain in the enumeration. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Q : Type} {B C D n : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (shape : InputShape H)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)

def computedClosingCertificate (bound : n ≤ D) (size : Fin (B+1))
    (keep : Fin size.val → ClosingLayer H I₁ I₂ n) :
    ClosingBoundaryCertificate H I₁ I₂ O₁ O₂ Q B D n :=
  ⟨size,expected,keep,computedClosingTarget shape step initial expected bound keep⟩

omit [Fintype O₁] [Fintype O₂] [Fintype Q] in
theorem computedClosingCertificate_checked (bound : n ≤ D) (size : Fin (B+1))
    (keep : Fin size.val → ClosingLayer H I₁ I₂ n)
    (live : ClosingLayer H I₁ I₂ n → Bool) (root : ClosingLayer H I₁ I₂ n) :
    checkClosingBoundaryCertificate shape step initial bound live root (fun _ => True)
      (computedClosingCertificate shape step initial expected bound size keep) = true ↔
      ClosingPolicyCoherent shape expected ∧
        checkClosingEnumeration (closingComponentMask (closingLayerShape shape n) live root) keep = true := by
  simp only [computedClosingCertificate,checkClosingBoundaryCertificate,checkClosingMove,
    Bool.and_eq_true,decide_eq_true_eq,and_true,eq_self]

variable (initialWindow : Bool) (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

/-- The collector searches only for a depth, an exit root, and a complete
target numbering. Every target label is recomputed from the carried policy. -/
theorem mem_scheduledClosingOffers_computed_iff (outcome : LeaderHandover Q B C) :
    outcome ∈ scheduledClosingOffers shape initialWindow boundary live step initial expected slot minimum ↔
      ∃ (t : Fin D) (root : ClosingLayer H I₁ I₂ (t.val+1)) (size : Fin (B+1))
        (keep : Fin size.val → ClosingLayer H I₁ I₂ (t.val+1)),
        closingWindowScheduled initialWindow D (t.val+1) = true ∧
        closingFlagAt live (t.val+1) root = true ∧
        closingFirstExit (closingFlagAt boundary) (t.val+1) root = true ∧
        ClosingPolicyCoherent shape expected ∧
        checkClosingEnumeration (closingComponentMask (closingLayerShape shape (t.val+1))
          (closingFlagAt live (t.val+1)) root) keep = true ∧
        certificateHandover slot minimum
          (computedClosingCertificate shape step initial expected (by omega) size keep) = outcome := by
  rw [mem_scheduledClosingOffers_iff]
  constructor
  · rintro ⟨t,root,⟨size,policy,keep,target⟩,member,output⟩
    have checked := (mem_scheduledClosingCertificates_iff shape initialWindow boundary live step initial expected t root _).mp member
    have policyEq : policy = expected := checked.1.2.2.2
    subst policy
    have checks := checked.2
    simp only [checkClosingBoundaryCertificate,checkClosingMove,Bool.and_eq_true,decide_eq_true_eq,and_true] at checks
    have targetEq : target = computedClosingTarget shape step initial expected (by omega) keep := checks.1.2
    subst target
    exact ⟨t,root,size,keep,checked.1.1,checked.1.2.1,checked.1.2.2.1,checks.1.1,checks.2,output⟩
  · rintro ⟨t,root,size,keep,scheduled,alive,exit,coherent,complete,output⟩
    refine ⟨t,root,computedClosingCertificate shape step initial expected (by omega) size keep,?_,output⟩
    apply (mem_scheduledClosingCertificates_iff shape initialWindow boundary live step initial expected t root _).mpr
    exact ⟨⟨scheduled,alive,exit,rfl⟩,
      (computedClosingCertificate_checked shape step initial expected (by omega) size keep _ root).mpr ⟨coherent,complete⟩⟩

end
end Characterisation
