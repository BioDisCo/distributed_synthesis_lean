/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayerOffersCorrect
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.ComputedClosingOffers
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayersCorrect

/-! Assemble the generated layer collectors into the exact existing
scheduled closing collector. Each selected component contributes its entire
numbered target with replayed labels, predecessors, and minima. -/
namespace Characterisation
open DistributedSynthesis

section
variable {H I₁ I₂ O₁ O₂ Q : Type} {B C D J : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (sizes : Fin D → Nat)
variable (numbers : (t : Fin D) → ClosingLayer H I₁ I₂ (t.val+1) ≃ Fin (sizes t))
variable (labelNumber : Q ≃ Fin J) (shape : InputShape H)
variable (initialWindow : Bool) (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

def scheduledLayerCode (t : Fin D) : EncodedClosingLayerOffers.Data :=
  EncodedClosingLayerOffers.encode (numbers t) labelNumber (closingLayerShape shape (t.val+1))
    (closingFlagAt live (t.val+1))
    (fun root => closingWindowScheduled initialWindow D (t.val+1) &&
      closingFlagAt live (t.val+1) root && closingFirstExit (closingFlagAt boundary) (t.val+1) root)
    (closingLayerLabels step initial expected (t.val+1) (by omega))
    (fun root => slot (closingLayerRoot (t.val+1) root))
    (fun root => minimum (closingLayerLabels step initial expected (t.val+1) (by omega) root))

def scheduledCollectorCode : Bool × List EncodedClosingLayerOffers.Data :=
  (decide (ClosingPolicyCoherent shape expected),
    List.ofFn (scheduledLayerCode sizes numbers labelNumber shape initialWindow boundary live step initial expected slot minimum))

/-- The computed data produce exactly the old scheduled collector, rather
than only a sound subset of its closing choices. -/
theorem scheduledCollectorCode_correct (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode labelNumber outcome ∈
      EncodedClosingLayerOffers.collect
        (scheduledCollectorCode sizes numbers labelNumber shape initialWindow boundary live step initial expected slot minimum) ↔
      outcome ∈ scheduledClosingOffers shape initialWindow boundary live step initial expected slot minimum := by
  rw [mem_scheduledClosingOffers_computed_iff]
  by_cases coherent : ClosingPolicyCoherent shape expected
  · simp only [EncodedClosingLayerOffers.collect,scheduledCollectorCode,coherent,decide_true,↓reduceIte,
      List.mem_flatMap,List.mem_ofFn]
    constructor
    · rintro ⟨data,⟨t,rfl⟩,member⟩
      obtain ⟨root,size,keep,exit,complete,output⟩ :=
        (EncodedClosingLayerOffers.offers_encode (numbers t) labelNumber _ _ _ _ _ _ outcome).mp member
      simp only [Bool.and_eq_true] at exit
      obtain ⟨⟨scheduled,alive⟩,first⟩ := exit
      exact ⟨t,root,size,keep,scheduled,alive,first,True.intro,complete,output⟩
    · rintro ⟨t,root,size,keep,scheduled,alive,first,_,complete,output⟩
      refine ⟨_,⟨t,rfl⟩,?_⟩
      apply (EncodedClosingLayerOffers.offers_encode (numbers t) labelNumber _ _ _ _ _ _ outcome).mpr
      exact ⟨root,size,keep,by simpa only [Bool.and_eq_true] using And.intro (And.intro scheduled alive) first,complete,output⟩
  · simp [EncodedClosingLayerOffers.collect,scheduledCollectorCode,coherent]

end

section Numbered
variable {H I₁ I₂ O₁ O₂ Q : Type} {B C D J R E : Nat}
variable [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
variable [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂]
variable [DecidableEq O₁] [DecidableEq O₂] [DecidableEq Q]
variable (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
variable (labelNumber : Q ≃ Fin J) (shape : InputShape H)
variable (initialWindow : Bool) (boundary live : ClosingFlagTable H I₁ I₂ D)
variable (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : H → Q)
variable (expected : ClosingPolicy H I₁ I₂ O₁ O₂ D)
variable (slot : H → Fin (B+1)) (minimum : Q → Fin (C+1))

/-- Fix the layer order to the numeric source-root/environment-word order. -/
noncomputable def numberedScheduledCollectorCode : Bool × List EncodedClosingLayerOffers.Data :=
  scheduledCollectorCode (fun t : Fin D => EncodedClosingLayers.count (R,E,t.val+1))
    (fun _ => EncodedClosingLayers.number root env) labelNumber shape initialWindow boundary live
    step initial expected slot minimum

theorem numberedScheduledCollectorCode_correct (outcome : LeaderHandover Q B C) :
    EncodedLeaderAlphabet.outcomeEncode labelNumber outcome ∈
      EncodedClosingLayerOffers.collect
        (numberedScheduledCollectorCode root env labelNumber shape initialWindow boundary live step initial expected slot minimum) ↔
      outcome ∈ scheduledClosingOffers shape initialWindow boundary live step initial expected slot minimum :=
  scheduledCollectorCode_correct _ _ labelNumber shape initialWindow boundary live step initial expected slot minimum outcome

end Numbered
end Characterisation
