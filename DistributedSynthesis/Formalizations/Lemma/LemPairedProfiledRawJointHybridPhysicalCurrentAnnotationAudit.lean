/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalEdgeAnnotation

/-!
# Audit of current-annotation provenance in the carried hybrid policy

The parent-linked construction proves that a child's annotation is exactly
the entry selected by its parent move.  It does **not** prove that, after
rationalization, the semantic source selected at that child would itself
have produced the installed annotation.  For the physical annotation this
is visible in the kernel: the update is replace-not-accumulate and ignores
its current-annotation argument, so the local parent-link validity relation
is invariant under replacing the current annotation arbitrarily.

This is a negative interface audit, not a new assumption.  It records why a
table target belonging to an independently built phase-live package cannot
be identified with the strict child selected by the carried policy merely
from current-state reachability.  The sound positive construction must use
the carried policy's selected move and its child-annotation table directly
when building the physical controller.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

/-- The concrete physical edge update contains no information about the
previously installed annotation. -/
theorem profiledRawJointHybridPhysicalAnnotationAdvance_current_irrel
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current₁ current₂ : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (direction : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current₁ direction =
      profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin source
        current₂ direction := by
  cases source <;> cases direction <;> rfl

/-- Kernel-level non-identifiability statement: the exact same semantic
source, raw move, and complete child-annotation table satisfy the concrete
parent-link law with *any* current physical annotation. -/
theorem profiledRawJointHybridPhysicalCarriedParentLinkValid_any_current
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current₁ current₂ : ProfiledRawJointHybridPhysicalEdgeAnnotation A) :
    ProfiledRawJointHybridCarriedParentLinkValid A strategy
      (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
      (source.code A) current₁ (source.move A)
      (fun direction ↦
        profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin
          source current₂ direction) := by
  refine ⟨source, rfl, rfl, ?_⟩
  intro direction
  exact profiledRawJointHybridPhysicalAnnotationAdvance_current_irrel A
    strategy hwin source current₁ current₂ direction

/-- Equivalently, concrete local parent-link legality cannot distinguish two
current physical annotations.  Reachability still says where the annotation
came from—the preceding parent—but this local inversion cannot reassign that
provenance to the semantic representative selected at the current node. -/
theorem profiledRawJointHybridPhysicalCarriedParentLinkValid_current_iff
    (code : ProfiledRawJointHybridCode A)
    (current₁ current₂ : ProfiledRawJointHybridPhysicalEdgeAnnotation A)
    (move : ProfiledRawJointHybridMove A)
    (children : ProfiledRawJointHybridDirection
      (In₁ := In₁) (In₂ := In₂) →
        ProfiledRawJointHybridPhysicalEdgeAnnotation A) :
    ProfiledRawJointHybridCarriedParentLinkValid A strategy
        (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
        code current₁ move children ↔
      ProfiledRawJointHybridCarriedParentLinkValid A strategy
        (profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin)
        code current₂ move children := by
  constructor
  · rintro ⟨source, hcode, hmove, hchildren⟩
    refine ⟨source, hcode, hmove, ?_⟩
    intro direction
    rw [profiledRawJointHybridPhysicalAnnotationAdvance_current_irrel A
      strategy hwin source current₂ current₁ direction]
    exact hchildren direction
  · rintro ⟨source, hcode, hmove, hchildren⟩
    refine ⟨source, hcode, hmove, ?_⟩
    intro direction
    rw [profiledRawJointHybridPhysicalAnnotationAdvance_current_irrel A
      strategy hwin source current₁ current₂ direction]
    exact hchildren direction

end

end DetParityAutomaton

end DistributedSynthesis
