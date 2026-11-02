/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalEdgeAnnotation

/-!
# Physical phase roots from one carried hybrid edge annotation

The carried finite physical-edge annotation is already the smallest phase
package.  On a strict edge it installs the sibling table belonging to the
literal semantic child.  The descriptor source of that table is exactly the
child's live thread root.  A row need not be stored in the annotation: it is
physical-cut proof data and is used only to show that the table-emitted target
code has a particular live slot.

This file supplies the final table-to-carrier adapter.  If the proof-tree
strict child is chosen to represent the target code literally emitted by the
physical table, then the root read from the child annotation is that target's
exact live slot.  Consequently its indexed-lineage thread priority is the
priority of the same slot.  There is no representative re-selection, policy
mosaic, history field, orientation oracle, or strict-leader signal.
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

/-- No additional phase coordinate is required beyond the physical tables
already selected at the exact parent semantic occurrence. -/
noncomputable abbrev ProfiledRawJointHybridPhysicalPhaseAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

/-- The initial phase annotation. -/
noncomputable abbrev profiledRawJointHybridInitialPhysicalPhaseAnnotation :=
  profiledRawJointHybridInitialPhysicalAnnotation A

/-- The phase update is exactly the source-sensitive carried edge update. -/
noncomputable abbrev profiledRawJointHybridPhysicalPhaseAnnotationAdvance :=
  profiledRawJointHybridPhysicalAnnotationAdvance A strategy hwin

/-- Optional pointwise priority read at a strict physical cut. -/
def profiledRawJointHybridStrictPhysicalCutPriority
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (annotation : ProfiledRawJointHybridPhysicalPhaseAnnotation A) :
    Option Nat :=
  (profiledRawJointHybridStrictPhysicalCutRoot A actual annotation).map
    (profiledRawJointThreadRootPriority A)

/-! ## Exact target-code handoff -/

/-- If a strict hybrid child represents one table-emitted target code, the
root read from the annotation installed at that edge is exactly the live-root
option of that target code.  This is the orientation-neutral core theorem. -/
theorem
    profiledRawJointHybridPhysicalPhaseAdvance_root_eq_targetCurrentSlots
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalPhaseAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hchild : source.step A (.strict actual) = .oneSided child)
    (hcode : child.code A = target) :
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointHybridPhysicalPhaseAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      profiledRawJointOneSidedCurrentSlots A actual.side.other target () := by
  rw [profiledRawJointHybridPhysicalAnnotationAdvance_strict_root_eq A
    strategy hwin]
  simp only [ProfiledRawJointHybridSemanticState.strictLiveRoot, hchild]
  rw [hcode]

/-- A table-emitted target with a live left slot gives the exact carried root
on a right physical block. -/
theorem profiledRawJointHybridPhysicalPhaseAdvance_rightRoot_eq
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalPhaseAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hside : actual.side = .right)
    (hchild : source.step A (.strict actual) = .oneSided child)
    (hcode : child.code A = target)
    (hlive : target.family.left () = some slot) :
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointHybridPhysicalPhaseAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      some (.inr slot) := by
  rw [profiledRawJointHybridPhysicalPhaseAdvance_root_eq_targetCurrentSlots A
    strategy hwin source current actual child target hchild hcode]
  simp [profiledRawJointOneSidedCurrentSlots, IndexedLineageSide.other,
    hside, hlive]

/-- Left physical-block mirror. -/
theorem profiledRawJointHybridPhysicalPhaseAdvance_leftRoot_eq
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalPhaseAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hside : actual.side = .left)
    (hchild : source.step A (.strict actual) = .oneSided child)
    (hcode : child.code A = target)
    (hlive : target.family.right () = some slot) :
    profiledRawJointHybridStrictPhysicalCutRoot A actual
        (profiledRawJointHybridPhysicalPhaseAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      some (.inl slot) := by
  rw [profiledRawJointHybridPhysicalPhaseAdvance_root_eq_targetCurrentSlots A
    strategy hwin source current actual child target hchild hcode]
  simp [profiledRawJointOneSidedCurrentSlots, IndexedLineageSide.other,
    hside, hlive]

/-! ## Pointwise priority readback -/

/-- The chosen indexed-lineage priority at a right close is exactly the
priority of the table-emitted live target slot. -/
theorem profiledRawJointHybridPhysicalPhaseAdvance_rightPriority_eq
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalPhaseAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawLeftSlot A)
    (hside : actual.side = .right)
    (hchild : source.step A (.strict actual) = .oneSided child)
    (hcode : child.code A = target)
    (hlive : target.family.left () = some slot) :
    profiledRawJointHybridStrictPhysicalCutPriority A actual
        (profiledRawJointHybridPhysicalPhaseAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      some (profiledRawJointThreadRootPriority A (.inr slot)) := by
  simp only [profiledRawJointHybridStrictPhysicalCutPriority]
  rw [profiledRawJointHybridPhysicalPhaseAdvance_rightRoot_eq A strategy hwin
    source current actual child target slot hside hchild hcode hlive]
  rfl

/-- Left-close mirror. -/
theorem profiledRawJointHybridPhysicalPhaseAdvance_leftPriority_eq
    (source : ProfiledRawJointHybridSemanticState A strategy)
    (current : ProfiledRawJointHybridPhysicalPhaseAnnotation A)
    (actual : ProfiledRawJointActualDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (child : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (slot : ProfiledRawRightSlot A)
    (hside : actual.side = .left)
    (hchild : source.step A (.strict actual) = .oneSided child)
    (hcode : child.code A = target)
    (hlive : target.family.right () = some slot) :
    profiledRawJointHybridStrictPhysicalCutPriority A actual
        (profiledRawJointHybridPhysicalPhaseAnnotationAdvance A strategy hwin
          source current (.strict actual)) =
      some (profiledRawJointThreadRootPriority A (.inl slot)) := by
  simp only [profiledRawJointHybridStrictPhysicalCutPriority]
  rw [profiledRawJointHybridPhysicalPhaseAdvance_leftRoot_eq A strategy hwin
    source current actual child target slot hside hchild hcode hlive]
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
