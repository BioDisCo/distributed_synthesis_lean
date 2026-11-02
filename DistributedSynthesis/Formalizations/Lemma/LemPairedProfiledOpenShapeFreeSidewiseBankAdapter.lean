/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenActiveLaneShapeFreeFibre
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedSidewiseBankAlphabet
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalControlledSemantic
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedPinnedProvenance

/-!
# Shape-free active-lane fibres in the fixed sidewise alphabet

The operational sidewise bank must not be indexed by the optional carrier's
four proof-side lane shapes.  In particular, process one cannot in general
distinguish a right-only point from a both-active point with the same literal
sender view, and process two cannot distinguish the left mirror.

There is an equally important hidden coordinate: the parity-DPA control.  A
local class must not freeze the control of one chosen anchor.  We therefore
form the fibre on the product of an active semantic point and its *literal*
control, while the relation compares only the active sender view.  Its finite
descriptor image simultaneously saturates all controls and both values of
the opposite-lane activity bit compatible with that view.

For an active right source the finite image is installed in the fixed family
alphabet as `(rightImage, ∅)`.  The active-left class is installed as
`(∅, leftImage)`.  The empty coordinate is merely a typing device for a
one-side fixed controller value; it is not a claim that the opposite semantic
lane is inactive.

All shape elimination, semantic witnesses, and lane projections below are
proof-side.  No process receives a graph, lane, orientation, strict-leader
flag, opposite-lane activity bit, or parity control.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))

private abbrev ShapeFreeDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

private abbrev ShapeFreeFamily :=
  ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode

private abbrev ShapeFreeControl :=
  (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State

noncomputable local instance shapeFreeDescriptorDecidableEq :
    DecidableEq (ShapeFreeDescriptor A initialCode) :=
  Classical.decEq _

/-! ## Active carriers with their literal hidden control -/

/-- Shape-free active-right semantics paired with its actual parity control.
The product contains no opposite-lane activity field beyond what remains in
the proof-only optional semantic point. -/
abbrev ProfiledOpenIndexedActiveRightControlledSemanticPoint :=
  ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
      (I := I) ×
    ShapeFreeControl A initialCode

/-- Active-left mirror. -/
abbrev ProfiledOpenIndexedActiveLeftControlledSemanticPoint :=
  ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
      (I := I) ×
    ShapeFreeControl A initialCode

/-- Reconstruct the already established optional controlled carrier. -/
def ProfiledOpenIndexedActiveRightControlledSemanticPoint.toOptionalControlled
    (point : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  (point.1.optional, point.2)

/-- Left reconstruction. -/
def ProfiledOpenIndexedActiveLeftControlledSemanticPoint.toOptionalControlled
    (point : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenIndexedOptionalControlledSemanticState A strategy hwin basis
      initialCode :=
  (point.1.optional, point.2)

/-- Attach the literal control to a right-only point without retaining its
`left = none` witness in the active carrier. -/
def ProfiledOpenIndexedRightOnlyFreshSemanticPoint.toActiveRightControlled
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) (q : ShapeFreeControl A initialCode) :
    ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy hwin
      basis initialCode :=
  (point.toActiveRight A strategy hwin basis, q)

/-- Both-active right projection with its literal control. -/
def ProfiledOpenIndexedLiveFreshSemanticPoint.toActiveRightControlled
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (q : ShapeFreeControl A initialCode) :
    ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy hwin
      basis initialCode :=
  (point.toActiveRight A strategy hwin basis, q)

/-- Left-only projection. -/
def ProfiledOpenIndexedLeftOnlyFreshSemanticPoint.toActiveLeftControlled
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) (q : ShapeFreeControl A initialCode) :
    ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy hwin basis
      initialCode :=
  (point.toActiveLeft A strategy hwin basis, q)

/-- Both-active left projection. -/
def ProfiledOpenIndexedLiveFreshSemanticPoint.toActiveLeftControlled
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (q : ShapeFreeControl A initialCode) :
    ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy hwin basis
      initialCode :=
  (point.toActiveLeft A strategy hwin basis, q)

/-! ## The view-only relations and actual descriptors -/

/-- Equality ignores the control and opposite-lane activity; both are
saturated by the descriptor image. -/
def ProfiledOpenIndexedActiveRightControlledLocalFibreRel
    (left right : ProfiledOpenIndexedActiveRightControlledSemanticPoint A
      strategy hwin basis initialCode) : Prop :=
  ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis left.1
    right.1

/-- Left mirror. -/
def ProfiledOpenIndexedActiveLeftControlledLocalFibreRel
    (left right : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A
      strategy hwin basis initialCode) : Prop :=
  ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis left.1
    right.1

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedActiveRightControlledLocalFibreRel_reflexive :
    Std.Refl
      (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  ⟨fun _ ↦ (profiledOpenIndexedActiveRightLocalFibreRel_reflexive A strategy
    hwin basis).refl _⟩

theorem profiledOpenIndexedActiveLeftControlledLocalFibreRel_reflexive :
    Std.Refl
      (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  ⟨fun _ ↦ (profiledOpenIndexedActiveLeftLocalFibreRel_reflexive A strategy
    hwin basis).refl _⟩

theorem profiledOpenIndexedActiveRightControlledLocalFibreRel_symmetric :
    Symmetric
      (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  fun _ _ h ↦
    profiledOpenIndexedActiveRightLocalFibreRel_symmetric A strategy hwin basis
      h

theorem profiledOpenIndexedActiveLeftControlledLocalFibreRel_symmetric :
    Symmetric
      (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  fun _ _ h ↦
    profiledOpenIndexedActiveLeftLocalFibreRel_symmetric A strategy hwin basis h

theorem profiledOpenIndexedActiveRightControlledLocalFibreRel_transitive :
    IsTrans _
      (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  ⟨fun _ _ _ h₁ h₂ ↦
    (profiledOpenIndexedActiveRightLocalFibreRel_transitive A strategy hwin basis).trans _ _ _ h₁ h₂⟩

theorem profiledOpenIndexedActiveLeftControlledLocalFibreRel_transitive :
    IsTrans _
      (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  ⟨fun _ _ _ h₁ h₂ ↦
    (profiledOpenIndexedActiveLeftLocalFibreRel_transitive A strategy hwin basis).trans _ _ _ h₁ h₂⟩

theorem profiledOpenIndexedActiveRightControlledLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_symmetric A strategy
      hwin basis initialCode)
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_transitive A
      strategy hwin basis initialCode)

theorem profiledOpenIndexedActiveLeftControlledLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin
        basis initialCode) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_symmetric A strategy
      hwin basis initialCode)
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_transitive A strategy
      hwin basis initialCode)

end

/-- The descriptor reads the literal control stored at this point. -/
noncomputable def profiledOpenActiveRightControlledDescriptor
    (point : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) : ShapeFreeDescriptor A initialCode :=
  profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin basis
    initialCode (point.toOptionalControlled A strategy hwin basis initialCode)

/-- Left mirror. -/
noncomputable def profiledOpenActiveLeftControlledDescriptor
    (point : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) : ShapeFreeDescriptor A initialCode :=
  profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin basis
    initialCode (point.toOptionalControlled A strategy hwin basis initialCode)

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenActiveRightControlledDescriptor_control
    (point : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode point).control = point.2 :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenActiveLeftControlledDescriptor_control
    (point : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode point).control = point.2 :=
  rfl

/-! ## The projected finite classes -/

/-- Finite right descriptor image over all shapes and all controls compatible
with the active sender view. -/
noncomputable def profiledOpenActiveRightProjectedClass
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) : Finset (ShapeFreeDescriptor A initialCode) :=
  semanticFibreImage
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode) source

/-- Left projected class. -/
noncomputable def profiledOpenActiveLeftProjectedClass
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) : Finset (ShapeFreeDescriptor A initialCode) :=
  semanticFibreImage
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode) source

/-- Install a right projected class in the fixed family type. -/
noncomputable def profiledOpenActiveRightProjectedFamily
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) : ShapeFreeFamily A initialCode :=
  (profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      source,
    ∅)

/-- Left installation. -/
noncomputable def profiledOpenActiveLeftProjectedFamily
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) : ShapeFreeFamily A initialCode :=
  (∅,
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      source)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenActiveRightProjectedFamily_fst
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
      source).1 =
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        source :=
  rfl

@[simp] theorem profiledOpenActiveRightProjectedFamily_snd
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
      source).2 = ∅ :=
  rfl

@[simp] theorem profiledOpenActiveLeftProjectedFamily_fst
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
      source).1 = ∅ :=
  rfl

@[simp] theorem profiledOpenActiveLeftProjectedFamily_snd
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
      source).2 =
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        source :=
  rfl

end

/-! ## Coverage and exact shape/control saturation -/

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenActiveRightControlledDescriptor_mem_projectedClass
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode source ∈
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        source :=
  descriptor_mem_semanticFibreImage
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode)
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_reflexive A strategy
      hwin basis initialCode).refl source

theorem profiledOpenActiveLeftControlledDescriptor_mem_projectedClass
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode source ∈
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        source :=
  descriptor_mem_semanticFibreImage
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode)
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_reflexive A strategy
      hwin basis initialCode).refl source

theorem profiledOpenActiveRightProjectedClass_eq_of_rel
    {left right : ProfiledOpenIndexedActiveRightControlledSemanticPoint A
      strategy hwin basis initialCode}
    (hrel : ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy
      hwin basis initialCode left right) :
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        left =
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        right :=
  semanticFibreImage_eq_of_rel
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode)
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_fibresAgree A
      strategy hwin basis initialCode) hrel

theorem profiledOpenActiveLeftProjectedClass_eq_of_rel
    {left right : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A
      strategy hwin basis initialCode}
    (hrel : ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy
      hwin basis initialCode left right) :
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        left =
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        right :=
  semanticFibreImage_eq_of_rel
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode)
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_fibresAgree A
      strategy hwin basis initialCode) hrel

/-- The dangerous right-only/both seam is erased even when the two proof
points carry different hidden parity controls. -/
theorem profiledOpenRightOnlyBoth_projectedClass_eq
    (rightOnly : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (rightControl bothControl : ShapeFreeControl A initialCode)
    (hobs : ProfiledOpenIndexedRightOnlyBothSameRuntimeObservation A strategy
      hwin basis rightOnly both) :
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        (rightOnly.toActiveRightControlled A strategy hwin basis initialCode
          rightControl) =
      profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
        (both.toActiveRightControlled A strategy hwin basis initialCode
          bothControl) :=
  profiledOpenActiveRightProjectedClass_eq_of_rel A strategy hwin basis
    initialCode hobs

/-- Left-only/both mirror, also across arbitrary controls. -/
theorem profiledOpenLeftOnlyBoth_projectedClass_eq
    (leftOnly : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (leftControl bothControl : ShapeFreeControl A initialCode)
    (hobs : ProfiledOpenIndexedLeftOnlyBothSameRuntimeObservation A strategy
      hwin basis leftOnly both) :
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        (leftOnly.toActiveLeftControlled A strategy hwin basis initialCode
          leftControl) =
      profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
        (both.toActiveLeftControlled A strategy hwin basis initialCode
          bothControl) :=
  profiledOpenActiveLeftProjectedClass_eq_of_rel A strategy hwin basis
    initialCode hobs

end

/-! ## Controlled source-fibre presentations

The generic active-lane fibre from
`LemPairedProfiledOpenActiveLaneShapeFreeFibre` rationalizes across shapes but
accepts a descriptor function on the uncontrolled active carrier.  The
operational descriptor contains the literal DPA control, so the source fibre
must instead live on the controlled product above.  The following direct
presentations are the control-saturated specializations consumed by the
provenance extractor.
-/

abbrev ProfiledOpenActiveRightControlledSourceFibreDescriptor
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  SemanticFibreAt
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode) source

abbrev ProfiledOpenActiveLeftControlledSourceFibreDescriptor
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  SemanticFibreAt
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode) source

noncomputable instance
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    Fintype
      (ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source) := by
  classical
  infer_instance

noncomputable instance
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    Fintype
      (ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source) := by
  classical
  infer_instance

noncomputable def profiledOpenActiveRightControlledSourceFibrePoint
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy hwin basis
      initialCode :=
  semanticFibreAtWitness
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode) source member

noncomputable def profiledOpenActiveLeftControlledSourceFibrePoint
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy hwin basis
      initialCode :=
  semanticFibreAtWitness
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode) source member

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenActiveRightControlledSourceFibrePoint_rel
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin basis
      initialCode source
      (profiledOpenActiveRightControlledSourceFibrePoint A strategy hwin basis
        initialCode source member) :=
  semanticFibreAtWitness_rel
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode) source member

theorem profiledOpenActiveLeftControlledSourceFibrePoint_rel
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode source
      (profiledOpenActiveLeftControlledSourceFibrePoint A strategy hwin basis
        initialCode source member) :=
  semanticFibreAtWitness_rel
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode) source member

theorem profiledOpenActiveRightControlledSourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode
        (profiledOpenActiveRightControlledSourceFibrePoint A strategy hwin basis
          initialCode source member) =
      member.1 :=
  semanticFibreAtWitness_descriptor
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode) source member

theorem profiledOpenActiveLeftControlledSourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode
        (profiledOpenActiveLeftControlledSourceFibrePoint A strategy hwin basis
          initialCode source member) =
      member.1 :=
  semanticFibreAtWitness_descriptor
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode) source member

end

noncomputable def profiledOpenActiveRightControlledSourceFibreSource
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) : ProfiledOpenRightViewClass A :=
  (profiledOpenActiveRightControlledSourceFibrePoint A strategy hwin basis
    initialCode source member).1.lane.source

noncomputable def profiledOpenActiveLeftControlledSourceFibreSource
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) : ProfiledOpenLeftViewClass A :=
  (profiledOpenActiveLeftControlledSourceFibrePoint A strategy hwin basis
    initialCode source member).1.lane.source

noncomputable def profiledOpenActiveRightControlledSourceFibreRealization
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenRightRealization A strategy hwin basis
      (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
        initialCode source member) :=
  (profiledOpenActiveRightControlledSourceFibrePoint A strategy hwin basis
    initialCode source member).1.lane.realization

noncomputable def profiledOpenActiveLeftControlledSourceFibreRealization
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy
      hwin basis initialCode source) :
    ProfiledOpenLeftRealization A strategy hwin basis
      (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
        initialCode source member) :=
  (profiledOpenActiveLeftControlledSourceFibrePoint A strategy hwin basis
    initialCode source member).1.lane.realization

noncomputable def profiledOpenActiveRightControlledSourceFibreCurrent
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin basis
      initialCode source :=
  semanticFibreAtCurrent
    (profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveRightControlledLocalFibreRel A strategy hwin
      basis initialCode)
    (profiledOpenIndexedActiveRightControlledLocalFibreRel_reflexive A strategy
      hwin basis initialCode).refl source

noncomputable def profiledOpenActiveLeftControlledSourceFibreCurrent
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin basis
      initialCode source :=
  semanticFibreAtCurrent
    (profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode)
    (ProfiledOpenIndexedActiveLeftControlledLocalFibreRel A strategy hwin basis
      initialCode)
    (profiledOpenIndexedActiveLeftControlledLocalFibreRel_reflexive A strategy
      hwin basis initialCode).refl source

noncomputable def profiledOpenActiveRightControlledSourceFibrePresentation
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ ↦ ULift.up ()
  representative := fun _ ↦
    profiledOpenActiveRightControlledSourceFibreCurrent A strategy hwin basis
      initialCode source
  representative_class := by intro c; exact Subsingleton.elim _ _

noncomputable def profiledOpenActiveLeftControlledSourceFibrePresentation
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ ↦ ULift.up ()
  representative := fun _ ↦
    profiledOpenActiveLeftControlledSourceFibreCurrent A strategy hwin basis
      initialCode source
  representative_class := by intro c; exact Subsingleton.elim _ _

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenActiveRightControlledSourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenRightFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
        basis initialCode source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenActiveRightControlledSourceFibreCurrent A
    strategy hwin basis initialCode source
  let actualPoint := profiledOpenActiveRightControlledSourceFibrePoint A
    strategy hwin basis initialCode source actual
  let representativePoint := profiledOpenActiveRightControlledSourceFibrePoint A
    strategy hwin basis initialCode source representative
  have hactual := profiledOpenActiveRightControlledSourceFibrePoint_rel A
    strategy hwin basis initialCode source actual
  have hrepresentative :=
    profiledOpenActiveRightControlledSourceFibrePoint_rel A strategy hwin basis
      initialCode source representative
  have hrel : ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      actualPoint.1 representativePoint.1 :=
    (profiledOpenIndexedActiveRightLocalFibreRel_symmetric A strategy hwin basis
      hactual).trans hrepresentative
  calc
    currentView Proc.one
        ((profiledOpenActiveRightControlledSourceFibreRealization A strategy
          hwin basis initialCode source actual).entry member).leftHistory =
      profiledOpenIndexedActiveRightView A strategy hwin basis actualPoint.1 := by
        simpa [profiledOpenActiveRightControlledSourceFibreRealization,
          profiledOpenIndexedActiveRightView] using
          (profiledOpenActiveRightControlledSourceFibreRealization A strategy
            hwin basis initialCode source actual).view_eq member
    _ = profiledOpenIndexedActiveRightView A strategy hwin basis
        representativePoint.1 := hrel
    _ = currentView Proc.one
        ((profiledOpenActiveRightControlledSourceFibreRealization A strategy
          hwin basis initialCode source representative).entry
          (profiledOpenActiveRightControlledSourceFibreRealization A strategy
            hwin basis initialCode source representative).pivot).leftHistory := by
      rfl

theorem profiledOpenActiveLeftControlledSourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenLeftFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
        basis initialCode source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenActiveLeftControlledSourceFibreCurrent A
    strategy hwin basis initialCode source
  let actualPoint := profiledOpenActiveLeftControlledSourceFibrePoint A strategy
    hwin basis initialCode source actual
  let representativePoint := profiledOpenActiveLeftControlledSourceFibrePoint A
    strategy hwin basis initialCode source representative
  have hactual := profiledOpenActiveLeftControlledSourceFibrePoint_rel A strategy
    hwin basis initialCode source actual
  have hrepresentative := profiledOpenActiveLeftControlledSourceFibrePoint_rel A
    strategy hwin basis initialCode source representative
  have hrel : ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      actualPoint.1 representativePoint.1 :=
    (profiledOpenIndexedActiveLeftLocalFibreRel_symmetric A strategy hwin basis
      hactual).trans hrepresentative
  calc
    currentView Proc.two
        ((profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
          basis initialCode source actual).entry member).rightHistory =
      profiledOpenIndexedActiveLeftView A strategy hwin basis actualPoint.1 := by
        simpa [profiledOpenActiveLeftControlledSourceFibreRealization,
          profiledOpenIndexedActiveLeftView] using
          (profiledOpenActiveLeftControlledSourceFibreRealization A strategy
            hwin basis initialCode source actual).view_eq member
    _ = profiledOpenIndexedActiveLeftView A strategy hwin basis
        representativePoint.1 := hrel
    _ = currentView Proc.two
        ((profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
          basis initialCode source representative).entry
          (profiledOpenActiveLeftControlledSourceFibreRealization A strategy
            hwin basis initialCode source representative).pivot).rightHistory := by
      rfl

theorem profiledOpenActiveRightControlledSourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenRightFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
        basis initialCode source) :=
  profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A
      (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
        basis initialCode source)
      (profiledOpenActiveRightControlledSourceFibreSenderViewsAgree A strategy
        hwin basis initialCode source))

theorem profiledOpenActiveLeftControlledSourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenLeftFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
        basis initialCode source) :=
  profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A
      (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
        basis initialCode source)
      strategy hwin basis
      (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
        initialCode source)
      (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
        basis initialCode source)
      (profiledOpenActiveLeftControlledSourceFibreSenderViewsAgree A strategy
        hwin basis initialCode source))

end

noncomputable abbrev
    ProfiledOpenActiveRightControlledSourceFibreProvenanceMove
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  ProfiledOpenRightPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable abbrev
    ProfiledOpenActiveLeftControlledSourceFibreProvenanceMove
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  ProfiledOpenLeftPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable def
    profiledOpenActiveRightControlledSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveRightControlledSourceFibreProvenanceMove A strategy hwin
      basis initialCode source :=
  profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenActiveRightControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveRightControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveRightControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (profiledOpenActiveRightControlledSourceFibreCommonSenderWins A strategy
      hwin basis initialCode source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable def
    profiledOpenActiveLeftControlledSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLeftControlledSourceFibreProvenanceMove A strategy hwin
      basis initialCode source :=
  profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenActiveLeftControlledSourceFibrePresentation A strategy hwin
      basis initialCode source)
    strategy hwin basis
    (profiledOpenActiveLeftControlledSourceFibreSource A strategy hwin basis
      initialCode source)
    (profiledOpenActiveLeftControlledSourceFibreRealization A strategy hwin
      basis initialCode source)
    (profiledOpenActiveLeftControlledSourceFibreCommonSenderWins A strategy
      hwin basis initialCode source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

/-! ## Canonical fixed right value with retained provenance -/

/-- Recover the proof-side active-right witness for one member of the
projected fixed family.  Membership is interpreted in the selected source
fibre; equality of another projected image is never reflected back into a
view relation. -/
noncomputable def profiledOpenActiveRightProjectedPoint
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)) :
    ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy hwin basis
      initialCode := by
  let sourceMember :
      ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1, by
      simpa [profiledOpenActiveRightProjectedFamily,
        profiledOpenActiveRightProjectedClass] using member.2⟩
  exact profiledOpenActiveRightControlledSourceFibrePoint A strategy hwin basis
    initialCode source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveRightProjectedPoint_descriptor
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)) :
    profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode
        (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
          source member) =
      member.1 := by
  let sourceMember :
      ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1, by
      simpa [profiledOpenActiveRightProjectedFamily,
        profiledOpenActiveRightProjectedClass] using member.2⟩
  exact profiledOpenActiveRightControlledSourceFibrePoint_descriptor A strategy
    hwin basis initialCode source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The stored old move exposes the realized right table of the member
witness. -/
theorem profiledOpenActiveRightProjectedPoint_moveIdentity
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)) :
    member.1.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right
        (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
          source member).1.lane.source
        ((((profiledOpenActiveRightProjectedPoint A strategy hwin basis
          initialCode source member).1.lane.realization.coherentTable A).table
          ).toClassified A
            (profiledOpenActiveRightProjectedPoint A strategy hwin basis
              initialCode source member).1.lane.source) := by
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source member
  have hdescriptor := profiledOpenActiveRightProjectedPoint_descriptor A
    strategy hwin basis initialCode source member
  have hmove : member.1.moveIdentity =
      point.1.optional.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  change member.1.moveIdentity.1 =
    ProfiledOpenClassifiedMove.right point.1.lane.source
      (((point.1.lane.realization.coherentTable A).table
        |>.toClassified A point.1.lane.source))
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.1.active,
    ProfiledOpenIndexedRightSemanticShadow.move]

noncomputable def profiledOpenActiveRightProjectedRoot
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source))
    (root : ProfiledOpenHiddenDescriptorRightRoot A member.1) :
    { root // root ∈
      (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
        source member).1.lane.source.1 } :=
  profiledOpenHiddenDescriptorRightRootToEq A member.1
    (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
      source member).1.lane.source
    ((((profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
      source member).1.lane.realization.coherentTable A).table).toClassified A
        (profiledOpenActiveRightProjectedPoint A strategy hwin basis initialCode
          source member).1.lane.source)
    (profiledOpenActiveRightProjectedPoint_moveIdentity A strategy hwin basis
      initialCode source member) root

/-- One sender for the complete shape-and-control-saturated right fibre. -/
noncomputable def profiledOpenActiveRightProjectedSender
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) : SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy
    (source.1.lane.realization.entry source.1.lane.realization.pivot
      ).lambdaOfStrategy

noncomputable def profiledOpenActiveRightProjectedReceiver
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenActiveRightProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)) :
    ReceiverBlockStrategy In₂ In₁ (ProfiledOpenRightClassifiedOutput A) :=
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source member.1
  profiledOpenRightSemanticClassifiedReceiver A point.1.lane.source strategy
    hwin point.1.lane.realization.entry basis
    (profiledOpenActiveRightProjectedRoot A strategy hwin basis initialCode
      source member.1 member.2)

noncomputable def profiledOpenActiveRightProjectedExpected
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenHiddenDescriptorRightExpected A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) :=
  fun member input ↦
    (input,
      profiledOpenActiveRightProjectedReceiver A strategy hwin basis
        initialCode source member [] input,
      profiledOpenActiveRightProjectedSender A strategy hwin basis initialCode
        source [] input.2)

noncomputable def profiledOpenActiveRightProjectedCurrent
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) :=
  ⟨profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode source,
    profiledOpenActiveRightControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source⟩

noncomputable def profiledOpenActiveRightProjectedDefaultMember
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1) := by
  let descriptor := profiledOpenActiveRightProjectedCurrent A strategy hwin
    basis initialCode source
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
      point.1.lane.source table hmove point.1.lane.realization.pivot⟩

/-- Literal semantic provenance for one fixed descriptor projection. -/
def profiledOpenActiveRightProjectedSemanticAllowed
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) : Prop :=
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source descriptor
  ProfiledOpenRightSemanticTableAllowed A point.1.lane.source strategy hwin
    point.1.lane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
            point.1.lane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveRightProjectedSemanticAllowed_implies_weak
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source))
    (responses :
      ((ProfiledOpenHiddenDescriptorRightRoot A descriptor.1 × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A)
    (hsemantic : profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin
      basis initialCode source descriptor responses) :
    ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source descriptor
  apply profiledOpenHiddenDescriptorRightWeakAllowed_ofEq A descriptor.1
    point.1.lane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
    point.1.lane.source strategy hwin point.1.lane.realization.entry
    point.1.lane.realization.minimum basis past

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveRightProjected_memberWins
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenActiveRightProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1))
    (env : Nat → In₂ × In₁) :
    (profiledOpenHiddenDescriptorRightMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenActiveRightProjectedReceiver A strategy hwin basis
          initialCode source member)
        (profiledOpenActiveRightProjectedSender A strategy hwin basis
          initialCode source)
        env) := by
  let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
    initialCode source member.1
  let root := profiledOpenActiveRightProjectedRoot A strategy hwin basis
    initialCode source member.1 member.2
  let sourceMember :
      ProfiledOpenActiveRightControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1.1, by
      simpa [profiledOpenActiveRightProjectedFamily,
        profiledOpenActiveRightProjectedClass] using member.1.2⟩
  have hsourceView :
      profiledOpenIndexedActiveRightView A strategy hwin basis point.1 =
        profiledOpenIndexedActiveRightView A strategy hwin basis source.1 :=
    (profiledOpenActiveRightControlledSourceFibrePoint_rel A strategy hwin
      basis initialCode source sourceMember).symm
  have hrootView :
      currentView Proc.one
          (point.1.lane.realization.entry root).leftHistory =
        currentView Proc.one
          (source.1.lane.realization.entry source.1.lane.realization.pivot
            ).leftHistory :=
    (point.1.lane.realization.view_eq root).trans hsourceView
  have hsender :
      pairedRightSenderStrategy
          (point.1.lane.realization.entry root).lambdaOfStrategy =
        profiledOpenActiveRightProjectedSender A strategy hwin basis initialCode
          source :=
    blockSenderOne_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin (point.1.lane.realization.entry root)
    (point.1.lane.realization.minimum root) basis env
  have hroot := point.1.lane.realization.root_eq root
  have hrootmember :
      (profiledOpenRightRootMonitor A
        (profiledOpenRightRootOfWinning A strategy hwin
          (point.1.lane.realization.entry root)
          (point.1.lane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A
            (point.1.lane.realization.entry root).code
            (point.1.lane.realization.entry root).lambdaOfStrategy)
          (pairedRightSenderStrategy
            (point.1.lane.realization.entry root).lambdaOfStrategy) env) := by
    simpa [profiledOpenRightRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenRightClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenActiveRightProjectedReceiver A strategy hwin basis
            initialCode source member)
          (profiledOpenActiveRightProjectedSender A strategy hwin basis
            initialCode source) env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenRightRootMonitor A root.1)
      (fun output : ProfiledOpenRightClassifiedOutput A ↦ output.1) _).mpr
    simpa [profiledOpenActiveRightProjectedReceiver,
      profiledOpenRightSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorRightMonitor_eq_ofEq A member.1.1
    point.1.lane.source
    (((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source))
    (profiledOpenActiveRightProjectedPoint_moveIdentity A strategy hwin basis
      initialCode source member.1) member.2]
  simpa [root, profiledOpenActiveRightProjectedRoot, point] using hclassified

/-- Strong and weak table laws are carried by the same root-pinned fixed
controller. -/
noncomputable abbrev ProfiledOpenActiveRightProjectedProvenanceMove
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveRightProjectedExpected A strategy hwin basis initialCode
      source)

noncomputable def profiledOpenActiveRightProjectedProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveRightProjectedProvenanceMove A strategy hwin basis
      initialCode source := by
  classical
  let family := profiledOpenActiveRightProjectedFamily A strategy hwin basis
    initialCode source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let expected := profiledOpenActiveRightProjectedExpected A strategy hwin basis
    initialCode source
  let Strong := profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin
    basis initialCode source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenActiveRightProjectedReceiver A strategy hwin basis
    initialCode source
  let sender := profiledOpenActiveRightProjectedSender A strategy hwin basis
    initialCode source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenActiveRightProjectedDefaultMember A strategy hwin basis
      initialCode source⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenActiveRightProjectedPoint A strategy hwin basis
      initialCode source descriptor
    let table := ((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source)
    let hmove := profiledOpenActiveRightProjectedPoint_moveIdentity A strategy
      hwin basis initialCode source descriptor
    refine ⟨past.map (fun old ↦
      ((point.1.lane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenActiveRightProjectedSemanticAllowed,
      profiledOpenRightSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenActiveRightProjectedReceiver,
      profiledOpenActiveRightProjectedRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorRightRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenActiveRightProjectedSemanticAllowed_implies_weak A strategy
        hwin basis initialCode source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenActiveRightProjected_memberWins A strategy hwin basis
      initialCode source
  · intro member input
    rfl
  · exact hstrong

noncomputable def
    ProfiledOpenActiveRightProjectedProvenanceMove.toPinnedMove
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (move : ProfiledOpenActiveRightProjectedProvenanceMove A strategy hwin basis
      initialCode source) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)
      (profiledOpenActiveRightProjectedExpected A strategy hwin basis
        initialCode source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveRightProjectedExpected A strategy hwin basis initialCode
      source) move

/-- The actual strategy-dependent value lies in the strategy-independent
fixed left alphabet. -/
noncomputable def profiledOpenActiveRightFixedValueOfWinning
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedRightPinnedValue A initialCode :=
  let provenance :=
    profiledOpenActiveRightProjectedProvenanceMoveOfWinning A strategy hwin
      basis initialCode source
  ⟨profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
      source,
    profiledOpenActiveRightProjectedExpected A strategy hwin basis initialCode
      source,
    provenance.toPinnedMove A strategy hwin basis initialCode source⟩

@[simp] theorem profiledOpenActiveRightFixedValueOfWinning_family
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
      initialCode source).1 =
      profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source :=
  rfl

/-- Companion proof predicate: the weak fixed value is the projection of one
literal strong extraction over the selected source fibre. -/
def ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (value : ProfiledOpenFixedRightPinnedValue A initialCode) : Prop :=
  ∃ provenance : ProfiledOpenActiveRightProjectedProvenanceMove A strategy
      hwin basis initialCode source,
    value =
      ⟨profiledOpenActiveRightProjectedFamily A strategy hwin basis
          initialCode source,
        profiledOpenActiveRightProjectedExpected A strategy hwin basis
          initialCode source,
        provenance.toPinnedMove A strategy hwin basis initialCode source⟩

theorem profiledOpenActiveRightFixedValueOfWinning_hasShapeFreeProvenance
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveRightFixedValueHasShapeFreeProvenance A strategy hwin
      basis initialCode source
      (profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
        initialCode source) := by
  exact ⟨profiledOpenActiveRightProjectedProvenanceMoveOfWinning A strategy
    hwin basis initialCode source, rfl⟩

/-- The literal current descriptor is covered by the fixed value advertised
at the source. -/
theorem profiledOpenActiveRightFixedValueOfWinning_current_mem
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode) :
    profiledOpenActiveRightControlledDescriptor A strategy hwin basis
        initialCode source ∈
      (profiledOpenActiveRightFixedValueOfWinning A strategy hwin basis
        initialCode source).1.1 := by
  change profiledOpenActiveRightControlledDescriptor A strategy hwin basis
      initialCode source ∈
    profiledOpenActiveRightProjectedClass A strategy hwin basis initialCode
      source
  exact profiledOpenActiveRightControlledDescriptor_mem_projectedClass A
    strategy hwin basis initialCode source

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every member projection of the returned fixed value retains literal
semantic-table provenance at every controller node.  This is the exact input
needed by re-anchored row consumption; it does not reflect equality of public
families back into equality of views. -/
theorem ProfiledOpenActiveRightProjectedProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenIndexedActiveRightControlledSemanticPoint A strategy
      hwin basis initialCode)
    (move : ProfiledOpenActiveRightProjectedProvenanceMove A strategy hwin basis
      initialCode source)
    (descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenActiveRightProjectedFamily A strategy hwin basis
              initialCode source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
          (profiledOpenActiveRightProjectedExpected A strategy hwin basis
            initialCode source) descriptor))
      (profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin basis
        initialCode source descriptor)
      ((move.toPinnedMove A strategy hwin basis initialCode source
        ).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
            (profiledOpenActiveRightProjectedFamily A strategy hwin basis
              initialCode source) ↦
            ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
              (profiledOpenActiveRightProjectedFamily A strategy hwin basis
                initialCode source) ↦
              ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
            (profiledOpenActiveRightProjectedExpected A strategy hwin basis
              initialCode source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenActiveRightProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root)
    (profiledOpenActiveRightProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveRightProjectedExpected A strategy hwin basis initialCode
      source) move descriptor

/-! ## Canonical fixed left value with retained provenance -/

noncomputable def profiledOpenActiveLeftProjectedPoint
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)) :
    ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy hwin basis
      initialCode := by
  let sourceMember :
      ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1, by
      simpa [profiledOpenActiveLeftProjectedFamily,
        profiledOpenActiveLeftProjectedClass] using member.2⟩
  exact profiledOpenActiveLeftControlledSourceFibrePoint A strategy hwin basis
    initialCode source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjectedPoint_descriptor
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)) :
    profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode
        (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
          source member) =
      member.1 := by
  let sourceMember :
      ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1, by
      simpa [profiledOpenActiveLeftProjectedFamily,
        profiledOpenActiveLeftProjectedClass] using member.2⟩
  exact profiledOpenActiveLeftControlledSourceFibrePoint_descriptor A strategy
    hwin basis initialCode source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjectedPoint_moveIdentity
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)) :
    member.1.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left
        (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
          source member).1.lane.source
        ((((profiledOpenActiveLeftProjectedPoint A strategy hwin basis
          initialCode source member).1.lane.realization.coherentTable A).table
          ).toClassified A
            (profiledOpenActiveLeftProjectedPoint A strategy hwin basis
              initialCode source member).1.lane.source) := by
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source member
  have hdescriptor := profiledOpenActiveLeftProjectedPoint_descriptor A
    strategy hwin basis initialCode source member
  have hmove : member.1.moveIdentity =
      point.1.optional.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  change member.1.moveIdentity.2 =
    ProfiledOpenClassifiedMove.left point.1.lane.source
      (((point.1.lane.realization.coherentTable A).table
        |>.toClassified A point.1.lane.source))
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.1.active,
    ProfiledOpenIndexedLeftSemanticShadow.move]

noncomputable def profiledOpenActiveLeftProjectedRoot
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source))
    (root : ProfiledOpenHiddenDescriptorLeftRoot A member.1) :
    { root // root ∈
      (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
        source member).1.lane.source.1 } :=
  profiledOpenHiddenDescriptorLeftRootToEq A member.1
    (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
      source member).1.lane.source
    ((((profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
      source member).1.lane.realization.coherentTable A).table).toClassified A
        (profiledOpenActiveLeftProjectedPoint A strategy hwin basis initialCode
          source member).1.lane.source)
    (profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy hwin basis
      initialCode source member) root

noncomputable def profiledOpenActiveLeftProjectedSender
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) : SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy
    (source.1.lane.realization.entry source.1.lane.realization.pivot
      ).lambdaOfStrategy

noncomputable def profiledOpenActiveLeftProjectedReceiver
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)) :
    ReceiverBlockStrategy In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) :=
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source member.1
  profiledOpenLeftSemanticClassifiedReceiver A point.1.lane.source strategy
    hwin point.1.lane.realization.entry basis
    (profiledOpenActiveLeftProjectedRoot A strategy hwin basis initialCode
      source member.1 member.2)

noncomputable def profiledOpenActiveLeftProjectedExpected
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenHiddenDescriptorLeftExpected A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) :=
  fun member input ↦
    (input,
      profiledOpenActiveLeftProjectedReceiver A strategy hwin basis initialCode
        source member [] input,
      profiledOpenActiveLeftProjectedSender A strategy hwin basis initialCode
        source [] input.2)

noncomputable def profiledOpenActiveLeftProjectedCurrent
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) :=
  ⟨profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode source,
    profiledOpenActiveLeftControlledDescriptor_mem_projectedClass A strategy
      hwin basis initialCode source⟩

noncomputable def profiledOpenActiveLeftProjectedDefaultMember
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1) := by
  let descriptor := profiledOpenActiveLeftProjectedCurrent A strategy hwin
    basis initialCode source
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy
    hwin basis initialCode source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
      point.1.lane.source table hmove point.1.lane.realization.pivot⟩

def profiledOpenActiveLeftProjectedSemanticAllowed
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) : Prop :=
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy hwin
    basis initialCode source descriptor
  ProfiledOpenLeftSemanticTableAllowed A point.1.lane.source strategy hwin
    point.1.lane.realization.entry basis (fun input ↦
      responses
        ((profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
            point.1.lane.source table hmove input.1.1,
          input.1.2), input.2))

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjectedSemanticAllowed_implies_weak
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source))
    (responses :
      ((ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1 × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A)
    (hsemantic : profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin
      basis initialCode source descriptor responses) :
    ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses := by
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source descriptor
  let table := ((point.1.lane.realization.coherentTable A).table
    |>.toClassified A point.1.lane.source)
  let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy hwin
    basis initialCode source descriptor
  apply profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq A descriptor.1
    point.1.lane.source table hmove
  rcases hsemantic with ⟨past, hpast⟩
  rw [hpast]
  exact profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
    point.1.lane.source strategy hwin point.1.lane.realization.entry
    point.1.lane.realization.minimum basis past

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftProjected_memberWins
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
          initialCode source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1))
    (env : Nat → In₁ × In₂) :
    (profiledOpenHiddenDescriptorLeftMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenActiveLeftProjectedReceiver A strategy hwin basis
          initialCode source member)
        (profiledOpenActiveLeftProjectedSender A strategy hwin basis
          initialCode source)
        env) := by
  let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
    initialCode source member.1
  let root := profiledOpenActiveLeftProjectedRoot A strategy hwin basis
    initialCode source member.1 member.2
  let sourceMember :
      ProfiledOpenActiveLeftControlledSourceFibreDescriptor A strategy hwin
        basis initialCode source :=
    ⟨member.1.1, by
      simpa [profiledOpenActiveLeftProjectedFamily,
        profiledOpenActiveLeftProjectedClass] using member.1.2⟩
  have hsourceView :
      profiledOpenIndexedActiveLeftView A strategy hwin basis point.1 =
        profiledOpenIndexedActiveLeftView A strategy hwin basis source.1 :=
    (profiledOpenActiveLeftControlledSourceFibrePoint_rel A strategy hwin
      basis initialCode source sourceMember).symm
  have hrootView :
      currentView Proc.two
          (point.1.lane.realization.entry root).rightHistory =
        currentView Proc.two
          (source.1.lane.realization.entry source.1.lane.realization.pivot
            ).rightHistory :=
    (point.1.lane.realization.view_eq root).trans hsourceView
  have hsender :
      pairedLeftSenderStrategy
          (point.1.lane.realization.entry root).lambdaOfStrategy =
        profiledOpenActiveLeftProjectedSender A strategy hwin basis initialCode
          source :=
    blockSenderTwo_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin (point.1.lane.realization.entry root)
    (point.1.lane.realization.minimum root) basis env
  have hroot := point.1.lane.realization.root_eq root
  have hrootmember :
      (profiledOpenLeftRootMonitor A
        (profiledOpenLeftRootOfWinning A strategy hwin
          (point.1.lane.realization.entry root)
          (point.1.lane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A
            (point.1.lane.realization.entry root).code
            (point.1.lane.realization.entry root).lambdaOfStrategy)
          (pairedLeftSenderStrategy
            (point.1.lane.realization.entry root).lambdaOfStrategy) env) := by
    simpa [profiledOpenLeftRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenLeftClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenActiveLeftProjectedReceiver A strategy hwin basis
            initialCode source member)
          (profiledOpenActiveLeftProjectedSender A strategy hwin basis
            initialCode source) env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenLeftRootMonitor A root.1)
      (fun output : ProfiledOpenLeftClassifiedOutput A ↦ output.1) _).mpr
    simpa [profiledOpenActiveLeftProjectedReceiver,
      profiledOpenLeftSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorLeftMonitor_eq_ofEq A member.1.1
    point.1.lane.source
    (((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source))
    (profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy hwin basis
      initialCode source member.1) member.2]
  simpa [root, profiledOpenActiveLeftProjectedRoot, point] using hclassified

/-- Strong and weak table laws are carried by the same root-pinned fixed
controller. -/
noncomputable abbrev ProfiledOpenActiveLeftProjectedProvenanceMove
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :=
  FiniteDescriptorFamilyPinnedProvenanceMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveLeftProjectedExpected A strategy hwin basis initialCode
      source)

noncomputable def profiledOpenActiveLeftProjectedProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLeftProjectedProvenanceMove A strategy hwin basis
      initialCode source := by
  classical
  let family := profiledOpenActiveLeftProjectedFamily A strategy hwin basis
    initialCode source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let baseM : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let expected := profiledOpenActiveLeftProjectedExpected A strategy hwin basis
    initialCode source
  let Strong := profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin
    basis initialCode source
  let Weak : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let receiver := profiledOpenActiveLeftProjectedReceiver A strategy hwin basis
    initialCode source
  let sender := profiledOpenActiveLeftProjectedSender A strategy hwin basis
    initialCode source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenActiveLeftProjectedDefaultMember A strategy hwin basis
      initialCode source⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    let point := profiledOpenActiveLeftProjectedPoint A strategy hwin basis
      initialCode source descriptor
    let table := ((point.1.lane.realization.coherentTable A).table
      |>.toClassified A point.1.lane.source)
    let hmove := profiledOpenActiveLeftProjectedPoint_moveIdentity A strategy
      hwin basis initialCode source descriptor
    refine ⟨past.map (fun old ↦
      ((point.1.lane.realization.pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenActiveLeftProjectedSemanticAllowed,
      profiledOpenLeftSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenActiveLeftProjectedReceiver,
      profiledOpenActiveLeftProjectedRoot, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def, point, table, hmove,
      profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq]
  apply finiteDescriptorFamilyPinnedProvenanceMoveOfStrategies Root baseM
    Strong Weak expected
    (fun descriptor responses hsemantic ↦
      profiledOpenActiveLeftProjectedSemanticAllowed_implies_weak A strategy
        hwin basis initialCode source descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · exact profiledOpenActiveLeftProjected_memberWins A strategy hwin basis
      initialCode source
  · intro member input
    rfl
  · exact hstrong

noncomputable def
    ProfiledOpenActiveLeftProjectedProvenanceMove.toPinnedMove
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (move : ProfiledOpenActiveLeftProjectedProvenanceMove A strategy hwin basis
      initialCode source) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)
      (profiledOpenActiveLeftProjectedExpected A strategy hwin basis
        initialCode source) :=
  FiniteDescriptorFamilyPinnedProvenanceMove.toPinnedMove
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveLeftProjectedExpected A strategy hwin basis initialCode
      source) move

/-- The actual strategy-dependent value lies in the strategy-independent
fixed right alphabet. -/
noncomputable def profiledOpenActiveLeftFixedValueOfWinning
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenFixedLeftPinnedValue A initialCode :=
  let provenance :=
    profiledOpenActiveLeftProjectedProvenanceMoveOfWinning A strategy hwin
      basis initialCode source
  ⟨profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
      source,
    profiledOpenActiveLeftProjectedExpected A strategy hwin basis initialCode
      source,
    provenance.toPinnedMove A strategy hwin basis initialCode source⟩

@[simp] theorem profiledOpenActiveLeftFixedValueOfWinning_family
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    (profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis
      initialCode source).1 =
      profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source :=
  rfl

/-- Companion proof predicate: the weak fixed value is the projection of one
literal strong extraction over the selected source fibre. -/
def ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (value : ProfiledOpenFixedLeftPinnedValue A initialCode) : Prop :=
  ∃ provenance : ProfiledOpenActiveLeftProjectedProvenanceMove A strategy
      hwin basis initialCode source,
    value =
      ⟨profiledOpenActiveLeftProjectedFamily A strategy hwin basis
          initialCode source,
        profiledOpenActiveLeftProjectedExpected A strategy hwin basis
          initialCode source,
        provenance.toPinnedMove A strategy hwin basis initialCode source⟩

theorem profiledOpenActiveLeftFixedValueOfWinning_hasShapeFreeProvenance
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    ProfiledOpenActiveLeftFixedValueHasShapeFreeProvenance A strategy hwin
      basis initialCode source
      (profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis
        initialCode source) := by
  exact ⟨profiledOpenActiveLeftProjectedProvenanceMoveOfWinning A strategy
    hwin basis initialCode source, rfl⟩

/-- The literal current descriptor is covered by the fixed value advertised
at the source. -/
theorem profiledOpenActiveLeftFixedValueOfWinning_current_mem
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode) :
    profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
        initialCode source ∈
      (profiledOpenActiveLeftFixedValueOfWinning A strategy hwin basis
        initialCode source).1.2 := by
  change profiledOpenActiveLeftControlledDescriptor A strategy hwin basis
      initialCode source ∈
    profiledOpenActiveLeftProjectedClass A strategy hwin basis initialCode
      source
  exact profiledOpenActiveLeftControlledDescriptor_mem_projectedClass A
    strategy hwin basis initialCode source

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every member projection of the returned fixed value retains literal
semantic-table provenance at every controller node.  This is the exact input
needed by re-anchored row consumption; it does not reflect equality of public
families back into equality of views. -/
theorem ProfiledOpenActiveLeftProjectedProvenanceMove.controllerFor_semantic
    (source : ProfiledOpenIndexedActiveLeftControlledSemanticPoint A strategy
      hwin basis initialCode)
    (move : ProfiledOpenActiveLeftProjectedProvenanceMove A strategy hwin basis
      initialCode source)
    (descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source)) :
    NarrowedTablesAllowed
      (finiteRootFamilyMonitor
        (descriptorRootPinnedMonitor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
              initialCode source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (fun descriptor root ↦
            profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
          (profiledOpenActiveLeftProjectedExpected A strategy hwin basis
            initialCode source) descriptor))
      (profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin basis
        initialCode source descriptor)
      ((move.toPinnedMove A strategy hwin basis initialCode source
        ).controllerFor
          (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
            (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
              initialCode source) ↦
            ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
          (descriptorRootPinnedMonitor
            (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
              (profiledOpenActiveLeftProjectedFamily A strategy hwin basis
                initialCode source) ↦
              ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
            (fun descriptor root ↦
              profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
            (profiledOpenActiveLeftProjectedExpected A strategy hwin basis
              initialCode source))
          (fun descriptor responses ↦
            ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1
              responses)
          descriptor |>.labeledTree) := by
  exact FiniteDescriptorFamilyPinnedProvenanceMove.controllerFor_strongAllowed
    (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenActiveLeftProjectedFamily A strategy hwin basis initialCode
        source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
    (fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root)
    (profiledOpenActiveLeftProjectedSemanticAllowed A strategy hwin basis
      initialCode source)
    (fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
    (profiledOpenActiveLeftProjectedExpected A strategy hwin basis initialCode
      source) move descriptor

end


end DetParityAutomaton

end DistributedSynthesis
