/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreProjection

/-!
# Direct finite carriers for attained semantic fibres

An attained fibre image should be consumed through the descriptor values
*inside that image*, not through all semantic envelopes that happen to have
the same image.  The distinction is important: every member of one image has
a semantic witness in one fixed exact-view fibre, so all such witnesses may
share the complete local strategy.  Equality of two images alone does not say
that arbitrary representatives of the two source fibres are related.

This module packages the direct carrier and its witnesses.  It is generic and
does not assume that equality of finite images reflects the semantic relation.
-/

namespace DistributedSynthesis

universe u v

section

variable {Semantic : Type u} {Descriptor : Type v}
variable [Fintype Descriptor] [DecidableEq Descriptor]

/-- Only finite semantic-fibre images that occur at an actual semantic point. -/
abbrev AttainedSemanticFibreImage
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop) :=
  AttainedFiniteImage (semanticFibreImage descriptor Rel)

/-- A fixed proof-side source whose exact fibre realizes an attained image. -/
noncomputable def attainedSemanticFibreSource
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel) : Semantic :=
  attainedFiniteImageRepresentative
    (semanticFibreImage descriptor Rel) image

omit [DecidableEq Descriptor] in
theorem attainedSemanticFibreSource_image
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel) :
    semanticFibreImage descriptor Rel
        (attainedSemanticFibreSource descriptor Rel image) =
      image.1 :=
  attainedFiniteImageRepresentative_spec
    (semanticFibreImage descriptor Rel) image

/-- The finite descriptor carrier of one attained exact fibre. -/
abbrev SemanticFibreDescriptor
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel) :=
  { value : Descriptor // value ∈ image.1 }

noncomputable instance semanticFibreDescriptor_fintype
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel) :
    Fintype (SemanticFibreDescriptor descriptor Rel image) := by
  classical
  exact Fintype.ofFinite _

omit [DecidableEq Descriptor] in
/-- Membership in the direct carrier gives a witness in the one fixed source
fibre chosen for the image. -/
theorem exists_semanticFibreMemberWitness
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (member : SemanticFibreDescriptor descriptor Rel image) :
    ∃ witness,
      Rel (attainedSemanticFibreSource descriptor Rel image) witness ∧
        descriptor witness = member.1 := by
  apply (mem_semanticFibreImage_iff descriptor Rel
    (attainedSemanticFibreSource descriptor Rel image) member.1).mp
  rw [attainedSemanticFibreSource_image descriptor Rel image]
  exact member.2

/-- Chosen semantic witness for one descriptor of the direct carrier. -/
noncomputable def semanticFibreMemberWitness
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (member : SemanticFibreDescriptor descriptor Rel image) : Semantic :=
  Classical.choose
    (exists_semanticFibreMemberWitness descriptor Rel image member)

section
omit [DecidableEq Descriptor]

theorem semanticFibreMemberWitness_rel
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (member : SemanticFibreDescriptor descriptor Rel image) :
    Rel (attainedSemanticFibreSource descriptor Rel image)
      (semanticFibreMemberWitness descriptor Rel image member) :=
  (Classical.choose_spec
    (exists_semanticFibreMemberWitness descriptor Rel image member)).1

theorem semanticFibreMemberWitness_descriptor
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (member : SemanticFibreDescriptor descriptor Rel image) :
    descriptor (semanticFibreMemberWitness descriptor Rel image member) =
      member.1 :=
  (Classical.choose_spec
    (exists_semanticFibreMemberWitness descriptor Rel image member)).2

/-- Any relation-invariant behavior is literally shared by every witness in
the direct carrier.  `Behavior` may be infinite here; finiteness is needed
only for the descriptor carrier.  In particular this theorem applies to a
complete blind `SenderBlockStrategy`. -/
theorem semanticFibreMemberWitness_behavior_eq
    {Behavior : Type*}
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (behavior : Semantic → Behavior)
    (hinvariant : ∀ {left right}, Rel left right →
      behavior left = behavior right)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (member : SemanticFibreDescriptor descriptor Rel image) :
    behavior (semanticFibreMemberWitness descriptor Rel image member) =
      behavior (attainedSemanticFibreSource descriptor Rel image) :=
  (hinvariant
    (semanticFibreMemberWitness_rel descriptor Rel image member)).symm

end

/-- The attained image containing one semantic source. -/
noncomputable def attainedSemanticFibreImageOf
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic) : AttainedSemanticFibreImage descriptor Rel :=
  ⟨semanticFibreImage descriptor Rel source, source, rfl⟩

/-- Under reflexivity, the current descriptor is a member of its direct
attained carrier. -/
noncomputable def semanticFibreDescriptorOf
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (source : Semantic) :
    SemanticFibreDescriptor descriptor Rel
      (attainedSemanticFibreImageOf descriptor Rel source) :=
  ⟨descriptor source,
    descriptor_mem_semanticFibreImage descriptor Rel hreflexive source⟩

omit [DecidableEq Descriptor] in
@[simp] theorem semanticFibreDescriptorOf_val
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (source : Semantic) :
    (semanticFibreDescriptorOf descriptor Rel hreflexive source).1 =
      descriptor source :=
  rfl

/-! ## Source-indexed carriers

`AttainedSemanticFibreImage` is the right finite *public code*: it forgets
which semantic point realizes the image.  During construction of the raw
history tree we must retain that point as proof-only data.  Otherwise the
chosen representative of an attained image need not lie in the current
source's exact fibre.

The following carrier is therefore deliberately indexed by the literal
current source.  Its underlying finite set is still exactly
`semanticFibreImage descriptor Rel source`, so erasing `source` recovers the
same public code.  The witness theorem, however, now returns `Rel source _`
directly.  This is the form needed to build both local family banks from one
common global semantic origin before the single input-free rationalization.
-/

/-- Descriptor values occurring in the exact fibre of one literal semantic
source.  The source is proof-side and is not part of the runtime carrier. -/
abbrev SemanticFibreAt
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic) :=
  { value : Descriptor //
      value ∈ semanticFibreImage descriptor Rel source }

noncomputable instance semanticFibreAt_fintype
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic) :
    Fintype (SemanticFibreAt descriptor Rel source) := by
  classical
  exact Fintype.ofFinite _

omit [DecidableEq Descriptor] in
/-- A member of the source-indexed carrier has a witness in the literal
current source fibre. -/
theorem exists_semanticFibreAtWitness
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic)
    (member : SemanticFibreAt descriptor Rel source) :
    ∃ witness, Rel source witness ∧ descriptor witness = member.1 := by
  exact (mem_semanticFibreImage_iff descriptor Rel source member.1).mp member.2

/-- Chosen witness in the literal current source fibre. -/
noncomputable def semanticFibreAtWitness
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic)
    (member : SemanticFibreAt descriptor Rel source) : Semantic :=
  Classical.choose
    (exists_semanticFibreAtWitness descriptor Rel source member)

section
omit [DecidableEq Descriptor]

theorem semanticFibreAtWitness_rel
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic)
    (member : SemanticFibreAt descriptor Rel source) :
    Rel source (semanticFibreAtWitness descriptor Rel source member) :=
  (Classical.choose_spec
    (exists_semanticFibreAtWitness descriptor Rel source member)).1

theorem semanticFibreAtWitness_descriptor
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic)
    (member : SemanticFibreAt descriptor Rel source) :
    descriptor (semanticFibreAtWitness descriptor Rel source member) =
      member.1 :=
  (Classical.choose_spec
    (exists_semanticFibreAtWitness descriptor Rel source member)).2

/-- A relation-invariant behavior of every chosen witness is literally the
behavior of the current source.  `Behavior` may be an infinite sender
strategy; only the domain of members is finite. -/
theorem semanticFibreAtWitness_behavior_eq
    {Behavior : Type*}
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (behavior : Semantic → Behavior)
    (hinvariant : ∀ {left right}, Rel left right →
      behavior left = behavior right)
    (source : Semantic)
    (member : SemanticFibreAt descriptor Rel source) :
    behavior (semanticFibreAtWitness descriptor Rel source member) =
      behavior source :=
  (hinvariant
    (semanticFibreAtWitness_rel descriptor Rel source member)).symm

end

/-- Under reflexivity, the current descriptor is a distinguished member of
the source-indexed carrier. -/
noncomputable def semanticFibreAtCurrent
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (source : Semantic) : SemanticFibreAt descriptor Rel source :=
  ⟨descriptor source,
    descriptor_mem_semanticFibreImage descriptor Rel hreflexive source⟩

omit [DecidableEq Descriptor] in
@[simp] theorem semanticFibreAtCurrent_val
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (source : Semantic) :
    (semanticFibreAtCurrent descriptor Rel hreflexive source).1 =
      descriptor source :=
  rfl

omit [DecidableEq Descriptor] in
/-- Erasing the proof-only source from a source-indexed carrier gives the
public attained-image code of that source definitionally. -/
theorem semanticFibreAt_publicImage
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (source : Semantic) :
    (attainedSemanticFibreImageOf descriptor Rel source).1 =
      semanticFibreImage descriptor Rel source :=
  rfl

end

end DistributedSynthesis
