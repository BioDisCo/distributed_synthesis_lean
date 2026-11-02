/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage

/-!
# Finite behavior projections determined by semantic fibre images

Equality of finite descriptor images generally does not reflect equality of
the underlying semantic relation.  That strong reflection property is also
unnecessary when a finite family construction consumes only a finite
behavior table.

If a projection of the descriptor is invariant on every semantic relation
fibre, then every nonempty fibre image has one constant projected value.
Consequently equal fibre images have equal projected values at their source
points.  This is the reusable replacement for relation reflection at a
finite-output extraction seam.

It does not by itself finite-state rationalize an infinite block strategy.
If a later construction consumes the entire strategy rather than a finite
behavior projection, that strategy must separately factor through finite
data; this lemma must not be read as supplying that retraction.
-/

namespace DistributedSynthesis

universe u v w

section


variable {Semantic : Type u} {Descriptor : Type v} {Behavior : Type w}
variable [Fintype Descriptor] [DecidableEq Descriptor]

/-- A descriptor projection is constant on exact semantic fibres. -/
def DescriptorProjectionInvariant
    (descriptor : Semantic → Descriptor)
    (projection : Descriptor → Behavior)
    (Rel : Semantic → Semantic → Prop) : Prop :=
  ∀ {left right}, Rel left right →
    projection (descriptor left) = projection (descriptor right)

section
omit [DecidableEq Descriptor]

/-- Equal finite fibre images determine every descriptor projection that is
constant on the underlying semantic fibres.  No converse from image equality
to `Rel` is used. -/
theorem descriptorProjection_eq_of_semanticFibreImage_eq
    (descriptor : Semantic → Descriptor)
    (projection : Descriptor → Behavior)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (hinvariant : DescriptorProjectionInvariant descriptor projection Rel)
    {left right : Semantic}
    (himage : semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right) :
    projection (descriptor left) = projection (descriptor right) := by
  have hmemLeft : descriptor left ∈
      semanticFibreImage descriptor Rel left :=
    descriptor_mem_semanticFibreImage descriptor Rel hreflexive left
  rw [himage, mem_semanticFibreImage_iff] at hmemLeft
  rcases hmemLeft with ⟨target, htarget, hdescriptor⟩
  calc
    projection (descriptor left) = projection (descriptor target) := by
      rw [hdescriptor]
    _ = projection (descriptor right) := (hinvariant htarget).symm

/-- Common-carrier form of finite-image equality.  Every descriptor in one
image has literal semantic preimages in both source fibres, with the same
descriptor value.  This gives downstream proofs one shared finite carrier
without asserting that the two source points themselves are related. -/
theorem exists_common_semanticFibre_witnesses_of_image_eq
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    {left right : Semantic}
    (himage : semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right)
    {value : Descriptor}
    (hvalue : value ∈ semanticFibreImage descriptor Rel left) :
    (∃ leftWitness, Rel left leftWitness ∧
        descriptor leftWitness = value) ∧
      (∃ rightWitness, Rel right rightWitness ∧
        descriptor rightWitness = value) := by
  have hleft := (mem_semanticFibreImage_iff descriptor Rel left value).mp
    hvalue
  have hrightMem : value ∈ semanticFibreImage descriptor Rel right := by
    rw [← himage]
    exact hvalue
  have hright := (mem_semanticFibreImage_iff descriptor Rel right value).mp
    hrightMem
  exact ⟨hleft, hright⟩

/-- With a reflexive relation, the current left descriptor is a canonical
common carrier of two semantic witnesses whenever the fibre images agree. -/
theorem exists_common_semanticFibre_witnesses_at_leftDescriptor
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    {left right : Semantic}
    (himage : semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right) :
    (∃ leftWitness, Rel left leftWitness ∧
        descriptor leftWitness = descriptor left) ∧
      (∃ rightWitness, Rel right rightWitness ∧
        descriptor rightWitness = descriptor left) := by
  apply exists_common_semanticFibre_witnesses_of_image_eq descriptor Rel himage
  exact descriptor_mem_semanticFibreImage descriptor Rel hreflexive left

/-- Semantic behavior determined by a descriptor projection is therefore
also determined by equality of the finite fibre image. -/
theorem semanticBehavior_eq_of_semanticFibreImage_eq
    (descriptor : Semantic → Descriptor)
    (projection : Descriptor → Behavior)
    (behavior : Semantic → Behavior)
    (hfactor : ∀ source, behavior source = projection (descriptor source))
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (hinvariant : DescriptorProjectionInvariant descriptor projection Rel)
    {left right : Semantic}
    (himage : semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right) :
    behavior left = behavior right := by
  rw [hfactor left, hfactor right]
  exact descriptorProjection_eq_of_semanticFibreImage_eq descriptor projection
    Rel hreflexive hinvariant himage

end

/-! ## Two-fibre public-code projections -/

section
omit [DecidableEq Descriptor]

/-- Equality of the process-one component of a two-fibre code determines
every process-one-invariant finite descriptor projection. -/
theorem descriptorProjection_eq_of_semanticTwoFibreCode_fst_eq
    (descriptor : Semantic → Descriptor)
    (projection : Descriptor → Behavior)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, RelOne source source)
    (hinvariant : DescriptorProjectionInvariant descriptor projection RelOne)
    {left right : Semantic}
    (hcode :
      (semanticTwoFibreCode descriptor RelOne RelTwo left).1 =
        (semanticTwoFibreCode descriptor RelOne RelTwo right).1) :
    projection (descriptor left) = projection (descriptor right) := by
  exact descriptorProjection_eq_of_semanticFibreImage_eq descriptor projection
    RelOne hreflexive hinvariant hcode

/-- Process-two mirror. -/
theorem descriptorProjection_eq_of_semanticTwoFibreCode_snd_eq
    (descriptor : Semantic → Descriptor)
    (projection : Descriptor → Behavior)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, RelTwo source source)
    (hinvariant : DescriptorProjectionInvariant descriptor projection RelTwo)
    {left right : Semantic}
    (hcode :
      (semanticTwoFibreCode descriptor RelOne RelTwo left).2 =
        (semanticTwoFibreCode descriptor RelOne RelTwo right).2) :
    projection (descriptor left) = projection (descriptor right) := by
  exact descriptorProjection_eq_of_semanticFibreImage_eq descriptor projection
    RelTwo hreflexive hinvariant hcode

/-- If the descriptor itself is fibre-invariant, equality of its finite
fibre images determines the actual descriptor.  This useful special case is
strictly weaker than reflecting the whole semantic relation. -/
theorem descriptor_eq_of_semanticFibreImage_eq
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source)
    (hinvariant : ∀ {left right}, Rel left right →
      descriptor left = descriptor right)
    {left right : Semantic}
    (himage : semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right) :
    descriptor left = descriptor right := by
  exact descriptorProjection_eq_of_semanticFibreImage_eq descriptor id Rel
    hreflexive hinvariant himage

end

end

end DistributedSynthesis
