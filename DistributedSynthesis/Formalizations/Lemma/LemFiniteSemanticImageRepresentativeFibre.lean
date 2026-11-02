/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreCarrier

/-!
# Pairwise laws inside one representative semantic fibre

`LemFiniteSemanticFibreCarrier` materializes an attained finite fibre image by
choosing every descriptor witness inside one fixed source fibre.  This file
adds the pairwise consequences used by a simultaneous direct-image union.

This is exactly the safe construction-side ingredient for a direct-image
union: all its raw local strategies may be taken from one semantic fibre.
It deliberately makes no claim that a different source with the same finite
image is related to the chosen representative.  Such a claim would be the
invalid image-reflection step.
-/

namespace DistributedSynthesis

universe u v w

section

variable {Semantic : Type u} {Descriptor : Type v}
variable [Fintype Descriptor] [DecidableEq Descriptor]
variable (descriptor : Semantic → Descriptor)
variable (Rel : Semantic → Semantic → Prop)

/-- All descriptor witnesses chosen for one attained image lie in one
relation class.  This is the fact that removes a separate common-sender
premise while constructing that one union. -/
theorem semanticFibreMemberWitness_pair_rel
    (hsymmetric : Symmetric Rel) (htransitive : Transitive Rel)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (left right : SemanticFibreDescriptor descriptor Rel image) :
    Rel (semanticFibreMemberWitness descriptor Rel image left)
      (semanticFibreMemberWitness descriptor Rel image right) := by
  exact htransitive
    (hsymmetric
      (semanticFibreMemberWitness_rel descriptor Rel image left))
    (semanticFibreMemberWitness_rel descriptor Rel image right)

/-- Any semantic behavior invariant on `Rel` is literally shared by every
witness in the direct-image carrier. -/
theorem semanticFibreMemberWitness_pair_behavior_eq
    {Behavior : Type w} (behavior : Semantic → Behavior)
    (hinvariant : ∀ {left right}, Rel left right →
      behavior left = behavior right)
    (hsymmetric : Symmetric Rel) (htransitive : Transitive Rel)
    (image : AttainedSemanticFibreImage descriptor Rel)
    (left right : SemanticFibreDescriptor descriptor Rel image) :
    behavior (semanticFibreMemberWitness descriptor Rel image left) =
      behavior (semanticFibreMemberWitness descriptor Rel image right) :=
  hinvariant (semanticFibreMemberWitness_pair_rel descriptor Rel hsymmetric
    htransitive image left right)

/-- The representative-fibre witness at the current descriptor has the same
finite descriptor as the source.  No semantic relation between those two
points is asserted. -/
theorem semanticFibreMemberWitness_at_source_descriptor
    (hreflexive : Reflexive Rel) (source : Semantic) :
    descriptor
        (semanticFibreMemberWitness descriptor Rel
          (attainedSemanticFibreImageOf descriptor Rel source)
          (semanticFibreDescriptorOf descriptor Rel hreflexive source)) =
      descriptor source := by
  exact semanticFibreMemberWitness_descriptor descriptor Rel _ _

end

end DistributedSynthesis
