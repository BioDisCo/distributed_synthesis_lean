/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreFamilyMove

/-!
# Finite presentations of an exact semantic relation

At one raw history only finitely many semantic witnesses are needed.  On that
finite carrier we may materialize the exact relation class of every witness
as a `Finset`, retain only attained classes, and choose one representative of
each class.  Unlike grouping by a finite descriptor image in the ambient
infinite semantic space, equality of these literal finite relation fibres
does imply the relation: reflexivity puts the representative into its own
fibre and equality moves that membership to the requested source fibre.

This is a construction-side device.  The semantic carrier and its class are
proof data; neither becomes a leader, orientation, or graph observation.
-/

namespace DistributedSynthesis

universe u v

section

variable {Carrier : Type u} [Fintype Carrier] [DecidableEq Carrier]

/-- The exact relation fibre of one point, materialized inside a finite
semantic carrier. -/
noncomputable def finiteRelationFibre
    (Rel : Carrier → Carrier → Prop) (source : Carrier) : Finset Carrier := by
  classical
  exact Finset.univ.filter (Rel source)

omit [DecidableEq Carrier] in
@[simp] theorem mem_finiteRelationFibre
    (Rel : Carrier → Carrier → Prop) (source target : Carrier) :
    target ∈ finiteRelationFibre Rel source ↔ Rel source target := by
  classical
  simp [finiteRelationFibre]

/-- Only relation fibres attained by the finite carrier. -/
abbrev AttainedFiniteRelationClass
    (Rel : Carrier → Carrier → Prop) :=
  AttainedFiniteImage (finiteRelationFibre Rel)

/-- The canonical attained class of one finite semantic point. -/
noncomputable def attainedFiniteRelationClassOf
    (Rel : Carrier → Carrier → Prop) (source : Carrier) :
    AttainedFiniteRelationClass Rel :=
  ⟨finiteRelationFibre Rel source, source, rfl⟩

/-- A proof-side representative for one attained exact class. -/
noncomputable def finiteRelationClassRepresentative
    (Rel : Carrier → Carrier → Prop)
    (c : AttainedFiniteRelationClass Rel) : Carrier :=
  attainedFiniteImageRepresentative (finiteRelationFibre Rel) c

omit [DecidableEq Carrier] in
theorem finiteRelationClassRepresentative_fibre
    (Rel : Carrier → Carrier → Prop)
    (c : AttainedFiniteRelationClass Rel) :
    finiteRelationFibre Rel
        (finiteRelationClassRepresentative Rel c) = c.1 :=
  attainedFiniteImageRepresentative_spec (finiteRelationFibre Rel) c

/-- Canonical representative-bearing presentation consumed by the finite
descriptor-family extraction. -/
noncomputable def finiteRelationPresentation
    (Rel : Carrier → Carrier → Prop) :
    DetParityAutomaton.ProfiledOpenFiniteFibrePresentation Carrier
      (AttainedFiniteRelationClass Rel) where
  classOf := attainedFiniteRelationClassOf Rel
  representative := finiteRelationClassRepresentative Rel
  representative_class := by
    intro c
    apply Subtype.ext
    exact finiteRelationClassRepresentative_fibre Rel c

section
omit [DecidableEq Carrier]

/-- Equality of materialized finite relation fibres gives the literal
relation, provided the relation is reflexive.  No descriptor-image reflection
principle is involved. -/
theorem rel_of_finiteRelationFibre_eq
    (Rel : Carrier → Carrier → Prop)
    (hreflexive : ∀ source, Rel source source)
    {left right : Carrier}
    (heq : finiteRelationFibre Rel left = finiteRelationFibre Rel right) :
    Rel left right := by
  have hmem : right ∈ finiteRelationFibre Rel right := by
    exact (mem_finiteRelationFibre Rel right right).2 (hreflexive right)
  rw [← heq] at hmem
  exact (mem_finiteRelationFibre Rel left right).1 hmem

/-- Equal canonical attained classes imply the underlying exact relation. -/
theorem rel_of_attainedFiniteRelationClassOf_eq
    (Rel : Carrier → Carrier → Prop)
    (hreflexive : ∀ source, Rel source source)
    {left right : Carrier}
    (heq : attainedFiniteRelationClassOf Rel left =
      attainedFiniteRelationClassOf Rel right) :
    Rel left right := by
  apply rel_of_finiteRelationFibre_eq Rel hreflexive
  exact congrArg Subtype.val heq

/-- Every point is related to the chosen representative of its attained
finite exact class. -/
theorem rel_finiteRelationClassRepresentative
    (Rel : Carrier → Carrier → Prop)
    (hreflexive : ∀ source, Rel source source)
    (source : Carrier) :
    Rel source
      (finiteRelationClassRepresentative Rel
        (attainedFiniteRelationClassOf Rel source)) := by
  let representative := finiteRelationClassRepresentative Rel
    (attainedFiniteRelationClassOf Rel source)
  have hclass :
      attainedFiniteRelationClassOf Rel representative =
        attainedFiniteRelationClassOf Rel source := by
    apply Subtype.ext
    exact finiteRelationClassRepresentative_fibre Rel
      (attainedFiniteRelationClassOf Rel source)
  exact rel_of_attainedFiniteRelationClassOf_eq Rel hreflexive hclass.symm

/-- Two points in one presented class are related whenever the relation is
symmetric and transitive. -/
theorem finiteRelationPresentation_pair_rel
    (Rel : Carrier → Carrier → Prop)
    (hreflexive : ∀ source, Rel source source)
    (hsymmetric : Symmetric Rel) (htransitive : IsTrans _ Rel)
    {left right : Carrier}
    (hclass : (finiteRelationPresentation Rel).classOf left =
      (finiteRelationPresentation Rel).classOf right) :
    Rel left right := by
  exact rel_of_attainedFiniteRelationClassOf_eq Rel hreflexive hclass

end

end

end DistributedSynthesis
