/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemHiddenCodeContinuityBundle

/-!
# Finite images of semantic local-view fibres

The exact local view of a perfect-recall process is generally infinite-state.
For staging a finite family move we do not store that view.  Instead, for one
semantic history, we store the image of its whole local-view equivalence class
under a fixed finite descriptor map.  In the profiled construction the
descriptor contains the public code together with the finite table move, so
two histories with the same code but different tables are not silently
identified.

This file is deliberately independent of the concrete view model.  It needs
only the elementary class law saying that related semantic points have the
same relation fibre.  No representative, orientation, or leader bit occurs in
the resulting finite code.
-/

namespace DistributedSynthesis

universe u v

section

variable {Semantic : Type u} {Descriptor : Type v}
variable [Fintype Descriptor] [DecidableEq Descriptor]

/-- The finite descriptor image of one semantic relation fibre. -/
noncomputable def semanticFibreImage
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop) (source : Semantic) :
    Finset Descriptor := by
  classical
  exact Finset.univ.filter fun value =>
    ∃ target, Rel source target ∧ descriptor target = value

omit [DecidableEq Descriptor] in
theorem mem_semanticFibreImage_iff
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop) (source : Semantic)
    (value : Descriptor) :
    value ∈ semanticFibreImage descriptor Rel source ↔
      ∃ target, Rel source target ∧ descriptor target = value := by
  classical
  simp [semanticFibreImage]

omit [DecidableEq Descriptor] in
/-- A reflexive semantic relation represents the current descriptor in its
own finite fibre image. -/
theorem descriptor_mem_semanticFibreImage
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hreflexive : ∀ source, Rel source source) (source : Semantic) :
    descriptor source ∈ semanticFibreImage descriptor Rel source := by
  rw [mem_semanticFibreImage_iff]
  exact ⟨source, hreflexive source, rfl⟩

/-- Extensional class law needed by the finite image construction.  Every
equivalence relation satisfies it, but the weaker formulation is convenient
for model-specific exact-view relations. -/
def RelationFibresAgree (Rel : Semantic → Semantic → Prop) : Prop :=
  ∀ {left right}, Rel left right → ∀ target,
    (Rel left target ↔ Rel right target)

omit [DecidableEq Descriptor] in
/-- Related semantic points have literally the same finite descriptor
family. -/
theorem semanticFibreImage_eq_of_rel
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop)
    (hfibres : RelationFibresAgree Rel)
    {left right : Semantic} (hrel : Rel left right) :
    semanticFibreImage descriptor Rel left =
      semanticFibreImage descriptor Rel right := by
  classical
  ext value
  simp only [mem_semanticFibreImage_iff]
  constructor
  · rintro ⟨target, htarget, rfl⟩
    exact ⟨target, (hfibres hrel target).mp htarget, rfl⟩
  · rintro ⟨target, htarget, rfl⟩
    exact ⟨target, (hfibres hrel target).mpr htarget, rfl⟩

/-- Symmetry and transitivity are sufficient for fibre agreement. -/
theorem relationFibresAgree_of_symmetric_transitive
    (Rel : Semantic → Semantic → Prop)
    (hsymmetric : Symmetric Rel) (htransitive : IsTrans _ Rel) :
    RelationFibresAgree Rel := by
  intro left right hrel target
  constructor
  · intro hleft
    exact htransitive.trans _ _ _ (hsymmetric hrel) hleft
  · intro hright
    exact htransitive.trans _ _ _ hrel hright

/-! ## The two-process public family code -/

/-- The public finite staging code consists of the two finite local-fibre
images.  It contains no distinguished actual descriptor; continuity of the
actual descriptor is the separate hidden-thread coordinate. -/
abbrev FiniteTwoFibreCode (Descriptor : Type v) [Fintype Descriptor] :=
  Finset Descriptor × Finset Descriptor

noncomputable instance :
    Fintype (FiniteTwoFibreCode Descriptor) := by
  classical
  infer_instance

/-- Abstract semantic construction of the two local descriptor families. -/
noncomputable def semanticTwoFibreCode
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) : FiniteTwoFibreCode Descriptor :=
  (semanticFibreImage descriptor RelOne source,
    semanticFibreImage descriptor RelTwo source)

section
omit [DecidableEq Descriptor]

@[simp] theorem semanticTwoFibreCode_fst
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (semanticTwoFibreCode descriptor RelOne RelTwo source).1 =
      semanticFibreImage descriptor RelOne source :=
  rfl

@[simp] theorem semanticTwoFibreCode_snd
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (semanticTwoFibreCode descriptor RelOne RelTwo source).2 =
      semanticFibreImage descriptor RelTwo source :=
  rfl

/-- Process-one-equivalent points expose the same process-one family. -/
theorem semanticTwoFibreCode_fst_eq_of_rel
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hfibres : RelationFibresAgree RelOne)
    {left right : Semantic} (hrel : RelOne left right) :
    (semanticTwoFibreCode descriptor RelOne RelTwo left).1 =
      (semanticTwoFibreCode descriptor RelOne RelTwo right).1 := by
  exact semanticFibreImage_eq_of_rel descriptor RelOne hfibres hrel

/-- Process-two mirror. -/
theorem semanticTwoFibreCode_snd_eq_of_rel
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hfibres : RelationFibresAgree RelTwo)
    {left right : Semantic} (hrel : RelTwo left right) :
    (semanticTwoFibreCode descriptor RelOne RelTwo left).2 =
      (semanticTwoFibreCode descriptor RelOne RelTwo right).2 := by
  exact semanticFibreImage_eq_of_rel descriptor RelTwo hfibres hrel

/-- Both actual descriptor memberships, used to initialize the persistent
hidden-code thread below the public family code. -/
theorem descriptor_mem_semanticTwoFibreCode
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hreflexiveOne : ∀ source, RelOne source source)
    (hreflexiveTwo : ∀ source, RelTwo source source)
    (source : Semantic) :
    descriptor source ∈
        (semanticTwoFibreCode descriptor RelOne RelTwo source).1 ∧
      descriptor source ∈
        (semanticTwoFibreCode descriptor RelOne RelTwo source).2 := by
  exact ⟨descriptor_mem_semanticFibreImage descriptor RelOne hreflexiveOne
      source,
    descriptor_mem_semanticFibreImage descriptor RelTwo hreflexiveTwo source⟩

end

/-! ## Finite semantic envelopes and attained representatives -/

/-- One finite semantic envelope retains the actual finite descriptor and
both local descriptor families.  Keeping all three coordinates prevents two
semantic states with the same descriptor but different local possibility
sets from being silently identified. -/
abbrev FiniteSemanticEnvelope (Descriptor : Type v)
    [Fintype Descriptor] :=
  Descriptor × FiniteTwoFibreCode Descriptor

noncomputable instance : Fintype (FiniteSemanticEnvelope Descriptor) := by
  classical
  infer_instance

/-- The finite envelope exposed by one exact semantic state. -/
noncomputable def semanticEnvelope
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) : FiniteSemanticEnvelope Descriptor :=
  (descriptor source,
    semanticTwoFibreCode descriptor RelOne RelTwo source)

section
omit [DecidableEq Descriptor]

@[simp] theorem semanticEnvelope_descriptor
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (semanticEnvelope descriptor RelOne RelTwo source).1 =
      descriptor source :=
  rfl

@[simp] theorem semanticEnvelope_oneFibre
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (semanticEnvelope descriptor RelOne RelTwo source).2.1 =
      semanticFibreImage descriptor RelOne source :=
  rfl

@[simp] theorem semanticEnvelope_twoFibre
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (semanticEnvelope descriptor RelOne RelTwo source).2.2 =
      semanticFibreImage descriptor RelTwo source :=
  rfl

end

section
omit [DecidableEq Descriptor]

/-- Process one sees the same first family component at related semantic
states; no equality of the hidden actual descriptor is asserted. -/
theorem semanticEnvelope_oneFibre_eq_of_rel
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hfibres : RelationFibresAgree RelOne)
    {left right : Semantic} (hrel : RelOne left right) :
    (semanticEnvelope descriptor RelOne RelTwo left).2.1 =
      (semanticEnvelope descriptor RelOne RelTwo right).2.1 := by
  exact semanticFibreImage_eq_of_rel descriptor RelOne hfibres hrel

/-- Process-two mirror. -/
theorem semanticEnvelope_twoFibre_eq_of_rel
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hfibres : RelationFibresAgree RelTwo)
    {left right : Semantic} (hrel : RelTwo left right) :
    (semanticEnvelope descriptor RelOne RelTwo left).2.2 =
      (semanticEnvelope descriptor RelOne RelTwo right).2.2 := by
  exact semanticFibreImage_eq_of_rel descriptor RelTwo hfibres hrel

/-- The actual descriptor is represented in both local families of its
envelope. -/
theorem semanticEnvelope_descriptor_mem
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (hreflexiveOne : ∀ source, RelOne source source)
    (hreflexiveTwo : ∀ source, RelTwo source source)
    (source : Semantic) :
    descriptor source ∈
        (semanticEnvelope descriptor RelOne RelTwo source).2.1 ∧
      descriptor source ∈
        (semanticEnvelope descriptor RelOne RelTwo source).2.2 := by
  exact descriptor_mem_semanticTwoFibreCode descriptor RelOne RelTwo
    hreflexiveOne hreflexiveTwo source

end

/-- Only envelopes that occur at some exact semantic state are retained as
global descriptors.  The subtype is finite although `Semantic` itself may be
infinite. -/
abbrev AttainedSemanticEnvelope
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop) :=
  { envelope : FiniteSemanticEnvelope Descriptor //
    ∃ source,
      semanticEnvelope descriptor RelOne RelTwo source = envelope }

noncomputable instance attainedSemanticEnvelope_fintype
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop) :
    Fintype (AttainedSemanticEnvelope descriptor RelOne RelTwo) := by
  classical
  exact Fintype.ofFinite _

/-- A proof-side exact representative of an attained finite envelope. -/
noncomputable def attainedSemanticEnvelopeRepresentative
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (envelope : AttainedSemanticEnvelope descriptor RelOne RelTwo) :
    Semantic :=
  Classical.choose envelope.property

omit [DecidableEq Descriptor] in
theorem attainedSemanticEnvelopeRepresentative_spec
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (envelope : AttainedSemanticEnvelope descriptor RelOne RelTwo) :
    semanticEnvelope descriptor RelOne RelTwo
        (attainedSemanticEnvelopeRepresentative descriptor RelOne RelTwo
          envelope) =
      envelope.1 :=
  Classical.choose_spec envelope.property

/-- Every exact semantic point determines an attained envelope. -/
noncomputable def attainedSemanticEnvelopeOf
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    AttainedSemanticEnvelope descriptor RelOne RelTwo :=
  ⟨semanticEnvelope descriptor RelOne RelTwo source, source, rfl⟩

omit [DecidableEq Descriptor] in
@[simp] theorem attainedSemanticEnvelopeOf_val
    (descriptor : Semantic → Descriptor)
    (RelOne RelTwo : Semantic → Semantic → Prop)
    (source : Semantic) :
    (attainedSemanticEnvelopeOf descriptor RelOne RelTwo source).1 =
      semanticEnvelope descriptor RelOne RelTwo source :=
  rfl

/-! ### Finite images with chosen preimages -/

/-- The attained image of a map out of a finite type.  Unlike the whole
codomain, every element of this subtype has a usable preimage. -/
abbrev AttainedFiniteImage {Global : Type u} {Class : Type v}
    (classOf : Global → Class) :=
  { value : Class // ∃ global, classOf global = value }

noncomputable instance attainedFiniteImage_fintype
    {Global : Type u} {Class : Type v}
    [Fintype Class] (classOf : Global → Class) :
    Fintype (AttainedFiniteImage classOf) := by
  classical
  exact Fintype.ofFinite _

/-- Chosen global representative of an attained finite image class. -/
noncomputable def attainedFiniteImageRepresentative
    {Global : Type u} {Class : Type v}
    (classOf : Global → Class)
    (c : AttainedFiniteImage classOf) : Global :=
  Classical.choose c.property

theorem attainedFiniteImageRepresentative_spec
    {Global : Type u} {Class : Type v}
    (classOf : Global → Class)
    (c : AttainedFiniteImage classOf) :
    classOf (attainedFiniteImageRepresentative classOf c) = c.1 :=
  Classical.choose_spec c.property

end

end DistributedSynthesis
