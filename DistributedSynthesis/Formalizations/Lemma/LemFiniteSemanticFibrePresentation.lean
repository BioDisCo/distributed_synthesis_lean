/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreFamilyMove

/-!
# Finite presentations of the two attained semantic fibres

The semantic space of exact local views can be infinite.  Its envelope range
is nevertheless finite because an envelope contains only a finite descriptor
and two finite sets of descriptors.  This module turns that attained range
into the representative-bearing presentations consumed by the paired
root-family extraction.

Only attained global envelopes and attained fibre classes are retained.  We
therefore never invent a representative for an impossible class and never
need a default orientation, graph, or leader value.
-/

namespace DistributedSynthesis

universe u v

section

variable {Semantic : Type u} {Descriptor : Type v}
variable [Fintype Descriptor] [DecidableEq Descriptor]

variable (descriptor : Semantic → Descriptor)
variable (RelOne RelTwo : Semantic → Semantic → Prop)

/-- The finite attained global carrier. -/
abbrev SemanticEnvelopeGlobal :=
  AttainedSemanticEnvelope descriptor RelOne RelTwo

/-- Process-one class of an attained envelope, before restricting the
codomain to attained values. -/
def semanticEnvelopeOneClassOf
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) :
    Finset Descriptor :=
  global.1.2.1

/-- Process-two mirror. -/
def semanticEnvelopeTwoClassOf
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) :
    Finset Descriptor :=
  global.1.2.2

/-- Only process-one fibre sets that actually occur. -/
abbrev SemanticEnvelopeOneClass :=
  AttainedFiniteImage
    (semanticEnvelopeOneClassOf descriptor RelOne RelTwo)

/-- Only process-two fibre sets that actually occur. -/
abbrev SemanticEnvelopeTwoClass :=
  AttainedFiniteImage
    (semanticEnvelopeTwoClassOf descriptor RelOne RelTwo)

/-- Canonical finite process-one presentation of attained envelopes. -/
noncomputable def semanticEnvelopeOnePresentation :
    DetParityAutomaton.ProfiledOpenFiniteFibrePresentation
      (SemanticEnvelopeGlobal descriptor RelOne RelTwo)
      (SemanticEnvelopeOneClass descriptor RelOne RelTwo) where
  classOf := fun global =>
    ⟨semanticEnvelopeOneClassOf descriptor RelOne RelTwo global,
      global, rfl⟩
  representative := fun c =>
    attainedFiniteImageRepresentative
      (semanticEnvelopeOneClassOf descriptor RelOne RelTwo) c
  representative_class := by
    intro c
    apply Subtype.ext
    exact attainedFiniteImageRepresentative_spec
      (semanticEnvelopeOneClassOf descriptor RelOne RelTwo) c

/-- Canonical finite process-two presentation. -/
noncomputable def semanticEnvelopeTwoPresentation :
    DetParityAutomaton.ProfiledOpenFiniteFibrePresentation
      (SemanticEnvelopeGlobal descriptor RelOne RelTwo)
      (SemanticEnvelopeTwoClass descriptor RelOne RelTwo) where
  classOf := fun global =>
    ⟨semanticEnvelopeTwoClassOf descriptor RelOne RelTwo global,
      global, rfl⟩
  representative := fun c =>
    attainedFiniteImageRepresentative
      (semanticEnvelopeTwoClassOf descriptor RelOne RelTwo) c
  representative_class := by
    intro c
    apply Subtype.ext
    exact attainedFiniteImageRepresentative_spec
      (semanticEnvelopeTwoClassOf descriptor RelOne RelTwo) c

/-- Exact semantic representative selected for one attained global
envelope. -/
noncomputable def semanticEnvelopeGlobalRepresentative
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) : Semantic :=
  attainedSemanticEnvelopeRepresentative descriptor RelOne RelTwo global

section
omit [DecidableEq Descriptor]

theorem semanticEnvelopeGlobalRepresentative_envelope
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) :
    semanticEnvelope descriptor RelOne RelTwo
        (semanticEnvelopeGlobalRepresentative descriptor RelOne RelTwo
          global) =
      global.1 :=
  attainedSemanticEnvelopeRepresentative_spec descriptor RelOne RelTwo global

/-- The chosen global representative has exactly the process-one fibre set
stored in the global envelope. -/
theorem semanticEnvelopeGlobalRepresentative_oneFibre
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) :
    semanticFibreImage descriptor RelOne
        (semanticEnvelopeGlobalRepresentative descriptor RelOne RelTwo
          global) =
      semanticEnvelopeOneClassOf descriptor RelOne RelTwo global := by
  have h := congrArg (fun envelope => envelope.2.1)
    (semanticEnvelopeGlobalRepresentative_envelope descriptor RelOne RelTwo
      global)
  exact h

/-- Process-two mirror. -/
theorem semanticEnvelopeGlobalRepresentative_twoFibre
    (global : SemanticEnvelopeGlobal descriptor RelOne RelTwo) :
    semanticFibreImage descriptor RelTwo
        (semanticEnvelopeGlobalRepresentative descriptor RelOne RelTwo
          global) =
      semanticEnvelopeTwoClassOf descriptor RelOne RelTwo global := by
  have h := congrArg (fun envelope => envelope.2.2)
    (semanticEnvelopeGlobalRepresentative_envelope descriptor RelOne RelTwo
      global)
  exact h

end

end


end DistributedSynthesis
