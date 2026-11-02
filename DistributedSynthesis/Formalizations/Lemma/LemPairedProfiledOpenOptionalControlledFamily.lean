/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFamilyAwareHiddenDescriptorThreadLifting
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalControlledSemantic
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedPinnedProvenance

/-!
# The fixed public family of an optional controlled semantic state

This file joins two already finite constructions without adding an observable
lane.  At a proof-side optional semantic state, the literal parity control is
frozen across the current exact fibre and the optional fixed-family adapter
selects one value of the common pinned family-move alphabet.  Its first
projection is the public family used at that state.

The only representation predicate recorded here is the exact four-way shape
proved by the optional adapter: inactive, right-only, left-only, or both.  The
disjunction is proof-side.  It supplies neither process with an orientation,
strict-leader flag, selected lane, or distinguished member of a family.

The final definition names, but deliberately does not prove, the remaining
family-aware exact-successor law.  In particular this file does not turn the
weak fixed controller into a provenance controller.  A later inhabitant of
that target must take provenance preservation as part of its `Valid` premise
and prove the two successor equalities required by the family-aware lifting
interface.
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

/-! ## Controlled fixed family and move -/

/-- The common fixed-alphabet move selected at one optional controlled
semantic state.  The literal parity control is held constant only while the
current exact semantic fibre is extracted. -/
noncomputable def profiledOpenOptionalControlledMoveOf
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x, y, s,
      0, 0} A (I := I) initialCode :=
  profiledOpenOptionalFixedPinnedSemanticMoveOfWinning.{i, u, v, x, y, s,
    0, 0} A strategy hwin basis (I := I) initialCode (fun _ ↦ point.2)
      point.1

/-- Public finite family selected at the current optional controlled state. -/
noncomputable def profiledOpenOptionalControlledFamilyOf
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode
    point).1

@[simp] theorem profiledOpenOptionalControlledMoveOf_family
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    (profiledOpenOptionalControlledMoveOf A strategy hwin basis initialCode
      point).1 =
      profiledOpenOptionalControlledFamilyOf A strategy hwin basis
        initialCode point :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed-family adapter's descriptor at the current source is literally
the optional controlled semantic descriptor. -/
@[simp] theorem profiledOpenOptionalFixedSemanticDescriptor_constControl
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode (fun _ ↦ point.2) point.1.state =
      profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
        basis initialCode point :=
  rfl

/-! ## Lane-shape-aware representation -/

/-- A descriptor is represented by the optional public family exactly in the
four shapes exposed by the source adapter.  The empty-family alternative is
kept explicitly because the total optional semantics contains inactive
states. -/
def ProfiledOpenOptionalControlledRepresented
    (descriptor : ProfiledOpenIndexedOldMoveHiddenDescriptor A initialCode)
    (family : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
      initialCode) :
    Prop :=
  family = (∅, ∅) ∨
    (descriptor ∈ family.1 ∧ family.2 = ∅) ∨
    (family.1 = ∅ ∧ descriptor ∈ family.2) ∨
    (descriptor ∈ family.1 ∧ descriptor ∈ family.2)

/-- Every optional controlled state is represented by its selected public
family.  This theorem is only the finite four-way shape theorem; it makes no
claim that either process can observe which alternative holds. -/
theorem profiledOpenOptionalControlledDescriptor_represented
    (point : ProfiledOpenIndexedOptionalControlledSemanticState A strategy
      hwin basis initialCode) :
    ProfiledOpenOptionalControlledRepresented A initialCode
      (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy
        hwin basis initialCode point)
      (profiledOpenOptionalControlledFamilyOf A strategy hwin basis
        initialCode point) := by
  classical
  letI : DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
    fixedPinnedProvenanceDescriptorDecidableEq A initialCode
  let control := fun _ : ProfiledOpenIndexedCorrelatedSemanticState A strategy
      hwin basis (I := I) ↦ point.2
  let bank :=
    profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) point.1
  simpa only [ProfiledOpenOptionalControlledRepresented,
    profiledOpenOptionalControlledFamilyOf,
    profiledOpenOptionalControlledMoveOf,
    profiledOpenOptionalFixedSemanticDescriptor_constControl] using
      (profiledOpenOptionalFixedPinnedSemanticMoveOfBank_shape A strategy hwin
        basis initialCode control point.1 bank)

/-! ## The remaining family-aware exact-successor obligation -/

/-- The concrete, family-aware exact-successor congruence still required for
the optional controlled semantics.

`Valid` is intentionally a parameter.  Its eventual concrete definition must
certify that the fixed controller is the provenance-preserving transport of
the source-fibre controller (and may totalize families which are not
attained).  No such transport is inferred from the weak fixed controller in
this file.  An inhabitant says that every `Valid` exact edge from the literal
current descriptor reaches both the literal semantic child descriptor and
the child's selected public family. -/
def ProfiledOpenOptionalControlledFamilyAwareExactSuccessorCongruence
    (ExactEdge :
      ProfiledOpenIndexedOldMoveHiddenDescriptor A initialCode →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x, y, s,
        0, 0} A (I := I) initialCode →
      ProfiledOpenIndexedFiniteDirectionTag A (I := I) →
      ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode →
      ProfiledOpenIndexedOldMoveHiddenDescriptor A initialCode → Prop)
    (Valid : ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I)
        initialCode →
      ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove.{i, u, v, x, y, s,
        0, 0} A (I := I) initialCode → Prop) : Prop :=
  FamilyAwareHiddenDescriptorEdgeLifter
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode)
    (profiledOpenIndexedOptionalControlledSemanticNext A strategy hwin basis
      initialCode)
    (profiledOpenIndexedOptionalControlledSemanticDescriptor A strategy hwin
      basis initialCode)
    (profiledOpenOptionalControlledFamilyOf A strategy hwin basis initialCode)
    ExactEdge Valid

end

end DetParityAutomaton

end DistributedSynthesis
