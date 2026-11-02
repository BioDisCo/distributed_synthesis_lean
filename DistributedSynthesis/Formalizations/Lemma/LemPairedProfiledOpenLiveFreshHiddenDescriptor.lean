/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreProvenanceMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet

/-!
# Full hidden descriptors at a live fresh semantic source

The source-indexed extraction is parameterized by an arbitrary finite
descriptor.  Here we instantiate that descriptor with exactly the finite
coordinate consumed by the anti-mosaic monitor:

```
((indexed public code, code-parity control), old finite semantic move).
```

The parity control is fixed while taking either exact local-view fibre.  It is
proof-side path state, not an observation of either process.  The resulting
two finite images are therefore one value of the fixed family-code type used
by the public alphabet.

This file deliberately stops before erasing the source-dependent controller
types.  Its endpoint is the exact, provenance-preserving bank that the fixed
alphabet adapter must transport without choosing a representative semantic
source.
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

noncomputable local instance :
    DecidableEq (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode) :=
  Classical.decEq _

/-- A live fresh semantic point together with the literal code-parity control
at that history.  The control is not recomputed from the semantic point. -/
abbrev ProfiledOpenIndexedControlledLiveFreshSemanticPoint :=
  ProfiledOpenSourceSemanticPoint A strategy hwin basis (I := I) ×
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State

/-- The old finite semantic move stored as proof-side identity. -/
noncomputable def profiledOpenIndexedLiveFreshOldMove
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedBiBeliefMove A :=
  point.state.move A strategy hwin basis

/-- Full hidden descriptor at a fixed path-dependent parity control. -/
noncomputable def profiledOpenIndexedLiveFreshHiddenDescriptorAt
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode :=
  ((point.state.code A strategy hwin basis, control),
    profiledOpenIndexedLiveFreshOldMove A strategy hwin basis point)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_code
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control point).code =
        point.state.code A strategy hwin basis :=
  rfl

@[simp] theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_control
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control point).control = control :=
  rfl

@[simp] theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_moveIdentity
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control point).moveIdentity =
        point.state.move A strategy hwin basis :=
  rfl

/-- The right half of the stored old move is literally the live right lane's
classified table.  This is the finite equality used to transport its roots
into the canonical descriptor-indexed root type. -/
theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_rightMove
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control point).moveIdentity.1 =
      .right point.rightLane.source
        ((point.rightLane.realization.coherentTable A).table.toClassified A
          point.rightLane.source) := by
  rw [profiledOpenIndexedLiveFreshHiddenDescriptorAt_moveIdentity]
  simp only [profiledOpenIndexedLiveFreshOldMove,
    ProfiledOpenIndexedCorrelatedSemanticState.move,
    point.right_eq,
    ProfiledOpenIndexedRightSemanticShadow.move]

/-- Left mirror of `profiledOpenIndexedLiveFreshHiddenDescriptorAt_rightMove`. -/
theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_leftMove
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (point : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control point).moveIdentity.2 =
      .left point.leftLane.source
        ((point.leftLane.realization.coherentTable A).table.toClassified A
          point.leftLane.source) := by
  rw [profiledOpenIndexedLiveFreshHiddenDescriptorAt_moveIdentity]
  simp only [profiledOpenIndexedLiveFreshOldMove,
    ProfiledOpenIndexedCorrelatedSemanticState.move,
    point.left_eq,
    ProfiledOpenIndexedLeftSemanticShadow.move]

end

/-- The public two-fibre family carried by one literal source and one literal
parity control. -/
noncomputable def profiledOpenIndexedLiveFreshFamilyAt
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  semanticTwoFibreCode
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I))
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenIndexedLiveFreshFamilyAt_right
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshFamilyAt A strategy hwin basis initialCode
      control source).1 =
      semanticFibreImage
        (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
          initialCode control)
        (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
          (I := I)) source :=
  rfl

@[simp] theorem profiledOpenIndexedLiveFreshFamilyAt_left
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    (profiledOpenIndexedLiveFreshFamilyAt A strategy hwin basis initialCode
      control source).2 =
      semanticFibreImage
        (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
          initialCode control)
        (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
          (I := I)) source :=
  rfl

/-- The actual full hidden descriptor is present in both public local-fibre
images. -/
theorem profiledOpenIndexedLiveFreshHiddenDescriptorAt_mem_family
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    let descriptor :=
      profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
        initialCode control source
    descriptor ∈
        (profiledOpenIndexedLiveFreshFamilyAt A strategy hwin basis initialCode
          control source).1 ∧
      descriptor ∈
        (profiledOpenIndexedLiveFreshFamilyAt A strategy hwin basis initialCode
          control source).2 := by
  exact profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control) source

end

/-- The exact source-indexed, provenance-preserving bank at the full hidden
descriptor.  Its type remains source-dependent; the fixed-alphabet adapter is
the next layer. -/
noncomputable abbrev ProfiledOpenIndexedLiveFreshProvenanceBankAt
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenPairedSourceFibreProvenanceBank A strategy hwin basis
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control) source

/-- Winning raw semantics supplies the full exact bank at every live source
and every path-dependent parity control. -/
noncomputable def profiledOpenIndexedLiveFreshProvenanceBankAtOfWinning
    (control : (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedLiveFreshProvenanceBankAt A strategy hwin basis
      initialCode control source :=
  profiledOpenPairedSourceFibreProvenanceBankOfWinning A strategy hwin basis
    (profiledOpenIndexedLiveFreshHiddenDescriptorAt A strategy hwin basis
      initialCode control) source

end

end DetParityAutomaton

end DistributedSynthesis
