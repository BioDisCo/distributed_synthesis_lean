/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreFamilyMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSemanticLocalFibres

/-!
# Source-indexed paired semantic-fibre banks

Fix one literal global semantic source.  On each side, the finite carrier is
the direct image of that source's exact local-view fibre under the finite
descriptor.  A member is realized by a witness related to that *same* source.
Thus the whole blind sender is automatically common inside each side's union,
and both side constructions retain one common global proof-side origin.

The source index is essential here.  This module proves the local finite
extraction brick; `ProfiledOpenPairedSourceFibreBank source` is not yet one
source-independent public alphabet.  Erasing/reindexing it into a fixed
finite family code must preserve the literal source-specific tables and their
dependent monitor states.  Choosing one representative source per equal
finite image is insufficient without an additional common-point exact lift.

There is a second, orthogonal boundary.  The inherited classified `Allowed`
law preserves targets and class membership, but not a literal semantic child
after an arbitrary non-root controller state.  Consequently this file does
not claim post-block `ExactEdge` transport.  That requires the stronger
semantic-provenance law exposed by `ProfiledOpen*SemanticTableAllowed`.

No graph, orientation, strict-leader bit, or chosen informed side is visible
to either extracted sender.
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

abbrev ProfiledOpenSourceSemanticPoint :=
  ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis (I := I)

variable {Descriptor : Type (max i u v x y s)}
variable [Fintype Descriptor] [DecidableEq Descriptor]
variable (semanticDescriptor :
  ProfiledOpenSourceSemanticPoint A strategy hwin basis (I := I) → Descriptor)

abbrev ProfiledOpenSourceFibreClass : Type (max i u v x y s) :=
  ULift.{max i u v x y s} Unit

/-! ## Direct finite carriers at one common semantic source -/

abbrev ProfiledOpenRightSourceFibreDescriptor
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source

abbrev ProfiledOpenLeftSourceFibreDescriptor
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenRightSourceFibrePoint
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenSourceSemanticPoint A strategy hwin basis (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenLeftSourceFibrePoint
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenSourceSemanticPoint A strategy hwin basis (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenRightSourceFibreSource
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenRightViewClass A :=
  (profiledOpenRightSourceFibrePoint A strategy hwin basis semanticDescriptor
    source member).rightLane.source

noncomputable def profiledOpenLeftSourceFibreSource
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenLeftViewClass A :=
  (profiledOpenLeftSourceFibrePoint A strategy hwin basis semanticDescriptor
    source member).leftLane.source

noncomputable def profiledOpenRightSourceFibreRealization
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenRightRealization A strategy hwin basis
      (profiledOpenRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenRightSourceFibrePoint A strategy hwin basis semanticDescriptor
    source member).rightLane.realization

noncomputable def profiledOpenLeftSourceFibreRealization
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenLeftRealization A strategy hwin basis
      (profiledOpenLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenLeftSourceFibrePoint A strategy hwin basis semanticDescriptor
    source member).leftLane.realization

/-! ## Trivial one-class presentations -/

noncomputable def profiledOpenRightSourceFibreCurrent
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedProcessOneLocalFibreRel_reflexive A strategy hwin
      basis).refl source

noncomputable def profiledOpenLeftSourceFibreCurrent
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedProcessTwoLocalFibreRel_reflexive A strategy hwin
      basis).refl source

noncomputable def profiledOpenRightSourceFibrePresentation
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenRightSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

noncomputable def profiledOpenLeftSourceFibrePresentation
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenLeftSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

/-! ## Automatic exact sender agreement -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenRightSourceFibrePoint_senderView_eq_source
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    currentView Proc.one
        ((profiledOpenRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member).rightSenderEntry A strategy hwin
            basis).leftHistory =
      currentView Proc.one
        (source.rightSenderEntry A strategy hwin basis).leftHistory :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I))
    (fun point => currentView Proc.one
      (point.rightSenderEntry A strategy hwin basis).leftHistory)
    (fun hrel => profiledOpenIndexedProcessOneLocalFibreRel_senderView_eq A
      strategy hwin basis hrel) source member

theorem profiledOpenLeftSourceFibrePoint_senderView_eq_source
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    currentView Proc.two
        ((profiledOpenLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member).leftSenderEntry A strategy hwin
            basis).rightHistory =
      currentView Proc.two
        (source.leftSenderEntry A strategy hwin basis).rightHistory :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I))
    (fun point => currentView Proc.two
      (point.leftSenderEntry A strategy hwin basis).rightHistory)
    (fun hrel => profiledOpenIndexedProcessTwoLocalFibreRel_senderView_eq A
      strategy hwin basis hrel) source member

theorem profiledOpenRightSourceFibreSenderViewsAgree
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenRightFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenRightSourceFibreCurrent A strategy hwin
    basis semanticDescriptor source
  calc
    currentView Proc.one
        ((profiledOpenRightSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).leftHistory =
      currentView Proc.one
        ((profiledOpenRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual).rightSenderEntry A strategy hwin
            basis).leftHistory := by
        simpa [profiledOpenRightSourceFibreRealization,
          ProfiledOpenIndexedLiveFreshSemanticPoint.rightSenderEntry] using
          (profiledOpenRightSourceFibreRealization A strategy hwin basis
            semanticDescriptor source actual).view_eq member
    _ = currentView Proc.one
        (source.rightSenderEntry A strategy hwin basis).leftHistory :=
      profiledOpenRightSourceFibrePoint_senderView_eq_source A strategy hwin
        basis semanticDescriptor source actual
    _ = currentView Proc.one
        ((profiledOpenRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative).rightSenderEntry A
            strategy hwin basis).leftHistory :=
      (profiledOpenRightSourceFibrePoint_senderView_eq_source A strategy hwin
        basis semanticDescriptor source representative).symm
    _ = currentView Proc.one
        ((profiledOpenRightSourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
            (profiledOpenRightSourceFibreRealization A strategy hwin basis
              semanticDescriptor source representative).pivot).leftHistory := by
      rfl

theorem profiledOpenLeftSourceFibreSenderViewsAgree
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenLeftFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenLeftSourceFibreCurrent A strategy hwin
    basis semanticDescriptor source
  calc
    currentView Proc.two
        ((profiledOpenLeftSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).rightHistory =
      currentView Proc.two
        ((profiledOpenLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual).leftSenderEntry A strategy hwin
            basis).rightHistory := by
        simpa [profiledOpenLeftSourceFibreRealization,
          ProfiledOpenIndexedLiveFreshSemanticPoint.leftSenderEntry] using
          (profiledOpenLeftSourceFibreRealization A strategy hwin basis
            semanticDescriptor source actual).view_eq member
    _ = currentView Proc.two
        (source.leftSenderEntry A strategy hwin basis).rightHistory :=
      profiledOpenLeftSourceFibrePoint_senderView_eq_source A strategy hwin
        basis semanticDescriptor source actual
    _ = currentView Proc.two
        ((profiledOpenLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative).leftSenderEntry A strategy
            hwin basis).rightHistory :=
      (profiledOpenLeftSourceFibrePoint_senderView_eq_source A strategy hwin
        basis semanticDescriptor source representative).symm
    _ = currentView Proc.two
        ((profiledOpenLeftSourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
            (profiledOpenLeftSourceFibreRealization A strategy hwin basis
              semanticDescriptor source representative).pivot).rightHistory := by
      rfl

end

/-! ## Common-sender certificates and extracted moves -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenRightSourceFibreCommonSenderWins
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenRightFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A
      (profiledOpenRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightSourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenLeftSourceFibreCommonSenderWins
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenLeftFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A
      (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftSourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

noncomputable abbrev ProfiledOpenRightSourceFibreMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenRightPinnedFibreMove.{u, v, x, y, s, i} A
    (profiledOpenRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenSourceFibreClass.{i, u, v, x, y, s})

noncomputable abbrev ProfiledOpenLeftSourceFibreMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenLeftPinnedFibreMove.{u, v, x, y, s, i} A
    (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenSourceFibreClass.{i, u, v, x, y, s})

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenRightSourceFibreMove A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenLeftSourceFibreMove A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenRightSourceFibreMoveOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenRightSourceFibreMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenRightPinnedFibreMoveOfCommonSenderWins A
    (profiledOpenRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightSourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenSourceFibreClass.{i, u, v, x, y, s})

noncomputable def profiledOpenLeftSourceFibreMoveOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenLeftSourceFibreMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenLeftPinnedFibreMoveOfCommonSenderWins A
    (profiledOpenLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftSourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenSourceFibreClass.{i, u, v, x, y, s})

/-- The two source-indexed extractions paired before any public-code erasure.
This is finite for every fixed source, but its type still depends on that
source and therefore is not yet the final fixed move alphabet. -/
noncomputable abbrev ProfiledOpenPairedSourceFibreBank
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenRightSourceFibreMove A strategy hwin basis semanticDescriptor
      source ×
    ProfiledOpenLeftSourceFibreMove A strategy hwin basis semanticDescriptor
      source

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenPairedSourceFibreBank A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenPairedSourceFibreBankOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenPairedSourceFibreBank A strategy hwin basis semanticDescriptor
      source :=
  (profiledOpenRightSourceFibreMoveOfWinning A strategy hwin basis
      semanticDescriptor source,
    profiledOpenLeftSourceFibreMoveOfWinning A strategy hwin basis
      semanticDescriptor source)

/-! ## Current-descriptor and common-origin laws -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenRightSourceFibreCurrentPoint_rel
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis source
      (profiledOpenRightSourceFibrePoint A strategy hwin basis
        semanticDescriptor source
        (profiledOpenRightSourceFibreCurrent A strategy hwin basis
          semanticDescriptor source)) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source
    (profiledOpenRightSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source)

theorem profiledOpenLeftSourceFibreCurrentPoint_rel
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis source
      (profiledOpenLeftSourceFibrePoint A strategy hwin basis
        semanticDescriptor source
        (profiledOpenLeftSourceFibreCurrent A strategy hwin basis
          semanticDescriptor source)) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source
    (profiledOpenLeftSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source)

theorem profiledOpenRightSourceFibreCurrentPoint_descriptor
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    semanticDescriptor
        (profiledOpenRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source
          (profiledOpenRightSourceFibreCurrent A strategy hwin basis
            semanticDescriptor source)) =
      semanticDescriptor source := by
  exact semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source
    (profiledOpenRightSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source)

theorem profiledOpenLeftSourceFibreCurrentPoint_descriptor
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    semanticDescriptor
        (profiledOpenLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source
          (profiledOpenLeftSourceFibreCurrent A strategy hwin basis
            semanticDescriptor source)) =
      semanticDescriptor source := by
  exact semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source
    (profiledOpenLeftSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source)

/-- The actual finite descriptor occurs in both direct carriers.  This is the
runtime selection law; it does not identify the two chosen semantic witnesses
or transport their dependent monitor states. -/
theorem profiledOpenSourceFibreCurrent_mem_both
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    semanticDescriptor source ∈
        semanticFibreImage semanticDescriptor
          (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
          source ∧
      semanticDescriptor source ∈
        semanticFibreImage semanticDescriptor
          (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
          source :=
  descriptor_mem_semanticTwoFibreCode semanticDescriptor
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I))
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedProcessOneLocalFibreRel_reflexive A strategy hwin
      basis).refl
    (profiledOpenIndexedProcessTwoLocalFibreRel_reflexive A strategy hwin
      basis).refl source

end

end

end DetParityAutomaton

end DistributedSynthesis
