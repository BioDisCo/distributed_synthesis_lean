/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyProvenanceReindexing
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreFamilyMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSourceFibreBank
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenCoherentTable

/-!
# Semantic provenance on one fibre-union controller

The public fibre move records only the finite classified-table law.  For the
raw history-dependent run we additionally need to know that every table read
from the *same* controller is a literal table of the original strategy at one
semantic past.  This module applies the provenance-preserving family
extraction before forgetting that stronger law.

Every member monitor is root-pinned before the descriptor union is formed.
Thus the returned weak controller has both properties simultaneously:

* its first record is the prescribed raw record at every descriptor/root;
* at every later controller node, each descriptor projection has a semantic
  history witness for its complete receiver table.

The semantic witness is proof-side.  The shared sender controller sees none
of the descriptor, root, orientation, or leader information.
-/

namespace DistributedSynthesis

universe i u v x y s z

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable {Global OneClass TwoClass : Type (max z u v x y s)}
variable [Fintype Global] [DecidableEq Global]
variable [Fintype OneClass] [DecidableEq OneClass]
variable [Fintype TwoClass] [DecidableEq TwoClass]

variable
  (oneFibre : ProfiledOpenFiniteFibrePresentation Global OneClass)
  (twoFibre : ProfiledOpenFiniteFibrePresentation Global TwoClass)

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

variable
  (rightSource : Global → ProfiledOpenRightViewClass A)
  (leftSource : Global → ProfiledOpenLeftViewClass A)
  (rightRealization : ∀ descriptor,
    ProfiledOpenRightRealization A strategy hwin basis
      (rightSource descriptor))
  (leftRealization : ∀ descriptor,
    ProfiledOpenLeftRealization A strategy hwin basis
      (leftSource descriptor))

/-! ## Strong descriptor laws -/

/-- Right semantic provenance, transported across the harmless `ULift` used
to put all descriptor roots in one universe. -/
def profiledOpenRightFibreSemanticAllowed (c : OneClass)
    (descriptor : oneFibre.Fibre c)
    (responses :
      ((ProfiledOpenRightFibreRoot A oneFibre rightSource c descriptor × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A) : Prop :=
  ProfiledOpenRightSemanticTableAllowed A (rightSource descriptor.1) strategy
    hwin (rightRealization descriptor.1).entry basis
    (fun input ↦ responses ((ULift.up input.1.1, input.1.2), input.2))

/-- Left semantic provenance law. -/
def profiledOpenLeftFibreSemanticAllowed (c : TwoClass)
    (descriptor : twoFibre.Fibre c)
    (responses :
      ((ProfiledOpenLeftFibreRoot A twoFibre leftSource c descriptor × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ProfiledOpenLeftSemanticTableAllowed A (leftSource descriptor.1) strategy
    hwin (leftRealization descriptor.1).entry basis
    (fun input ↦ responses ((ULift.up input.1.1, input.1.2), input.2))

omit [Fintype Global] [DecidableEq Global] [Fintype OneClass] [DecidableEq OneClass]
    [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRightFibreSemanticAllowed_implies_allowed
    (c : OneClass) (descriptor : oneFibre.Fibre c) (responses :
      ((ProfiledOpenRightFibreRoot A oneFibre rightSource c descriptor × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A)
    (hsemantic : profiledOpenRightFibreSemanticAllowed A oneFibre strategy hwin
      basis rightSource rightRealization c descriptor responses) :
    profiledOpenRightFibreAllowed A oneFibre rightSource c descriptor
      responses := by
  rcases hsemantic with ⟨past, hpast⟩
  unfold profiledOpenRightFibreAllowed
  rw [hpast]
  exact profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
    (rightSource descriptor.1) strategy hwin
    (rightRealization descriptor.1).entry
    (rightRealization descriptor.1).minimum basis past

omit [Fintype Global] [DecidableEq Global] [Fintype TwoClass] [DecidableEq TwoClass]
    [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftFibreSemanticAllowed_implies_allowed
    (c : TwoClass) (descriptor : twoFibre.Fibre c) (responses :
      ((ProfiledOpenLeftFibreRoot A twoFibre leftSource c descriptor × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A)
    (hsemantic : profiledOpenLeftFibreSemanticAllowed A twoFibre strategy hwin
      basis leftSource leftRealization c descriptor responses) :
    profiledOpenLeftFibreAllowed A twoFibre leftSource c descriptor
      responses := by
  rcases hsemantic with ⟨past, hpast⟩
  unfold profiledOpenLeftFibreAllowed
  rw [hpast]
  exact profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
    (leftSource descriptor.1) strategy hwin
    (leftRealization descriptor.1).entry
    (leftRealization descriptor.1).minimum basis past

/-! ## Pinned provenance moves -/

/-- One right fibre controller, weakly usable by the finite outer alphabet,
but retaining the literal semantic-table law on the same labeled tree. -/
noncomputable abbrev ProfiledOpenRightPinnedFibreProvenanceMove
    (c : OneClass) :=
  FiniteDescriptorFamilyProvenanceMove
    (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
    (descriptorRootPinnedMonitor
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
      (profiledOpenRightFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
        A oneFibre rightSource c)
      (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c))
    (profiledOpenRightFibreSemanticAllowed A oneFibre strategy hwin basis
      rightSource rightRealization c)
    (profiledOpenRightFibreAllowed A oneFibre rightSource c)

/-- Left mirror. -/
noncomputable abbrev ProfiledOpenLeftPinnedFibreProvenanceMove
    (c : TwoClass) :=
  FiniteDescriptorFamilyProvenanceMove
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
    (descriptorRootPinnedMonitor
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
      (profiledOpenLeftFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
        A twoFibre leftSource c)
      (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization c))
    (profiledOpenLeftFibreSemanticAllowed A twoFibre strategy hwin basis
      leftSource leftRealization c)
    (profiledOpenLeftFibreAllowed A twoFibre leftSource c)

/-! ## One-pass extraction -/

noncomputable def profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins
    (hwins : ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization)
    (c : OneClass) :
    ProfiledOpenRightPinnedFibreProvenanceMove A oneFibre strategy hwin basis
      rightSource rightRealization c := by
  classical
  let representative : oneFibre.Fibre c :=
    ⟨oneFibre.representative c, oneFibre.representative_class c⟩
  let Root := ProfiledOpenRightFibreRoot A oneFibre rightSource c
  let baseM := profiledOpenRightFibreMonitor.{u, v, x, y, s, z,
    max z u v x y s} A oneFibre rightSource c
  let expected := profiledOpenRightFibreExpected A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  let M := descriptorRootPinnedMonitor Root baseM expected
  let Strong := profiledOpenRightFibreSemanticAllowed A oneFibre strategy hwin
    basis rightSource rightRealization c
  let Weak := profiledOpenRightFibreAllowed A oneFibre rightSource c
  let receiver := profiledOpenRightFibreReceiver A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  let sender := profiledOpenRightFibreSender A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  letI : Inhabited (Sigma Root) :=
    ⟨⟨representative,
      ULift.up (rightRealization (oneFibre.representative c)).pivot⟩⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    refine ⟨past.map (fun old ↦
      (((rightRealization descriptor.1).pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenRightFibreSemanticAllowed,
      profiledOpenRightSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenRightFibreReceiver, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def]
  apply finiteDescriptorFamilyProvenanceMoveOfStrategies Root M Strong Weak
    (fun descriptor responses hsemantic =>
      profiledOpenRightFibreSemanticAllowed_implies_allowed A oneFibre strategy
        hwin basis rightSource rightRealization c descriptor responses
        hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · intro member env
    apply (baseM member.1 member.2).rootPinned_realizable
      (expected member) (receiver member) sender
    · exact hwins c member
    · intro move
      rfl
  · exact hstrong

noncomputable def profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins
    (hwins : ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization)
    (c : TwoClass) :
    ProfiledOpenLeftPinnedFibreProvenanceMove A twoFibre strategy hwin basis
      leftSource leftRealization c := by
  classical
  let representative : twoFibre.Fibre c :=
    ⟨twoFibre.representative c, twoFibre.representative_class c⟩
  let Root := ProfiledOpenLeftFibreRoot A twoFibre leftSource c
  let baseM := profiledOpenLeftFibreMonitor.{u, v, x, y, s, z,
    max z u v x y s} A twoFibre leftSource c
  let expected := profiledOpenLeftFibreExpected A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  let M := descriptorRootPinnedMonitor Root baseM expected
  let Strong := profiledOpenLeftFibreSemanticAllowed A twoFibre strategy hwin
    basis leftSource leftRealization c
  let Weak := profiledOpenLeftFibreAllowed A twoFibre leftSource c
  let receiver := profiledOpenLeftFibreReceiver A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  let sender := profiledOpenLeftFibreSender A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  letI : Inhabited (Sigma Root) :=
    ⟨⟨representative,
      ULift.up (leftRealization (twoFibre.representative c)).pivot⟩⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  have hstrong : ∀ past,
      DescriptorRootUnionAllowed Root Strong
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    refine ⟨past.map (fun old ↦
      (((leftRealization descriptor.1).pivot, old.1.2), old.2)), ?_⟩
    funext input
    simp [Strong, profiledOpenLeftFibreSemanticAllowed,
      profiledOpenLeftSemanticClassifiedFamilyReceiver, receiver,
      profiledOpenLeftFibreReceiver, finiteRootFamilyReceiver,
      List.map_map, Function.comp_def]
  apply finiteDescriptorFamilyProvenanceMoveOfStrategies Root M Strong Weak
    (fun descriptor responses hsemantic =>
      profiledOpenLeftFibreSemanticAllowed_implies_allowed A twoFibre strategy
        hwin basis leftSource leftRealization c descriptor responses hsemantic)
    (finiteRootFamilyReceiver receiver []) (hstrong []) receiver sender
  · intro member env
    apply (baseM member.1 member.2).rootPinned_realizable
      (expected member) (receiver member) sender
    · exact hwins c member
    · intro move
      rfl
  · exact hstrong

/-! ## Weak readback and arbitrary-node provenance -/

/-- Forget the right proof-only provenance.  The result is definitionally the
old root-pinned weak move; no controller, transition, or label is changed. -/
noncomputable def ProfiledOpenRightPinnedFibreProvenanceMove.toPinnedMove
    (c : OneClass)
    (move : ProfiledOpenRightPinnedFibreProvenanceMove A oneFibre strategy hwin
      basis rightSource rightRealization c) :
    ProfiledOpenRightPinnedFibreMove A oneFibre strategy hwin basis rightSource
      rightRealization c :=
  move.1

/-- Left weak readback. -/
noncomputable def ProfiledOpenLeftPinnedFibreProvenanceMove.toPinnedMove
    (c : TwoClass)
    (move : ProfiledOpenLeftPinnedFibreProvenanceMove A twoFibre strategy hwin
      basis leftSource leftRealization c) :
    ProfiledOpenLeftPinnedFibreMove A twoFibre strategy hwin basis leftSource
      leftRealization c :=
  move.1

omit [Fintype OneClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every right descriptor projection at every controller word and every
proof-side monitor state is one literal original-strategy family table.  The
existential semantic past is shared by all roots and input rows in that
table. -/
theorem ProfiledOpenRightPinnedFibreProvenanceMove.controllerFor_semantic
    (c : OneClass)
    (move : ProfiledOpenRightPinnedFibreProvenanceMove A oneFibre strategy hwin
      basis rightSource rightRealization c)
    (descriptor : oneFibre.Fibre c)
    (word : List In₁)
    (state : (finiteRootFamilyMonitor
      (descriptorRootPinnedMonitor
        (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
        (profiledOpenRightFibreMonitor A oneFibre rightSource c)
        (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
          hwin basis rightSource rightRealization c)
        descriptor)).State) :
    ∃ semanticPast,
      (fun input =>
        (((move.1.controllerFor
          (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
          (descriptorRootPinnedMonitor
            (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
            (profiledOpenRightFibreMonitor A oneFibre rightSource c)
            (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
              hwin basis rightSource rightRealization c))
          (profiledOpenRightFibreAllowed A oneFibre rightSource c)
          descriptor).labeledTree word).2 state
            ((ULift.up input.1.1, input.1.2), input.2))) =
        profiledOpenRightSemanticClassifiedFamilyReceiver A
          (rightSource descriptor.1) strategy hwin
          (rightRealization descriptor.1).entry basis semanticPast := by
  have hallowed := move.controllerFor_strongAllowed
    (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
    (descriptorRootPinnedMonitor
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
      (profiledOpenRightFibreMonitor A oneFibre rightSource c)
      (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c))
    (profiledOpenRightFibreSemanticAllowed A oneFibre strategy hwin basis
      rightSource rightRealization c)
    (profiledOpenRightFibreAllowed A oneFibre rightSource c) descriptor
  exact hallowed word state

omit [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left arbitrary-node semantic provenance. -/
theorem ProfiledOpenLeftPinnedFibreProvenanceMove.controllerFor_semantic
    (c : TwoClass)
    (move : ProfiledOpenLeftPinnedFibreProvenanceMove A twoFibre strategy hwin
      basis leftSource leftRealization c)
    (descriptor : twoFibre.Fibre c)
    (word : List In₂)
    (state : (finiteRootFamilyMonitor
      (descriptorRootPinnedMonitor
        (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
        (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
        (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
          basis leftSource leftRealization c)
        descriptor)).State) :
    ∃ semanticPast,
      (fun input =>
        (((move.1.controllerFor
          (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
          (descriptorRootPinnedMonitor
            (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
            (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
            (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy
              hwin basis leftSource leftRealization c))
          (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
          descriptor).labeledTree word).2 state
            ((ULift.up input.1.1, input.1.2), input.2))) =
        profiledOpenLeftSemanticClassifiedFamilyReceiver A
          (leftSource descriptor.1) strategy hwin
          (leftRealization descriptor.1).entry basis semanticPast := by
  have hallowed := move.controllerFor_strongAllowed
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
    (descriptorRootPinnedMonitor
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
      (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
      (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization c))
    (profiledOpenLeftFibreSemanticAllowed A twoFibre strategy hwin basis
      leftSource leftRealization c)
    (profiledOpenLeftFibreAllowed A twoFibre leftSource c) descriptor
  exact hallowed word state

omit [Fintype OneClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Root pin and provenance coexist on the right weak readback. -/
theorem ProfiledOpenRightPinnedFibreProvenanceMove.member_root_record
    (c : OneClass)
    (move : ProfiledOpenRightPinnedFibreProvenanceMove A oneFibre strategy hwin
      basis rightSource rightRealization c)
    (descriptor : oneFibre.Fibre c)
    (root : ProfiledOpenRightFibreRoot A oneFibre rightSource c descriptor)
    (input : In₂ × In₁) :
    narrowedRecord
        ((profiledOpenRightFibreMonitor A oneFibre rightSource c descriptor
          root).rootPinned
          (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
            hwin basis rightSource rightRealization c ⟨descriptor, root⟩))
        (((move.toPinnedMove A oneFibre strategy hwin basis rightSource
          rightRealization c).memberController
            (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
            (profiledOpenRightFibreMonitor A oneFibre rightSource c)
            (profiledOpenRightFibreAllowed A oneFibre rightSource c)
            (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
              hwin basis rightSource rightRealization c)
            descriptor root).labeledTree [])
        ((profiledOpenRightFibreMonitor A oneFibre rightSource c descriptor
          root).rootPinned
          (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy
            hwin basis rightSource rightRealization c ⟨descriptor, root⟩)).initial
          input =
      profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c ⟨descriptor, root⟩ input := by
  exact (move.toPinnedMove A oneFibre strategy hwin basis rightSource
    rightRealization c).member_root_record
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
      (profiledOpenRightFibreMonitor A oneFibre rightSource c)
      (profiledOpenRightFibreAllowed A oneFibre rightSource c)
      (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c) descriptor root input

omit [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left root-pin/provenance coexistence. -/
theorem ProfiledOpenLeftPinnedFibreProvenanceMove.member_root_record
    (c : TwoClass)
    (move : ProfiledOpenLeftPinnedFibreProvenanceMove A twoFibre strategy hwin
      basis leftSource leftRealization c)
    (descriptor : twoFibre.Fibre c)
    (root : ProfiledOpenLeftFibreRoot A twoFibre leftSource c descriptor)
    (input : In₁ × In₂) :
    narrowedRecord
        ((profiledOpenLeftFibreMonitor A twoFibre leftSource c descriptor
          root).rootPinned
          (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
            basis leftSource leftRealization c ⟨descriptor, root⟩))
        (((move.toPinnedMove A twoFibre strategy hwin basis leftSource
          leftRealization c).memberController
            (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
            (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
            (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
            (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy
              hwin basis leftSource leftRealization c)
            descriptor root).labeledTree [])
        ((profiledOpenLeftFibreMonitor A twoFibre leftSource c descriptor
          root).rootPinned
          (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
            basis leftSource leftRealization c ⟨descriptor, root⟩)).initial
          input =
      profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin basis
        leftSource leftRealization c ⟨descriptor, root⟩ input := by
  exact (move.toPinnedMove A twoFibre strategy hwin basis leftSource
    leftRealization c).member_root_record
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
      (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
      (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
      (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization c) descriptor root input

/-! ## Source-indexed direct-fibre endpoint -/

section SourceIndexed

variable {I : Type i} [Fintype I]
variable {Descriptor : Type (max i u v x y s)}
variable [Fintype Descriptor] [DecidableEq Descriptor]
variable (semanticDescriptor :
  ProfiledOpenSourceSemanticPoint A strategy hwin basis (I := I) → Descriptor)

/-- The right direct fibre at one literal semantic history, now with sticky
semantic provenance in addition to the existing weak pinned move. -/
noncomputable abbrev ProfiledOpenRightSourceFibreProvenanceMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenRightPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenSourceFibreClass.{i, u, v, x, y, s})

/-- Left source-fibre provenance endpoint. -/
noncomputable abbrev ProfiledOpenLeftSourceFibreProvenanceMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenLeftPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
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
    Fintype (ProfiledOpenRightSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable instance
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    Fintype (ProfiledOpenLeftSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

/-- Direct-fibre common-sender compatibility supplies the strong extraction;
there is no additional semantic-reflection hypothesis. -/
noncomputable def profiledOpenRightSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenRightSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins A
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

noncomputable def profiledOpenLeftSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenLeftSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins A
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

/-- Forgetting the right provenance produces the already exposed source-fibre
move definitionally, so downstream finite APIs need no conversion theorem. -/
noncomputable def ProfiledOpenRightSourceFibreProvenanceMove.toWeakMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenRightSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenRightSourceFibreMove A strategy hwin basis semanticDescriptor
      source :=
  move.1

noncomputable def ProfiledOpenLeftSourceFibreProvenanceMove.toWeakMove
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I))
    (move : ProfiledOpenLeftSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenLeftSourceFibreMove A strategy hwin basis semanticDescriptor
      source :=
  move.1

/-- Both semantic fibre unions are extracted at one common literal history.
This dependent proof package is used to build the raw accepting run; only its
weak finite projections are exposed to the later rational policy. -/
noncomputable abbrev ProfiledOpenPairedSourceFibreProvenanceBank
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :=
  ProfiledOpenRightSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source ×
    ProfiledOpenLeftSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source

noncomputable def profiledOpenPairedSourceFibreProvenanceBankOfWinning
    (source : ProfiledOpenSourceSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenPairedSourceFibreProvenanceBank A strategy hwin basis
      semanticDescriptor source :=
  (profiledOpenRightSourceFibreProvenanceMoveOfWinning A strategy hwin basis
      semanticDescriptor source,
    profiledOpenLeftSourceFibreProvenanceMoveOfWinning A strategy hwin basis
      semanticDescriptor source)

end SourceIndexed

end

end DetParityAutomaton

end DistributedSynthesis
