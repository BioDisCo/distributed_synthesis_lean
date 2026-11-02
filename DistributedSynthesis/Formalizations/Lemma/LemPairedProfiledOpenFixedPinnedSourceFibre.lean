/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenHiddenDescriptorFamilyAlphabet
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenSourceFibreBank

/-!
# A source-indexed extraction into one fixed finite alphabet

The literal semantic source is used only while constructing a raw
history-dependent move.  Its public family code is the pair of finite images
of the two exact-view fibres.  Every descriptor member is realized inside the
literal source fibre, while the controller itself is typed solely by the
finite hidden descriptor and the public family code.

The finite expected-record tables are stored in the move.  They cannot in
general be replaced by the root labels of the old classified move: that old
table was obtained by an acceptance-preserving state-controlled extraction
which does not preserve the raw root label.  Storing the tables is finite and
avoids choosing one semantic representative for all occurrences of an image.
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

abbrev ProfiledOpenFixedPinnedSemanticPoint :=
  ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis (I := I)

variable
  (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
  (control : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I) →
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)

noncomputable local instance fixedPinnedOldMoveHiddenDescriptorDecidableEq :
    DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
  Classical.decEq _

/-- Full finite hidden descriptor of a live semantic source. -/
noncomputable def profiledOpenFixedPinnedSemanticDescriptor
    (point : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode :=
  ((point.state.code A strategy hwin basis, control point),
    point.state.move A strategy hwin basis)

/-- Public two-fibre family at one exact semantic source. -/
noncomputable def profiledOpenFixedPinnedFamilyCode
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  semanticTwoFibreCode
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I))
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source

/-! ## Literal member witnesses -/

noncomputable def profiledOpenFixedPinnedRightPoint
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis (I := I) :=
  semanticFibreAtWitness
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenFixedPinnedLeftPoint
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis (I := I) :=
  semanticFibreAtWitness
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedRightPoint_descriptor
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control
        (profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
          control source member) =
      member.1 :=
  semanticFibreAtWitness_descriptor
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedLeftPoint_descriptor
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control
        (profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
          control source member) =
      member.1 :=
  semanticFibreAtWitness_descriptor
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      (I := I)) source member

/-! ## The old move identity fixes every dependent source type -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedRightPoint_moveIdentity
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    member.1.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right
        (profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
          control source member).rightLane.source
        (((profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
          control source member).rightLane.realization.coherentTable A).table
            |>.toClassified A
              (profiledOpenFixedPinnedRightPoint A strategy hwin basis
                initialCode control source member).rightLane.source) := by
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source member
  have hdescriptor := profiledOpenFixedPinnedRightPoint_descriptor A strategy
    hwin basis initialCode control source member
  have hmove : member.1.moveIdentity =
      point.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  have hright := point.right_eq
  change member.1.moveIdentity.1 =
    ProfiledOpenClassifiedMove.right point.rightLane.source
      (((point.rightLane.realization.coherentTable A).table
        |>.toClassified A point.rightLane.source))
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move,
    ProfiledOpenIndexedRightSemanticShadow.move, hright]

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedLeftPoint_moveIdentity
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)) :
    member.1.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left
        (profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
          control source member).leftLane.source
        (((profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
          control source member).leftLane.realization.coherentTable A).table
            |>.toClassified A
              (profiledOpenFixedPinnedLeftPoint A strategy hwin basis
                initialCode control source member).leftLane.source) := by
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source member
  have hdescriptor := profiledOpenFixedPinnedLeftPoint_descriptor A strategy
    hwin basis initialCode control source member
  have hmove : member.1.moveIdentity =
      point.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  have hleft := point.left_eq
  change member.1.moveIdentity.2 =
    ProfiledOpenClassifiedMove.left point.leftLane.source
      (((point.leftLane.realization.coherentTable A).table
        |>.toClassified A point.leftLane.source))
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move,
    ProfiledOpenIndexedLeftSemanticShadow.move, hleft]

/-! ## Canonical root readback and raw strategies -/

noncomputable def profiledOpenFixedPinnedRightRoot
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (root : ProfiledOpenHiddenDescriptorRightRoot A member.1) :
    { root // root ∈
      (profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
        control source member).rightLane.source.1 } :=
  profiledOpenHiddenDescriptorRightRootToEq A member.1
    (profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
      control source member).rightLane.source
    (((profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
      control source member).rightLane.realization.coherentTable A).table
        |>.toClassified A
          (profiledOpenFixedPinnedRightPoint A strategy hwin basis initialCode
            control source member).rightLane.source)
    (profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin basis
      initialCode control source member) root

noncomputable def profiledOpenFixedPinnedLeftRoot
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source))
    (root : ProfiledOpenHiddenDescriptorLeftRoot A member.1) :
    { root // root ∈
      (profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
        control source member).leftLane.source.1 } :=
  profiledOpenHiddenDescriptorLeftRootToEq A member.1
    (profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
      control source member).leftLane.source
    (((profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
      control source member).leftLane.realization.coherentTable A).table
        |>.toClassified A
          (profiledOpenFixedPinnedLeftPoint A strategy hwin basis initialCode
            control source member).leftLane.source)
    (profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin basis
      initialCode control source member) root

/-- One blind sender for the whole process-one exact fibre. -/
noncomputable def profiledOpenFixedPinnedRightSender
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) : SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy
    (source.rightSenderEntry A strategy hwin basis).lambdaOfStrategy

/-- Process-two blind sender. -/
noncomputable def profiledOpenFixedPinnedLeftSender
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) : SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy
    (source.leftSenderEntry A strategy hwin basis).lambdaOfStrategy

/-- Canonically typed right receiver selected by a descriptor/root member. -/
noncomputable def profiledOpenFixedPinnedRightReceiver
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
          control source) =>
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledOpenRightClassifiedOutput A) :=
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source member.1
  profiledOpenRightSemanticClassifiedReceiver A point.rightLane.source strategy
    hwin point.rightLane.realization.entry basis
    (profiledOpenFixedPinnedRightRoot A strategy hwin basis initialCode control
      source member.1 member.2)

/-- Left receiver. -/
noncomputable def profiledOpenFixedPinnedLeftReceiver
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
          control source) =>
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledOpenLeftClassifiedOutput A) :=
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source member.1
  profiledOpenLeftSemanticClassifiedReceiver A point.leftLane.source strategy
    hwin point.leftLane.realization.entry basis
    (profiledOpenFixedPinnedLeftRoot A strategy hwin basis initialCode control
      source member.1 member.2)

/-! ## Finite expected tables stored in the move -/

noncomputable def profiledOpenFixedPinnedRightExpected
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorRightExpected A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  fun member input =>
    (input,
      profiledOpenFixedPinnedRightReceiver A strategy hwin basis initialCode
        control source member [] input,
      profiledOpenFixedPinnedRightSender A strategy hwin basis source []
        input.2)

noncomputable def profiledOpenFixedPinnedLeftExpected
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorLeftExpected A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  fun member input =>
    (input,
      profiledOpenFixedPinnedLeftReceiver A strategy hwin basis initialCode
        control source member [] input,
      profiledOpenFixedPinnedLeftSender A strategy hwin basis source []
        input.2)

/-! ## Canonical inhabitants for the nonempty live fibres -/

noncomputable def profiledOpenFixedPinnedRightCurrent
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  ⟨profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control source,
    (profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control) source).1⟩

noncomputable def profiledOpenFixedPinnedLeftCurrent
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  ⟨profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode control source,
    (profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control) source).2⟩

/-- One canonical descriptor/root member, used only to supply harmless
defaults to the finite extraction. -/
noncomputable def profiledOpenFixedPinnedRightDefaultMember
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) =>
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1) := by
  let descriptor := profiledOpenFixedPinnedRightCurrent A strategy hwin basis
    initialCode control source
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.rightLane.realization.coherentTable A).table
    |>.toClassified A point.rightLane.source)
  let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
      point.rightLane.source table hmove point.rightLane.realization.pivot⟩

noncomputable def profiledOpenFixedPinnedLeftDefaultMember
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) =>
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1) := by
  let descriptor := profiledOpenFixedPinnedLeftCurrent A strategy hwin basis
    initialCode control source
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.leftLane.realization.coherentTable A).table
    |>.toClassified A point.leftLane.source)
  let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
      point.leftLane.source table hmove point.leftLane.realization.pivot⟩

/-! ## Realizability of every canonical member -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedRight_memberWins
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
          control source) =>
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1))
    (env : Nat → In₂ × In₁) :
    (profiledOpenHiddenDescriptorRightMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenFixedPinnedRightReceiver A strategy hwin basis
          initialCode control source member)
        (profiledOpenFixedPinnedRightSender A strategy hwin basis source)
        env) := by
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source member.1
  let root := profiledOpenFixedPinnedRightRoot A strategy hwin basis
    initialCode control source member.1 member.2
  have hrel : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      source point :=
    semanticFibreAtWitness_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)) source member.1
  have hsourceView :=
    profiledOpenIndexedProcessOneLocalFibreRel_senderView_eq A strategy hwin
      basis hrel
  have hrootView :
      currentView Proc.one
          (point.rightLane.realization.entry root).leftHistory =
        currentView Proc.one
          (source.rightSenderEntry A strategy hwin basis).leftHistory := by
    exact point.rightLane.realization.view_eq root |>.trans hsourceView.symm
  have hsender :
      pairedRightSenderStrategy
          (point.rightLane.realization.entry root).lambdaOfStrategy =
        profiledOpenFixedPinnedRightSender A strategy hwin basis source := by
    exact blockSenderOne_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin (point.rightLane.realization.entry root)
    (point.rightLane.realization.minimum root) basis env
  have hroot := point.rightLane.realization.root_eq root
  have hrootmember :
      (profiledOpenRightRootMonitor A
        (profiledOpenRightRootOfWinning A strategy hwin
          (point.rightLane.realization.entry root)
          (point.rightLane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A
            (point.rightLane.realization.entry root).code
            (point.rightLane.realization.entry root).lambdaOfStrategy)
          (pairedRightSenderStrategy
            (point.rightLane.realization.entry root).lambdaOfStrategy)
          env) := by
    simpa [profiledOpenRightRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenRightClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenFixedPinnedRightReceiver A strategy hwin basis
            initialCode control source member)
          (profiledOpenFixedPinnedRightSender A strategy hwin basis source)
          env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenRightRootMonitor A root.1)
      (fun output : ProfiledOpenRightClassifiedOutput A => output.1) _).mpr
    simpa [profiledOpenFixedPinnedRightReceiver,
      profiledOpenRightSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorRightMonitor_eq_ofEq A member.1.1
    point.rightLane.source
    (((point.rightLane.realization.coherentTable A).table
      |>.toClassified A point.rightLane.source))
    (profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin basis
      initialCode control source member.1) member.2]
  simpa [root, profiledOpenFixedPinnedRightRoot, point] using hclassified

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenFixedPinnedLeft_memberWins
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
          control source) =>
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1))
    (env : Nat → In₁ × In₂) :
    (profiledOpenHiddenDescriptorLeftMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenFixedPinnedLeftReceiver A strategy hwin basis initialCode
          control source member)
        (profiledOpenFixedPinnedLeftSender A strategy hwin basis source)
        env) := by
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source member.1
  let root := profiledOpenFixedPinnedLeftRoot A strategy hwin basis
    initialCode control source member.1 member.2
  have hrel : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      source point :=
    semanticFibreAtWitness_rel
      (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
        initialCode control)
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)) source member.1
  have hsourceView :=
    profiledOpenIndexedProcessTwoLocalFibreRel_senderView_eq A strategy hwin
      basis hrel
  have hrootView :
      currentView Proc.two
          (point.leftLane.realization.entry root).rightHistory =
        currentView Proc.two
          (source.leftSenderEntry A strategy hwin basis).rightHistory := by
    exact point.leftLane.realization.view_eq root |>.trans hsourceView.symm
  have hsender :
      pairedLeftSenderStrategy
          (point.leftLane.realization.entry root).lambdaOfStrategy =
        profiledOpenFixedPinnedLeftSender A strategy hwin basis source := by
    exact blockSenderTwo_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin (point.leftLane.realization.entry root)
    (point.leftLane.realization.minimum root) basis env
  have hroot := point.leftLane.realization.root_eq root
  have hrootmember :
      (profiledOpenLeftRootMonitor A
        (profiledOpenLeftRootOfWinning A strategy hwin
          (point.leftLane.realization.entry root)
          (point.leftLane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A
            (point.leftLane.realization.entry root).code
            (point.leftLane.realization.entry root).lambdaOfStrategy)
          (pairedLeftSenderStrategy
            (point.leftLane.realization.entry root).lambdaOfStrategy)
          env) := by
    simpa [profiledOpenLeftRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenLeftClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenFixedPinnedLeftReceiver A strategy hwin basis
            initialCode control source member)
          (profiledOpenFixedPinnedLeftSender A strategy hwin basis source)
          env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenLeftRootMonitor A root.1)
      (fun output : ProfiledOpenLeftClassifiedOutput A => output.1) _).mpr
    simpa [profiledOpenFixedPinnedLeftReceiver,
      profiledOpenLeftSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorLeftMonitor_eq_ofEq A member.1.1
    point.leftLane.source
    (((point.leftLane.realization.coherentTable A).table
      |>.toClassified A point.leftLane.source))
    (profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin basis
      initialCode control source member.1) member.2]
  simpa [root, profiledOpenFixedPinnedLeftRoot, point] using hclassified

/-! ## Every union table obeys the source law -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The direct right receivers satisfy every descriptor law simultaneously.
Past descriptor/root tags disappear at the blind physical interface; the
current tag is transported back to its literal semantic source. -/
theorem profiledOpenFixedPinnedRight_tablesAllowed
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (past : List
      (((Sigma (fun descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) =>
          ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)) × In₂) ×
        In₁)) :
    DescriptorRootUnionAllowed
      (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) =>
        ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
      (fun descriptor responses =>
        ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
      (finiteRootFamilyReceiver
        (profiledOpenFixedPinnedRightReceiver A strategy hwin basis initialCode
          control source) past) := by
  intro descriptor
  let point := profiledOpenFixedPinnedRightPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.rightLane.realization.coherentTable A).table
    |>.toClassified A point.rightLane.source)
  let hmove := profiledOpenFixedPinnedRightPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorRightWeakAllowed_ofEq A descriptor.1
    point.rightLane.source table hmove
  have hsemantic :=
    profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
      point.rightLane.source strategy hwin point.rightLane.realization.entry
      point.rightLane.realization.minimum basis
      (past.map fun old =>
        ((point.rightLane.realization.pivot, old.1.2), old.2))
  unfold profiledOpenRightSemanticClassifiedFamilyReceiver
    finiteRootFamilyReceiver at hsemantic
  simp only [List.map_map] at hsemantic
  simpa [profiledOpenFixedPinnedRightReceiver,
    profiledOpenFixedPinnedRightRoot, finiteRootFamilyReceiver,
    List.map_map, Function.comp_def, point, table, hmove,
    profiledOpenHiddenDescriptorRightRootToEq_rootOfEq] using hsemantic

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of `profiledOpenFixedPinnedRight_tablesAllowed`. -/
theorem profiledOpenFixedPinnedLeft_tablesAllowed
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I))
    (past : List
      (((Sigma (fun descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) =>
          ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)) × In₁) ×
        In₂)) :
    DescriptorRootUnionAllowed
      (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
            control source) =>
        ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
      (fun descriptor responses =>
        ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
      (finiteRootFamilyReceiver
        (profiledOpenFixedPinnedLeftReceiver A strategy hwin basis initialCode
          control source) past) := by
  intro descriptor
  let point := profiledOpenFixedPinnedLeftPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.leftLane.realization.coherentTable A).table
    |>.toClassified A point.leftLane.source)
  let hmove := profiledOpenFixedPinnedLeftPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq A descriptor.1
    point.leftLane.source table hmove
  have hsemantic :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
      point.leftLane.source strategy hwin point.leftLane.realization.entry
      point.leftLane.realization.minimum basis
      (past.map fun old =>
        ((point.leftLane.realization.pivot, old.1.2), old.2))
  unfold profiledOpenLeftSemanticClassifiedFamilyReceiver
    finiteRootFamilyReceiver at hsemantic
  simp only [List.map_map] at hsemantic
  simpa [profiledOpenFixedPinnedLeftReceiver,
    profiledOpenFixedPinnedLeftRoot, finiteRootFamilyReceiver,
    List.map_map, Function.comp_def, point, table, hmove,
    profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq] using hsemantic

/-! ## Per-side extraction and the fixed sigma value -/

/-- Direct extraction of the right live fibre into the source-independent
root-pinned family alphabet. -/
noncomputable def profiledOpenFixedPinnedRightMoveOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
        control source) := by
  classical
  let family := profiledOpenFixedPinnedFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family => ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root =>
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses =>
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := profiledOpenFixedPinnedRightExpected A strategy hwin basis
    initialCode control source
  let receiver := profiledOpenFixedPinnedRightReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenFixedPinnedRightSender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenFixedPinnedRightDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let defaultTable := finiteRootFamilyReceiver receiver []
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies Root M Allowed
    expected defaultTable
    (profiledOpenFixedPinnedRight_tablesAllowed A strategy hwin basis
      initialCode control source []) receiver sender
  · intro member env
    exact profiledOpenFixedPinnedRight_memberWins A strategy hwin basis
      initialCode control source member env
  · intro member input
    rfl
  · exact profiledOpenFixedPinnedRight_tablesAllowed A strategy hwin basis
      initialCode control source

/-- Direct extraction of the left live fibre. -/
noncomputable def profiledOpenFixedPinnedLeftMoveOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source)
      (profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
        control source) := by
  classical
  let family := profiledOpenFixedPinnedFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family => ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root =>
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses =>
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := profiledOpenFixedPinnedLeftExpected A strategy hwin basis
    initialCode control source
  let receiver := profiledOpenFixedPinnedLeftReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenFixedPinnedLeftSender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenFixedPinnedLeftDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let defaultTable := finiteRootFamilyReceiver receiver []
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies Root M Allowed
    expected defaultTable
    (profiledOpenFixedPinnedLeft_tablesAllowed A strategy hwin basis
      initialCode control source []) receiver sender
  · intro member env
    exact profiledOpenFixedPinnedLeft_memberWins A strategy hwin basis
      initialCode control source member env
  · intro member input
    rfl
  · exact profiledOpenFixedPinnedLeft_tablesAllowed A strategy hwin basis
      initialCode control source

/-- Both live directions at the public family selected by the exact source. -/
noncomputable def profiledOpenFixedPinnedPairedMoveAtOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
        control source) :=
  ⟨profiledOpenFixedPinnedRightExpected A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedLeftExpected A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedRightMoveOfWinning A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedLeftMoveOfWinning A strategy hwin basis initialCode
      control source⟩

/-- The raw semantic history selects one value of a single fixed finite
alphabet.  No semantic source or table is chosen once per public image. -/
noncomputable def profiledOpenFixedPinnedPairedMoveOfWinning
    (source : ProfiledOpenFixedPinnedSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode :=
  ⟨profiledOpenFixedPinnedFamilyCode A strategy hwin basis initialCode
      control source,
    profiledOpenFixedPinnedPairedMoveAtOfWinning A strategy hwin basis
      initialCode control source⟩

end

end DetParityAutomaton

end DistributedSynthesis
