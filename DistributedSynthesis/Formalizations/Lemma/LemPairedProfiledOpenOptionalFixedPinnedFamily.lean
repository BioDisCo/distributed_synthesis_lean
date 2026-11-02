/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteEmptyDescriptorFamilyPinnedMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFixedPinnedSourceFibre
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalLaneFibres

/-!
# Optional semantic lanes in the fixed pinned family alphabet

The correlated semantic construction has four proof-side shapes: no live
lane, right only, left only, and both.  This file maps all four shapes into
the *same* finite root-pinned move alphabet.  Empty sides use the vacuous
empty-family controller; a live side is extracted over its exact local-view
fibre; and the two-live case reuses the paired source adapter.

The case distinction below is not an observation.  In particular no lane,
orientation, or strict-leader tag is supplied to either sender controller.
The only runtime value is the already fixed finite family move.
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
variable (control :
  ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis (I := I) →
    (profiledOpenIndexedBiBeliefCodeParityDPA A initialCode).State)

noncomputable local instance optionalFixedOldMoveDescriptorDecidableEq :
    DecidableEq
      (ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode) :=
  Classical.decEq _

/-! ## One uniform full descriptor -/

/-- The full finite descriptor of an optional-lane semantic state.  The
parity control is proof-side history state, not a local observation. -/
noncomputable def profiledOpenOptionalFixedSemanticDescriptor
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode :=
  ((state.code A strategy hwin basis, control state),
    state.move A strategy hwin basis)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem profiledOpenOptionalFixedSemanticDescriptor_code
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control state).code = state.code A strategy hwin basis :=
  rfl

@[simp] theorem profiledOpenOptionalFixedSemanticDescriptor_control
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control state).control = control state :=
  rfl

@[simp] theorem profiledOpenOptionalFixedSemanticDescriptor_moveIdentity
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I)) :
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control state).moveIdentity =
        state.move A strategy hwin basis :=
  rfl

end

/-! ## Harmless global classified-output defaults

The controller over an empty descriptor family is never queried at a member,
but its ambient finite table still needs a total label.  Winning raw
semantics supplies one right and one left open root already at the first
`left/both` and `right/both` pair.  These defaults carry no semantic lane tag
and are used only in unreachable empty-family labels. -/

noncomputable def profiledOpenOptionalDefaultProcOneEntry :
    ProcOnePairedEntryRep strategy :=
  procOneFreshPair strategy [] StrategyGeneratedPrefix.empty default default

noncomputable def profiledOpenOptionalDefaultProcTwoEntry :
    ProcTwoPairedEntryRep strategy :=
  procTwoFreshPair strategy [] StrategyGeneratedPrefix.empty default default

noncomputable def profiledOpenOptionalDefaultRightRoot :
    ProfiledOpenRightRoot A :=
  profiledOpenRightRootOfWinning A strategy hwin
    (profiledOpenOptionalDefaultProcOneEntry strategy) A.initial basis

noncomputable def profiledOpenOptionalDefaultLeftRoot :
    ProfiledOpenLeftRoot A :=
  profiledOpenLeftRootOfWinning A strategy hwin
    (profiledOpenOptionalDefaultProcTwoEntry strategy) A.initial basis

noncomputable def profiledOpenOptionalDefaultRightViewClass :
    ProfiledOpenRightViewClass A := by
  classical
  let entry := profiledOpenOptionalDefaultProcOneEntry strategy
  let root := profiledOpenOptionalDefaultRightRoot A strategy hwin basis
  refine ⟨{root}, by simp, ?_⟩
  refine ⟨(fun _ ↦ profiledRightReceiverStrategy A entry.code
      entry.lambdaOfStrategy), ?_⟩
  refine ⟨pairedRightSenderStrategy entry.lambdaOfStrategy, ?_⟩
  intro member env
  have hmember : member.1 = root := Finset.mem_singleton.mp member.2
  change (profiledOpenRightRootMonitor A member.1).WinsPlay
    (pairPlay (profiledRightReceiverStrategy A entry.code
      entry.lambdaOfStrategy)
      (pairedRightSenderStrategy entry.lambdaOfStrategy) env)
  rw [hmember]
  simpa [root, profiledOpenOptionalDefaultRightRoot] using
    (profiledOpenRightBlockMonitor_realizable_of_winning A strategy hwin entry
      A.initial basis env)

noncomputable def profiledOpenOptionalDefaultLeftViewClass :
    ProfiledOpenLeftViewClass A := by
  classical
  let entry := profiledOpenOptionalDefaultProcTwoEntry strategy
  let root := profiledOpenOptionalDefaultLeftRoot A strategy hwin basis
  refine ⟨{root}, by simp, ?_⟩
  refine ⟨(fun _ ↦ profiledLeftReceiverStrategy A entry.code
      entry.lambdaOfStrategy), ?_⟩
  refine ⟨pairedLeftSenderStrategy entry.lambdaOfStrategy, ?_⟩
  intro member env
  have hmember : member.1 = root := Finset.mem_singleton.mp member.2
  change (profiledOpenLeftRootMonitor A member.1).WinsPlay
    (pairPlay (profiledLeftReceiverStrategy A entry.code
      entry.lambdaOfStrategy)
      (pairedLeftSenderStrategy entry.lambdaOfStrategy) env)
  rw [hmember]
  simpa [root, profiledOpenOptionalDefaultLeftRoot] using
    (profiledOpenLeftBlockMonitor_realizable_of_winning A strategy hwin entry
      A.initial basis env)

noncomputable def profiledOpenOptionalDefaultRightClassifiedOutput :
    ProfiledOpenRightClassifiedOutput A :=
  (default, fun _ ↦
    (profiledOpenOptionalDefaultLeftRoot A strategy hwin basis,
      profiledOpenOptionalDefaultLeftViewClass (strategy := strategy)
        (hwin := hwin) (basis := basis) A))

noncomputable def profiledOpenOptionalDefaultLeftClassifiedOutput :
    ProfiledOpenLeftClassifiedOutput A :=
  (default, fun _ ↦
    (profiledOpenOptionalDefaultRightRoot A strategy hwin basis,
      profiledOpenOptionalDefaultRightViewClass (strategy := strategy)
        (hwin := hwin) (basis := basis) A))

/-! ## Right-only canonical family extraction -/

abbrev ProfiledOpenOptionalFixedDescriptor :=
  ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode

noncomputable def profiledOpenOptionalRightOnlyFamilyCode
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  profiledOpenRightOnlyFamilyCode A strategy hwin basis
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control) source

noncomputable def profiledOpenOptionalRightOnlyPoint
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) := by
  let sourceMember : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1, by
      simpa [profiledOpenOptionalRightOnlyFamilyCode,
        profiledOpenRightOnlyFamilyCode] using member.2⟩
  exact profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
    (profiledOpenRightOnlyDescriptor A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control)) source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalRightOnlyPoint_descriptor
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control
        (profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
          control source member).optional.state = member.1 :=
  let sourceMember : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1, by
      simpa [profiledOpenOptionalRightOnlyFamilyCode,
        profiledOpenRightOnlyFamilyCode] using member.2⟩
  profiledOpenRightOnlySourceFibrePoint_descriptor A strategy hwin basis
    (profiledOpenRightOnlyDescriptor A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control)) source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalRightOnlyPoint_moveIdentity
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    member.1.moveIdentity.1 =
      ProfiledOpenClassifiedMove.right
        (profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
          control source member).lane.source
        ((((profiledOpenOptionalRightOnlyPoint A strategy hwin basis
          initialCode control source member).lane.realization.coherentTable A
          ).table).toClassified A
            (profiledOpenOptionalRightOnlyPoint A strategy hwin basis
              initialCode control source member).lane.source) := by
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode control source member
  have hdescriptor := profiledOpenOptionalRightOnlyPoint_descriptor A strategy
    hwin basis initialCode control source member
  have hmove : member.1.moveIdentity =
      point.optional.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  change member.1.moveIdentity.1 =
    ProfiledOpenClassifiedMove.right point.lane.source
      (((point.lane.realization.coherentTable A).table).toClassified A
        point.lane.source)
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.right_eq,
    ProfiledOpenIndexedRightSemanticShadow.move]

noncomputable def profiledOpenOptionalRightOnlyRoot
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source))
    (root : ProfiledOpenHiddenDescriptorRightRoot A member.1) :
    { root // root ∈
      (profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
        control source member).lane.source.1 } :=
  profiledOpenHiddenDescriptorRightRootToEq A member.1
    (profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
      control source member).lane.source
    ((((profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
      control source member).lane.realization.coherentTable A).table
      ).toClassified A
        (profiledOpenOptionalRightOnlyPoint A strategy hwin basis initialCode
          control source member).lane.source)
    (profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin basis
      initialCode control source member) root

noncomputable def profiledOpenOptionalRightOnlySender
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : SenderBlockStrategy In₁ Out₁ :=
  pairedRightSenderStrategy
    (source.lane.realization.entry source.lane.realization.pivot
      ).lambdaOfStrategy

noncomputable def profiledOpenOptionalRightOnlyReceiver
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
          initialCode control source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)) :
    ReceiverBlockStrategy In₂ In₁
      (ProfiledOpenRightClassifiedOutput A) :=
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode control source member.1
  profiledOpenRightSemanticClassifiedReceiver A point.lane.source strategy hwin
    point.lane.realization.entry basis
    (profiledOpenOptionalRightOnlyRoot A strategy hwin basis initialCode
      control source member.1 member.2)

noncomputable def profiledOpenOptionalRightOnlyExpected
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorRightExpected A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  fun member input ↦
    (input,
      profiledOpenOptionalRightOnlyReceiver A strategy hwin basis initialCode
        control source member [] input,
      profiledOpenOptionalRightOnlySender A strategy hwin basis source []
        input.2)

noncomputable def profiledOpenOptionalRightOnlyCurrent
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  ⟨profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control source.optional.state,
    (profiledOpenRightOnlyDescriptor_mem_family A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) source).1⟩

noncomputable def profiledOpenOptionalRightOnlyDefaultMember
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1) := by
  let descriptor := profiledOpenOptionalRightOnlyCurrent A strategy hwin basis
    initialCode control source
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorRightRootOfEq A descriptor.1
      point.lane.source table hmove point.lane.realization.pivot⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalRightOnly_memberWins
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorRightCarrier A
        (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
          initialCode control source) ↦
      ProfiledOpenHiddenDescriptorRightRoot A descriptor.1))
    (env : Nat → In₂ × In₁) :
    (profiledOpenHiddenDescriptorRightMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenOptionalRightOnlyReceiver A strategy hwin basis
          initialCode control source member)
        (profiledOpenOptionalRightOnlySender A strategy hwin basis source)
        env) := by
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode control source member.1
  let root := profiledOpenOptionalRightOnlyRoot A strategy hwin basis
    initialCode control source member.1 member.2
  let sourceMember : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1.1, by
      simpa [profiledOpenOptionalRightOnlyFamilyCode,
        profiledOpenRightOnlyFamilyCode] using member.1.2⟩
  have hsourceView :=
    profiledOpenRightOnlySourceFibrePoint_senderView_eq_source A strategy hwin
      basis
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source sourceMember
  have hrootView :
      currentView Proc.one
          (point.lane.realization.entry root).leftHistory =
        currentView Proc.one
          (source.lane.realization.entry source.lane.realization.pivot
          ).leftHistory :=
    (point.lane.realization.view_eq root).trans hsourceView
  have hsender :
      pairedRightSenderStrategy
          (point.lane.realization.entry root).lambdaOfStrategy =
        profiledOpenOptionalRightOnlySender A strategy hwin basis source :=
    blockSenderOne_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin (point.lane.realization.entry root)
    (point.lane.realization.minimum root) basis env
  have hroot := point.lane.realization.root_eq root
  have hrootmember :
      (profiledOpenRightRootMonitor A
        (profiledOpenRightRootOfWinning A strategy hwin
          (point.lane.realization.entry root)
          (point.lane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A
            (point.lane.realization.entry root).code
            (point.lane.realization.entry root).lambdaOfStrategy)
          (pairedRightSenderStrategy
            (point.lane.realization.entry root).lambdaOfStrategy) env) := by
    simpa [profiledOpenRightRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenRightClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenOptionalRightOnlyReceiver A strategy hwin basis
            initialCode control source member)
          (profiledOpenOptionalRightOnlySender A strategy hwin basis source)
          env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenRightRootMonitor A root.1)
      (fun output : ProfiledOpenRightClassifiedOutput A ↦ output.1) _).mpr
    simpa [profiledOpenOptionalRightOnlyReceiver,
      profiledOpenRightSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorRightMonitor_eq_ofEq A member.1.1
    point.lane.source
    (((point.lane.realization.coherentTable A).table
      |>.toClassified A point.lane.source))
    (profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin basis
      initialCode control source member.1) member.2]
  simpa [root, profiledOpenOptionalRightOnlyRoot, point] using hclassified

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalRightOnly_tablesAllowed
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (past : List
      (((Sigma (fun descriptor :
        ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
            initialCode control source) ↦
          ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)) × In₂) ×
        In₁)) :
    DescriptorRootUnionAllowed
      (fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
          (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
            initialCode control source) ↦
        ProfiledOpenHiddenDescriptorRightRoot A descriptor.1)
      (fun descriptor responses ↦
        ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses)
      (finiteRootFamilyReceiver
        (profiledOpenOptionalRightOnlyReceiver A strategy hwin basis
          initialCode control source) past) := by
  intro descriptor
  let point := profiledOpenOptionalRightOnlyPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalRightOnlyPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorRightWeakAllowed_ofEq A descriptor.1
    point.lane.source table hmove
  have hsemantic :=
    profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
      point.lane.source strategy hwin point.lane.realization.entry
      point.lane.realization.minimum basis
      (past.map fun old ↦
        ((point.lane.realization.pivot, old.1.2), old.2))
  unfold profiledOpenRightSemanticClassifiedFamilyReceiver
    finiteRootFamilyReceiver at hsemantic
  simp only [List.map_map] at hsemantic
  simpa [profiledOpenOptionalRightOnlyReceiver,
    profiledOpenOptionalRightOnlyRoot, finiteRootFamilyReceiver,
    List.map_map, Function.comp_def, point, table, hmove,
    profiledOpenHiddenDescriptorRightRootToEq_rootOfEq] using hsemantic

noncomputable def profiledOpenOptionalRightOnlyPinnedMoveOfWinning
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source)
      (profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
        control source) := by
  classical
  let family := profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalRightOnlyExpected A strategy hwin basis
    initialCode control source
  let receiver := profiledOpenOptionalRightOnlyReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenOptionalRightOnlySender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenOptionalRightOnlyDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  let defaultTable := finiteRootFamilyReceiver receiver []
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies Root M Allowed
    expected defaultTable
    (profiledOpenOptionalRightOnly_tablesAllowed A strategy hwin basis
      initialCode control source []) receiver sender
  · intro member env
    exact profiledOpenOptionalRightOnly_memberWins A strategy hwin basis
      initialCode control source member env
  · intro member input
    rfl
  · exact profiledOpenOptionalRightOnly_tablesAllowed A strategy hwin basis
      initialCode control source

/-! ## Left-only canonical family extraction -/

noncomputable def profiledOpenOptionalLeftOnlyFamilyCode
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  profiledOpenLeftOnlyFamilyCode A strategy hwin basis
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control) source

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenOptionalRightOnlyFamilyCode_left
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis initialCode
      control source).2 = ∅ :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledOpenOptionalLeftOnlyFamilyCode_right
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis initialCode
      control source).1 = ∅ :=
  rfl

noncomputable def profiledOpenOptionalLeftOnlyPoint
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) := by
  let sourceMember : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1, by
      simpa [profiledOpenOptionalLeftOnlyFamilyCode,
        profiledOpenLeftOnlyFamilyCode] using member.2⟩
  exact profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
    (profiledOpenLeftOnlyDescriptor A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control)) source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalLeftOnlyPoint_descriptor
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control
        (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
          control source member).optional.state = member.1 :=
  let sourceMember : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1, by
      simpa [profiledOpenOptionalLeftOnlyFamilyCode,
        profiledOpenLeftOnlyFamilyCode] using member.2⟩
  profiledOpenLeftOnlySourceFibrePoint_descriptor A strategy hwin basis
    (profiledOpenLeftOnlyDescriptor A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control)) source sourceMember

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalLeftOnlyPoint_moveIdentity
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source)) :
    member.1.moveIdentity.2 =
      ProfiledOpenClassifiedMove.left
        (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
          control source member).lane.source
        ((((profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
          initialCode control source member).lane.realization.coherentTable A
          ).table).toClassified A
            (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
              initialCode control source member).lane.source) := by
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode control source member
  have hdescriptor := profiledOpenOptionalLeftOnlyPoint_descriptor A strategy
    hwin basis initialCode control source member
  have hmove : member.1.moveIdentity =
      point.optional.state.move A strategy hwin basis := by
    rw [← hdescriptor]
    rfl
  change member.1.moveIdentity.2 =
    ProfiledOpenClassifiedMove.left point.lane.source
      (((point.lane.realization.coherentTable A).table).toClassified A
        point.lane.source)
  rw [hmove]
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.left_eq,
    ProfiledOpenIndexedLeftSemanticShadow.move]

noncomputable def profiledOpenOptionalLeftOnlyRoot
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source))
    (root : ProfiledOpenHiddenDescriptorLeftRoot A member.1) :
    { root // root ∈
      (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
        control source member).lane.source.1 } :=
  profiledOpenHiddenDescriptorLeftRootToEq A member.1
    (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
      control source member).lane.source
    ((((profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
      control source member).lane.realization.coherentTable A).table
      ).toClassified A
        (profiledOpenOptionalLeftOnlyPoint A strategy hwin basis initialCode
          control source member).lane.source)
    (profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin basis
      initialCode control source member) root

noncomputable def profiledOpenOptionalLeftOnlySender
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : SenderBlockStrategy In₂ Out₂ :=
  pairedLeftSenderStrategy
    (source.lane.realization.entry source.lane.realization.pivot
      ).lambdaOfStrategy

noncomputable def profiledOpenOptionalLeftOnlyReceiver
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
          initialCode control source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)) :
    ReceiverBlockStrategy In₁ In₂
      (ProfiledOpenLeftClassifiedOutput A) :=
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode control source member.1
  profiledOpenLeftSemanticClassifiedReceiver A point.lane.source strategy hwin
    point.lane.realization.entry basis
    (profiledOpenOptionalLeftOnlyRoot A strategy hwin basis initialCode
      control source member.1 member.2)

noncomputable def profiledOpenOptionalLeftOnlyExpected
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorLeftExpected A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  fun member input ↦
    (input,
      profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis initialCode
        control source member [] input,
      profiledOpenOptionalLeftOnlySender A strategy hwin basis source []
        input.2)

noncomputable def profiledOpenOptionalLeftOnlyCurrent
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  ⟨profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control source.optional.state,
    (profiledOpenLeftOnlyDescriptor_mem_family A strategy hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) source).2⟩

noncomputable def profiledOpenOptionalLeftOnlyDefaultMember
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Sigma (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1) := by
  let descriptor := profiledOpenOptionalLeftOnlyCurrent A strategy hwin basis
    initialCode control source
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  exact ⟨descriptor,
    profiledOpenHiddenDescriptorLeftRootOfEq A descriptor.1
      point.lane.source table hmove point.lane.realization.pivot⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalLeftOnly_memberWins
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : Sigma (fun descriptor :
      ProfiledOpenHiddenDescriptorLeftCarrier A
        (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
          initialCode control source) ↦
      ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1))
    (env : Nat → In₁ × In₂) :
    (profiledOpenHiddenDescriptorLeftMonitor A member.1.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis
          initialCode control source member)
        (profiledOpenOptionalLeftOnlySender A strategy hwin basis source)
        env) := by
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode control source member.1
  let root := profiledOpenOptionalLeftOnlyRoot A strategy hwin basis
    initialCode control source member.1 member.2
  let sourceMember : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin
      basis
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source :=
    ⟨member.1.1, by
      simpa [profiledOpenOptionalLeftOnlyFamilyCode,
        profiledOpenLeftOnlyFamilyCode] using member.1.2⟩
  have hsourceView :=
    profiledOpenLeftOnlySourceFibrePoint_senderView_eq_source A strategy hwin
      basis
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)) source sourceMember
  have hrootView :
      currentView Proc.two
          (point.lane.realization.entry root).rightHistory =
        currentView Proc.two
          (source.lane.realization.entry source.lane.realization.pivot
          ).rightHistory :=
    (point.lane.realization.view_eq root).trans hsourceView
  have hsender :
      pairedLeftSenderStrategy
          (point.lane.realization.entry root).lambdaOfStrategy =
        profiledOpenOptionalLeftOnlySender A strategy hwin basis source :=
    blockSenderTwo_eq_of_view_eq strategy hrootView
  have hmember := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin (point.lane.realization.entry root)
    (point.lane.realization.minimum root) basis env
  have hroot := point.lane.realization.root_eq root
  have hrootmember :
      (profiledOpenLeftRootMonitor A
        (profiledOpenLeftRootOfWinning A strategy hwin
          (point.lane.realization.entry root)
          (point.lane.realization.minimum root) basis)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A
            (point.lane.realization.entry root).code
            (point.lane.realization.entry root).lambdaOfStrategy)
          (pairedLeftSenderStrategy
            (point.lane.realization.entry root).lambdaOfStrategy) env) := by
    simpa [profiledOpenLeftRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  have hclassified :
      (profiledOpenLeftClassifiedRootMonitor A root.1).WinsPlay
        (pairPlay
          (profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis
            initialCode control source member)
          (profiledOpenOptionalLeftOnlySender A strategy hwin basis source)
          env) := by
    apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
      (profiledOpenLeftRootMonitor A root.1)
      (fun output : ProfiledOpenLeftClassifiedOutput A ↦ output.1) _).mpr
    simpa [profiledOpenOptionalLeftOnlyReceiver,
      profiledOpenLeftSemanticClassifiedReceiver, pairPlay, treePlay,
      treeOfPair, blockLabelApply] using hrootmember
  rw [profiledOpenHiddenDescriptorLeftMonitor_eq_ofEq A member.1.1
    point.lane.source
    (((point.lane.realization.coherentTable A).table
      |>.toClassified A point.lane.source))
    (profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin basis
      initialCode control source member.1) member.2]
  simpa [root, profiledOpenOptionalLeftOnlyRoot, point] using hclassified

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenOptionalLeftOnly_tablesAllowed
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (past : List
      (((Sigma (fun descriptor :
        ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
            initialCode control source) ↦
          ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)) × In₁) ×
        In₂)) :
    DescriptorRootUnionAllowed
      (fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
          (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
            initialCode control source) ↦
        ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1)
      (fun descriptor responses ↦
        ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses)
      (finiteRootFamilyReceiver
        (profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis
          initialCode control source) past) := by
  intro descriptor
  let point := profiledOpenOptionalLeftOnlyPoint A strategy hwin basis
    initialCode control source descriptor
  let table := ((point.lane.realization.coherentTable A).table
    |>.toClassified A point.lane.source)
  let hmove := profiledOpenOptionalLeftOnlyPoint_moveIdentity A strategy hwin
    basis initialCode control source descriptor
  apply profiledOpenHiddenDescriptorLeftWeakAllowed_ofEq A descriptor.1
    point.lane.source table hmove
  have hsemantic :=
    profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
      point.lane.source strategy hwin point.lane.realization.entry
      point.lane.realization.minimum basis
      (past.map fun old ↦
        ((point.lane.realization.pivot, old.1.2), old.2))
  unfold profiledOpenLeftSemanticClassifiedFamilyReceiver
    finiteRootFamilyReceiver at hsemantic
  simp only [List.map_map] at hsemantic
  simpa [profiledOpenOptionalLeftOnlyReceiver,
    profiledOpenOptionalLeftOnlyRoot, finiteRootFamilyReceiver,
    List.map_map, Function.comp_def, point, table, hmove,
    profiledOpenHiddenDescriptorLeftRootToEq_rootOfEq] using hsemantic

noncomputable def profiledOpenOptionalLeftOnlyPinnedMoveOfWinning
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source)
      (profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
        control source) := by
  classical
  let family := profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalLeftOnlyExpected A strategy hwin basis
    initialCode control source
  let receiver := profiledOpenOptionalLeftOnlyReceiver A strategy hwin basis
    initialCode control source
  let sender := profiledOpenOptionalLeftOnlySender A strategy hwin basis source
  letI : Inhabited (Sigma Root) :=
    ⟨profiledOpenOptionalLeftOnlyDefaultMember A strategy hwin basis
      initialCode control source⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  let defaultTable := finiteRootFamilyReceiver receiver []
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies Root M Allowed
    expected defaultTable
    (profiledOpenOptionalLeftOnly_tablesAllowed A strategy hwin basis
      initialCode control source []) receiver sender
  · intro member env
    exact profiledOpenOptionalLeftOnly_memberWins A strategy hwin basis
      initialCode control source member env
  · intro member input
    rfl
  · exact profiledOpenOptionalLeftOnly_tablesAllowed A strategy hwin basis
      initialCode control source

/-! ## Empty inactive sides -/

noncomputable def profiledOpenOptionalRightOnlyLeftExpected
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorLeftExpected A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  fun member _ ↦ False.elim (by
    rcases member.1 with ⟨descriptor, hmem⟩
    simpa using hmem)

noncomputable def profiledOpenOptionalLeftOnlyRightExpected
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorRightExpected A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  fun member _ ↦ False.elim (by
    rcases member.1 with ⟨descriptor, hmem⟩
    simpa using hmem)

noncomputable def profiledOpenOptionalRightOnlyEmptyLeftMove
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source)
      (profiledOpenOptionalRightOnlyLeftExpected A strategy hwin basis
        initialCode control source) := by
  classical
  let family := profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalRightOnlyLeftExpected A strategy hwin
    basis initialCode control source
  letI : IsEmpty (ProfiledOpenHiddenDescriptorLeftCarrier A family) :=
    ⟨fun descriptor ↦ by
      rcases descriptor with ⟨descriptor, hmem⟩
      simpa [family] using hmem⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  exact finiteEmptyDescriptorFamilyPinnedAllowedMove Root M Allowed expected

noncomputable def profiledOpenOptionalLeftOnlyEmptyRightMove
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source)
      (profiledOpenOptionalLeftOnlyRightExpected A strategy hwin basis
        initialCode control source) := by
  classical
  let family := profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
    initialCode control source
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalLeftOnlyRightExpected A strategy hwin
    basis initialCode control source
  letI : IsEmpty (ProfiledOpenHiddenDescriptorRightCarrier A family) :=
    ⟨fun descriptor ↦ by
      rcases descriptor with ⟨descriptor, hmem⟩
      simpa [family] using hmem⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  exact finiteEmptyDescriptorFamilyPinnedAllowedMove Root M Allowed expected

noncomputable def profiledOpenOptionalSinkFamilyCode :
    ProfiledOpenIndexedHiddenDescriptorFamilyCode A (I := I) initialCode :=
  (∅, ∅)

noncomputable def profiledOpenOptionalSinkRightExpected :
    ProfiledOpenHiddenDescriptorRightExpected A
      (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode) :=
  fun member _ ↦ False.elim (by
    rcases member.1 with ⟨descriptor, hmem⟩
    simpa [profiledOpenOptionalSinkFamilyCode] using hmem)

noncomputable def profiledOpenOptionalSinkLeftExpected :
    ProfiledOpenHiddenDescriptorLeftExpected A
      (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode) :=
  fun member _ ↦ False.elim (by
    rcases member.1 with ⟨descriptor, hmem⟩
    simpa [profiledOpenOptionalSinkFamilyCode] using hmem)

noncomputable def profiledOpenOptionalSinkEmptyRightMove :
    ProfiledOpenHiddenDescriptorRightPinnedFamilyMove A
      (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode)
      (profiledOpenOptionalSinkRightExpected A (I := I) initialCode) := by
  classical
  let family := profiledOpenOptionalSinkFamilyCode A (I := I) initialCode
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorRightCarrier A
      family ↦ ProfiledOpenHiddenDescriptorRightRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorRightMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₂) × In₁) →
        ProfiledOpenRightClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorRightWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalSinkRightExpected A (I := I) initialCode
  letI : IsEmpty (ProfiledOpenHiddenDescriptorRightCarrier A family) :=
    ⟨fun descriptor ↦ by
      rcases descriptor with ⟨descriptor, hmem⟩
      simpa [family, profiledOpenOptionalSinkFamilyCode] using hmem⟩
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultRightClassifiedOutput A strategy hwin basis⟩
  exact finiteEmptyDescriptorFamilyPinnedAllowedMove Root M Allowed expected

noncomputable def profiledOpenOptionalSinkEmptyLeftMove :
    ProfiledOpenHiddenDescriptorLeftPinnedFamilyMove A
      (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode)
      (profiledOpenOptionalSinkLeftExpected A (I := I) initialCode) := by
  classical
  let family := profiledOpenOptionalSinkFamilyCode A (I := I) initialCode
  let Root := fun descriptor : ProfiledOpenHiddenDescriptorLeftCarrier A
      family ↦ ProfiledOpenHiddenDescriptorLeftRoot A descriptor.1
  let M : ∀ descriptor, Root descriptor →
      BlockRecordMonitor In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
    fun descriptor root ↦
      profiledOpenHiddenDescriptorLeftMonitor A descriptor.1 root
  let Allowed : ∀ descriptor,
      (((Root descriptor × In₁) × In₂) →
        ProfiledOpenLeftClassifiedOutput A) → Prop :=
    fun descriptor responses ↦
      ProfiledOpenHiddenDescriptorLeftWeakAllowed A descriptor.1 responses
  let expected := profiledOpenOptionalSinkLeftExpected A (I := I) initialCode
  letI : IsEmpty (ProfiledOpenHiddenDescriptorLeftCarrier A family) :=
    ⟨fun descriptor ↦ by
      rcases descriptor with ⟨descriptor, hmem⟩
      simpa [family, profiledOpenOptionalSinkFamilyCode] using hmem⟩
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨profiledOpenOptionalDefaultLeftClassifiedOutput A strategy hwin basis⟩
  exact finiteEmptyDescriptorFamilyPinnedAllowedMove Root M Allowed expected

/-! ## The four proof-side cases in one fixed alphabet -/

noncomputable def profiledOpenOptionalRightOnlyPinnedMoveAtOfWinning
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  ⟨profiledOpenOptionalRightOnlyExpected A strategy hwin basis initialCode
      control source,
    profiledOpenOptionalRightOnlyLeftExpected A strategy hwin basis
      initialCode control source,
    profiledOpenOptionalRightOnlyPinnedMoveOfWinning A strategy hwin basis
      initialCode control source,
    profiledOpenOptionalRightOnlyEmptyLeftMove A strategy hwin basis
      initialCode control source⟩

noncomputable def profiledOpenOptionalLeftOnlyPinnedMoveAtOfWinning
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
        initialCode control source) :=
  ⟨profiledOpenOptionalLeftOnlyRightExpected A strategy hwin basis
      initialCode control source,
    profiledOpenOptionalLeftOnlyExpected A strategy hwin basis initialCode
      control source,
    profiledOpenOptionalLeftOnlyEmptyRightMove A strategy hwin basis
      initialCode control source,
    profiledOpenOptionalLeftOnlyPinnedMoveOfWinning A strategy hwin basis
      initialCode control source⟩

noncomputable def profiledOpenOptionalSinkPinnedMoveAt :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMoveAt A
      (profiledOpenOptionalSinkFamilyCode A (I := I) initialCode) :=
  ⟨profiledOpenOptionalSinkRightExpected A (I := I) initialCode,
    profiledOpenOptionalSinkLeftExpected A (I := I) initialCode,
    profiledOpenOptionalSinkEmptyRightMove A strategy hwin basis initialCode,
    profiledOpenOptionalSinkEmptyLeftMove A strategy hwin basis initialCode⟩

/-- Map one already selected optional source-fibre provenance bank into the
single finite pinned alphabet.  The bank is used to retain the exact
proof-side lane case.  The value returned here carries root pins and all weak
classified-table laws.  Its runtime type does *not* claim the later
arbitrary-node one-origin provenance invariant; that invariant belongs in
the finite `Valid`/semantic-lift layer.

The `move` proof fields of the source bank are deliberately not exposed to a
process.  The canonical extraction is performed over the same literal exact
fibre, so no representative semantic source is chosen for a public image. -/
noncomputable def profiledOpenOptionalFixedPinnedFamilyMoveOfBank
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) point) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode :=
  match bank with
  | .sink _ _ =>
      ⟨profiledOpenOptionalSinkFamilyCode A (I := I) initialCode,
        profiledOpenOptionalSinkPinnedMoveAt A strategy hwin basis
          initialCode⟩
  | .rightOnly lane hright hleft _ =>
      let source := point.toRightOnly A strategy hwin basis lane hright hleft
      ⟨profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
          initialCode control source,
        profiledOpenOptionalRightOnlyPinnedMoveAtOfWinning A strategy hwin
          basis initialCode control source⟩
  | .leftOnly lane hright hleft _ =>
      let source := point.toLeftOnly A strategy hwin basis lane hright hleft
      ⟨profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
          initialCode control source,
        profiledOpenOptionalLeftOnlyPinnedMoveAtOfWinning A strategy hwin
          basis initialCode control source⟩
  | .both rightLane leftLane hright hleft _ =>
      let source := point.toLiveFresh A strategy hwin basis rightLane leftLane
        hright hleft
      profiledOpenFixedPinnedPairedMoveOfWinning A strategy hwin basis
        initialCode (fun live ↦ control live.state) source

/-- Winning raw semantics supplies a fixed-alphabet value at every total
optional-lane history.  The four-way split is entirely proof-side. -/
noncomputable def profiledOpenOptionalFixedPinnedFamilyMoveOfWinning
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenHiddenDescriptorPairedPinnedFamilyMove A initialCode :=
  profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
    initialCode control point
    (profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) point)

/-! ## Shape and current-descriptor readback -/

/-- Exact shape of the selected public family and membership of the current
descriptor on every active component.  The alternatives are proof-side only:
the finite move contains no distinguished descriptor and no lane flag. -/
theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_shape
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (bank : ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy
      hwin basis
      (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
        initialCode control) point) :
    let move := profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin
      basis initialCode control point bank
    let descriptor := profiledOpenOptionalFixedSemanticDescriptor A strategy
      hwin basis initialCode control point.state
    move.1 = (∅, ∅) ∨
      (descriptor ∈ move.1.1 ∧ move.1.2 = ∅) ∨
      (move.1.1 = ∅ ∧ descriptor ∈ move.1.2) ∨
      (descriptor ∈ move.1.1 ∧ descriptor ∈ move.1.2) := by
  classical
  cases bank with
  | sink hright hleft =>
      exact Or.inl rfl
  | rightOnly lane hright hleft bankMove =>
      apply Or.inr
      apply Or.inl
      exact profiledOpenRightOnlyDescriptor_mem_family A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)
        (point.toRightOnly A strategy hwin basis lane hright hleft)
  | leftOnly lane hright hleft bankMove =>
      apply Or.inr
      apply Or.inr
      apply Or.inl
      exact profiledOpenLeftOnlyDescriptor_mem_family A strategy hwin basis
        (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control)
        (point.toLeftOnly A strategy hwin basis lane hright hleft)
  | both rightLane leftLane hright hleft bankMove =>
      apply Or.inr
      apply Or.inr
      apply Or.inr
      let source := point.toLiveFresh A strategy hwin basis rightLane leftLane
        hright hleft
      exact profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
        (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
          initialCode (fun live ↦ control live.state)) source

@[simp] theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_sink_family
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = none) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.sink hright hleft)).1 =
        profiledOpenOptionalSinkFamilyCode A (I := I) initialCode :=
  rfl

@[simp] theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_sink_moveAt
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = none) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.sink hright hleft)).2 =
        profiledOpenOptionalSinkPinnedMoveAt A strategy hwin basis
          initialCode :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_rightOnly_family
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some lane)
    (hleft : point.state.left = none)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.rightOnly lane hright hleft bankMove)).1 =
        profiledOpenOptionalRightOnlyFamilyCode A strategy hwin basis
          initialCode control
          (point.toRightOnly A strategy hwin basis lane hright hleft) :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_rightOnly_moveAt
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some lane)
    (hleft : point.state.left = none)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.rightOnly lane hright hleft bankMove)).2 =
        profiledOpenOptionalRightOnlyPinnedMoveAtOfWinning A strategy hwin
          basis initialCode control
          (point.toRightOnly A strategy hwin basis lane hright hleft) :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_leftOnly_family
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = some lane)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.leftOnly lane hright hleft bankMove)).1 =
        profiledOpenOptionalLeftOnlyFamilyCode A strategy hwin basis
          initialCode control
          (point.toLeftOnly A strategy hwin basis lane hright hleft) :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_leftOnly_moveAt
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = some lane)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.leftOnly lane hright hleft bankMove)).2 =
        profiledOpenOptionalLeftOnlyPinnedMoveAtOfWinning A strategy hwin
          basis initialCode control
          (point.toLeftOnly A strategy hwin basis lane hright hleft) :=
  rfl

@[simp] theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_both
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some rightLane)
    (hleft : point.state.left = some leftLane)
    (bankMove : _) :
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
        initialCode control point
        (.both rightLane leftLane hright hleft bankMove) =
      profiledOpenFixedPinnedPairedMoveOfWinning A strategy hwin basis
        initialCode (fun live ↦ control live.state)
        (point.toLiveFresh A strategy hwin basis rightLane leftLane hright
          hleft) :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_rightOnly_rightMove
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some lane)
    (hleft : point.state.left = none)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.rightOnly lane hright hleft bankMove)).2.2.2.1 =
        profiledOpenOptionalRightOnlyPinnedMoveOfWinning A strategy hwin basis
          initialCode control
          (point.toRightOnly A strategy hwin basis lane hright hleft) :=
  rfl

@[simp] theorem
    profiledOpenOptionalFixedPinnedFamilyMoveOfBank_leftOnly_leftMove
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = some lane)
    (bankMove : _) :
    (profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin basis
      initialCode control point
      (.leftOnly lane hright hleft bankMove)).2.2.2.2 =
        profiledOpenOptionalLeftOnlyPinnedMoveOfWinning A strategy hwin basis
          initialCode control
          (point.toLeftOnly A strategy hwin basis lane hright hleft) :=
  rfl

theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_rightOnly_current
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some lane)
    (hleft : point.state.left = none)
    (bankMove : _) :
    let move := profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin
      basis initialCode control point
      (.rightOnly lane hright hleft bankMove)
    profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control point.state ∈ move.1.1 ∧
      move.1.2 = ∅ := by
  exact profiledOpenRightOnlyDescriptor_mem_family A strategy hwin basis
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (point.toRightOnly A strategy hwin basis lane hright hleft)

theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_leftOnly_current
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = some lane)
    (bankMove : _) :
    let move := profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin
      basis initialCode control point
      (.leftOnly lane hright hleft bankMove)
    move.1.1 = ∅ ∧
      profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
          initialCode control point.state ∈ move.1.2 := by
  exact profiledOpenLeftOnlyDescriptor_mem_family A strategy hwin basis
    (profiledOpenOptionalFixedSemanticDescriptor A strategy hwin basis
      initialCode control)
    (point.toLeftOnly A strategy hwin basis lane hright hleft)

theorem profiledOpenOptionalFixedPinnedFamilyMoveOfBank_both_current
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some rightLane)
    (hleft : point.state.left = some leftLane)
    (bankMove : _) :
    let move := profiledOpenOptionalFixedPinnedFamilyMoveOfBank A strategy hwin
      basis initialCode control point
      (.both rightLane leftLane hright hleft bankMove)
    let descriptor := profiledOpenOptionalFixedSemanticDescriptor A strategy
      hwin basis initialCode control point.state
    descriptor ∈ move.1.1 ∧ descriptor ∈ move.1.2 := by
  let source := point.toLiveFresh A strategy hwin basis rightLane leftLane
    hright hleft
  exact profiledOpenSourceFibreCurrent_mem_both A strategy hwin basis
    (profiledOpenFixedPinnedSemanticDescriptor A strategy hwin basis
      initialCode (fun live ↦ control live.state)) source

end

end DetParityAutomaton

end DistributedSynthesis
