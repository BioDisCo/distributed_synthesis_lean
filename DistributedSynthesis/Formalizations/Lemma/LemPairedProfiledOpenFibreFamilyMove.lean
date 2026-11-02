/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyPinnedReindexing
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRawInitialOutputCoherence

/-!
# Joint right/left moves over the two local-belief fibre partitions

A global descriptor is seen through two different finite quotient maps: the
process-one fibre and the process-two fibre.  It is unsound to form one right
and one left union over the same descriptor set.  Instead:

* the right sender controller is union-extracted inside each process-one
  fibre;
* the left sender controller is union-extracted inside each process-two
  fibre;
* the opposite receiver projections are root-pinned, so they can be compared
  across the other process's fibres without pretending that their senders are
  shared.

The resulting move is one finite bank containing both families.  Reading it
at a global descriptor gives one right and one left foreign-control
projection.  These projections cannot be coerced to the old
`ProfiledOpenIndexedBiBeliefMove`: that type fixes each controller to a
descriptor-local restricted-automaton state, whereas locality requires the
union controller state to remain literal.  We therefore expose a dedicated
readback surface and prove exactly the two side-specific sibling-install
laws there.

No current graph, orientation, lineage, or leader bit is an input of either
sender controller.
-/

namespace DistributedSynthesis

universe u v x y s z

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

/-! ## Finite fibre presentations -/

/-- A finite quotient together with a representative of every (therefore
nonempty) fibre. -/
structure ProfiledOpenFiniteFibrePresentation
    (Global Class : Type z) where
  classOf : Global → Class
  representative : Class → Global
  representative_class : ∀ c, classOf (representative c) = c

namespace ProfiledOpenFiniteFibrePresentation

variable {Global Class : Type z}

/-- The concrete descriptor fibre over `c`. -/
abbrev Fibre (P : ProfiledOpenFiniteFibrePresentation
    Global Class)
    (c : Class) := { descriptor : Global // P.classOf descriptor = c }

noncomputable instance fibreInhabited
    (P : ProfiledOpenFiniteFibrePresentation
      Global Class)
    (c : Class) : Inhabited (P.Fibre c) :=
  ⟨⟨P.representative c, P.representative_class c⟩⟩

end ProfiledOpenFiniteFibrePresentation

/-! ## Semantic data attached to every global descriptor -/

variable {Global OneClass TwoClass : Type (max z u v x y s)}
variable [Fintype Global] [DecidableEq Global]
variable [Fintype OneClass] [DecidableEq OneClass]
variable [Fintype TwoClass] [DecidableEq TwoClass]

variable
  (oneFibre : ProfiledOpenFiniteFibrePresentation
    Global OneClass)
  (twoFibre : ProfiledOpenFiniteFibrePresentation
    Global TwoClass)

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

/-! ## Fibre-local root and monitor families -/

abbrev ProfiledOpenRightFibreRoot (c : OneClass)
    (descriptor : oneFibre.Fibre c) :=
  ULift.{max z u v x y s}
    { root // root ∈ (rightSource descriptor.1).1 }

abbrev ProfiledOpenLeftFibreRoot (c : TwoClass)
    (descriptor : twoFibre.Fibre c) :=
  ULift.{max z u v x y s}
    { root // root ∈ (leftSource descriptor.1).1 }

noncomputable abbrev profiledOpenRightFibreMonitor (c : OneClass)
    (descriptor : oneFibre.Fibre c)
    (root : ProfiledOpenRightFibreRoot A oneFibre rightSource c descriptor) :=
  profiledOpenRightClassifiedRootMonitor A root.down.1

noncomputable abbrev profiledOpenLeftFibreMonitor (c : TwoClass)
    (descriptor : twoFibre.Fibre c)
    (root : ProfiledOpenLeftFibreRoot A twoFibre leftSource c descriptor) :=
  profiledOpenLeftClassifiedRootMonitor A root.down.1

def profiledOpenRightFibreAllowed (c : OneClass)
    (descriptor : oneFibre.Fibre c)
    (responses :
      ((ProfiledOpenRightFibreRoot A oneFibre rightSource c descriptor × In₂) ×
        In₁) → ProfiledOpenRightClassifiedOutput A) : Prop :=
  ProfiledOpenRightClassifiedTableAllowed A (rightSource descriptor.1)
    (fun input => responses ((ULift.up input.1.1, input.1.2), input.2))

def profiledOpenLeftFibreAllowed (c : TwoClass)
    (descriptor : twoFibre.Fibre c)
    (responses :
      ((ProfiledOpenLeftFibreRoot A twoFibre leftSource c descriptor × In₁) ×
        In₂) → ProfiledOpenLeftClassifiedOutput A) : Prop :=
  ProfiledOpenLeftClassifiedTableAllowed A (leftSource descriptor.1)
    (fun input => responses ((ULift.up input.1.1, input.1.2), input.2))

/-! ## Raw receivers and the genuinely fibre-local senders -/

noncomputable def profiledOpenRightFibreReceiver (c : OneClass)
    (member : Sigma
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c)) :
    ReceiverBlockStrategy In₂ In₁ (ProfiledOpenRightClassifiedOutput A) :=
  profiledOpenRightSemanticClassifiedReceiver A
    (rightSource member.1.1) strategy hwin
    (rightRealization member.1.1).entry basis member.2.down

noncomputable def profiledOpenLeftFibreReceiver (c : TwoClass)
    (member : Sigma
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)) :
    ReceiverBlockStrategy In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) :=
  profiledOpenLeftSemanticClassifiedReceiver A
    (leftSource member.1.1) strategy hwin
    (leftRealization member.1.1).entry basis member.2.down

/-- The right sender is chosen from the representative of the process-one
fibre, never from a current graph/orientation. -/
noncomputable def profiledOpenRightFibreSender (c : OneClass) :
    SenderBlockStrategy In₁ Out₁ :=
  let realization := rightRealization (oneFibre.representative c)
  pairedRightSenderStrategy
    (realization.entry realization.pivot).lambdaOfStrategy

/-- Left sender chosen inside one process-two fibre. -/
noncomputable def profiledOpenLeftFibreSender (c : TwoClass) :
    SenderBlockStrategy In₂ Out₂ :=
  let realization := leftRealization (twoFibre.representative c)
  pairedLeftSenderStrategy
    (realization.entry realization.pivot).lambdaOfStrategy

/-! ## Records pinned before either union extraction -/

noncomputable def profiledOpenRightFibreExpected (c : OneClass)
    (member : Sigma
      (ProfiledOpenRightFibreRoot A oneFibre rightSource c))
    (input : In₂ × In₁) :
    RealizedBlockRound In₂ In₁ (ProfiledOpenRightClassifiedOutput A)
      Out₁ :=
  (input,
    profiledOpenRightFibreReceiver A (oneFibre := oneFibre) strategy hwin
      basis rightSource rightRealization c member [] input,
    profiledOpenRightFibreSender A (oneFibre := oneFibre) strategy hwin
      basis rightSource rightRealization c [] input.2)

noncomputable def profiledOpenLeftFibreExpected (c : TwoClass)
    (member : Sigma
      (ProfiledOpenLeftFibreRoot A twoFibre leftSource c))
    (input : In₁ × In₂) :
    RealizedBlockRound In₁ In₂ (ProfiledOpenLeftClassifiedOutput A)
      Out₂ :=
  (input,
    profiledOpenLeftFibreReceiver A (twoFibre := twoFibre) strategy hwin
      basis leftSource leftRealization c member [] input,
    profiledOpenLeftFibreSender A (twoFibre := twoFibre) strategy hwin
      basis leftSource leftRealization c [] input.2)

/-! ## One finite paired bank -/

/-- One process-one-fibre union, with every semantic member root pinned before
the union extraction. -/
noncomputable abbrev ProfiledOpenRightPinnedFibreMove (c : OneClass) :=
  FiniteDescriptorFamilyPinnedAllowedMove
    (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
    (profiledOpenRightFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A oneFibre rightSource c)
    (profiledOpenRightFibreAllowed A oneFibre rightSource c)
    (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
      basis rightSource rightRealization c)

/-- Process-two-fibre mirror. -/
noncomputable abbrev ProfiledOpenLeftPinnedFibreMove (c : TwoClass) :=
  FiniteDescriptorFamilyPinnedAllowedMove
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
    (profiledOpenLeftFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A twoFibre leftSource c)
    (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
    (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
      basis leftSource leftRealization c)

noncomputable instance (c : OneClass) : Fintype
    (ProfiledOpenRightPinnedFibreMove (A := A) (oneFibre := oneFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (rightSource := rightSource) (rightRealization := rightRealization) c) := by
  classical
  infer_instance

noncomputable instance (c : TwoClass) : Fintype
    (ProfiledOpenLeftPinnedFibreMove (A := A) (twoFibre := twoFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (leftSource := leftSource) (leftRealization := leftRealization) c) := by
  classical
  infer_instance

/-- The public move alphabet produced by the joint extraction.  It is one
finite pair containing both local-fibre banks.  Its components are not old
classified moves: their union-controller state remains literal, which is the
sharing property needed at the sibling-install seam. -/
noncomputable abbrev ProfiledOpenPairedFibreFamilyMove :=
  (∀ c : OneClass,
      ProfiledOpenRightPinnedFibreMove (A := A) (oneFibre := oneFibre)
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (rightSource := rightSource) (rightRealization := rightRealization) c) ×
    (∀ c : TwoClass,
      ProfiledOpenLeftPinnedFibreMove (A := A) (twoFibre := twoFibre)
        (strategy := strategy) (hwin := hwin) (basis := basis)
        (leftSource := leftSource) (leftRealization := leftRealization) c)

set_option synthInstance.maxHeartbeats 200000 in
noncomputable instance : Fintype
    (ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization)) := by
  classical
  infer_instance

/-! ## Raw locality premises used by the two extractions -/

/-- All process-one semantic roots stored in one process-one fibre use the
same blind sender view as that fibre's fixed representative.  This is a
proof-side view equality, not an observable fibre or orientation tag. -/
def ProfiledOpenRightFibreSenderViewsAgree : Prop :=
  ∀ c (descriptor : oneFibre.Fibre c)
      (member : {root // root ∈ (rightSource descriptor.1).1}),
    currentView Proc.one
        ((rightRealization descriptor.1).entry member).leftHistory =
      currentView Proc.one
        ((rightRealization (oneFibre.representative c)).entry
          (rightRealization (oneFibre.representative c)).pivot).leftHistory

/-- Process-two mirror. -/
def ProfiledOpenLeftFibreSenderViewsAgree : Prop :=
  ∀ c (descriptor : twoFibre.Fibre c)
      (member : {root // root ∈ (leftSource descriptor.1).1}),
    currentView Proc.two
        ((leftRealization descriptor.1).entry member).rightHistory =
      currentView Proc.two
        ((leftRealization (twoFibre.representative c)).entry
          (leftRealization (twoFibre.representative c)).pivot).rightHistory

/-- The exact premise consumed by the right union extraction: every semantic
member in one process-one fibre has the representative's *whole* blind block
sender, at every finite own-input history.  Unlike exact-view equality, this
does not ask how that strategy equality was obtained. -/
def ProfiledOpenRightFibreSenderStrategiesAgree : Prop :=
  ∀ c (descriptor : oneFibre.Fibre c)
      (member : {root // root ∈ (rightSource descriptor.1).1}),
    pairedRightSenderStrategy
        ((rightRealization descriptor.1).entry member).lambdaOfStrategy =
      profiledOpenRightFibreSender A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization c

/-- Process-two mirror of `ProfiledOpenRightFibreSenderStrategiesAgree`. -/
def ProfiledOpenLeftFibreSenderStrategiesAgree : Prop :=
  ∀ c (descriptor : twoFibre.Fibre c)
      (member : {root // root ∈ (leftSource descriptor.1).1}),
    pairedLeftSenderStrategy
        ((leftRealization descriptor.1).entry member).lambdaOfStrategy =
      profiledOpenLeftFibreSender A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization c

/-- The logically weakest right-side premise consumed by the fixed
root-pinned extraction: the representative sender wins every semantic member
of its fibre with that member's receiver.  It need not be identified with the
member's original infinite sender strategy. -/
def ProfiledOpenRightFibreCommonSenderWins : Prop :=
  ∀ c
      (member : Sigma
        (ProfiledOpenRightFibreRoot A oneFibre rightSource c))
      (env : Nat → In₂ × In₁),
    (profiledOpenRightFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A oneFibre rightSource c member.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenRightFibreReceiver A (oneFibre := oneFibre) strategy hwin
          basis rightSource rightRealization c member)
        (profiledOpenRightFibreSender A (oneFibre := oneFibre) strategy hwin
          basis rightSource rightRealization c)
        env)

/-- Left-side common-sender winning premise. -/
def ProfiledOpenLeftFibreCommonSenderWins : Prop :=
  ∀ c
      (member : Sigma
        (ProfiledOpenLeftFibreRoot A twoFibre leftSource c))
      (env : Nat → In₁ × In₂),
    (profiledOpenLeftFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A twoFibre leftSource c member.1 member.2).WinsPlay
      (pairPlay
        (profiledOpenLeftFibreReceiver A (twoFibre := twoFibre) strategy hwin
          basis leftSource leftRealization c member)
        (profiledOpenLeftFibreSender A (twoFibre := twoFibre) strategy hwin
          basis leftSource leftRealization c)
        env)

/-- A descriptor code determines the complete process-one blind block sender.
The codomain is a strategy space, but the code itself may be finite.  This is
the weakest useful controller-factor interface: equality of codes gives
equality at every blind-block node, not merely equality of the first output. -/
def ProfiledOpenRightSenderStrategyFactorsThrough
    {SenderCode : Type z}
    (code : Global → SenderCode)
    (senderOf : SenderCode → SenderBlockStrategy In₁ Out₁) : Prop :=
  ∀ descriptor
      (member : {root // root ∈ (rightSource descriptor).1}),
    pairedRightSenderStrategy
        ((rightRealization descriptor).entry member).lambdaOfStrategy =
      senderOf (code descriptor)

/-- Left-side whole-strategy factor interface. -/
def ProfiledOpenLeftSenderStrategyFactorsThrough
    {SenderCode : Type z}
    (code : Global → SenderCode)
    (senderOf : SenderCode → SenderBlockStrategy In₂ Out₂) : Prop :=
  ∀ descriptor
      (member : {root // root ∈ (leftSource descriptor).1}),
    pairedLeftSenderStrategy
        ((leftRealization descriptor).entry member).lambdaOfStrategy =
      senderOf (code descriptor)

/-- The right sender code is constant on the process-one semantic fibres. -/
def ProfiledOpenRightSenderCodeFibreConstant
    {SenderCode : Type z}
    (_rightSource : Global → ProfiledOpenRightViewClass A)
    (code : Global → SenderCode) : Prop :=
  ∀ c (descriptor : oneFibre.Fibre c),
    code descriptor.1 = code (oneFibre.representative c)

/-- The left sender code is constant on the process-two semantic fibres. -/
def ProfiledOpenLeftSenderCodeFibreConstant
    {SenderCode : Type z}
    (_leftSource : Global → ProfiledOpenLeftViewClass A)
    (code : Global → SenderCode) : Prop :=
  ∀ c (descriptor : twoFibre.Fibre c),
    code descriptor.1 = code (twoFibre.representative c)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype OneClass] [DecidableEq OneClass] in
/-- Exact-view equality is one sufficient source of whole-sender equality. -/
theorem profiledOpenRightFibreSenderStrategiesAgree_of_views
    (hviews : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization) :
    ProfiledOpenRightFibreSenderStrategiesAgree A oneFibre strategy hwin basis
      rightSource rightRealization := by
  intro c descriptor member
  unfold profiledOpenRightFibreSender pairedRightSenderStrategy
  exact blockSenderOne_eq_of_view_eq strategy (hviews c descriptor member)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype TwoClass] [DecidableEq TwoClass] in
/-- Left mirror of
`profiledOpenRightFibreSenderStrategiesAgree_of_views`. -/
theorem profiledOpenLeftFibreSenderStrategiesAgree_of_views
    (hviews : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization) :
    ProfiledOpenLeftFibreSenderStrategiesAgree A twoFibre strategy hwin basis
      leftSource leftRealization := by
  intro c descriptor member
  unfold profiledOpenLeftFibreSender pairedLeftSenderStrategy
  exact blockSenderTwo_eq_of_view_eq strategy (hviews c descriptor member)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype OneClass] [DecidableEq OneClass] in
/-- A finite descriptor code that determines the complete sender and is
constant on right fibres discharges the extraction premise without reflecting
semantic-image equality back to exact views. -/
theorem profiledOpenRightFibreSenderStrategiesAgree_of_finiteFactor
    {SenderCode : Type z} [Fintype SenderCode]
    (code : Global → SenderCode)
    (senderOf : SenderCode → SenderBlockStrategy In₁ Out₁)
    (hfactor : ProfiledOpenRightSenderStrategyFactorsThrough A strategy hwin
      basis rightSource rightRealization code senderOf)
    (hconstant : ProfiledOpenRightSenderCodeFibreConstant A oneFibre
      rightSource code) :
    ProfiledOpenRightFibreSenderStrategiesAgree A oneFibre strategy hwin basis
      rightSource rightRealization := by
  intro c descriptor member
  rw [hfactor descriptor.1 member, hconstant c descriptor]
  symm
  simpa [profiledOpenRightFibreSender] using
    hfactor (oneFibre.representative c)
      (rightRealization (oneFibre.representative c)).pivot

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype TwoClass] [DecidableEq TwoClass] in
/-- Left finite whole-sender factor. -/
theorem profiledOpenLeftFibreSenderStrategiesAgree_of_finiteFactor
    {SenderCode : Type z} [Fintype SenderCode]
    (code : Global → SenderCode)
    (senderOf : SenderCode → SenderBlockStrategy In₂ Out₂)
    (hfactor : ProfiledOpenLeftSenderStrategyFactorsThrough A strategy hwin
      basis leftSource leftRealization code senderOf)
    (hconstant : ProfiledOpenLeftSenderCodeFibreConstant A twoFibre leftSource
      code) :
    ProfiledOpenLeftFibreSenderStrategiesAgree A twoFibre strategy hwin basis
      leftSource leftRealization := by
  intro c descriptor member
  rw [hfactor descriptor.1 member, hconstant c descriptor]
  symm
  simpa [profiledOpenLeftFibreSender] using
    hfactor (twoFibre.representative c)
      (leftRealization (twoFibre.representative c)).pivot

omit [Fintype Global] [DecidableEq Global] [Fintype OneClass] [DecidableEq OneClass]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- Whole-sender equality supplies the common-sender winning premise, but the
conclusion deliberately forgets that stronger equality. -/
theorem profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree
    (hsenders : ProfiledOpenRightFibreSenderStrategiesAgree A oneFibre strategy
      hwin basis rightSource rightRealization) :
    ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin basis
      rightSource rightRealization := by
  intro c member env
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenRightRootMonitor A member.2.down.1)
    (fun output : ProfiledOpenRightClassifiedOutput A => output.1) _).mpr
  have hmember := profiledOpenRightBlockMonitor_realizable_of_winning A
    strategy hwin
    ((rightRealization member.1.1).entry member.2.down)
    ((rightRealization member.1.1).minimum member.2.down) basis env
  have hsender := hsenders c member.1 member.2.down
  have hroot := (rightRealization member.1.1).root_eq member.2.down
  have hrootmember :
      (profiledOpenRightRootMonitor A
        (profiledOpenRightRootOfWinning A strategy hwin
          ((rightRealization member.1.1).entry member.2.down)
          ((rightRealization member.1.1).minimum member.2.down) basis)).WinsPlay
        (pairPlay
          (profiledRightReceiverStrategy A
            ((rightRealization member.1.1).entry member.2.down).code
            ((rightRealization member.1.1).entry member.2.down).lambdaOfStrategy)
          (pairedRightSenderStrategy
            ((rightRealization member.1.1).entry member.2.down).lambdaOfStrategy)
          env) := by
    simpa [profiledOpenRightRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  simpa [BlockRecordMonitor.projectReceiverPlay,
    profiledOpenRightFibreReceiver, pairPlay, treePlay, treeOfPair,
    blockLabelApply] using hrootmember

omit [Fintype Global] [DecidableEq Global] [Fintype TwoClass] [DecidableEq TwoClass]
    [Inhabited Out₁] [Inhabited Out₂] in
/-- Left mirror of
`profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree`. -/
theorem profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree
    (hsenders : ProfiledOpenLeftFibreSenderStrategiesAgree A twoFibre strategy
      hwin basis leftSource leftRealization) :
    ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin basis
      leftSource leftRealization := by
  intro c member env
  apply (BlockRecordMonitor.comapReceiverOutput_wins_iff
    (profiledOpenLeftRootMonitor A member.2.down.1)
    (fun output : ProfiledOpenLeftClassifiedOutput A => output.1) _).mpr
  have hmember := profiledOpenLeftBlockMonitor_realizable_of_winning A
    strategy hwin
    ((leftRealization member.1.1).entry member.2.down)
    ((leftRealization member.1.1).minimum member.2.down) basis env
  have hsender := hsenders c member.1 member.2.down
  have hroot := (leftRealization member.1.1).root_eq member.2.down
  have hrootmember :
      (profiledOpenLeftRootMonitor A
        (profiledOpenLeftRootOfWinning A strategy hwin
          ((leftRealization member.1.1).entry member.2.down)
          ((leftRealization member.1.1).minimum member.2.down) basis)).WinsPlay
        (pairPlay
          (profiledLeftReceiverStrategy A
            ((leftRealization member.1.1).entry member.2.down).code
            ((leftRealization member.1.1).entry member.2.down).lambdaOfStrategy)
          (pairedLeftSenderStrategy
            ((leftRealization member.1.1).entry member.2.down).lambdaOfStrategy)
          env) := by
    simpa [profiledOpenLeftRootOfWinning] using hmember
  rw [hroot, hsender] at hrootmember
  simpa [BlockRecordMonitor.projectReceiverPlay,
    profiledOpenLeftFibreReceiver, pairPlay, treePlay, treeOfPair,
    blockLabelApply] using hrootmember

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype OneClass] [DecidableEq OneClass] in
/-- The representative formulation immediately gives pairwise pivot-view
equality inside a process-one fibre. -/
theorem profiledOpenRightPivotViewsAgree_of_fibreSenderViewsAgree
    (hviews : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization)
    (left right : Global)
    (hclass : oneFibre.classOf left = oneFibre.classOf right) :
    currentView Proc.one
        ((rightRealization left).entry
          (rightRealization left).pivot).leftHistory =
      currentView Proc.one
        ((rightRealization right).entry
          (rightRealization right).pivot).leftHistory := by
  let leftDescriptor : oneFibre.Fibre (oneFibre.classOf left) :=
    ⟨left, rfl⟩
  let rightDescriptor : oneFibre.Fibre (oneFibre.classOf left) :=
    ⟨right, hclass.symm⟩
  exact (hviews (oneFibre.classOf left) leftDescriptor
      (rightRealization left).pivot).trans
    (hviews (oneFibre.classOf left) rightDescriptor
      (rightRealization right).pivot).symm

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype Global] [DecidableEq Global]
    [Fintype TwoClass] [DecidableEq TwoClass] in
theorem profiledOpenLeftPivotViewsAgree_of_fibreSenderViewsAgree
    (hviews : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization)
    (left right : Global)
    (hclass : twoFibre.classOf left = twoFibre.classOf right) :
    currentView Proc.two
        ((leftRealization left).entry
          (leftRealization left).pivot).rightHistory =
      currentView Proc.two
        ((leftRealization right).entry
          (leftRealization right).pivot).rightHistory := by
  let leftDescriptor : twoFibre.Fibre (twoFibre.classOf left) :=
    ⟨left, rfl⟩
  let rightDescriptor : twoFibre.Fibre (twoFibre.classOf left) :=
    ⟨right, hclass.symm⟩
  exact (hviews (twoFibre.classOf left) leftDescriptor
      (leftRealization left).pivot).trans
    (hviews (twoFibre.classOf left) rightDescriptor
      (leftRealization right).pivot).symm

/-! ## Extract each fibre bank exactly once -/

/-- One right fibre is rationalized as a single root-pinned descriptor union
from its common-sender winning certificate.  Every descriptor/root projection
keeps the literal union sender control. -/
noncomputable def profiledOpenRightPinnedFibreMoveOfCommonSenderWins
    (hwins : ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization)
    (c : OneClass) :
    ProfiledOpenRightPinnedFibreMove (A := A) (oneFibre := oneFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (rightSource := rightSource) (rightRealization := rightRealization) c := by
  classical
  let representative : oneFibre.Fibre c :=
    ⟨oneFibre.representative c, oneFibre.representative_class c⟩
  letI : Inhabited
      (Sigma (ProfiledOpenRightFibreRoot A oneFibre rightSource c)) :=
    ⟨⟨representative,
      ULift.up (rightRealization (oneFibre.representative c)).pivot⟩⟩
  let receiver := profiledOpenRightFibreReceiver A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  letI : Inhabited (ProfiledOpenRightClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let sender := profiledOpenRightFibreSender A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  let defaultTable := finiteRootFamilyReceiver receiver []
  have hallowed : ∀ past,
      DescriptorRootUnionAllowed
        (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
        (profiledOpenRightFibreAllowed A oneFibre rightSource c)
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    unfold profiledOpenRightFibreAllowed
    intro member move row
    have hsemantic :=
      profiledOpenRightSemanticClassifiedFamilyReceiver_allowed A
        (rightSource descriptor.1) strategy hwin
        (rightRealization descriptor.1).entry
        (rightRealization descriptor.1).minimum basis
        (past.map fun old =>
          (((rightRealization descriptor.1).pivot, old.1.2), old.2))
        member move row
    simpa [receiver, profiledOpenRightFibreReceiver,
      profiledOpenRightSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, List.map_map, Function.comp_def] using
      hsemantic
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies
    (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
    (profiledOpenRightFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A oneFibre rightSource c)
    (profiledOpenRightFibreAllowed A oneFibre rightSource c)
    (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
      basis rightSource rightRealization c)
    defaultTable (hallowed []) receiver sender
  · intro member env
    exact hwins c member env
  · intro member input
    rfl
  · exact hallowed

/-- Whole-strategy agreement is one sufficient way to obtain the right
common-sender certificate. -/
noncomputable def profiledOpenRightPinnedFibreMoveOfSenderStrategiesAgree
    (hsenders : ProfiledOpenRightFibreSenderStrategiesAgree A oneFibre strategy
      hwin basis rightSource rightRealization)
    (c : OneClass) :
    ProfiledOpenRightPinnedFibreMove (A := A) (oneFibre := oneFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (rightSource := rightSource) (rightRealization := rightRealization) c :=
  profiledOpenRightPinnedFibreMoveOfCommonSenderWins A oneFibre strategy hwin
    basis rightSource rightRealization
    (profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A oneFibre
      strategy hwin basis rightSource rightRealization hsenders) c

/-- Exact-view compatibility remains a convenient corollary of the weaker
whole-sender extraction. -/
noncomputable def profiledOpenRightPinnedFibreMoveOfWinning
    (hviews : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization)
    (c : OneClass) :
    ProfiledOpenRightPinnedFibreMove (A := A) (oneFibre := oneFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (rightSource := rightSource) (rightRealization := rightRealization) c :=
  profiledOpenRightPinnedFibreMoveOfSenderStrategiesAgree A oneFibre strategy
    hwin basis rightSource rightRealization
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A oneFibre strategy
      hwin basis rightSource rightRealization hviews) c

/-- Left-fibre mirror of
`profiledOpenRightPinnedFibreMoveOfCommonSenderWins`. -/
noncomputable def profiledOpenLeftPinnedFibreMoveOfCommonSenderWins
    (hwins : ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization)
    (c : TwoClass) :
    ProfiledOpenLeftPinnedFibreMove (A := A) (twoFibre := twoFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (leftSource := leftSource) (leftRealization := leftRealization) c := by
  classical
  let representative : twoFibre.Fibre c :=
    ⟨twoFibre.representative c, twoFibre.representative_class c⟩
  letI : Inhabited
      (Sigma (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)) :=
    ⟨⟨representative,
      ULift.up (leftRealization (twoFibre.representative c)).pivot⟩⟩
  let receiver := profiledOpenLeftFibreReceiver A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  letI : Inhabited (ProfiledOpenLeftClassifiedOutput A) :=
    ⟨receiver default [] default⟩
  let sender := profiledOpenLeftFibreSender A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  let defaultTable := finiteRootFamilyReceiver receiver []
  have hallowed : ∀ past,
      DescriptorRootUnionAllowed
        (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
        (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
        (finiteRootFamilyReceiver receiver past) := by
    intro past descriptor
    unfold profiledOpenLeftFibreAllowed
    intro member move row
    have hsemantic :=
      profiledOpenLeftSemanticClassifiedFamilyReceiver_allowed A
        (leftSource descriptor.1) strategy hwin
        (leftRealization descriptor.1).entry
        (leftRealization descriptor.1).minimum basis
        (past.map fun old =>
          (((leftRealization descriptor.1).pivot, old.1.2), old.2))
        member move row
    simpa [receiver, profiledOpenLeftFibreReceiver,
      profiledOpenLeftSemanticClassifiedFamilyReceiver,
      finiteRootFamilyReceiver, List.map_map, Function.comp_def] using
      hsemantic
  apply finiteDescriptorFamilyPinnedAllowedMoveOfStrategies
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
    (profiledOpenLeftFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
      A twoFibre leftSource c)
    (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
    (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
      basis leftSource leftRealization c)
    defaultTable (hallowed []) receiver sender
  · intro member env
    exact hwins c member env
  · intro member input
    rfl
  · exact hallowed

/-- Whole-strategy agreement supplies the left common-sender certificate. -/
noncomputable def profiledOpenLeftPinnedFibreMoveOfSenderStrategiesAgree
    (hsenders : ProfiledOpenLeftFibreSenderStrategiesAgree A twoFibre strategy
      hwin basis leftSource leftRealization)
    (c : TwoClass) :
    ProfiledOpenLeftPinnedFibreMove (A := A) (twoFibre := twoFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (leftSource := leftSource) (leftRealization := leftRealization) c :=
  profiledOpenLeftPinnedFibreMoveOfCommonSenderWins A twoFibre strategy hwin
    basis leftSource leftRealization
    (profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A twoFibre
      strategy hwin basis leftSource leftRealization hsenders) c

/-- Exact-view corollary of the left whole-sender extraction. -/
noncomputable def profiledOpenLeftPinnedFibreMoveOfWinning
    (hviews : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization)
    (c : TwoClass) :
    ProfiledOpenLeftPinnedFibreMove (A := A) (twoFibre := twoFibre)
      (strategy := strategy) (hwin := hwin) (basis := basis)
      (leftSource := leftSource) (leftRealization := leftRealization) c :=
  profiledOpenLeftPinnedFibreMoveOfSenderStrategiesAgree A twoFibre strategy
    hwin basis leftSource leftRealization
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A twoFibre strategy
      hwin basis leftSource leftRealization hviews) c

/-- Joint extraction from exactly the two common-sender winning premises.  The
two independently typed union controllers are chosen together as one value of
the finite public paired-bank alphabet. -/
noncomputable def profiledOpenPairedFibreFamilyMoveOfCommonSenderWins
    (hright : ProfiledOpenRightFibreCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization) :
    ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  (profiledOpenRightPinnedFibreMoveOfCommonSenderWins A oneFibre strategy hwin
      basis rightSource rightRealization hright,
    profiledOpenLeftPinnedFibreMoveOfCommonSenderWins A twoFibre strategy hwin
      basis leftSource leftRealization hleft)

/-- Whole-sender agreement is one route to the joint common-sender
certificate. -/
noncomputable def profiledOpenPairedFibreFamilyMoveOfSenderStrategiesAgree
    (hright : ProfiledOpenRightFibreSenderStrategiesAgree A oneFibre strategy
      hwin basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreSenderStrategiesAgree A twoFibre strategy
      hwin basis leftSource leftRealization) :
    ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  profiledOpenPairedFibreFamilyMoveOfCommonSenderWins A oneFibre twoFibre
    strategy hwin basis rightSource leftSource rightRealization leftRealization
    (profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A oneFibre
      strategy hwin basis rightSource rightRealization hright)
    (profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A twoFibre
      strategy hwin basis leftSource leftRealization hleft)

/-- Joint extraction through two finite descriptor codes.  This route needs
no exact-view reflection theorem: the required mathematical input is instead
that each finite code determines the complete corresponding blind sender. -/
noncomputable def profiledOpenPairedFibreFamilyMoveOfFiniteFactors
    {RightSenderCode LeftSenderCode : Type z}
    [Fintype RightSenderCode] [Fintype LeftSenderCode]
    (rightCode : Global → RightSenderCode)
    (rightSenderOf : RightSenderCode → SenderBlockStrategy In₁ Out₁)
    (leftCode : Global → LeftSenderCode)
    (leftSenderOf : LeftSenderCode → SenderBlockStrategy In₂ Out₂)
    (hrightFactor : ProfiledOpenRightSenderStrategyFactorsThrough A strategy
      hwin basis rightSource rightRealization rightCode rightSenderOf)
    (hrightConstant : ProfiledOpenRightSenderCodeFibreConstant A oneFibre
      rightSource rightCode)
    (hleftFactor : ProfiledOpenLeftSenderStrategyFactorsThrough A strategy
      hwin basis leftSource leftRealization leftCode leftSenderOf)
    (hleftConstant : ProfiledOpenLeftSenderCodeFibreConstant A twoFibre
      leftSource leftCode) :
    ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  profiledOpenPairedFibreFamilyMoveOfSenderStrategiesAgree A oneFibre twoFibre
    strategy hwin basis rightSource leftSource rightRealization leftRealization
    (profiledOpenRightFibreSenderStrategiesAgree_of_finiteFactor A oneFibre
      strategy hwin basis rightSource rightRealization rightCode rightSenderOf
      hrightFactor hrightConstant)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_finiteFactor A twoFibre
      strategy hwin basis leftSource leftRealization leftCode leftSenderOf
      hleftFactor hleftConstant)

/-- Exact-view compatibility remains a corollary of the whole-sender joint
extraction. -/
noncomputable def profiledOpenPairedFibreFamilyMoveOfWinning
    (hright : ProfiledOpenRightFibreSenderViewsAgree A oneFibre strategy hwin
      basis rightSource rightRealization)
    (hleft : ProfiledOpenLeftFibreSenderViewsAgree A twoFibre strategy hwin
      basis leftSource leftRealization) :
    ProfiledOpenPairedFibreFamilyMove (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization) :=
  profiledOpenPairedFibreFamilyMoveOfSenderStrategiesAgree A oneFibre twoFibre
    strategy hwin basis rightSource leftSource rightRealization leftRealization
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A oneFibre strategy
      hwin basis rightSource rightRealization hright)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A twoFibre strategy
      hwin basis leftSource leftRealization hleft)

/-! ## Foreign-control member readback -/

def profiledOpenRightFibreDescriptor (descriptor : Global) :
    oneFibre.Fibre (oneFibre.classOf descriptor) :=
  ⟨descriptor, rfl⟩

def profiledOpenLeftFibreDescriptor (descriptor : Global) :
    twoFibre.Fibre (twoFibre.classOf descriptor) :=
  ⟨descriptor, rfl⟩

/-- Complete initial record read from the right union controller at one
global descriptor and one semantic member. -/
noncomputable def profiledOpenPairedRightInitialRecord
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (rightSource descriptor).1})
    (input : In₂ × In₁) :
    RealizedBlockRound In₂ In₁ (ProfiledOpenRightClassifiedOutput A) Out₁ :=
  let c := oneFibre.classOf descriptor
  let sourceDescriptor :=
    profiledOpenRightFibreDescriptor.{u, v, x, y, s} oneFibre descriptor
  let root : ProfiledOpenRightFibreRoot A oneFibre rightSource c
      sourceDescriptor := ULift.up member
  let base := profiledOpenRightFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
    A oneFibre rightSource c sourceDescriptor root
  let expected := profiledOpenRightFibreExpected A (oneFibre := oneFibre)
    strategy hwin basis rightSource rightRealization c
  let pin := base.rootPinned (expected ⟨sourceDescriptor, root⟩)
  let controller := (move.1 c).memberController
    (ProfiledOpenRightFibreRoot A oneFibre rightSource c)
    (profiledOpenRightFibreMonitor A oneFibre rightSource c)
    (profiledOpenRightFibreAllowed A oneFibre rightSource c)
    expected sourceDescriptor root
  narrowedRecord pin
    (controller.labeledTree [])
    pin.initial input

/-- Left record readback. -/
noncomputable def profiledOpenPairedLeftInitialRecord
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (leftSource descriptor).1})
    (input : In₁ × In₂) :
    RealizedBlockRound In₁ In₂ (ProfiledOpenLeftClassifiedOutput A) Out₂ :=
  let c := twoFibre.classOf descriptor
  let sourceDescriptor :=
    profiledOpenLeftFibreDescriptor.{u, v, x, y, s} twoFibre descriptor
  let root : ProfiledOpenLeftFibreRoot A twoFibre leftSource c
      sourceDescriptor := ULift.up member
  let base := profiledOpenLeftFibreMonitor.{u, v, x, y, s, z, max z u v x y s}
    A twoFibre leftSource c sourceDescriptor root
  let expected := profiledOpenLeftFibreExpected A (twoFibre := twoFibre)
    strategy hwin basis leftSource leftRealization c
  let pin := base.rootPinned (expected ⟨sourceDescriptor, root⟩)
  let controller := (move.2 c).memberController
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource c)
    (profiledOpenLeftFibreMonitor A twoFibre leftSource c)
    (profiledOpenLeftFibreAllowed A twoFibre leftSource c)
    expected sourceDescriptor root
  narrowedRecord pin
    (controller.labeledTree [])
    pin.initial input

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Root pin exposes the exact raw right record through the foreign-control
readback; no conversion to a descriptor-local controller is performed. -/
theorem profiledOpenPairedRightInitialRecord_eq_expected
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (rightSource descriptor).1})
    (input : In₂ × In₁) :
    profiledOpenPairedRightInitialRecord A oneFibre twoFibre strategy hwin
        basis rightSource leftSource rightRealization leftRealization move
        descriptor member input =
      profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
        basis rightSource rightRealization (oneFibre.classOf descriptor)
        ⟨profiledOpenRightFibreDescriptor.{u, v, x, y, s}
            oneFibre descriptor,
          ULift.up member⟩ input := by
  exact (move.1 (oneFibre.classOf descriptor)).member_root_record
    (ProfiledOpenRightFibreRoot A oneFibre rightSource
      (oneFibre.classOf descriptor))
    (profiledOpenRightFibreMonitor A oneFibre rightSource
      (oneFibre.classOf descriptor))
    (profiledOpenRightFibreAllowed A oneFibre rightSource
      (oneFibre.classOf descriptor))
    (profiledOpenRightFibreExpected A (oneFibre := oneFibre) strategy hwin
      basis rightSource rightRealization (oneFibre.classOf descriptor))
    (profiledOpenRightFibreDescriptor.{u, v, x, y, s} oneFibre descriptor)
    (ULift.up member)
    input

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenPairedLeftInitialRecord_eq_expected
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (leftSource descriptor).1})
    (input : In₁ × In₂) :
    profiledOpenPairedLeftInitialRecord A oneFibre twoFibre strategy hwin
        basis rightSource leftSource rightRealization leftRealization move
        descriptor member input =
      profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
        basis leftSource leftRealization (twoFibre.classOf descriptor)
        ⟨profiledOpenLeftFibreDescriptor.{u, v, x, y, s}
            twoFibre descriptor,
          ULift.up member⟩ input := by
  exact (move.2 (twoFibre.classOf descriptor)).member_root_record
    (ProfiledOpenLeftFibreRoot A twoFibre leftSource
      (twoFibre.classOf descriptor))
    (profiledOpenLeftFibreMonitor A twoFibre leftSource
      (twoFibre.classOf descriptor))
    (profiledOpenLeftFibreAllowed A twoFibre leftSource
      (twoFibre.classOf descriptor))
    (profiledOpenLeftFibreExpected A (twoFibre := twoFibre) strategy hwin
      basis leftSource leftRealization (twoFibre.classOf descriptor))
    (profiledOpenLeftFibreDescriptor.{u, v, x, y, s} twoFibre descriptor)
    (ULift.up member)
    input

/-! ## The four initial projections of the paired foreign-control move -/

noncomputable def profiledOpenPairedFibreRightBlindInitialOutput
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global) (inputOne : In₁) : Out₁ :=
  (profiledOpenPairedRightInitialRecord (A := A) (oneFibre := oneFibre)
    (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
    (basis := basis) (rightSource := rightSource) (leftSource := leftSource)
    (rightRealization := rightRealization) (leftRealization := leftRealization)
    move descriptor (rightRealization descriptor).pivot
    (default, inputOne)).2.2

noncomputable def profiledOpenPairedFibreLeftBlindInitialOutput
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global) (inputTwo : In₂) : Out₂ :=
  (profiledOpenPairedLeftInitialRecord (A := A) (oneFibre := oneFibre)
    (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
    (basis := basis) (rightSource := rightSource) (leftSource := leftSource)
    (rightRealization := rightRealization) (leftRealization := leftRealization)
    move descriptor (leftRealization descriptor).pivot
    (default, inputTwo)).2.2

noncomputable def profiledOpenPairedFibreRightReceiveInitialOutput
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (rightSource descriptor).1})
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) : Out₂ :=
  pairedRightInformedForRow row
    (profiledOpenPairedRightInitialRecord (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource) (leftSource := leftSource)
      (rightRealization := rightRealization)
      (leftRealization := leftRealization) move descriptor member
      (inputTwo, inputOne)).2.1.1.physical

noncomputable def profiledOpenPairedFibreLeftReceiveInitialOutput
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (descriptor : Global)
    (member : {root // root ∈ (leftSource descriptor).1})
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) : Out₁ :=
  pairedLeftInformedForRow row
    (profiledOpenPairedLeftInitialRecord (A := A) (oneFibre := oneFibre)
      (twoFibre := twoFibre) (strategy := strategy) (hwin := hwin)
      (basis := basis) (rightSource := rightSource) (leftSource := leftSource)
      (rightRealization := rightRealization)
      (leftRealization := leftRealization) move descriptor member
      (inputOne, inputTwo)).2.1.1.physical

variable {Lineage : Type (max z u v x y s)}

/-- Exactly process one's two stored projections: blind right sender and
informed left receiver. -/
def ProfiledOpenPairedFibreProcessOneInitialOutputCoherent
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (leftMember : ∀ descriptor : Global, Lineage →
      {root // root ∈ (leftSource descriptor).1})
    (left right : Global) : Prop :=
  (∀ inputOne,
      profiledOpenPairedFibreRightBlindInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move left inputOne =
        profiledOpenPairedFibreRightBlindInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move right inputOne) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenPairedFibreLeftReceiveInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move left (leftMember left lineage) row inputOne
          inputTwo =
        profiledOpenPairedFibreLeftReceiveInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move right (leftMember right lineage) row inputOne
          inputTwo)

/-- Process-two mirror. -/
def ProfiledOpenPairedFibreProcessTwoInitialOutputCoherent
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (rightMember : ∀ descriptor : Global, Lineage →
      {root // root ∈ (rightSource descriptor).1})
    (left right : Global) : Prop :=
  (∀ inputTwo,
      profiledOpenPairedFibreLeftBlindInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move left inputTwo =
        profiledOpenPairedFibreLeftBlindInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move right inputTwo) ∧
    (∀ lineage row inputOne inputTwo,
      profiledOpenPairedFibreRightReceiveInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move left (rightMember left lineage) row inputOne
          inputTwo =
        profiledOpenPairedFibreRightReceiveInitialOutput A oneFibre twoFibre
          strategy hwin basis rightSource leftSource rightRealization
          leftRealization move right (rightMember right lineage) row inputOne
          inputTwo)

/-! ## The two staging laws, and only those two -/

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Root-pinned extraction preserves the exact process-one raw fibre law.

The premises are deliberately semantic: the selected left entries retain
fresh-child provenance, and equality of the finite process-one class exposes
the two exact local-view equalities used by the raw strategy.  Equality of a
finite descriptor-image envelope alone is not used and is not sufficient. -/
theorem profiledOpenPairedFibre_processOneInitialOutputCoherent
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (leftMember : ∀ descriptor : Global, Lineage →
      {root // root ∈ (leftSource descriptor).1})
    (leftFresh : ∀ descriptor lineage,
      ProcTwoViewClassChildProvenance strategy
        ((leftRealization descriptor).entry (leftMember descriptor lineage)))
    (hrightView : ∀ left right,
      oneFibre.classOf left = oneFibre.classOf right →
      currentView Proc.one
          ((rightRealization left).entry
            (rightRealization left).pivot).leftHistory =
        currentView Proc.one
          ((rightRealization right).entry
            (rightRealization right).pivot).leftHistory)
    (hleftView : ∀ left right,
      oneFibre.classOf left = oneFibre.classOf right →
      ∀ lineage,
        currentView Proc.two
            ((leftRealization left).entry
              (leftMember left lineage)).rightHistory =
          currentView Proc.two
            ((leftRealization right).entry
              (leftMember right lineage)).rightHistory)
    (left right : Global)
    (hclass : oneFibre.classOf left = oneFibre.classOf right) :
    ProfiledOpenPairedFibreProcessOneInitialOutputCoherent A oneFibre
      twoFibre strategy hwin basis rightSource leftSource rightRealization
      leftRealization move leftMember left right := by
  have hraw := profiledOpenProcessOneRawFibreInitialOutputCoherent A
    oneFibre.classOf
    (fun descriptor =>
      (rightRealization descriptor).entry
        (rightRealization descriptor).pivot)
    (fun descriptor lineage =>
      (leftRealization descriptor).entry (leftMember descriptor lineage))
    leftFresh hrightView hleftView left right hclass
  constructor
  · intro inputOne
    simp only [profiledOpenPairedFibreRightBlindInitialOutput,
      profiledOpenPairedRightInitialRecord_eq_expected]
    simp only [profiledOpenRightFibreExpected,
      profiledOpenRightFibreSender]
    rw [hclass]
  · intro lineage row inputOne inputTwo
    simp only [profiledOpenPairedFibreLeftReceiveInitialOutput,
      profiledOpenPairedLeftInitialRecord_eq_expected]
    simpa [profiledOpenLeftFibreExpected, profiledOpenLeftFibreReceiver,
      profiledOpenLeftSemanticClassifiedReceiver] using
      hraw.2 lineage row inputOne inputTwo

omit [Fintype OneClass] [Fintype TwoClass] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror.  It consumes the corresponding exact semantic fibre
premises and proves only the blind-left/informed-right staging pair. -/
theorem profiledOpenPairedFibre_processTwoInitialOutputCoherent
    (move : ProfiledOpenPairedFibreFamilyMove (A := A)
      (oneFibre := oneFibre) (twoFibre := twoFibre) (strategy := strategy)
      (hwin := hwin) (basis := basis) (rightSource := rightSource)
      (leftSource := leftSource) (rightRealization := rightRealization)
      (leftRealization := leftRealization))
    (rightMember : ∀ descriptor : Global, Lineage →
      {root // root ∈ (rightSource descriptor).1})
    (rightFresh : ∀ descriptor lineage,
      ProcOneViewClassChildProvenance strategy
        ((rightRealization descriptor).entry
          (rightMember descriptor lineage)))
    (hleftView : ∀ left right,
      twoFibre.classOf left = twoFibre.classOf right →
      currentView Proc.two
          ((leftRealization left).entry
            (leftRealization left).pivot).rightHistory =
        currentView Proc.two
          ((leftRealization right).entry
            (leftRealization right).pivot).rightHistory)
    (hrightView : ∀ left right,
      twoFibre.classOf left = twoFibre.classOf right →
      ∀ lineage,
        currentView Proc.one
            ((rightRealization left).entry
              (rightMember left lineage)).leftHistory =
          currentView Proc.one
            ((rightRealization right).entry
              (rightMember right lineage)).leftHistory)
    (left right : Global)
    (hclass : twoFibre.classOf left = twoFibre.classOf right) :
    ProfiledOpenPairedFibreProcessTwoInitialOutputCoherent A oneFibre
      twoFibre strategy hwin basis rightSource leftSource rightRealization
      leftRealization move rightMember left right := by
  have hraw := profiledOpenProcessTwoRawFibreInitialOutputCoherent A
    twoFibre.classOf
    (fun descriptor =>
      (leftRealization descriptor).entry
        (leftRealization descriptor).pivot)
    (fun descriptor lineage =>
      (rightRealization descriptor).entry (rightMember descriptor lineage))
    rightFresh hleftView hrightView left right hclass
  constructor
  · intro inputTwo
    simp only [profiledOpenPairedFibreLeftBlindInitialOutput,
      profiledOpenPairedLeftInitialRecord_eq_expected]
    simp only [profiledOpenLeftFibreExpected,
      profiledOpenLeftFibreSender]
    rw [hclass]
  · intro lineage row inputOne inputTwo
    simp only [profiledOpenPairedFibreRightReceiveInitialOutput,
      profiledOpenPairedRightInitialRecord_eq_expected]
    simpa [profiledOpenRightFibreExpected, profiledOpenRightFibreReceiver,
      profiledOpenRightSemanticClassifiedReceiver] using
      hraw.2 lineage row inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
