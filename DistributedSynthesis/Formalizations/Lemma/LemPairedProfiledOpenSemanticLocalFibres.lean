/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteSemanticFibreImage
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenRawInitialOutputCoherence
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedRawSemantic

/-!
# Exact local fibres of a live fresh semantic state

The indexed correlated semantic state intentionally forgets the literal
fresh-child witnesses produced by a handoff.  Those witnesses are needed only
in the proof that a receiving strategy is constant on a local fibre; they are
not observable data and must not be added to the public state.

This file therefore uses the smallest proof-side wrapper needed on the
post-handoff region:

* both semantic lanes are active;
* every realization member retains its literal fresh-child provenance.

For each process, its local fibre is the kernel of one exact-view signature.
The signature contains the blind sender's current view and, for every
persistent lineage, the opposite fresh child's receiving view.  Consequently
the relations are equivalence relations, their fibres agree extensionally,
and the raw initial-output coherence lemmas apply directly.  No graph,
orientation, strict-leader bit, or chosen informed side occurs in the wrapper
or either relation.
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

/-! ## The proof-side live fresh point -/

/-- A correlated semantic point in the post-handoff region, with the literal
fresh-child provenance that `ProfiledOpenIndexedCorrelatedSemanticState`
deliberately erases.

The two lane equalities say only that the lanes are active.  The provenance
fields are proof witnesses about the realizations' histories; neither they nor
the lanes are exposed to either process. -/
structure ProfiledOpenIndexedLiveFreshSemanticPoint where
  state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
    (I := I)
  rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
    (I := I)
  right_eq : state.right = some rightLane
  leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
    (I := I)
  left_eq : state.left = some leftLane
  rightFresh : ∀ member : {root // root ∈ rightLane.source.1},
    ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (rightLane.realization.entry member)
  leftFresh : ∀ member : {root // root ∈ leftLane.source.1},
    ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (leftLane.realization.entry member)

/-! ## The four literal entries read at a semantic point -/

/-- The representative used by the process-one blind sender. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.rightSenderEntry
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProcOnePairedEntryRep strategy :=
  point.rightLane.realization.entry point.rightLane.realization.pivot

/-- The representative used by the process-two blind sender. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.leftSenderEntry
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProcTwoPairedEntryRep strategy :=
  point.leftLane.realization.entry point.leftLane.realization.pivot

/-- Decode one lineage into the process-two entry used by the process-one
receiver projection. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.leftReceiverEntry
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (lineage : I) :
    ProcTwoPairedEntryRep strategy :=
  point.leftLane.realization.entry
    (profiledOpenIndexedLeftSourceMember A
      (point.state.code A strategy hwin basis) point.leftLane.source lineage)

/-- Decode one lineage into the process-one entry used by the process-two
receiver projection. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.rightReceiverEntry
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (lineage : I) :
    ProcOnePairedEntryRep strategy :=
  point.rightLane.realization.entry
    (profiledOpenIndexedRightSourceMember A
      (point.state.code A strategy hwin basis) point.rightLane.source lineage)

/-- Fresh provenance for the decoded process-two receiver member. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.leftReceiverFresh
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (lineage : I) :
    ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.leftReceiverEntry A strategy hwin basis lineage) :=
  point.leftFresh _

/-- Fresh provenance for the decoded process-one receiver member. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.rightReceiverFresh
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) (lineage : I) :
    ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.rightReceiverEntry A strategy hwin basis lineage) :=
  point.rightFresh _

/-! ## Exact local-view signatures and their kernel relations -/

/-- Everything from one semantic point that can affect the initial staged
process-one move: its blind sender view and every possible process-two fresh
receiver view. -/
noncomputable def profiledOpenIndexedProcessOneLocalViewSignature
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :=
  (currentView Proc.one
      (point.rightSenderEntry A strategy hwin basis).leftHistory,
    fun lineage : I =>
      currentView Proc.two
        (point.leftReceiverEntry A strategy hwin basis lineage).rightHistory)

/-- Process-two mirror of the exact local-view signature. -/
noncomputable def profiledOpenIndexedProcessTwoLocalViewSignature
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :=
  (currentView Proc.two
      (point.leftSenderEntry A strategy hwin basis).rightHistory,
    fun lineage : I =>
      currentView Proc.one
        (point.rightReceiverEntry A strategy hwin basis lineage).leftHistory)

/-- The process-one proof-side local-fibre relation. -/
def ProfiledOpenIndexedProcessOneLocalFibreRel
    (left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)) : Prop :=
  profiledOpenIndexedProcessOneLocalViewSignature A strategy hwin basis left =
    profiledOpenIndexedProcessOneLocalViewSignature A strategy hwin basis right

/-- The process-two proof-side local-fibre relation. -/
def ProfiledOpenIndexedProcessTwoLocalFibreRel
    (left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)) : Prop :=
  profiledOpenIndexedProcessTwoLocalViewSignature A strategy hwin basis left =
    profiledOpenIndexedProcessTwoLocalViewSignature A strategy hwin basis right

/-! ## Equivalence and fibre-agreement laws -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedProcessOneLocalFibreRel_reflexive :
    Std.Refl
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)) := by
  constructor
  intro point
  rfl

theorem profiledOpenIndexedProcessOneLocalFibreRel_symmetric :
    Symmetric
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)) := by
  intro left right hrel
  exact hrel.symm

theorem profiledOpenIndexedProcessOneLocalFibreRel_transitive :
    IsTrans _
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)) := by
  constructor
  intro left middle right hleft hright
  exact hleft.trans hright

end

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedProcessOneLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedProcessOneLocalFibreRel_symmetric A strategy hwin basis)
    (profiledOpenIndexedProcessOneLocalFibreRel_transitive A strategy hwin basis)

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedProcessTwoLocalFibreRel_reflexive :
    Std.Refl
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)) := by
  constructor
  intro point
  rfl

theorem profiledOpenIndexedProcessTwoLocalFibreRel_symmetric :
    Symmetric
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)) := by
  intro left right hrel
  exact hrel.symm

theorem profiledOpenIndexedProcessTwoLocalFibreRel_transitive :
    IsTrans _
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)) := by
  constructor
  intro left middle right hleft hright
  exact hleft.trans hright

end

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedProcessTwoLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedProcessTwoLocalFibreRel_symmetric A strategy hwin basis)
    (profiledOpenIndexedProcessTwoLocalFibreRel_transitive A strategy hwin basis)

/-! ## The finite-image reflection boundary

`semanticFibreImage_eq_of_rel` proves the forward implication needed to make
the image constant on exact-view fibres.  Its converse is not valid in
general: two different exact-view classes can have the same set of finite
descriptors.  The following named predicate is precisely the extra finite
retraction fact that would be needed before equality of the current finite
class could be used as an exact-view equality.
-/

/-- Equality of finite descriptor images reflects the underlying semantic
relation.  This is a genuine finite-retraction/completeness premise; it does
not follow from `RelationFibresAgree`, reflexivity, symmetry, or transitivity. -/
def SemanticFibreImageReflectsRelation
    {Semantic : Type*} {Descriptor : Type*}
    [Fintype Descriptor] [DecidableEq Descriptor]
    (descriptor : Semantic → Descriptor)
    (Rel : Semantic → Semantic → Prop) : Prop :=
  ∀ {left right},
    semanticFibreImage descriptor Rel left =
        semanticFibreImage descriptor Rel right →
      Rel left right

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact process-one relation follows from equality of its finite image
only when the reflection/retraction premise is supplied explicitly. -/
theorem profiledOpenIndexedProcessOneLocalFibreRel_of_fibreImage_eq
    {Descriptor : Type*} [Fintype Descriptor] [DecidableEq Descriptor]
    (descriptor :
      ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
        (I := I) → Descriptor)
    (hreflect : SemanticFibreImageReflectsRelation descriptor
      (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
        (I := I)))
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (himage :
      semanticFibreImage descriptor
          (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
          left =
        semanticFibreImage descriptor
          (ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis)
          right) :
    ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis left
      right :=
  hreflect himage

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two mirror of the explicit reflection boundary. -/
theorem profiledOpenIndexedProcessTwoLocalFibreRel_of_fibreImage_eq
    {Descriptor : Type*} [Fintype Descriptor] [DecidableEq Descriptor]
    (descriptor :
      ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
        (I := I) → Descriptor)
    (hreflect : SemanticFibreImageReflectsRelation descriptor
      (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
        (I := I)))
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (himage :
      semanticFibreImage descriptor
          (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
          left =
        semanticFibreImage descriptor
          (ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis)
          right) :
    ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis left
      right :=
  hreflect himage

/-! ## The exact invariants exposed by the two fibres -/

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

/-- Process-one fibre equality fixes its blind sender's exact current view. -/
theorem profiledOpenIndexedProcessOneLocalFibreRel_senderView_eq
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      left right) :
    currentView Proc.one
        (left.rightSenderEntry A strategy hwin basis).leftHistory =
      currentView Proc.one
        (right.rightSenderEntry A strategy hwin basis).leftHistory := by
  simpa [ProfiledOpenIndexedProcessOneLocalFibreRel,
    profiledOpenIndexedProcessOneLocalViewSignature] using
    congrArg (fun signature => signature.1) hrel

/-- Process-one fibre equality fixes every opposite fresh child's receiving
view, at the same persistent lineage. -/
theorem profiledOpenIndexedProcessOneLocalFibreRel_receiverView_eq
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      left right) (lineage : I) :
    currentView Proc.two
        (left.leftReceiverEntry A strategy hwin basis lineage).rightHistory =
      currentView Proc.two
        (right.leftReceiverEntry A strategy hwin basis lineage).rightHistory := by
  simpa [ProfiledOpenIndexedProcessOneLocalFibreRel,
    profiledOpenIndexedProcessOneLocalViewSignature] using
    congrArg (fun signature => signature.2 lineage) hrel

/-- Process-two fibre equality fixes its blind sender's exact current view. -/
theorem profiledOpenIndexedProcessTwoLocalFibreRel_senderView_eq
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      left right) :
    currentView Proc.two
        (left.leftSenderEntry A strategy hwin basis).rightHistory =
      currentView Proc.two
        (right.leftSenderEntry A strategy hwin basis).rightHistory := by
  simpa [ProfiledOpenIndexedProcessTwoLocalFibreRel,
    profiledOpenIndexedProcessTwoLocalViewSignature] using
    congrArg (fun signature => signature.1) hrel

/-- Process-two fibre equality fixes every opposite fresh child's receiving
view. -/
theorem profiledOpenIndexedProcessTwoLocalFibreRel_receiverView_eq
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      left right) (lineage : I) :
    currentView Proc.one
        (left.rightReceiverEntry A strategy hwin basis lineage).leftHistory =
      currentView Proc.one
        (right.rightReceiverEntry A strategy hwin basis lineage).leftHistory := by
  simpa [ProfiledOpenIndexedProcessTwoLocalFibreRel,
    profiledOpenIndexedProcessTwoLocalViewSignature] using
    congrArg (fun signature => signature.2 lineage) hrel

end

/-! ## Immediate raw initial-output coherence -/

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The process-one fibre relation supplies exactly the raw sender and
receiver laws required by the finite root-pinned extraction. -/
theorem profiledOpenIndexedProcessOneLocalFibreRel_initialOutputCoherent
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessOneLocalFibreRel A strategy hwin basis
      left right) :
    (∀ inputOne,
      (left.rightSenderEntry A strategy hwin basis).lambdaOfStrategy.blind []
          inputOne =
        (right.rightSenderEntry A strategy hwin basis).lambdaOfStrategy.blind []
          inputOne) ∧
      (∀ lineage row inputOne inputTwo,
        pairedLeftInformedForRow row
            (profiledLeftReceiverStrategy A
              (left.leftReceiverEntry A strategy hwin basis lineage).code
              (left.leftReceiverEntry A strategy hwin basis lineage
                ).lambdaOfStrategy [] (inputOne, inputTwo)).physical =
          pairedLeftInformedForRow row
            (profiledLeftReceiverStrategy A
              (right.leftReceiverEntry A strategy hwin basis lineage).code
              (right.leftReceiverEntry A strategy hwin basis lineage
                ).lambdaOfStrategy [] (inputOne, inputTwo)).physical) := by
  constructor
  · intro inputOne
    exact procOnePairedEntry_blindInitialOutput_eq_of_view_eq
      (left.rightSenderEntry A strategy hwin basis)
      (right.rightSenderEntry A strategy hwin basis)
      (profiledOpenIndexedProcessOneLocalFibreRel_senderView_eq A strategy
        hwin basis hrel) inputOne
  · intro lineage row inputOne inputTwo
    exact
      procTwoPairedEntry_leftReceiveInitialOutput_eq_of_fresh_view_eq.{u, v, x,
        y, s, max i u v x y s, max i u v x y s} A
      (left.leftReceiverEntry A strategy hwin basis lineage)
      (right.leftReceiverEntry A strategy hwin basis lineage)
      (left.leftReceiverFresh A strategy hwin basis lineage)
      (right.leftReceiverFresh A strategy hwin basis lineage)
      (profiledOpenIndexedProcessOneLocalFibreRel_receiverView_eq A strategy
        hwin basis hrel lineage) row inputOne inputTwo

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-two raw initial-output coherence. -/
theorem profiledOpenIndexedProcessTwoLocalFibreRel_initialOutputCoherent
    {left right : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin
      basis (I := I)}
    (hrel : ProfiledOpenIndexedProcessTwoLocalFibreRel A strategy hwin basis
      left right) :
    (∀ inputTwo,
      (left.leftSenderEntry A strategy hwin basis).lambdaOfStrategy.blind []
          inputTwo =
        (right.leftSenderEntry A strategy hwin basis).lambdaOfStrategy.blind []
          inputTwo) ∧
      (∀ lineage row inputOne inputTwo,
        pairedRightInformedForRow row
            (profiledRightReceiverStrategy A
              (left.rightReceiverEntry A strategy hwin basis lineage).code
              (left.rightReceiverEntry A strategy hwin basis lineage
                ).lambdaOfStrategy [] (inputTwo, inputOne)).physical =
          pairedRightInformedForRow row
            (profiledRightReceiverStrategy A
              (right.rightReceiverEntry A strategy hwin basis lineage).code
              (right.rightReceiverEntry A strategy hwin basis lineage
                ).lambdaOfStrategy [] (inputTwo, inputOne)).physical) := by
  constructor
  · intro inputTwo
    exact procTwoPairedEntry_blindInitialOutput_eq_of_view_eq
      (left.leftSenderEntry A strategy hwin basis)
      (right.leftSenderEntry A strategy hwin basis)
      (profiledOpenIndexedProcessTwoLocalFibreRel_senderView_eq A strategy
        hwin basis hrel) inputTwo
  · intro lineage row inputOne inputTwo
    exact
      procOnePairedEntry_rightReceiveInitialOutput_eq_of_fresh_view_eq.{u, v, x,
        y, s, max i u v x y s, max i u v x y s} A
      (left.rightReceiverEntry A strategy hwin basis lineage)
      (right.rightReceiverEntry A strategy hwin basis lineage)
      (left.rightReceiverFresh A strategy hwin basis lineage)
      (right.rightReceiverFresh A strategy hwin basis lineage)
      (profiledOpenIndexedProcessTwoLocalFibreRel_receiverView_eq A strategy
        hwin basis hrel lineage) row inputOne inputTwo

end

end DetParityAutomaton

end DistributedSynthesis
