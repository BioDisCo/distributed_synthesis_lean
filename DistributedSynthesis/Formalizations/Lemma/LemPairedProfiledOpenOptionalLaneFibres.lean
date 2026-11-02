/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenFibreProvenanceMove
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenLiveFreshSuccessor

/-!
# Optional-lane fresh semantics and one-sided exact fibres

The total correlated semantics permits all four lane shapes.  In particular,
one normalized survivor family may be empty while the other is nonempty.  It
is therefore unsound to restrict the history construction to semantic points
whose two lanes are active.

`LemPairedProfiledOpenLiveFreshSuccessor` supplies the total proof-side
carrier: fresh provenance is required only for lanes which are actually
active, and every total correlated successor has that property.  Here, on a
mixed node, the active lane is rationalized through its own exact blind-sender
fibre; the inactive lane remains the literal public `sink`.  The case
distinction is made only in the global proof-side construction.  Neither
process receives a lane, orientation, or strict-leader flag.

For a two-active node the stronger paired local fibres remain necessary,
because their signatures also pin the opposite fresh receiver.  The one-sided
relations below are deliberately restricted to right-only and left-only
points; they must not be substituted for the paired relation at a two-active
node.
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

/-! ## One-active semantic points -/

/-- A right-only point.  The active lane carries fresh provenance; the left
public move is definitionally the sink. -/
structure ProfiledOpenIndexedRightOnlyFreshSemanticPoint where
  optional : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
    basis (I := I)
  lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I)
  right_eq : optional.state.right = some lane
  left_eq : optional.state.left = none

/-- Left-only mirror. -/
structure ProfiledOpenIndexedLeftOnlyFreshSemanticPoint where
  optional : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
    basis (I := I)
  lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I)
  right_eq : optional.state.right = none
  left_eq : optional.state.left = some lane

noncomputable def ProfiledOpenIndexedRightOnlyFreshSemanticPoint.fresh
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : {root // root ∈ point.lane.source.1}) :
    ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.lane.realization.entry member) :=
  point.optional.rightFresh point.lane point.right_eq member

noncomputable def ProfiledOpenIndexedLeftOnlyFreshSemanticPoint.fresh
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : {root // root ∈ point.lane.source.1}) :
    ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.lane.realization.entry member) :=
  point.optional.leftFresh point.lane point.left_eq member

/-- Package one right-only case as its one-active semantic source. -/
def ProfiledOpenIndexedOptionalFreshSemanticPoint.toRightOnly
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = some lane)
    (hleft : point.state.left = none) :
    ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨point, lane, hright, hleft⟩

/-- Package one left-only case. -/
def ProfiledOpenIndexedOptionalFreshSemanticPoint.toLeftOnly
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I))
    (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
      (I := I))
    (hright : point.state.right = none)
    (hleft : point.state.left = some lane) :
    ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨point, lane, hright, hleft⟩

section
omit [Fintype I]

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem ProfiledOpenIndexedRightOnlyFreshSemanticPoint.move_left
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (point.optional.state.move A strategy hwin basis).2 = .sink := by
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.left_eq,
    ProfiledOpenIndexedLeftSemanticShadow.move]

@[simp] theorem ProfiledOpenIndexedRightOnlyFreshSemanticPoint.move_right
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (point.optional.state.move A strategy hwin basis).1 =
      .right point.lane.source
        ((point.lane.realization.coherentTable A).table.toClassified A
          point.lane.source) := by
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.right_eq,
    ProfiledOpenIndexedRightSemanticShadow.move]

@[simp] theorem ProfiledOpenIndexedLeftOnlyFreshSemanticPoint.move_right
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (point.optional.state.move A strategy hwin basis).1 = .sink := by
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.right_eq,
    ProfiledOpenIndexedRightSemanticShadow.move]

@[simp] theorem ProfiledOpenIndexedLeftOnlyFreshSemanticPoint.move_left
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (point.optional.state.move A strategy hwin basis).2 =
      .left point.lane.source
        ((point.lane.realization.coherentTable A).table.toClassified A
          point.lane.source) := by
  simp [ProfiledOpenIndexedCorrelatedSemanticState.move, point.left_eq,
    ProfiledOpenIndexedLeftSemanticShadow.move]

end

end

/-! ## One-sided exact local fibres -/

/-- The complete local datum needed by the right-only blind sender.  There is
no opposite active receiver to pin at a right-only node. -/
noncomputable def profiledOpenIndexedRightOnlyLocalViewSignature
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  currentView Proc.one
    (point.lane.realization.entry point.lane.realization.pivot).leftHistory

/-- Left-only blind-sender signature. -/
noncomputable def profiledOpenIndexedLeftOnlyLocalViewSignature
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  currentView Proc.two
    (point.lane.realization.entry point.lane.realization.pivot).rightHistory

def ProfiledOpenIndexedRightOnlyLocalFibreRel
    (left right : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  profiledOpenIndexedRightOnlyLocalViewSignature A strategy hwin basis left =
    profiledOpenIndexedRightOnlyLocalViewSignature A strategy hwin basis right

def ProfiledOpenIndexedLeftOnlyLocalFibreRel
    (left right : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  profiledOpenIndexedLeftOnlyLocalViewSignature A strategy hwin basis left =
    profiledOpenIndexedLeftOnlyLocalViewSignature A strategy hwin basis right

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedRightOnlyLocalFibreRel_reflexive :
    Std.Refl (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I)) := ⟨fun _ => rfl⟩

theorem profiledOpenIndexedLeftOnlyLocalFibreRel_reflexive :
    Std.Refl (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I)) := ⟨fun _ => rfl⟩

theorem profiledOpenIndexedRightOnlyLocalFibreRel_senderView_eq
    {left right : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      left right) :
    currentView Proc.one
        (left.lane.realization.entry left.lane.realization.pivot).leftHistory =
      currentView Proc.one
        (right.lane.realization.entry right.lane.realization.pivot
          ).leftHistory :=
  hrel

theorem profiledOpenIndexedLeftOnlyLocalFibreRel_senderView_eq
    {left right : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      left right) :
    currentView Proc.two
        (left.lane.realization.entry left.lane.realization.pivot).rightHistory =
      currentView Proc.two
        (right.lane.realization.entry right.lane.realization.pivot
          ).rightHistory :=
  hrel

end

/-! ## Right-only source-indexed provenance extraction -/

variable {Descriptor : Type (max i u v x y s)}
variable [Fintype Descriptor] [DecidableEq Descriptor]

abbrev ProfiledOpenOptionalSourceFibreClass : Type (max i u v x y s) :=
  ULift.{max i u v x y s} Unit

section RightOnly

variable (semanticDescriptor :
  ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin basis
    (I := I) → Descriptor)

abbrev ProfiledOpenRightOnlySourceFibreDescriptor
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source

noncomputable instance
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenRightOnlySourceFibrePoint
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenRightOnlySourceFibrePoint_rel
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis source
      (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
        semanticDescriptor source member) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenRightOnlySourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    semanticDescriptor
        (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) = member.1 :=
  semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenRightOnlySourceFibreSource
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenRightViewClass A :=
  (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.source

noncomputable def profiledOpenRightOnlySourceFibreRealization
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenRightRealization A strategy hwin basis
      (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.realization

noncomputable def profiledOpenRightOnlySourceFibreCurrent
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedRightOnlyLocalFibreRel_reflexive A strategy hwin basis).refl
    source

noncomputable def profiledOpenRightOnlySourceFibrePresentation
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenRightOnlySourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenRightOnlySourceFibrePoint_senderView_eq_source
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenRightOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    currentView Proc.one
        ((profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source member).lane.realization.entry
          (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source member).lane.realization.pivot
        ).leftHistory =
      currentView Proc.one
        (source.lane.realization.entry source.lane.realization.pivot
        ).leftHistory :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
      (I := I))
    (fun point => currentView Proc.one
      (point.lane.realization.entry point.lane.realization.pivot).leftHistory)
    (fun hrel => profiledOpenIndexedRightOnlyLocalFibreRel_senderView_eq A
      strategy hwin basis hrel) source member

theorem profiledOpenRightOnlySourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenRightOnlySourceFibreCurrent A strategy
    hwin basis semanticDescriptor source
  calc
    currentView Proc.one
        ((profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).leftHistory =
      currentView Proc.one
        ((profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual).lane.realization.entry
          (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source actual).lane.realization.pivot
        ).leftHistory := by
      simpa [profiledOpenRightOnlySourceFibreRealization] using
        (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).view_eq member
    _ = currentView Proc.one
        (source.lane.realization.entry source.lane.realization.pivot
        ).leftHistory :=
      profiledOpenRightOnlySourceFibrePoint_senderView_eq_source A strategy
        hwin basis semanticDescriptor source actual
    _ = currentView Proc.one
        ((profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative).lane.realization.entry
          (profiledOpenRightOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source representative).lane.realization.pivot
        ).leftHistory :=
      (profiledOpenRightOnlySourceFibrePoint_senderView_eq_source A strategy
        hwin basis semanticDescriptor source representative).symm
    _ = currentView Proc.one
        ((profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
          (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
            semanticDescriptor source representative).pivot).leftHistory := by
      rfl

theorem profiledOpenRightOnlySourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A
      (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenRightOnlySourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

end

/-- The one-sided active controller, retaining semantic table provenance at
every controller state. -/
noncomputable abbrev ProfiledOpenRightOnlySourceFibreProvenanceMove
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  ProfiledOpenRightPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable instance
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenRightOnlySourceFibreProvenanceMove A strategy hwin
      basis semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenRightOnlySourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightOnlySourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenRightOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenRightOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightOnlySourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

end RightOnly

/-! ## Left-only source-indexed provenance extraction -/

section LeftOnly

variable (semanticDescriptor :
  ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin basis
    (I := I) → Descriptor)

abbrev ProfiledOpenLeftOnlySourceFibreDescriptor
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source

noncomputable instance
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenLeftOnlySourceFibrePoint
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenLeftOnlySourceFibrePoint_rel
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis source
      (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
        semanticDescriptor source member) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenLeftOnlySourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    semanticDescriptor
        (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) = member.1 :=
  semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenLeftOnlySourceFibreSource
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenLeftViewClass A :=
  (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.source

noncomputable def profiledOpenLeftOnlySourceFibreRealization
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenLeftRealization A strategy hwin basis
      (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.realization

noncomputable def profiledOpenLeftOnlySourceFibreCurrent
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedLeftOnlyLocalFibreRel_reflexive A strategy hwin basis).refl
    source

noncomputable def profiledOpenLeftOnlySourceFibrePresentation
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenLeftOnlySourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenLeftOnlySourceFibrePoint_senderView_eq_source
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenLeftOnlySourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    currentView Proc.two
        ((profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source member).lane.realization.entry
          (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source member).lane.realization.pivot
        ).rightHistory =
      currentView Proc.two
        (source.lane.realization.entry source.lane.realization.pivot
        ).rightHistory :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
      (I := I))
    (fun point => currentView Proc.two
      (point.lane.realization.entry point.lane.realization.pivot).rightHistory)
    (fun hrel => profiledOpenIndexedLeftOnlyLocalFibreRel_senderView_eq A
      strategy hwin basis hrel) source member

theorem profiledOpenLeftOnlySourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenLeftOnlySourceFibreCurrent A strategy
    hwin basis semanticDescriptor source
  calc
    currentView Proc.two
        ((profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).rightHistory =
      currentView Proc.two
        ((profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual).lane.realization.entry
          (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source actual).lane.realization.pivot
        ).rightHistory := by
      simpa [profiledOpenLeftOnlySourceFibreRealization] using
        (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).view_eq member
    _ = currentView Proc.two
        (source.lane.realization.entry source.lane.realization.pivot
        ).rightHistory :=
      profiledOpenLeftOnlySourceFibrePoint_senderView_eq_source A strategy
        hwin basis semanticDescriptor source actual
    _ = currentView Proc.two
        ((profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative).lane.realization.entry
          (profiledOpenLeftOnlySourceFibrePoint A strategy hwin basis
            semanticDescriptor source representative).lane.realization.pivot
        ).rightHistory :=
      (profiledOpenLeftOnlySourceFibrePoint_senderView_eq_source A strategy
        hwin basis semanticDescriptor source representative).symm
    _ = currentView Proc.two
        ((profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
          (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
            semanticDescriptor source representative).pivot).rightHistory := by
      rfl

theorem profiledOpenLeftOnlySourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A
      (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenLeftOnlySourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

end

/-- Left-only controller with sticky semantic table provenance. -/
noncomputable abbrev ProfiledOpenLeftOnlySourceFibreProvenanceMove
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  ProfiledOpenLeftPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable instance
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenLeftOnlySourceFibreProvenanceMove A strategy hwin
      basis semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenLeftOnlySourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftOnlySourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenLeftOnlySourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenLeftOnlySourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftOnlySourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftOnlySourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

end LeftOnly

/-! ## One total source-indexed provenance bank -/

section TotalBank

variable (semanticDescriptor :
  ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
    (I := I) → Descriptor)

/-- The descriptor lifted to right-only proof points. -/
abbrev profiledOpenRightOnlyDescriptor
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : Descriptor :=
  semanticDescriptor point.optional.state

/-- Left-only descriptor lift. -/
abbrev profiledOpenLeftOnlyDescriptor
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : Descriptor :=
  semanticDescriptor point.optional.state

/-- Two-active descriptor lift. -/
abbrev profiledOpenLiveFreshDescriptor
    (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) : Descriptor :=
  semanticDescriptor point.state

/-- Right-only finite family: the exact active fibre and an empty inactive
left carrier. -/
noncomputable def profiledOpenRightOnlyFamilyCode
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : FiniteTwoFibreCode Descriptor :=
  (semanticFibreImage
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        semanticDescriptor)
      (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
        (I := I)) source,
    ∅)

/-- Left-only finite family. -/
noncomputable def profiledOpenLeftOnlyFamilyCode
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) : FiniteTwoFibreCode Descriptor :=
  (∅,
    semanticFibreImage
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        semanticDescriptor)
      (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
        (I := I)) source)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
/-- The actual descriptor occurs in the active half of a right-only family;
the other half is definitionally empty. -/
theorem profiledOpenRightOnlyDescriptor_mem_family
    (source : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    semanticDescriptor source.optional.state ∈
        (profiledOpenRightOnlyFamilyCode A strategy hwin basis
          semanticDescriptor source).1 ∧
      (profiledOpenRightOnlyFamilyCode A strategy hwin basis
        semanticDescriptor source).2 = ∅ := by
  constructor
  · exact descriptor_mem_semanticFibreImage
      (profiledOpenRightOnlyDescriptor A strategy hwin basis
        semanticDescriptor)
      (ProfiledOpenIndexedRightOnlyLocalFibreRel A strategy hwin basis
        (I := I))
      (profiledOpenIndexedRightOnlyLocalFibreRel_reflexive A strategy hwin
        basis).refl source
  · rfl

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
/-- Left-only current-descriptor membership. -/
theorem profiledOpenLeftOnlyDescriptor_mem_family
    (source : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    (profiledOpenLeftOnlyFamilyCode A strategy hwin basis semanticDescriptor
        source).1 = ∅ ∧
      semanticDescriptor source.optional.state ∈
        (profiledOpenLeftOnlyFamilyCode A strategy hwin basis
          semanticDescriptor source).2 := by
  constructor
  · rfl
  · exact descriptor_mem_semanticFibreImage
      (profiledOpenLeftOnlyDescriptor A strategy hwin basis
        semanticDescriptor)
      (ProfiledOpenIndexedLeftOnlyLocalFibreRel A strategy hwin basis
        (I := I))
      (profiledOpenIndexedLeftOnlyLocalFibreRel_reflexive A strategy hwin
        basis).refl source

/-- The exact extraction selected by a total semantic source.

`sink` carries no controller, a mixed case carries only the active lane's
controller, and `both` carries the existing paired extraction.  The lane case
and all semantic witnesses stay proof-side. -/
inductive ProfiledOpenIndexedOptionalSourceFibreProvenanceBank
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I)) : Type (max i u v x y s)
  | sink
      (hright : point.state.right = none)
      (hleft : point.state.left = none)
  | rightOnly
      (lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (hright : point.state.right = some lane)
      (hleft : point.state.left = none)
      (move : ProfiledOpenRightOnlySourceFibreProvenanceMove A strategy hwin
        basis
        (profiledOpenRightOnlyDescriptor A strategy hwin basis
          semanticDescriptor)
        (point.toRightOnly A strategy hwin basis lane hright hleft))
  | leftOnly
      (lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (hright : point.state.right = none)
      (hleft : point.state.left = some lane)
      (move : ProfiledOpenLeftOnlySourceFibreProvenanceMove A strategy hwin
        basis
        (profiledOpenLeftOnlyDescriptor A strategy hwin basis
          semanticDescriptor)
        (point.toLeftOnly A strategy hwin basis lane hright hleft))
  | both
      (rightLane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis
        (I := I))
      (leftLane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis
        (I := I))
      (hright : point.state.right = some rightLane)
      (hleft : point.state.left = some leftLane)
      (move : ProfiledOpenPairedSourceFibreProvenanceBank A strategy hwin basis
        (profiledOpenLiveFreshDescriptor A strategy hwin basis
          semanticDescriptor)
        (point.toLiveFresh A strategy hwin basis rightLane leftLane hright
          hleft))

/-- Winning raw semantics fills the appropriate exact provenance bank for
every optional-lane source.  This is the source-indexed endpoint; erasure into
one fixed finite public alphabet is deliberately a separate operation. -/
noncomputable def profiledOpenIndexedOptionalSourceFibreProvenanceBankOfWinning
    (point : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedOptionalSourceFibreProvenanceBank A strategy hwin basis
      semanticDescriptor point := by
  classical
  cases point.state.laneShape A strategy hwin basis with
  | inactive hright hleft => exact .sink hright hleft
  | rightOnly lane hright hleft =>
      exact .rightOnly lane hright hleft
        (profiledOpenRightOnlySourceFibreProvenanceMoveOfWinning A strategy
          hwin basis
          (profiledOpenRightOnlyDescriptor A strategy hwin basis
            semanticDescriptor)
          (point.toRightOnly A strategy hwin basis lane hright hleft))
  | leftOnly lane hright hleft =>
      exact .leftOnly lane hright hleft
        (profiledOpenLeftOnlySourceFibreProvenanceMoveOfWinning A strategy
          hwin basis
          (profiledOpenLeftOnlyDescriptor A strategy hwin basis
            semanticDescriptor)
          (point.toLeftOnly A strategy hwin basis lane hright hleft))
  | both rightLane leftLane hright hleft =>
      exact .both rightLane leftLane hright hleft
        (profiledOpenPairedSourceFibreProvenanceBankOfWinning A strategy hwin
          basis
          (profiledOpenLiveFreshDescriptor A strategy hwin basis
            semanticDescriptor)
          (point.toLiveFresh A strategy hwin basis rightLane leftLane hright
            hleft))

end TotalBank

end

end DetParityAutomaton

end DistributedSynthesis
