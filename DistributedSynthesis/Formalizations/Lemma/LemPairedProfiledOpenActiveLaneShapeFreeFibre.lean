/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenOptionalLaneFibres

/-!
# Shape-free active-lane fibres

The optional semantic carrier has four proof-side shapes.  A process must not
select a different controller merely because the other lane is absent or
present: that fresh one-bit distinction need not be locally recoverable.

This file therefore forgets the inactive/opposite lane completely.  An active
right point is an optional point together with a witness that its right lane is
present; an active left point is the mirror.  The fibre relation remembers only
the literal view of the active lane's blind sender.  Consequently right-only
and both-active points with that same view belong to one fibre and are
rationalized jointly.  No shape, orientation, or strict-leader flag is an
argument of the relation or of the resulting controller.

The view kernel gives more than equality of the first sender output.  It fixes
the whole blind sender strategy.  Fresh-child provenance also turns the same
view equality into equality of the complete physical receiver strategy on
each old-history row.  This is direct indistinguishability, not recovery of a
lost graph bit.
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

/-! ## Shape-free active carriers -/

/-- An optional semantic point with an active right lane.  There is no field
describing whether the left lane is active. -/
structure ProfiledOpenIndexedActiveRightFreshSemanticPoint where
  optional : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
    basis (I := I)
  lane : ProfiledOpenIndexedRightSemanticLane A strategy hwin basis (I := I)
  active : optional.state.right = some lane

/-- Left mirror, again with no information about the opposite lane. -/
structure ProfiledOpenIndexedActiveLeftFreshSemanticPoint where
  optional : ProfiledOpenIndexedOptionalFreshSemanticPoint A strategy hwin
    basis (I := I)
  lane : ProfiledOpenIndexedLeftSemanticLane A strategy hwin basis (I := I)
  active : optional.state.left = some lane

noncomputable def ProfiledOpenIndexedActiveRightFreshSemanticPoint.fresh
    (point : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : {root // root ∈ point.lane.source.1}) :
    ProcOneViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.lane.realization.entry member) :=
  point.optional.rightFresh point.lane point.active member

noncomputable def ProfiledOpenIndexedActiveLeftFreshSemanticPoint.fresh
    (point : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : {root // root ∈ point.lane.source.1}) :
    ProcTwoViewClassChildProvenance.{max i u v x y s, u, v, x, y} strategy
      (point.lane.realization.entry member) :=
  point.optional.leftFresh point.lane point.active member

/-- A right-only point embeds without exposing its `left = none` proof. -/
noncomputable def ProfiledOpenIndexedRightOnlyFreshSemanticPoint.toActiveRight
    (point : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨point.optional, point.lane, point.right_eq⟩

/-- A both-active point embeds into the same right carrier. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.toActiveRight
  (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh A strategy hwin
      basis point,
    point.rightLane, point.right_eq⟩

/-- Left-only embedding. -/
noncomputable def ProfiledOpenIndexedLeftOnlyFreshSemanticPoint.toActiveLeft
    (point : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨point.optional, point.lane, point.left_eq⟩

/-- Both-active left embedding. -/
noncomputable def ProfiledOpenIndexedLiveFreshSemanticPoint.toActiveLeft
  (point : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) :
    ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  ⟨ProfiledOpenIndexedOptionalFreshSemanticPoint.ofLiveFresh A strategy hwin
      basis point,
    point.leftLane, point.left_eq⟩

/-! ## The shape-free view kernels -/

noncomputable def profiledOpenIndexedActiveRightView
    (point : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  currentView Proc.one
    (point.lane.realization.entry point.lane.realization.pivot).leftHistory

noncomputable def profiledOpenIndexedActiveLeftView
    (point : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  currentView Proc.two
    (point.lane.realization.entry point.lane.realization.pivot).rightHistory

/-- Same-runtime-observation relation for every active right lane, independent
of whether the opposite lane is absent or active. -/
def ProfiledOpenIndexedActiveRightLocalFibreRel
    (left right : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  profiledOpenIndexedActiveRightView A strategy hwin basis left =
    profiledOpenIndexedActiveRightView A strategy hwin basis right

/-- Shape-free active-left mirror. -/
def ProfiledOpenIndexedActiveLeftLocalFibreRel
    (left right : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  profiledOpenIndexedActiveLeftView A strategy hwin basis left =
    profiledOpenIndexedActiveLeftView A strategy hwin basis right

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedActiveRightLocalFibreRel_reflexive :
    Std.Refl (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin
      basis (I := I)) := ⟨fun _ => rfl⟩

theorem profiledOpenIndexedActiveLeftLocalFibreRel_reflexive :
    Std.Refl (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin
      basis (I := I)) := ⟨fun _ => rfl⟩

theorem profiledOpenIndexedActiveRightLocalFibreRel_symmetric :
    Symmetric (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin
      basis (I := I)) := fun _ _ h => h.symm

theorem profiledOpenIndexedActiveLeftLocalFibreRel_symmetric :
    Symmetric (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin
      basis (I := I)) := fun _ _ h => h.symm

theorem profiledOpenIndexedActiveRightLocalFibreRel_transitive :
    IsTrans _ (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin
      basis (I := I)) := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

theorem profiledOpenIndexedActiveLeftLocalFibreRel_transitive :
    IsTrans _ (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin
      basis (I := I)) := ⟨fun _ _ _ h₁ h₂ => h₁.trans h₂⟩

end

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedActiveRightLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
        (I := I)) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedActiveRightLocalFibreRel_symmetric A strategy hwin
      basis)
    (profiledOpenIndexedActiveRightLocalFibreRel_transitive A strategy hwin
      basis)

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenIndexedActiveLeftLocalFibreRel_fibresAgree :
    RelationFibresAgree
      (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
        (I := I)) :=
  relationFibresAgree_of_symmetric_transitive _
    (profiledOpenIndexedActiveLeftLocalFibreRel_symmetric A strategy hwin
      basis)
    (profiledOpenIndexedActiveLeftLocalFibreRel_transitive A strategy hwin
      basis)

/-! ## Complete physical behavior forced by one literal view -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] in
/-- Equality of both current views fixes the complete right-block receiver,
not only its first output. -/
theorem blockReceiverTwo_eq_of_currentViews_eq
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hone : currentView Proc.one left = currentView Proc.one right)
    (htwo : currentView Proc.two left = currentView Proc.two right) :
    blockReceiverTwo strategy left = blockReceiverTwo strategy right := by
  funext node move
  apply congrArg strategy.two
  have hviews := currentViews_extendPrefix_eq_of_currentViews_eq strategy left
    right hone htwo (node.map rightEnvironment)
  have hone' :
      (viewPair (extendPrefix strategy left (node.map rightEnvironment))).1 =
        (viewPair (extendPrefix strategy right
          (node.map rightEnvironment))).1 := by
    simpa [currentView] using hviews.1
  have htwo' :
      (viewPair (extendPrefix strategy left (node.map rightEnvironment))).2 =
        (viewPair (extendPrefix strategy right
          (node.map rightEnvironment))).2 := by
    simpa [currentView] using hviews.2
  simp [blockReceiverTwo, nextView, advanceViewsWithEnvironment, hone', htwo']

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] in
/-- Left-block receiver mirror. -/
theorem blockReceiverOne_eq_of_currentViews_eq
    (left right : History In₁ In₂ Graph Out₁ Out₂)
    (hone : currentView Proc.one left = currentView Proc.one right)
    (htwo : currentView Proc.two left = currentView Proc.two right) :
    blockReceiverOne strategy left = blockReceiverOne strategy right := by
  funext node move
  apply congrArg strategy.one
  have hviews := currentViews_extendPrefix_eq_of_currentViews_eq strategy left
    right hone htwo (node.map leftEnvironment)
  have hone' :
      (viewPair (extendPrefix strategy left (node.map leftEnvironment))).1 =
        (viewPair (extendPrefix strategy right
          (node.map leftEnvironment))).1 := by
    simpa [currentView] using hviews.1
  have htwo' :
      (viewPair (extendPrefix strategy left (node.map leftEnvironment))).2 =
        (viewPair (extendPrefix strategy right
          (node.map leftEnvironment))).2 := by
    simpa [currentView] using hviews.2
  simp [blockReceiverOne, nextView, advanceViewsWithEnvironment, hone', htwo']

/-- Physical process-two receiver selected by one old-history row. -/
def procOnePairedEntryRightReceiverForRow
    (entry : ProcOnePairedEntryRep strategy) : PairedEntryRow →
      ReceiverBlockStrategy In₂ In₁ Out₂
  | .first => blockReceiverTwo strategy entry.leftHistory
  | .both => blockReceiverTwo strategy entry.bothHistory

/-- Physical process-one receiver selected by one old-history row. -/
def procTwoPairedEntryLeftReceiverForRow
    (entry : ProcTwoPairedEntryRep strategy) : PairedEntryRow →
      ReceiverBlockStrategy In₁ In₂ Out₁
  | .first => blockReceiverOne strategy entry.rightHistory
  | .both => blockReceiverOne strategy entry.bothHistory

/-- Extensional active-right behavior that a local consumer is allowed to
observe.  It contains the complete blind sender and every complete physical
receiver row, but no classified successor, graph shape, control, or lane tag.
-/
def ProfiledOpenIndexedActiveRightCompleteBehaviorEq
    (left right : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  (pairedRightSenderStrategy
        (left.lane.realization.entry left.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedRightSenderStrategy
        (right.lane.realization.entry right.lane.realization.pivot
          ).lambdaOfStrategy) ∧
    ∀ (leftMember : {root // root ∈ left.lane.source.1})
      (rightMember : {root // root ∈ right.lane.source.1})
      (row : PairedEntryRow),
      procOnePairedEntryRightReceiverForRow strategy
          (left.lane.realization.entry leftMember) row =
        procOnePairedEntryRightReceiverForRow strategy
          (right.lane.realization.entry rightMember) row

/-- Active-left complete physical behavior. -/
def ProfiledOpenIndexedActiveLeftCompleteBehaviorEq
    (left right : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy
      hwin basis (I := I)) : Prop :=
  (pairedLeftSenderStrategy
        (left.lane.realization.entry left.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedLeftSenderStrategy
        (right.lane.realization.entry right.lane.realization.pivot
          ).lambdaOfStrategy) ∧
    ∀ (leftMember : {root // root ∈ left.lane.source.1})
      (rightMember : {root // root ∈ right.lane.source.1})
      (row : PairedEntryRow),
      procTwoPairedEntryLeftReceiverForRow strategy
          (left.lane.realization.entry leftMember) row =
        procTwoPairedEntryLeftReceiverForRow strategy
          (right.lane.realization.entry rightMember) row

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] in
theorem procOnePairedEntry_rightReceiverForRow_eq_of_fresh_view_eq
    (left right : ProcOnePairedEntryRep strategy)
    (leftFresh : ProcOneViewClassChildProvenance strategy left)
    (rightFresh : ProcOneViewClassChildProvenance strategy right)
    (hview : currentView Proc.one left.leftHistory =
      currentView Proc.one right.leftHistory)
    (row : PairedEntryRow) :
    procOnePairedEntryRightReceiverForRow strategy left row =
      procOnePairedEntryRightReceiverForRow strategy right row := by
  rcases leftFresh with
    ⟨leftIndex, leftEntry, leftPast, leftInput, leftCandidate, hleft⟩
  rcases rightFresh with
    ⟨rightIndex, rightEntry, rightPast, rightInput, rightCandidate, hright⟩
  subst left
  subst right
  have hrows := procOneViewClassChildren_row_currentViews_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput leftCandidate
      rightCandidate hview row
  cases row <;>
    exact blockReceiverTwo_eq_of_currentViews_eq strategy _ _ hrows.1 hrows.2

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited In₂] in
theorem procTwoPairedEntry_leftReceiverForRow_eq_of_fresh_view_eq
    (left right : ProcTwoPairedEntryRep strategy)
    (leftFresh : ProcTwoViewClassChildProvenance strategy left)
    (rightFresh : ProcTwoViewClassChildProvenance strategy right)
    (hview : currentView Proc.two left.rightHistory =
      currentView Proc.two right.rightHistory)
    (row : PairedEntryRow) :
    procTwoPairedEntryLeftReceiverForRow strategy left row =
      procTwoPairedEntryLeftReceiverForRow strategy right row := by
  rcases leftFresh with
    ⟨leftIndex, leftEntry, leftPast, leftInput, leftCandidate, hleft⟩
  rcases rightFresh with
    ⟨rightIndex, rightEntry, rightPast, rightInput, rightCandidate, hright⟩
  subst left
  subst right
  have hrows := procTwoViewClassChildren_row_currentViews_eq_of_view_eq
    leftEntry rightEntry leftPast rightPast leftInput rightInput leftCandidate
      rightCandidate hview row
  cases row <;>
    exact blockReceiverOne_eq_of_currentViews_eq strategy _ _ hrows.1 hrows.2

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

/-- Shape-free right fibre equality fixes every member's whole blind sender
and every member pair's whole physical receiver, for both old-history rows. -/
theorem profiledOpenIndexedActiveRightLocalFibreRel_completeBehavior
    {left right : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      left right) :
    (pairedRightSenderStrategy
        (left.lane.realization.entry left.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedRightSenderStrategy
        (right.lane.realization.entry right.lane.realization.pivot
          ).lambdaOfStrategy) ∧
      ∀ (leftMember : {root // root ∈ left.lane.source.1})
        (rightMember : {root // root ∈ right.lane.source.1})
        (row : PairedEntryRow),
        procOnePairedEntryRightReceiverForRow strategy
            (left.lane.realization.entry leftMember) row =
          procOnePairedEntryRightReceiverForRow strategy
            (right.lane.realization.entry rightMember) row := by
  have hpivot : currentView Proc.one
        (left.lane.realization.entry left.lane.realization.pivot).leftHistory =
      currentView Proc.one
        (right.lane.realization.entry right.lane.realization.pivot
          ).leftHistory := hrel
  constructor
  · unfold pairedRightSenderStrategy
    exact blockSenderOne_eq_of_view_eq strategy hpivot
  · intro leftMember rightMember row
    have hview : currentView Proc.one
          (left.lane.realization.entry leftMember).leftHistory =
        currentView Proc.one
          (right.lane.realization.entry rightMember).leftHistory :=
      (left.lane.realization.view_eq leftMember).trans
        (hpivot.trans (right.lane.realization.view_eq rightMember).symm)
    exact procOnePairedEntry_rightReceiverForRow_eq_of_fresh_view_eq strategy
      (left.lane.realization.entry leftMember)
      (right.lane.realization.entry rightMember) (left.fresh A strategy hwin
        basis leftMember) (right.fresh A strategy hwin basis rightMember)
      hview row

/-- The same theorem packaged as the behavior relation consumed by later
shape-free bank code. -/
theorem profiledOpenIndexedActiveRightCompleteBehaviorEq_of_rel
    {left right : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      left right) :
    ProfiledOpenIndexedActiveRightCompleteBehaviorEq A strategy hwin basis
      left right :=
  profiledOpenIndexedActiveRightLocalFibreRel_completeBehavior A strategy hwin
    basis hrel

/-- Adding any proof-side decoration (in particular a hidden parity control)
does not weaken the behavioral conclusion, because the relation and behavior
both project to the literal active point. -/
theorem profiledOpenIndexedActiveRightCompleteBehaviorEq_of_decoratedRel
    {Control : Type*}
    {left right :
      ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
          (I := I) ×
        Control}
    (hrel : ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      left.1 right.1) :
    ProfiledOpenIndexedActiveRightCompleteBehaviorEq A strategy hwin basis
      left.1 right.1 :=
  profiledOpenIndexedActiveRightCompleteBehaviorEq_of_rel A strategy hwin basis
    hrel

/-- Shape-free left mirror. -/
theorem profiledOpenIndexedActiveLeftLocalFibreRel_completeBehavior
    {left right : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      left right) :
    (pairedLeftSenderStrategy
        (left.lane.realization.entry left.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedLeftSenderStrategy
        (right.lane.realization.entry right.lane.realization.pivot
          ).lambdaOfStrategy) ∧
      ∀ (leftMember : {root // root ∈ left.lane.source.1})
        (rightMember : {root // root ∈ right.lane.source.1})
        (row : PairedEntryRow),
        procTwoPairedEntryLeftReceiverForRow strategy
            (left.lane.realization.entry leftMember) row =
          procTwoPairedEntryLeftReceiverForRow strategy
            (right.lane.realization.entry rightMember) row := by
  have hpivot : currentView Proc.two
        (left.lane.realization.entry left.lane.realization.pivot).rightHistory =
      currentView Proc.two
        (right.lane.realization.entry right.lane.realization.pivot
          ).rightHistory := hrel
  constructor
  · unfold pairedLeftSenderStrategy
    exact blockSenderTwo_eq_of_view_eq strategy hpivot
  · intro leftMember rightMember row
    have hview : currentView Proc.two
          (left.lane.realization.entry leftMember).rightHistory =
        currentView Proc.two
          (right.lane.realization.entry rightMember).rightHistory :=
      (left.lane.realization.view_eq leftMember).trans
        (hpivot.trans (right.lane.realization.view_eq rightMember).symm)
    exact procTwoPairedEntry_leftReceiverForRow_eq_of_fresh_view_eq strategy
      (left.lane.realization.entry leftMember)
      (right.lane.realization.entry rightMember) (left.fresh A strategy hwin
        basis leftMember) (right.fresh A strategy hwin basis rightMember)
      hview row

theorem profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_rel
    {left right : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      left right) :
    ProfiledOpenIndexedActiveLeftCompleteBehaviorEq A strategy hwin basis
      left right :=
  profiledOpenIndexedActiveLeftLocalFibreRel_completeBehavior A strategy hwin
    basis hrel

theorem profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_decoratedRel
    {Control : Type*}
    {left right :
      ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
          (I := I) ×
        Control}
    (hrel : ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      left.1 right.1) :
    ProfiledOpenIndexedActiveLeftCompleteBehaviorEq A strategy hwin basis
      left.1 right.1 :=
  profiledOpenIndexedActiveLeftCompleteBehaviorEq_of_rel A strategy hwin basis
    hrel

end

/-! ## The exact right-only/both and left-only/both corollaries -/

def ProfiledOpenIndexedRightOnlyBothSameRuntimeObservation
    (rightOnly : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) : Prop :=
  ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
    (rightOnly.toActiveRight A strategy hwin basis)
    (both.toActiveRight A strategy hwin basis)

def ProfiledOpenIndexedLeftOnlyBothSameRuntimeObservation
    (leftOnly : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I)) : Prop :=
  ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
    (leftOnly.toActiveLeft A strategy hwin basis)
    (both.toActiveLeft A strategy hwin basis)

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedRightOnlyBoth_sender_eq
    (rightOnly : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hobs : ProfiledOpenIndexedRightOnlyBothSameRuntimeObservation A strategy
      hwin basis rightOnly both) :
    pairedRightSenderStrategy
        (rightOnly.lane.realization.entry rightOnly.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedRightSenderStrategy
        (both.rightLane.realization.entry both.rightLane.realization.pivot
          ).lambdaOfStrategy :=
  (profiledOpenIndexedActiveRightLocalFibreRel_completeBehavior A strategy hwin
    basis hobs).1

theorem profiledOpenIndexedRightOnlyBoth_receiver_eq
    (rightOnly : ProfiledOpenIndexedRightOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hobs : ProfiledOpenIndexedRightOnlyBothSameRuntimeObservation A strategy
      hwin basis rightOnly both)
    (rightOnlyMember : {root // root ∈ rightOnly.lane.source.1})
    (bothMember : {root // root ∈ both.rightLane.source.1})
    (row : PairedEntryRow) :
    procOnePairedEntryRightReceiverForRow strategy
        (rightOnly.lane.realization.entry rightOnlyMember) row =
      procOnePairedEntryRightReceiverForRow strategy
        (both.rightLane.realization.entry bothMember) row :=
  (profiledOpenIndexedActiveRightLocalFibreRel_completeBehavior A strategy hwin
    basis hobs).2 rightOnlyMember bothMember row

theorem profiledOpenIndexedLeftOnlyBoth_sender_eq
    (leftOnly : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hobs : ProfiledOpenIndexedLeftOnlyBothSameRuntimeObservation A strategy
      hwin basis leftOnly both) :
    pairedLeftSenderStrategy
        (leftOnly.lane.realization.entry leftOnly.lane.realization.pivot
          ).lambdaOfStrategy =
      pairedLeftSenderStrategy
        (both.leftLane.realization.entry both.leftLane.realization.pivot
          ).lambdaOfStrategy :=
  (profiledOpenIndexedActiveLeftLocalFibreRel_completeBehavior A strategy hwin
    basis hobs).1

theorem profiledOpenIndexedLeftOnlyBoth_receiver_eq
    (leftOnly : ProfiledOpenIndexedLeftOnlyFreshSemanticPoint A strategy hwin
      basis (I := I))
    (both : ProfiledOpenIndexedLiveFreshSemanticPoint A strategy hwin basis
      (I := I))
    (hobs : ProfiledOpenIndexedLeftOnlyBothSameRuntimeObservation A strategy
      hwin basis leftOnly both)
    (leftOnlyMember : {root // root ∈ leftOnly.lane.source.1})
    (bothMember : {root // root ∈ both.leftLane.source.1})
    (row : PairedEntryRow) :
    procTwoPairedEntryLeftReceiverForRow strategy
        (leftOnly.lane.realization.entry leftOnlyMember) row =
      procTwoPairedEntryLeftReceiverForRow strategy
        (both.leftLane.realization.entry bothMember) row :=
  (profiledOpenIndexedActiveLeftLocalFibreRel_completeBehavior A strategy hwin
    basis hobs).2 leftOnlyMember bothMember row

end

/-! ## Shape-free source-indexed provenance extraction

The presentation below is the operational payoff of the preceding theorem.
One finite fibre now contains every optional semantic state with the same
active-side view, irrespective of the opposite lane's activity.  The generic
root-family construction therefore rationalizes right-only and both-active
requirements in one controller rather than comparing two independently
chosen controllers afterwards.
-/

variable {Descriptor : Type (max i u v x y s)}
variable [Fintype Descriptor] [DecidableEq Descriptor]

section ActiveRight

variable (semanticDescriptor :
  ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
    (I := I) → Descriptor)

/-- The finite, shape-saturated descriptor image at one active-right view. -/
noncomputable def profiledOpenActiveRightDescriptorImage
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) : Finset Descriptor :=
  semanticFibreImage semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I)) source

omit [DecidableEq Descriptor] [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Same-view active-right anchors have literally the same projected finite
class.  In particular a right-only anchor and a both-active anchor are not
separated by their proof-side shape. -/
theorem profiledOpenActiveRightDescriptorImage_eq_of_rel
    {left right : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      left right) :
    profiledOpenActiveRightDescriptorImage A strategy hwin basis
        semanticDescriptor left =
      profiledOpenActiveRightDescriptorImage A strategy hwin basis
        semanticDescriptor right :=
  semanticFibreImage_eq_of_rel semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveRightLocalFibreRel_fibresAgree A strategy hwin
      basis) hrel

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveRightDescriptor_mem_image
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    semanticDescriptor source ∈
      profiledOpenActiveRightDescriptorImage A strategy hwin basis
        semanticDescriptor source :=
  descriptor_mem_semanticFibreImage semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveRightLocalFibreRel_reflexive A strategy hwin
      basis).refl source

abbrev ProfiledOpenActiveRightSourceFibreDescriptor
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I)) source

noncomputable instance
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenActiveRightSourceFibrePoint
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveRightSourceFibrePoint_rel
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis source
      (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
        semanticDescriptor source member) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveRightSourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    semanticDescriptor
        (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) = member.1 :=
  semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenActiveRightSourceFibreSource
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenRightViewClass A :=
  (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.source

noncomputable def profiledOpenActiveRightSourceFibreRealization
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenRightRealization A strategy hwin basis
      (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.realization

noncomputable def profiledOpenActiveRightSourceFibreCurrent
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveRightLocalFibreRel_reflexive A strategy hwin
      basis).refl source

noncomputable def profiledOpenActiveRightSourceFibrePresentation
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenActiveRightSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenActiveRightSourceFibrePoint_view_eq_source
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveRightSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    profiledOpenIndexedActiveRightView A strategy hwin basis
        (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) =
      profiledOpenIndexedActiveRightView A strategy hwin basis source :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedActiveRightLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveRightView A strategy hwin basis)
    (fun hrel => hrel) source member

theorem profiledOpenActiveRightSourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenActiveRightSourceFibreCurrent A strategy
    hwin basis semanticDescriptor source
  calc
    currentView Proc.one
        ((profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).leftHistory =
      profiledOpenIndexedActiveRightView A strategy hwin basis
        (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual) := by
      simpa [profiledOpenActiveRightSourceFibreRealization,
        profiledOpenIndexedActiveRightView] using
        (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).view_eq member
    _ = profiledOpenIndexedActiveRightView A strategy hwin basis source :=
      profiledOpenActiveRightSourceFibrePoint_view_eq_source A strategy hwin
        basis semanticDescriptor source actual
    _ = profiledOpenIndexedActiveRightView A strategy hwin basis
        (profiledOpenActiveRightSourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative) :=
      (profiledOpenActiveRightSourceFibrePoint_view_eq_source A strategy hwin
        basis semanticDescriptor source representative).symm
    _ = currentView Proc.one
        ((profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
          (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
            semanticDescriptor source representative).pivot).leftHistory := by
      rfl

theorem profiledOpenActiveRightSourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenRightFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenRightFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenRightFibreSenderStrategiesAgree_of_views A
      (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveRightSourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

end

noncomputable abbrev ProfiledOpenActiveRightSourceFibreProvenanceMove
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  ProfiledOpenRightPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable instance
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenActiveRightSourceFibreProvenanceMove A strategy hwin
      basis semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenActiveRightSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveRightFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenActiveRightSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenRightPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenActiveRightSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveRightSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveRightSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveRightSourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

end ActiveRight

section ActiveLeft

variable (semanticDescriptor :
  ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
    (I := I) → Descriptor)

noncomputable def profiledOpenActiveLeftDescriptorImage
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) : Finset Descriptor :=
  semanticFibreImage semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I)) source

omit [DecidableEq Descriptor] [Fintype I] [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenActiveLeftDescriptorImage_eq_of_rel
    {left right : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy
      hwin basis (I := I)}
    (hrel : ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      left right) :
    profiledOpenActiveLeftDescriptorImage A strategy hwin basis
        semanticDescriptor left =
      profiledOpenActiveLeftDescriptorImage A strategy hwin basis
        semanticDescriptor right :=
  semanticFibreImage_eq_of_rel semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveLeftLocalFibreRel_fibresAgree A strategy hwin
      basis) hrel

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveLeftDescriptor_mem_image
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    semanticDescriptor source ∈
      profiledOpenActiveLeftDescriptorImage A strategy hwin basis
        semanticDescriptor source :=
  descriptor_mem_semanticFibreImage semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveLeftLocalFibreRel_reflexive A strategy hwin
      basis).refl source

abbrev ProfiledOpenActiveLeftSourceFibreDescriptor
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  SemanticFibreAt semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I)) source

noncomputable instance
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenActiveLeftSourceFibrePoint
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin basis
      (I := I) :=
  semanticFibreAtWitness semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveLeftSourceFibrePoint_rel
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis source
      (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
        semanticDescriptor source member) :=
  semanticFibreAtWitness_rel semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I)) source member

omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor] in
theorem profiledOpenActiveLeftSourceFibrePoint_descriptor
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    semanticDescriptor
        (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) = member.1 :=
  semanticFibreAtWitness_descriptor semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I)) source member

noncomputable def profiledOpenActiveLeftSourceFibreSource
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) : ProfiledOpenLeftViewClass A :=
  (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.source

noncomputable def profiledOpenActiveLeftSourceFibreRealization
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    ProfiledOpenLeftRealization A strategy hwin basis
      (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source member) :=
  (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
    semanticDescriptor source member).lane.realization

noncomputable def profiledOpenActiveLeftSourceFibreCurrent
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source :=
  semanticFibreAtCurrent semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveLeftLocalFibreRel_reflexive A strategy hwin
      basis).refl source

noncomputable def profiledOpenActiveLeftSourceFibrePresentation
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenFiniteFibrePresentation
      (ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
        semanticDescriptor source)
      (ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s}) where
  classOf := fun _ => ULift.up ()
  representative := fun _ =>
    profiledOpenActiveLeftSourceFibreCurrent A strategy hwin basis
      semanticDescriptor source
  representative_class := by intro c; exact Subsingleton.elim _ _

section
omit [Fintype I] [Inhabited Out₁] [Inhabited Out₂] [DecidableEq Descriptor]

theorem profiledOpenActiveLeftSourceFibrePoint_view_eq_source
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I))
    (member : ProfiledOpenActiveLeftSourceFibreDescriptor A strategy hwin basis
      semanticDescriptor source) :
    profiledOpenIndexedActiveLeftView A strategy hwin basis
        (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source member) =
      profiledOpenIndexedActiveLeftView A strategy hwin basis source :=
  semanticFibreAtWitness_behavior_eq semanticDescriptor
    (ProfiledOpenIndexedActiveLeftLocalFibreRel A strategy hwin basis
      (I := I))
    (profiledOpenIndexedActiveLeftView A strategy hwin basis)
    (fun hrel => hrel) source member

theorem profiledOpenActiveLeftSourceFibreSenderViewsAgree
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftFibreSenderViewsAgree.{u, v, x, y, s, i} A
      (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) := by
  intro c descriptor member
  let actual := descriptor.1
  let representative := profiledOpenActiveLeftSourceFibreCurrent A strategy
    hwin basis semanticDescriptor source
  calc
    currentView Proc.two
        ((profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).entry member).rightHistory =
      profiledOpenIndexedActiveLeftView A strategy hwin basis
        (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source actual) := by
      simpa [profiledOpenActiveLeftSourceFibreRealization,
        profiledOpenIndexedActiveLeftView] using
        (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
          semanticDescriptor source actual).view_eq member
    _ = profiledOpenIndexedActiveLeftView A strategy hwin basis source :=
      profiledOpenActiveLeftSourceFibrePoint_view_eq_source A strategy hwin
        basis semanticDescriptor source actual
    _ = profiledOpenIndexedActiveLeftView A strategy hwin basis
        (profiledOpenActiveLeftSourceFibrePoint A strategy hwin basis
          semanticDescriptor source representative) :=
      (profiledOpenActiveLeftSourceFibrePoint_view_eq_source A strategy hwin
        basis semanticDescriptor source representative).symm
    _ = currentView Proc.two
        ((profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
          semanticDescriptor source representative).entry
          (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
            semanticDescriptor source representative).pivot).rightHistory := by
      rfl

theorem profiledOpenActiveLeftSourceFibreCommonSenderWins
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenLeftFibreCommonSenderWins.{u, v, x, y, s, i} A
      (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source) :=
  profiledOpenLeftFibreCommonSenderWins_of_senderStrategiesAgree A
    (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenLeftFibreSenderStrategiesAgree_of_views A
      (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
        semanticDescriptor source)
      strategy hwin basis
      (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
        semanticDescriptor source)
      (profiledOpenActiveLeftSourceFibreSenderViewsAgree A strategy hwin basis
        semanticDescriptor source))

end

noncomputable abbrev ProfiledOpenActiveLeftSourceFibreProvenanceMove
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :=
  ProfiledOpenLeftPinnedFibreProvenanceMove.{u, v, x, y, s, i} A
    (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

noncomputable instance
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    Fintype (ProfiledOpenActiveLeftSourceFibreProvenanceMove A strategy hwin
      basis semanticDescriptor source) := by
  classical
  infer_instance

noncomputable def profiledOpenActiveLeftSourceFibreProvenanceMoveOfWinning
    (source : ProfiledOpenIndexedActiveLeftFreshSemanticPoint A strategy hwin
      basis (I := I)) :
    ProfiledOpenActiveLeftSourceFibreProvenanceMove A strategy hwin basis
      semanticDescriptor source :=
  profiledOpenLeftPinnedFibreProvenanceMoveOfCommonSenderWins A
    (profiledOpenActiveLeftSourceFibrePresentation A strategy hwin basis
      semanticDescriptor source)
    strategy hwin basis
    (profiledOpenActiveLeftSourceFibreSource A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveLeftSourceFibreRealization A strategy hwin basis
      semanticDescriptor source)
    (profiledOpenActiveLeftSourceFibreCommonSenderWins A strategy hwin basis
      semanticDescriptor source)
    (ULift.up () : ProfiledOpenOptionalSourceFibreClass.{i, u, v, x, y, s})

end ActiveLeft

end

end DetParityAutomaton

end DistributedSynthesis
