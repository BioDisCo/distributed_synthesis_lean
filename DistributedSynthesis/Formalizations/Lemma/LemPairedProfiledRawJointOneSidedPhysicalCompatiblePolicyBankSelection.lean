/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBank

/-!
# A replaceable selection of physical-compatible policies

The original policy bank chooses an arbitrary accepting rational policy at
each realizable root.  A later rollback-aware regularization must be able to
replace that choice.  This file isolates the dependent policy-selection
parameter and gives the root, successor, reachability, and target-resolution
operations relative to it.  The old bank is retained as the default
selection, so the existing development remains a specialization of this API.

No semantic safety property is assumed here.  In particular, merely being a
`PolicySelection` does not imply rollback or realizable-monitor acceptance.
-/

namespace DistributedSynthesis

universe u v x y s

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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev BankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleBankControl A strategy hwin

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

/-- One accepting rational policy for every realizable root key.  This is the
replaceable datum that the rollback-aware regularization must construct. -/
abbrev ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection :=
  ∀ key : RootKey A strategy,
    ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
      key.1.1 key.1.2

/-- The previously constructed arbitrary bank, viewed as a policy selection.
It is useful as a regression specialization but carries no rollback-safety
claim. -/
noncomputable def
    profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection :
    ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
      hwin :=
  fun key ↦
    profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin key

/-- A pointwise property of the policies in a selection. -/
def ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection.Satisfies
    (Good : ∀ key : RootKey A strategy,
      ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
        key.1.1 key.1.2 → Prop)
    (selection :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin) : Prop :=
  ∀ key, Good key (selection key)

/-- Independent witnesses at each root key assemble into one dependent policy
selection.  No cross-key product or compatibility premise is needed. -/
theorem
    exists_profiledRawJointOneSidedPhysicalCompatiblePolicySelection_of_pointwise
    (Good : ∀ key : RootKey A strategy,
      ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
        key.1.1 key.1.2 → Prop)
    (hexists : ∀ key, ∃ policy, Good key policy) :
    ∃ selection :
        ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
          hwin,
      selection.Satisfies A strategy hwin Good := by
  choose selection hselection using hexists
  exact ⟨selection, hselection⟩

/-- Conversely, a safe selection contains the required witness at every
individual key. -/
theorem
    forall_exists_of_profiledRawJointOneSidedPhysicalCompatiblePolicySelection
    (Good : ∀ key : RootKey A strategy,
      ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
        key.1.1 key.1.2 → Prop)
    (selection :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (hselection : selection.Satisfies A strategy hwin Good) :
    ∀ key, ∃ policy, Good key policy := by
  intro key
  exact ⟨selection key, hselection key⟩

namespace ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

variable
  (selection :
    ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy hwin)

/-- Two selections agree at one root key when they choose the same rational
policy there.  Fixed-key locality will make this the only equality needed to
assemble independently regularized fibres. -/
def AgreeAt
    (other :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (key : RootKey A strategy) : Prop :=
  selection key = other key

/-- Enter the policy selected at `key`. -/
noncomputable def root (key : RootKey A strategy) :
    BankControl A strategy hwin :=
  ⟨key, (selection key).run []⟩

/-- Advance inside the selected policy while retaining the root key. -/
noncomputable def successor (state : BankControl A strategy hwin)
    (childCode : LinkedCode A) : BankControl A strategy hwin :=
  ⟨state.1, (selection state.1).successor state.2 childCode⟩

@[simp] theorem root_index (key : RootKey A strategy) :
    (selection.root A strategy hwin key).1 = key :=
  rfl

@[simp] theorem successor_index (state : BankControl A strategy hwin)
    (childCode : LinkedCode A) :
    (selection.successor A strategy hwin state childCode).1 = state.1 :=
  rfl

/-- The selected rational root exposes the public data of its key. -/
theorem root_data (key : RootKey A strategy) :
    (selection.root A strategy hwin key).2.1 = key.1 := by
  exact congrArg Prod.fst (selection key).accepts.1.1

/-- Reachability relative to the replaceable selected policy. -/
abbrev Reachable (state : BankControl A strategy hwin) : Prop :=
  ProfiledRawJointOneSidedPhysicalCompatibleReachable A strategy hwin
    state.1.1.1 state.1.1.2 (selection state.1) state.2

theorem root_reachable (key : RootKey A strategy) :
    selection.Reachable A strategy hwin
      (selection.root A strategy hwin key) :=
  ⟨[], rfl⟩

theorem successor_reachable
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (childCode : LinkedCode A) :
    selection.Reachable A strategy hwin
      (selection.successor A strategy hwin state childCode) :=
  profiledRawJointOneSidedPhysicalCompatible_successor_reachable A strategy
    hwin state.1.1.1 state.1.1.2 (selection state.1) state.2 hreachable
      childCode

/-- Reachability depends only on the policy chosen at the state's key. -/
theorem reachable_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (hkey : state.1 = key)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.Reachable A strategy hwin state ↔
      other.Reachable A strategy hwin state := by
  subst key
  unfold AgreeAt at hagrees
  change
    ProfiledRawJointOneSidedPhysicalCompatibleReachable A strategy hwin
        state.1.1.1 state.1.1.2 (selection state.1) state.2 ↔
      ProfiledRawJointOneSidedPhysicalCompatibleReachable A strategy hwin
        state.1.1.1 state.1.1.2 (other state.1) state.2
  rw [hagrees]

/-- A linked child realizes a bare target relative to `selection`.  Besides
the semantic source equations, the last field pins the child to the selected
policy's literal successor table. -/
def ChildRealizes
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A) : Prop :=
  ∃ move : SourceFreeBeliefParentLinkedMove
      (Direction := ProfiledRawJointActualDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
      (Annotation := PhysicalAnnotation A),
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ProfiledRawJointActualDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂),
        source.code A = state.2.1.1 ∧
          source.move A = move.1 ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            source state.2.1.2 ∧
          (∀ direction,
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
                source state.2.1.2 direction =
              move.2 direction) ∧
          childCode = sourceFreeBeliefParentLinkedNext
            (profiledRawJointOneSidedNext A) state.2.1 move actual ∧
          childCode.1 = target ∧
          (selection state.1).successor state.2 childCode =
            (childCode,
            (sourceFreeBeliefParentLinkedCodeParityDPA
                (Annotation := PhysicalAnnotation A)
                (profiledRawJointOneSidedCodeParityDPA A
                  state.1.1.1)).step state.2.2 childCode)

/-- Child realization depends only on the policy chosen at the state's key. -/
theorem childRealizes_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.ChildRealizes A strategy hwin state target childCode ↔
      other.ChildRealizes A strategy hwin state target childCode := by
  subst key
  unfold AgreeAt at hagrees
  unfold ChildRealizes
  rw [hagrees]

/-- A realizing child is a literal semantic child with the requested bare
code and the annotation produced by that same semantic step. -/
theorem ChildRealizes.exists_child
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A)
    (hrealizes : selection.ChildRealizes A strategy hwin state target
      childCode) :
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      ∃ actual : ProfiledRawJointActualDirection
          (I := Unit) (In₁ := In₁) (In₂ := In₂),
        (source.step A actual).code A = target ∧
          childCode.2 =
            profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
              source state.2.1.2 actual ∧
          ProfiledRawJointOneSidedPhysicalAnnotationCompatible A strategy
            (source.step A actual) childCode.2 := by
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, _hcompatible, hchildren,
      hchildCode, hbare, _hsuccessor⟩
  have hstepCode : (source.step A actual).code A = childCode.1 := by
    rw [ProfiledRawJointOneSidedSemanticState.step_code]
    rw [hcode, hmove, hchildCode]
    rfl
  have hannotation :
      childCode.2 =
        profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
          source state.2.1.2 actual := by
    rw [hchildCode]
    exact (hchildren actual).symm
  refine ⟨source, actual, hstepCode.trans hbare, hannotation, ?_⟩
  rw [hannotation]
  exact
    profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
      hwin source state.2.1.2 actual

/-- Total target resolver relative to a supplied policy selection. -/
noncomputable def resolveTarget
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) : LinkedCode A := by
  classical
  exact if h : ∃ childCode,
      selection.ChildRealizes A strategy hwin state target childCode then
    Classical.choose h
  else
    state.2.1

theorem resolveTarget_realizes
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      selection.ChildRealizes A strategy hwin state target childCode) :
    selection.ChildRealizes A strategy hwin state target
      (selection.resolveTarget A strategy hwin state target) := by
  classical
  simp only [resolveTarget]
  split
  next h => exact Classical.choose_spec h
  next h => exact (h hexists).elim

/-- Deterministic target resolution is extensional at a fixed key. -/
theorem resolveTarget_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (hkey : state.1 = key)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.resolveTarget A strategy hwin state target =
      other.resolveTarget A strategy hwin state target := by
  subst key
  unfold AgreeAt at hagrees
  unfold resolveTarget ChildRealizes
  rw [hagrees]

/-- The selected successor table is likewise extensional at a fixed key. -/
theorem successor_congr_at
    (other :
      ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection A strategy
        hwin)
    (key : RootKey A strategy)
    (state : BankControl A strategy hwin)
    (hkey : state.1 = key)
    (childCode : LinkedCode A)
    (hagrees : selection.AgreeAt A strategy hwin other key) :
    selection.successor A strategy hwin state childCode =
      other.successor A strategy hwin state childCode := by
  subst key
  unfold AgreeAt at hagrees
  unfold successor
  rw [hagrees]

/-- The deterministic resolver preserves every bank invariant exposed by the
generic selection interface. -/
theorem resolveTarget_spec
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (hexists : ∃ childCode,
      selection.ChildRealizes A strategy hwin state target childCode) :
    let childCode := selection.resolveTarget A strategy hwin state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin state target childCode ∧
      (selection.successor A strategy hwin state childCode).1 = state.1 ∧
      selection.Reachable A strategy hwin
        (selection.successor A strategy hwin state childCode) := by
  dsimp only
  have hrealizes :=
    selection.resolveTarget_realizes A strategy hwin state target hexists
  rcases hrealizes with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
      hchildCode, hbare, hsuccessor⟩
  refine ⟨hbare,
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren,
      hchildCode, hbare, hsuccessor⟩,
    rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin state hreachable _

/-! ## Installed-table target closure for a supplied selection -/

/-- Every target allowed by the installed right table is realized by a
linked child code of the policy selected at the state's fixed root key. -/
theorem exists_rightTargetSuccessor
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        selection.ChildRealizes A strategy hwin state target childCode ∧
        (selection.successor A strategy hwin state childCode).1 = state.1 ∧
        selection.Reachable A strategy hwin
          (selection.successor A strategy hwin state childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleRightTargetSuccessor A
        strategy hwin state.1.1.1 state.1.1.2 (selection state.1) state.2
        hreachable currentCode hcurrentCode root hroot phaseMove hphaseMove
        target htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 move actual
  have hrealizes :
      selection.ChildRealizes A strategy hwin state target childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin state hreachable
    childCode

/-- Deterministic right-target closure, relative to `selection`. -/
theorem resolveRightTarget_spec
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (phaseMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.1 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointRightPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode := selection.resolveTarget A strategy hwin state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin state target childCode ∧
      (selection.successor A strategy hwin state childCode).1 = state.1 ∧
      selection.Reachable A strategy hwin
        (selection.successor A strategy hwin state childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    selection.exists_rightTargetSuccessor A strategy hwin state hreachable
      currentCode hcurrentCode root hroot phaseMove hphaseMove target htarget
  exact selection.resolveTarget_spec A strategy hwin state hreachable target
    ⟨childCode, hrealizes⟩

/-- Left-orientation mirror of installed-table target closure. -/
theorem exists_leftTargetSuccessor
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    ∃ childCode : LinkedCode A,
      childCode.1 = target ∧
        selection.ChildRealizes A strategy hwin state target childCode ∧
        (selection.successor A strategy hwin state childCode).1 = state.1 ∧
        selection.Reachable A strategy hwin
          (selection.successor A strategy hwin state childCode) := by
  rcases
      exists_profiledRawJointOneSidedPhysicalCompatibleLeftTargetSuccessor A
        strategy hwin state.1.1.1 state.1.1.2 (selection state.1) state.2
        hreachable currentCode hcurrentCode root hroot phaseMove hphaseMove
        target htarget with
    ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, _hside,
      _hactualTarget, _hchildAnnotation, hchildBare, hsuccessor⟩
  let childCode := sourceFreeBeliefParentLinkedNext
    (profiledRawJointOneSidedNext A) state.2.1 move actual
  have hrealizes :
      selection.ChildRealizes A strategy hwin state target childCode := by
    exact ⟨move, source, actual, hcode, hmove, hcompatible, hchildren, rfl,
      hchildBare, hsuccessor⟩
  refine ⟨childCode, hchildBare, hrealizes, rfl, ?_⟩
  exact selection.successor_reachable A strategy hwin state hreachable
    childCode

/-- Deterministic left-target closure, relative to `selection`. -/
theorem resolveLeftTarget_spec
    (state : BankControl A strategy hwin)
    (hreachable : selection.Reachable A strategy hwin state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcurrentCode : state.2.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (phaseMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hphaseMove : state.2.1.2.2 = some phaseMove)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (htarget : profiledRawJointLeftPhysicalSiblingAllowed A phaseMove.1
      target) :
    let childCode := selection.resolveTarget A strategy hwin state target
    childCode.1 = target ∧
      selection.ChildRealizes A strategy hwin state target childCode ∧
      (selection.successor A strategy hwin state childCode).1 = state.1 ∧
      selection.Reachable A strategy hwin
        (selection.successor A strategy hwin state childCode) := by
  obtain ⟨childCode, _hbare, hrealizes, _hindex, _hnext⟩ :=
    selection.exists_leftTargetSuccessor A strategy hwin state hreachable
      currentCode hcurrentCode root hroot phaseMove hphaseMove target htarget
  exact selection.resolveTarget_spec A strategy hwin state hreachable target
    ⟨childCode, hrealizes⟩

@[simp] theorem default_root
    (key : RootKey A strategy) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).root A strategy hwin key =
      profiledRawJointOneSidedPhysicalCompatibleBankRoot A strategy hwin key :=
  rfl

@[simp] theorem default_successor
    (state : BankControl A strategy hwin) (childCode : LinkedCode A) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).successor A strategy hwin state childCode =
      profiledRawJointOneSidedPhysicalCompatibleBankSuccessor A strategy hwin
        state childCode :=
  rfl

@[simp] theorem default_reachable
    (state : BankControl A strategy hwin) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).Reachable A strategy hwin state ↔
      ProfiledRawJointOneSidedPhysicalCompatibleBankReachable A strategy hwin
        state :=
  Iff.rfl

@[simp] theorem default_childRealizes
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit))
    (childCode : LinkedCode A) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).ChildRealizes A strategy hwin state target childCode ↔
      ProfiledRawJointOneSidedPhysicalCompatibleBankChildRealizes A strategy
        hwin state target childCode :=
  Iff.rfl

@[simp] theorem default_resolveTarget
    (state : BankControl A strategy hwin)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    (profiledRawJointOneSidedPhysicalCompatibleDefaultPolicySelection A
      strategy hwin).resolveTarget A strategy hwin state target =
      profiledRawJointOneSidedPhysicalCompatibleBankResolveTarget A strategy
        hwin state target := by
  rfl

end ProfiledRawJointOneSidedPhysicalCompatiblePolicySelection

end

end DetParityAutomaton

end DistributedSynthesis
