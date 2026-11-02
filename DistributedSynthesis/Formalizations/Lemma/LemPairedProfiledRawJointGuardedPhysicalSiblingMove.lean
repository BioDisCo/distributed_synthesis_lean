/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingMove
import DistributedSynthesis.Formalizations.Lemma.LemBlockRecordMonitorFirstLetterGuard

/-!
# First-record guarded pre-policy sibling moves

A receive immediately after a common shadow is locally indistinguishable on
a repeated simultaneous round and on the first strict round.  Consequently a
shared sibling table must preserve the literal semantic root record, not only
accept the same omega objective.  This file adds the reusable finite guard at
the pre-policy sibling layer.

The complete first record is pinned before narrowing.  All later records are
still chosen by the one finite sibling controller shared by its two hidden
members.  The guard is objective data only; it supplies no graph, orientation,
leader, or member signal to a runtime process.
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

private abbrev RightReceiverOutput :=
  ProfiledRawJointTargetRightReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)

private abbrev LeftReceiverOutput :=
  ProfiledRawJointTargetLeftReceiverOutput
    (Out₁ := Out₁) (Out₂ := Out₂) (ProfiledRawJointUnitTarget A)

/-! ## Literal semantic root records -/

/-- First right record of the literal semantic sibling strategy.  The
`false` member is only a proof-side normal form; the member-independence lemma
below shows that `true` produces the same record. -/
noncomputable def profiledRawJointRightSiblingLiteralRootRecord
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (input : In₂ × In₁) :
    RealizedBlockRound In₂ In₁ (RightReceiverOutput A) Out₁ :=
  (input,
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember false [] input,
    profiledRawJointRightSiblingSender A semanticMember [] input.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Both hidden right sibling members have the same complete semantic root
record. -/
theorem profiledRawJointRightPhysicalSiblingReceiver_root_eq_false
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (input : In₂ × In₁) :
    profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member [] input =
      profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember false [] input := by
  cases member <;> rfl

/-- Finite first-record predicate used by the guarded right monitor. -/
noncomputable def profiledRawJointRightSiblingLiteralRootAllowed
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (record : RealizedBlockRound In₂ In₁ (RightReceiverOutput A) Out₁) : Bool := by
  classical
  exact decide
    (record = profiledRawJointRightSiblingLiteralRootRecord A hwin family
      direction semanticMember hmember record.1)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
theorem profiledRawJointRightSiblingLiteralRootAllowed_pairPlay
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (env : Nat → In₂ × In₁) :
    profiledRawJointRightSiblingLiteralRootAllowed A hwin family direction
      semanticMember hmember
      (pairPlay
        (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointRightSiblingSender A semanticMember) env 0) = true := by
  rw [show pairPlay
      (profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member)
      (profiledRawJointRightSiblingSender A semanticMember) env 0 =
    (env 0,
      profiledRawJointRightPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member [] (env 0),
      profiledRawJointRightSiblingSender A semanticMember [] (env 0).2) by
        rfl]
  rw [profiledRawJointRightPhysicalSiblingReceiver_root_eq_false A hwin family
    direction semanticMember hmember member (env 0)]
  simp [profiledRawJointRightSiblingLiteralRootAllowed,
    profiledRawJointRightSiblingLiteralRootRecord]

/-! ## Finite right guarded move -/

/-- All finite data defining the guarded right monitor. -/
structure ProfiledRawJointGuardedRightPhysicalSiblingDescriptor where
  base : ProfiledRawJointRightPhysicalSiblingDescriptor A
  firstAllowed :
    RealizedBlockRound In₂ In₁ (RightReceiverOutput A) Out₁ → Bool

noncomputable instance :
    Fintype (ProfiledRawJointGuardedRightPhysicalSiblingDescriptor A) := by
  classical
  letI : Fintype A.State := A.stateFinite
  letI : Fintype (ProfiledRawJointUnitTarget A) := Fintype.ofFinite _
  letI : Fintype (RightReceiverOutput A) := Fintype.ofFinite _
  letI : Fintype
      (RealizedBlockRound In₂ In₁ (RightReceiverOutput A) Out₁) :=
    Fintype.ofFinite _
  let Rep := ProfiledRawJointRightPhysicalSiblingDescriptor A ×
    (RealizedBlockRound In₂ In₁ (RightReceiverOutput A) Out₁ → Bool)
  let equiv : ProfiledRawJointGuardedRightPhysicalSiblingDescriptor A ≃ Rep :=
    { toFun := fun descriptor ↦ (descriptor.base, descriptor.firstAllowed)
      invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
      left_inv := by intro descriptor; cases descriptor; rfl
      right_inv := by intro descriptor; cases descriptor; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

abbrev profiledRawJointGuardedRightPhysicalSiblingMonitor
    (descriptor : ProfiledRawJointGuardedRightPhysicalSiblingDescriptor A)
    (_member : Bool) :=
  (profiledRawJointRightPhysicalSiblingMonitor A descriptor.base false
    ).firstLetterGuard descriptor.firstAllowed

noncomputable abbrev ProfiledRawJointGuardedRightPhysicalSiblingMove :=
  Sigma fun descriptor :
      ProfiledRawJointGuardedRightPhysicalSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointGuardedRightPhysicalSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointGuardedRightPhysicalSiblingMove A) := by
  classical
  infer_instance

noncomputable def
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (_member : Bool) :=
  finiteRootMemberController
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree false

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_eq
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (left right : Bool) :
    move.memberController A left = move.memberController A right :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_wins
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 false

/-- Construct the guarded finite table from one semantic sibling pair. -/
noncomputable def profiledRawJointGuardedRightPhysicalSiblingMoveOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember) :
    ProfiledRawJointGuardedRightPhysicalSiblingMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor : ProfiledRawJointGuardedRightPhysicalSiblingDescriptor A :=
    ⟨profiledRawJointRightPhysicalSiblingDescriptorOf A family direction
        semanticMember,
      profiledRawJointRightSiblingLiteralRootAllowed A hwin family direction
        semanticMember hmember⟩
  let receiver := profiledRawJointRightPhysicalSiblingReceiver A hwin family
    direction semanticMember hmember
  let sender := profiledRawJointRightSiblingSender A semanticMember
  have hguard : ∀ member env,
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A descriptor member
        ).WinsPlay (pairPlay (receiver member) sender env) := by
    intro member env
    exact BlockRecordMonitor.firstLetterGuard_realizable
      (profiledRawJointRightPhysicalSiblingMonitor A descriptor.base false)
      descriptor.firstAllowed (receiver member) sender
      (by
        intro arbitraryEnv
        simpa [descriptor, receiver, sender] using
          profiledRawJointRightPhysicalSiblingMonitor_realizable A hwin
            family direction semanticMember hmember member arbitraryEnv)
      (by
        intro arbitraryEnv
        simpa [descriptor, receiver, sender] using
          profiledRawJointRightSiblingLiteralRootAllowed_pairPlay A hwin
            family direction semanticMember hmember member arbitraryEnv)
      env
  let table := finiteRootFamilyTable
    (profiledRawJointGuardedRightPhysicalSiblingMonitor A descriptor)
    receiver sender hguard
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointGuardedRightPhysicalSiblingMonitor A descriptor)
      receiver sender hguard⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Every selected guarded controller satisfies its finite first-record
predicate at every possible first input. -/
theorem
    ProfiledRawJointGuardedRightPhysicalSiblingMove.memberController_root_allowed
    (move : ProfiledRawJointGuardedRightPhysicalSiblingMove A)
    (member : Bool) (input : In₂ × In₁) :
    move.1.firstAllowed
      (narrowedRecord
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member)
        ((move.memberController A member).labeledTree [])
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member
          ).initial input) = true := by
  exact BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointRightPhysicalSiblingMonitor A move.1.base false)
    move.1.firstAllowed
    (move.memberController A member).labeledTree
    (move.memberController_wins A member) input

/-- The constructed right controller's complete first record is the literal
semantic sibling record.  This is the local indistinguishability equation
needed at a repeated-`both`/first-strict receive. -/
theorem profiledRawJointGuardedRightPhysicalSiblingMoveOf_root_record
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) (input : In₂ × In₁) :
    let move := profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    narrowedRecord
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member)
        ((move.memberController A member).labeledTree [])
        (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member
          ).initial input =
      profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
        semanticMember hmember input := by
  classical
  dsimp only
  let move := profiledRawJointGuardedRightPhysicalSiblingMoveOf A hwin family
    direction semanticMember hmember
  have hallowed := move.memberController_root_allowed A member input
  change decide
      (narrowedRecord
          (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member)
          ((move.memberController A member).labeledTree [])
          (profiledRawJointGuardedRightPhysicalSiblingMonitor A move.1 member
            ).initial input =
        profiledRawJointRightSiblingLiteralRootRecord A hwin family direction
          semanticMember hmember input) = true at hallowed
  exact of_decide_eq_true hallowed

/-! ## Left mirror -/

noncomputable def profiledRawJointLeftSiblingLiteralRootRecord
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (input : In₁ × In₂) :
    RealizedBlockRound In₁ In₂ (LeftReceiverOutput A) Out₂ :=
  (input,
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
      semanticMember hmember false [] input,
    profiledRawJointLeftSiblingSender A semanticMember [] input.2)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
theorem profiledRawJointLeftPhysicalSiblingReceiver_root_eq_false
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (input : In₁ × In₂) :
    profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member [] input =
      profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember false [] input := by
  cases member <;> rfl

noncomputable def profiledRawJointLeftSiblingLiteralRootAllowed
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (record : RealizedBlockRound In₁ In₂ (LeftReceiverOutput A) Out₂) : Bool := by
  classical
  exact decide
    (record = profiledRawJointLeftSiblingLiteralRootRecord A hwin family
      direction semanticMember hmember record.1)

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] in
theorem profiledRawJointLeftSiblingLiteralRootAllowed_pairPlay
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (env : Nat → In₁ × In₂) :
    profiledRawJointLeftSiblingLiteralRootAllowed A hwin family direction
      semanticMember hmember
      (pairPlay
        (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
          semanticMember hmember member)
        (profiledRawJointLeftSiblingSender A semanticMember) env 0) = true := by
  rw [show pairPlay
      (profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member)
      (profiledRawJointLeftSiblingSender A semanticMember) env 0 =
    (env 0,
      profiledRawJointLeftPhysicalSiblingReceiver A hwin family direction
        semanticMember hmember member [] (env 0),
      profiledRawJointLeftSiblingSender A semanticMember [] (env 0).2) by
        rfl]
  rw [profiledRawJointLeftPhysicalSiblingReceiver_root_eq_false A hwin family
    direction semanticMember hmember member (env 0)]
  simp [profiledRawJointLeftSiblingLiteralRootAllowed,
    profiledRawJointLeftSiblingLiteralRootRecord]

structure ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor where
  base : ProfiledRawJointLeftPhysicalSiblingDescriptor A
  firstAllowed :
    RealizedBlockRound In₁ In₂ (LeftReceiverOutput A) Out₂ → Bool

noncomputable instance :
    Fintype (ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor A) := by
  classical
  letI : Fintype A.State := A.stateFinite
  letI : Fintype (ProfiledRawJointUnitTarget A) := Fintype.ofFinite _
  letI : Fintype (LeftReceiverOutput A) := Fintype.ofFinite _
  letI : Fintype
      (RealizedBlockRound In₁ In₂ (LeftReceiverOutput A) Out₂) :=
    Fintype.ofFinite _
  let Rep := ProfiledRawJointLeftPhysicalSiblingDescriptor A ×
    (RealizedBlockRound In₁ In₂ (LeftReceiverOutput A) Out₂ → Bool)
  let equiv : ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor A ≃ Rep :=
    { toFun := fun descriptor ↦ (descriptor.base, descriptor.firstAllowed)
      invFun := fun descriptor ↦ ⟨descriptor.1, descriptor.2⟩
      left_inv := by intro descriptor; cases descriptor; rfl
      right_inv := by intro descriptor; cases descriptor; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

abbrev profiledRawJointGuardedLeftPhysicalSiblingMonitor
    (descriptor : ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor A)
    (_member : Bool) :=
  (profiledRawJointLeftPhysicalSiblingMonitor A descriptor.base false
    ).firstLetterGuard descriptor.firstAllowed

noncomputable abbrev ProfiledRawJointGuardedLeftPhysicalSiblingMove :=
  Sigma fun descriptor :
      ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor A ↦
    { table : FiniteRootFamilyTable
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A descriptor) //
      NarrowedAllThreadsWin
        (finiteRootFamilyMonitor
          (profiledRawJointGuardedLeftPhysicalSiblingMonitor A descriptor))
        table.toTransitionRationalTree.labeledTree }

noncomputable instance :
    Fintype (ProfiledRawJointGuardedLeftPhysicalSiblingMove A) := by
  classical
  infer_instance

noncomputable def
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (_member : Bool) :=
  finiteRootMemberController
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree false

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_eq
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (left right : Bool) :
    move.memberController A left = move.memberController A right :=
  rfl

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_wins
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (member : Bool) :
    NarrowedAllThreadsWin
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member)
      (move.memberController A member).labeledTree := by
  exact finiteRootMemberController_allThreadsWin
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1)
    move.2.1.toTransitionRationalTree move.2.2 false

noncomputable def profiledRawJointGuardedLeftPhysicalSiblingMoveOf
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember) :
    ProfiledRawJointGuardedLeftPhysicalSiblingMove A := by
  letI : Inhabited (ProfiledRawJointUnitTarget A) :=
    ⟨family.incidenceCode A⟩
  let descriptor : ProfiledRawJointGuardedLeftPhysicalSiblingDescriptor A :=
    ⟨profiledRawJointLeftPhysicalSiblingDescriptorOf A family direction
        semanticMember,
      profiledRawJointLeftSiblingLiteralRootAllowed A hwin family direction
        semanticMember hmember⟩
  let receiver := profiledRawJointLeftPhysicalSiblingReceiver A hwin family
    direction semanticMember hmember
  let sender := profiledRawJointLeftSiblingSender A semanticMember
  have hguard : ∀ member env,
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A descriptor member
        ).WinsPlay (pairPlay (receiver member) sender env) := by
    intro member env
    exact BlockRecordMonitor.firstLetterGuard_realizable
      (profiledRawJointLeftPhysicalSiblingMonitor A descriptor.base false)
      descriptor.firstAllowed (receiver member) sender
      (by
        intro arbitraryEnv
        simpa [descriptor, receiver, sender] using
          profiledRawJointLeftPhysicalSiblingMonitor_realizable A hwin
            family direction semanticMember hmember member arbitraryEnv)
      (by
        intro arbitraryEnv
        simpa [descriptor, receiver, sender] using
          profiledRawJointLeftSiblingLiteralRootAllowed_pairPlay A hwin family
            direction semanticMember hmember member arbitraryEnv)
      env
  let table := finiteRootFamilyTable
    (profiledRawJointGuardedLeftPhysicalSiblingMonitor A descriptor)
    receiver sender hguard
  exact ⟨descriptor, table,
    finiteRootFamilyTable_wins
      (profiledRawJointGuardedLeftPhysicalSiblingMonitor A descriptor)
      receiver sender hguard⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem
    ProfiledRawJointGuardedLeftPhysicalSiblingMove.memberController_root_allowed
    (move : ProfiledRawJointGuardedLeftPhysicalSiblingMove A)
    (member : Bool) (input : In₁ × In₂) :
    move.1.firstAllowed
      (narrowedRecord
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member)
        ((move.memberController A member).labeledTree [])
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member
          ).initial input) = true := by
  exact BlockRecordMonitor.firstLetterGuard_root_allowed
    (profiledRawJointLeftPhysicalSiblingMonitor A move.1.base false)
    move.1.firstAllowed
    (move.memberController A member).labeledTree
    (move.memberController_wins A member) input

theorem profiledRawJointGuardedLeftPhysicalSiblingMoveOf_root_record
    {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) (input : In₁ × In₂) :
    let move := profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin family
      direction semanticMember hmember
    narrowedRecord
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member)
        ((move.memberController A member).labeledTree [])
        (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member
          ).initial input =
      profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
        semanticMember hmember input := by
  classical
  dsimp only
  let move := profiledRawJointGuardedLeftPhysicalSiblingMoveOf A hwin family
    direction semanticMember hmember
  have hallowed := move.memberController_root_allowed A member input
  change decide
      (narrowedRecord
          (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member)
          ((move.memberController A member).labeledTree [])
          (profiledRawJointGuardedLeftPhysicalSiblingMonitor A move.1 member
            ).initial input =
        profiledRawJointLeftSiblingLiteralRootRecord A hwin family direction
          semanticMember hmember input) = true at hallowed
  exact of_decide_eq_true hallowed

end


end DetParityAutomaton

end DistributedSynthesis
