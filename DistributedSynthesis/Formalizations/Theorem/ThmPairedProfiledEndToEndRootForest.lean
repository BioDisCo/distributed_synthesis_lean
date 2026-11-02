/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemInputFreeStateIndexedGuard
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledGuardedHandoff
import DistributedSynthesis.Formalizations.Theorem.ThmPairedInitialDelayedHandoff

/-!
# One profiled run for the initial phase and every recurrent entry

This file performs the first end-to-end gluing step of the input-free route.
One outer transition represents the two possible initial homogeneous blocks.
Every finite boundary enters its own genuine recurrent profiled run, carrying
the finite pending overlap check in the reached automaton state.  The complete
forest is rationalized only after it has been assembled.

The `PairedEntryRow` component of a direction remains a latent automaton
branch.  It is never exposed as a strict-leader signal to a process.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-- The finite overlap obligation staged by an initial-left or initial-right
boundary. -/
abbrev InitialProfiledGuard :=
  ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) ⊕
    ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂)

/-- The process-one overlap table read directly from an arbitrary initial-left
block lambda. -/
def initialLeftPendingProfile
    (lambda : InitialLeftLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₁ × In₂)) (move : In₁ × In₂) :
    ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) :=
  fun nextMove => lambda.informedOne
    (past ++ [move]) (nextMove.2, nextMove.1)

/-- Mirror pending table. -/
def initialRightPendingProfile
    (lambda : InitialRightLambda
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (past : List (In₂ × In₁)) (move : In₂ × In₁) :
    ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂) :=
  fun nextMove => lambda.informedTwo
    (past ++ [move]) (nextMove.2, nextMove.1)

/-- One finite recurrent automaton carrier; its displayed initial state is
irrelevant because every forest child installs its own profiled entry. -/
noncomputable abbrev pairedProfiledForestBase :=
  pairedProfiledEntryRunAutomaton A
    (Sum.inl PUnit.unit : PairedProfiledTreeState A)

/-- A staged overlap is checked by the already proved profiled root guard. -/
def pairedInitialProfiledGuardAllowed
    (guard : InitialProfiledGuard
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂))
    (state : PairedProfiledTreeState A)
    (children : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      PairedProfiledTreeState A) : Prop :=
  match guard with
  | .inl profile => pairedProfiledEntryRootGuard A state
      profile.Matches (fun _ => True) children
  | .inr profile => pairedProfiledEntryRootGuard A state
      (fun _ => True) profile.Matches children

/-- The common outer root retains both initial lambdas.  Each finite possible
boundary must stage the delayed paired DPA target and its exact overlap table.
The row is intentionally ignored here: it is resolved only inside the paired
recurrent automaton. -/
def PairedInitialProfiledOuterAllowed
    (next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      ((pairedProfiledForestBase A).stateIndexedGuarded
        (pairedInitialProfiledGuardAllowed A)).State) : Prop :=
  ∃ left : InitialLeftLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
    ∃ right : InitialRightLambda
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂),
      InitialLeftForeverAccepts A left ∧
      InitialRightForeverAccepts A right ∧
      (∀ move : In₁ × In₂,
        left.informedOne [] move =
          right.reversingOne [] (move.2, move.1)) ∧
      (∀ move : In₁ × In₂,
        left.reversingTwo [] move =
          right.informedTwo [] (move.2, move.1)) ∧
      (∀ row past move,
        (next (.fromTwo row past move)).1 =
          some (Sum.inl (initialLeftPendingProfile left past move)) ∧
        erasePairedProfiledState A (next (.fromTwo row past move)).2 =
          initialLeftDelayedTarget A
            (initialLeftScanAfter A left past)
            (initialLeftLetterAt left past move)) ∧
      (∀ row past move,
        (next (.fromOne row past move)).1 =
          some (Sum.inr (initialRightPendingProfile right past move)) ∧
        erasePairedProfiledState A (next (.fromOne row past move)).2 =
          initialRightDelayedTarget A
            (initialRightScanAfter A right past)
            (initialRightLetterAt right past move))

/-- The one finite automaton to which the input-free rational-run theorem is
applied: common initial root, per-boundary pending guard, then the ordinary
profiled recurrent automaton. -/
noncomputable abbrev pairedInitialProfiledForestAutomaton :=
  ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).rootGuarded
    (PairedInitialProfiledOuterAllowed A)

namespace PairedStrategyMemory

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}

/-- Genuine recurrent memory selected by a possible finite initial exit. -/
def initialProfiledMemoryAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      PairedStrategyMemory A strategy
  | .fromOne _ past move => initialRightProfiledMemory A strategy past move
  | .fromTwo _ past move => initialLeftProfiledMemory A strategy past move

/-- Finite pending guard carried by that exit. -/
def initialProfiledGuardAt
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂) :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
      InitialProfiledGuard
        (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  | .fromOne _ past move =>
      .inr (initialRightNextBothProfile strategy past move)
  | .fromTwo _ past move =>
      .inl (initialLeftNextBothProfile strategy past move)

/-- The complete history-sensitive recurrent forest supplied by the original
strategy before rationalization. -/
def initialProfiledForest
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    TreeNode (PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) →
      PairedProfiledTreeState A :=
  profiledRun (A := A) (initialProfiledMemoryAt A strategy direction)

omit [DecidableEq In₁] [DecidableEq In₂] in
/-- Every subtree in the raw forest accepts under one fixed globally winning
distributed strategy. -/
theorem initialProfiledForest_accepts
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    ((pairedProfiledForestBase A).withInitial
      (initialProfiledForest A strategy direction [])).IsAcceptingRun
        InputFreeRunParityTreeAutomaton.uniqueTree
          (initialProfiledForest A strategy direction) := by
  let memory := initialProfiledMemoryAt A strategy direction
  simpa [pairedProfiledForestBase, initialProfiledForest, memory,
    InputFreeRunParityTreeAutomaton.withInitial] using
    (profiledIsAcceptingRun (A := A) memory
      (memory.foreverAccepts_of_winning (A := A) hwin)
      (switchingAccepts_of_winning hwin memory))

omit [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Every raw recurrent subtree satisfies the finite guard stored at its
root. -/
theorem initialProfiledForest_guarded
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    pairedInitialProfiledGuardAllowed A
      (initialProfiledGuardAt strategy direction)
      (initialProfiledForest A strategy direction [])
      (fun next => initialProfiledForest A strategy direction [next]) := by
  cases direction with
  | fromOne row past move =>
      let memory := initialRightProfiledMemory A strategy past move
      apply profiledRootGuard_at_run A memory
        (fun _ => True)
        (initialRightNextBothProfile strategy past move).Matches
        (memory.foreverAccepts_of_winning (A := A) hwin)
      dsimp [RootLambdaAllowed, memory, initialRightProfiledMemory]
      simpa using initialRightNextBothProfile_matches_generated
        strategy past move
  | fromTwo row past move =>
      let memory := initialLeftProfiledMemory A strategy past move
      apply profiledRootGuard_at_run A memory
        (initialLeftNextBothProfile strategy past move).Matches
        (fun _ => True)
        (memory.foreverAccepts_of_winning (A := A) hwin)
      dsimp [RootLambdaAllowed, memory, initialLeftProfiledMemory]
      simpa using initialLeftNextBothProfile_matches_generated
        strategy past move

/-- The initial restrictions of the same raw strategy witness the common
outer transition and stage precisely the recurrent memories above. -/
theorem initialProfiledForest_outerAllowed
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env)) :
    PairedInitialProfiledOuterAllowed A (fun direction =>
      (some (initialProfiledGuardAt strategy direction),
        initialProfiledForest A strategy direction [])) := by
  refine ⟨initialLeftLambdaOfStrategy strategy,
    initialRightLambdaOfStrategy strategy,
    initialLeftForeverAccepts_lambdaOfStrategy A strategy hwin,
    initialRightForeverAccepts_lambdaOfStrategy A strategy hwin,
    ?_, ?_, ?_, ?_⟩
  · intro move
    rfl
  · intro move
    rfl
  · intro row past move
    constructor
    · rfl
    · change erasePairedProfiledState A
        (toProfiledTreeState (A := A)
          (initialLeftProfiledMemory A strategy past move)) = _
      rw [erase_toProfiledTreeState]
      exact initialLeftDelayedTarget_lambdaOfStrategy A strategy past move |>.symm
  · intro row past move
    constructor
    · rfl
    · change erasePairedProfiledState A
        (toProfiledTreeState (A := A)
          (initialRightProfiledMemory A strategy past move)) = _
      rw [erase_toProfiledTreeState]
      exact initialRightDelayedTarget_lambdaOfStrategy A strategy past move |>.symm

/-- A realizing strategy supplies one accepting composite run, and the named
input-free basis rationalizes the whole initial/recurrent forest in one
application. -/
theorem pairedInitialProfiledForest_hasRationalRun_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (basis : (pairedInitialProfiledForestAutomaton A).RationalRunBasis) :
    (pairedInitialProfiledForestAutomaton A).HasRationalRun := by
  apply InputFreeRunParityTreeAutomaton.rootStateIndexedGuardedForest_hasRationalRun
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (PairedInitialProfiledOuterAllowed A)
      (initialProfiledGuardAt strategy)
      (initialProfiledForest A strategy)
  · exact initialProfiledForest_accepts A strategy hwin
  · exact initialProfiledForest_guarded A strategy hwin
  · exact initialProfiledForest_outerAllowed A strategy hwin
  · exact basis

/-! ## Inverting the single rational run -/

/-- The finite transition policy obtained from the one composite
rationalization, together with the two initial lambdas certified by its common
root.  This package deliberately keeps a single policy: no recurrent policy
is chosen independently at a boundary. -/
structure PairedInitialProfiledRationalPackage where
  policy : (pairedInitialProfiledForestAutomaton A).RationalTransitionPolicy
  next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
    ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).State
  left : InitialLeftLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  right : InitialRightLambda
    (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
  leftForever : InitialLeftForeverAccepts A left
  rightForever : InitialRightForeverAccepts A right
  rootOutputOne : ∀ move : In₁ × In₂,
    left.informedOne [] move = right.reversingOne [] (move.2, move.1)
  rootOutputTwo : ∀ move : In₁ × In₂,
    left.reversingTwo [] move = right.informedTwo [] (move.2, move.1)
  child_eq : ∀ direction,
    policy.run [direction] = (false, next direction)
  leftBoundary : ∀ row past move,
    (next (.fromTwo row past move)).1 =
      some (Sum.inl (initialLeftPendingProfile left past move)) ∧
    erasePairedProfiledState A (next (.fromTwo row past move)).2 =
      initialLeftDelayedTarget A
        (initialLeftScanAfter A left past)
        (initialLeftLetterAt left past move)
  rightBoundary : ∀ row past move,
    (next (.fromOne row past move)).1 =
      some (Sum.inr (initialRightPendingProfile right past move)) ∧
    erasePairedProfiledState A (next (.fromOne row past move)).2 =
      initialRightDelayedTarget A
        (initialRightScanAfter A right past)
        (initialRightLetterAt right past move)

omit [Inhabited In₁] [Inhabited In₂] in
/-- A rational run of the composite automaton exposes one common package.
The `Nonempty` wrapper is the correct Prop-to-Type boundary. -/
theorem nonempty_initialProfiledRationalPackage_of_hasRationalRun
    (h : (pairedInitialProfiledForestAutomaton A).HasRationalRun) :
    Nonempty (PairedInitialProfiledRationalPackage A) := by
  classical
  rcases InputFreeRunParityTreeAutomaton.nonempty_rationalTransitionPolicy_of_hasRationalRun
        (pairedInitialProfiledForestAutomaton A) h with ⟨policy⟩
  rcases InputFreeRunParityTreeAutomaton.rootAllowed_of_rootGuarded_isRun
      ((pairedProfiledForestBase A).stateIndexedGuarded
        (pairedInitialProfiledGuardAllowed A))
      (PairedInitialProfiledOuterAllowed A) policy.run policy.accepts.1 with
    ⟨next, houter, _, hchildren⟩
  rcases houter with
    ⟨left, right, hleftForever, hrightForever,
      hrootOutputOne, hrootOutputTwo, hleftBoundary, hrightBoundary⟩
  refine ⟨{
    policy := policy
    next := next
    left := left
    right := right
    leftForever := hleftForever
    rightForever := hrightForever
    rootOutputOne := hrootOutputOne
    rootOutputTwo := hrootOutputTwo
    child_eq := ?_
    leftBoundary := hleftBoundary
    rightBoundary := hrightBoundary
  }⟩
  intro direction
  exact congrFun hchildren direction

namespace PairedInitialProfiledRationalPackage

/-- The rational subtree below one initial boundary, before consuming its
stored overlap guard. -/
noncomputable def guardedPolicyAt
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :=
  InputFreeRunParityTreeAutomaton.ordinaryPolicyBelowRootGuard
    ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A))
    (PairedInitialProfiledOuterAllowed A) package.policy direction

section
omit [Inhabited In₁] [Inhabited In₂]

/-- The projected subtree starts at the exact state advertised by the common
root transition. -/
theorem guardedPolicyAt_initial_eq
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂)) :
    (package.guardedPolicyAt A direction).run [] = package.next direction := by
  change (package.policy.run [direction]).2 = package.next direction
  simpa using congrArg Prod.snd (package.child_eq direction)

/-- At an initial-left boundary, the one rational subtree still carries the
exact process-one overlap obligation. -/
theorem guardedPolicyAt_left_pending
    (package : PairedInitialProfiledRationalPackage A)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    ((package.guardedPolicyAt A (.fromTwo row past move)).run []).1 =
      some (Sum.inl (initialLeftPendingProfile package.left past move)) := by
  rw [package.guardedPolicyAt_initial_eq A]
  exact (package.leftBoundary row past move).1

/-- Initial-right mirror. -/
theorem guardedPolicyAt_right_pending
    (package : PairedInitialProfiledRationalPackage A)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    ((package.guardedPolicyAt A (.fromOne row past move)).run []).1 =
      some (Sum.inr (initialRightPendingProfile package.right past move)) := by
  rw [package.guardedPolicyAt_initial_eq A]
  exact (package.rightBoundary row past move).1

/-- Reading the next transition after an initial-left boundary recovers the
model-specific profiled root guard from the single rational policy. -/
theorem exists_profiledRootGuard_at_initialLeft
    (package : PairedInitialProfiledRationalPackage A)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (move : In₁ × In₂) :
    ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
        PairedProfiledTreeState A,
      pairedProfiledEntryRootGuard A
        ((package.guardedPolicyAt A (.fromTwo row past move)).run []).2
        (initialLeftPendingProfile package.left past move).Matches
        (fun _ => True) next ∧
      ∀ direction,
        (package.guardedPolicyAt A (.fromTwo row past move)).run [direction] =
          (none, next direction) := by
  exact InputFreeRunParityTreeAutomaton.exists_allowed_at_stateIndexedGuard_root
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [.fromTwo row past move]).2
      (package.guardedPolicyAt A (.fromTwo row past move))
      (Sum.inl (initialLeftPendingProfile package.left past move))
      (package.guardedPolicyAt_left_pending A row past move)

/-- Initial-right mirror. -/
theorem exists_profiledRootGuard_at_initialRight
    (package : PairedInitialProfiledRationalPackage A)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (move : In₂ × In₁) :
    ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
        PairedProfiledTreeState A,
      pairedProfiledEntryRootGuard A
        ((package.guardedPolicyAt A (.fromOne row past move)).run []).2
        (fun _ => True)
        (initialRightPendingProfile package.right past move).Matches next ∧
      ∀ direction,
        (package.guardedPolicyAt A (.fromOne row past move)).run [direction] =
          (none, next direction) := by
  exact InputFreeRunParityTreeAutomaton.exists_allowed_at_stateIndexedGuard_root
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [.fromOne row past move]).2
      (package.guardedPolicyAt A (.fromOne row past move))
      (Sum.inr (initialRightPendingProfile package.right past move))
      (package.guardedPolicyAt_right_pending A row past move)

/-- Any process-one guarded state in the image of the common outer policy can
be activated directly, independently of which initial controller selected
that image state.  This is the image-level form needed after sender
narrowing, where the extracted controller need not reproduce the raw outer
root function pointwise. -/
theorem exists_profiledRootGuard_at_image_left
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (source : ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).State)
    (profile : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (himage : package.next direction = source)
    (hpending : source.1 = some (Sum.inl profile)) :
    ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
        PairedProfiledTreeState A,
      pairedProfiledEntryRootGuard A source.2
        profile.Matches (fun _ => True) next ∧
      ∀ first,
        (package.guardedPolicyAt A direction).run [first] =
          (none, next first) := by
  have hroot : (package.guardedPolicyAt A direction).run [] = source := by
    rw [package.guardedPolicyAt_initial_eq A, himage]
  have hguard :
      ((package.guardedPolicyAt A direction).run []).1 =
        some (Sum.inl profile) := by
    rw [hroot, hpending]
  obtain ⟨next, hallowed, hchildren⟩ :=
    InputFreeRunParityTreeAutomaton.exists_allowed_at_stateIndexedGuard_root
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [direction]).2
      (package.guardedPolicyAt A direction)
      (Sum.inl profile) hguard
  refine ⟨next, ?_, hchildren⟩
  simpa [pairedInitialProfiledGuardAllowed, hroot] using hallowed

/-- Process-two image-level activation. -/
theorem exists_profiledRootGuard_at_image_right
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (source : ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).State)
    (profile : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (himage : package.next direction = source)
    (hpending : source.1 = some (Sum.inr profile)) :
    ∃ next : PairedEntryDirection (In₁ := In₁) (In₂ := In₂) →
        PairedProfiledTreeState A,
      pairedProfiledEntryRootGuard A source.2
        (fun _ => True) profile.Matches next ∧
      ∀ first,
        (package.guardedPolicyAt A direction).run [first] =
          (none, next first) := by
  have hroot : (package.guardedPolicyAt A direction).run [] = source := by
    rw [package.guardedPolicyAt_initial_eq A, himage]
  have hguard :
      ((package.guardedPolicyAt A direction).run []).1 =
        some (Sum.inr profile) := by
    rw [hroot, hpending]
  obtain ⟨next, hallowed, hchildren⟩ :=
    InputFreeRunParityTreeAutomaton.exists_allowed_at_stateIndexedGuard_root
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [direction]).2
      (package.guardedPolicyAt A direction)
      (Sum.inr profile) hguard
  refine ⟨next, ?_, hchildren⟩
  simpa [pairedInitialProfiledGuardAllowed, hroot] using hallowed

end

/-- The process-one image state, with its one-shot bit retained, is exactly a
guarded-first policy at that state.  Its successor table is inherited from
the common composite policy; no representative policy is selected here. -/
noncomputable def profiledGuardedPolicyAt_image_left
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (source : ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).State)
    (profile : ProcOneEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁))
    (himage : package.next direction = source)
    (hpending : source.1 = some (Sum.inl profile)) :
    (rightProfiledGuardedAutomaton A source.2 profile).RationalTransitionPolicy := by
  have hinitial : (package.policy.run [direction]).2 = source := by
    change (package.guardedPolicyAt A direction).run [] = source
    rw [package.guardedPolicyAt_initial_eq A, himage]
  have hguard :
      ((package.guardedPolicyAt A direction).run []).1 =
        some (Sum.inl profile) := by
    rw [package.guardedPolicyAt_initial_eq A, himage, hpending]
  let result :=
    InputFreeRunParityTreeAutomaton.rootGuardedPolicyOfStateIndexedGuard
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [direction]).2
      (package.guardedPolicyAt A direction)
      (Sum.inl profile) hguard
  rw [hinitial] at result
  simpa [pairedProfiledForestBase, pairedInitialProfiledGuardAllowed,
    rightProfiledGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.withInitial] using result

/-- Process-two mirror. -/
noncomputable def profiledGuardedPolicyAt_image_right
    (package : PairedInitialProfiledRationalPackage A)
    (direction : PairedEntryDirection (In₁ := In₁) (In₂ := In₂))
    (source : ((pairedProfiledForestBase A).stateIndexedGuarded
      (pairedInitialProfiledGuardAllowed A)).State)
    (profile : ProcTwoEntryOverlapProfile
      (In₁ := In₁) (In₂ := In₂) (Out₂ := Out₂))
    (himage : package.next direction = source)
    (hpending : source.1 = some (Sum.inr profile)) :
    (leftProfiledGuardedAutomaton A source.2 profile).RationalTransitionPolicy := by
  have hinitial : (package.policy.run [direction]).2 = source := by
    change (package.guardedPolicyAt A direction).run [] = source
    rw [package.guardedPolicyAt_initial_eq A, himage]
  have hguard :
      ((package.guardedPolicyAt A direction).run []).1 =
        some (Sum.inr profile) := by
    rw [package.guardedPolicyAt_initial_eq A, himage, hpending]
  let result :=
    InputFreeRunParityTreeAutomaton.rootGuardedPolicyOfStateIndexedGuard
      (pairedProfiledForestBase A)
      (pairedInitialProfiledGuardAllowed A)
      (package.policy.run [direction]).2
      (package.guardedPolicyAt A direction)
      (Sum.inr profile) hguard
  rw [hinitial] at result
  simpa [pairedProfiledForestBase, pairedInitialProfiledGuardAllowed,
    leftProfiledGuardedAutomaton,
    InputFreeRunParityTreeAutomaton.withInitial] using result

end PairedInitialProfiledRationalPackage

end PairedStrategyMemory

end

end

end DetParityAutomaton

end DistributedSynthesis
