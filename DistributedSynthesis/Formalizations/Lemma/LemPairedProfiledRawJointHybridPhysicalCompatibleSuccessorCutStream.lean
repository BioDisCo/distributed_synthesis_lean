/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointAlignedCanonicalPhysicalSchedule
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleSuccessorDecoration
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleMachineAlignment

/-!
# A successor-decorated recurrent cut stream

The successor-decorated receiver retains three finite pieces at a physical
close: the old bare target, the table row which selected it, and one exact
successor key of the unchanged compatible policy.  This file packages the
proof-side iteration of those labels.

The bare target determines the crossed live root.  The retained key carries
the exact `CompatibleTargetTransitionAt`.  Equality between that key and the
next stream state then constructs one coherent `CompatibleTargetPath`, while
the literal physical block-minimum equations construct the corresponding
`CompatibleMachinePathAlignment`.

Rows, sides, roots, and compatible-policy states in this file are proof-side
audit data.  No executable controller is given a row reset, graph direction,
hierarchy side, or leader bit.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev CompatiblePolicy
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleRationalPolicy A strategy hwin
    initial

private abbrev CompatibleState
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatiblePolicyState A strategy hwin initial

private abbrev SuccessorTarget
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :=
  ProfiledRawJointHybridPhysicalCompatibleSuccessorTarget A strategy hwin
    initial

/-! ## One decorated target, split into its two exact roles -/

/-- The crossed live root carried by the *bare* projection of a decorated
target.  A right close reaches a left lineage state with a live left slot;
the left-close constructor is its mirror. -/
inductive ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy} :
    SuccessorTarget A strategy hwin initial →
      IndexedLineageSide → ProfiledRawJointThreadRoot A → Prop where
  | right
      (target : SuccessorTarget A strategy hwin initial)
      (slot : ProfiledRawLeftSlot A)
      (target_live : target.1.family.left () = some slot) :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt
        target .left (.inr slot)
  | left
      (target : SuccessorTarget A strategy hwin initial)
      (slot : ProfiledRawRightSlot A)
      (target_live : target.1.family.right () = some slot) :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt
        target .right (.inl slot)

namespace ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt

/-- The root predicate identifies the right-monitor projection literally. -/
theorem right_projection_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {target : SuccessorTarget A strategy hwin initial}
    {slot : ProfiledRawLeftSlot A}
    (hroot :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt A strategy
        hwin target .left (.inr slot)) :
    profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection A
        strategy hwin target = .inr (.inr slot) := by
  cases hroot with
  | right _ hlive =>
      simp [profiledRawJointHybridPhysicalCompatibleSuccessorRightTargetProjection,
        profiledRawJointUnitRightTargetProjection, hlive]

/-- Left-monitor projection mirror. -/
theorem left_projection_eq
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {target : SuccessorTarget A strategy hwin initial}
    {slot : ProfiledRawRightSlot A}
    (hroot :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt A strategy
        hwin target .right (.inl slot)) :
    profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection A
        strategy hwin target = .inr (.inl slot) := by
  cases hroot with
  | left _ hlive =>
      simp [profiledRawJointHybridPhysicalCompatibleSuccessorLeftTargetProjection,
        profiledRawJointUnitLeftTargetProjection, hlive]

end ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt

/-- One decorated target simultaneously has its bare crossed root and an
exact transition to its retained compatible-policy key. -/
structure ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) : Prop where
  root_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt A strategy
      hwin target side root
  transition : Nonempty
    (ProfiledRawJointHybridPhysicalCompatibleTargetTransitionAt A strategy
      hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        side root)

/-- Root-aligned refinement of a decorated successor target.  It retains the
same crossed live root and additionally records that the physical move stored
in the successor annotation starts at that root. -/
structure ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (side : IndexedLineageSide)
    (root : ProfiledRawJointThreadRoot A) : Prop where
  root_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetRootAt A strategy
      hwin target side root
  transition : Nonempty
    (ProfiledRawJointHybridPhysicalCompatibleRootAlignedTargetTransitionAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        side root)

theorem
    ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt.toSuccessorTargetAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    {policy : CompatiblePolicy A strategy hwin initial}
    {state : CompatibleState A strategy hwin initial}
    {target : SuccessorTarget A strategy hwin initial}
    {side : IndexedLineageSide} {root : ProfiledRawJointThreadRoot A}
    (aligned :
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target side root) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy state target side root := by
  rcases aligned with ⟨rootAt, ⟨transition⟩⟩
  exact ⟨rootAt, ⟨transition.transition⟩⟩

/-- A checked right successor-key relation yields the combined decorated
target predicate. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleSuccessorTargetAt_of_rightKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (hkey : ProfiledRawJointHybridPhysicalCompatibleRightSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1) :
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state target .left (.inr slot) := by
  rcases hkey with ⟨slot, hlive, htransition⟩
  exact ⟨slot, ⟨.right target slot hlive, htransition⟩⟩

/-- Left successor-key mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleSuccessorTargetAt_of_leftKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (hkey : ProfiledRawJointHybridPhysicalCompatibleLeftSuccessorKeyAt A
      strategy hwin policy state
        (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
          hwin target)
        target.1) :
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy
        hwin policy state target .right (.inl slot) := by
  rcases hkey with ⟨slot, hlive, htransition⟩
  exact ⟨slot, ⟨.left target slot hlive, htransition⟩⟩

/-- A root-aligned right successor key yields the combined decorated target
packet without forgetting its installed move source. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt_of_rightKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (hkey :
      ProfiledRawJointHybridPhysicalCompatibleRightRootAlignedSuccessorKeyAt A
        strategy hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    ∃ slot : ProfiledRawLeftSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .left (.inr slot) := by
  rcases hkey with ⟨slot, hlive, htransition⟩
  exact ⟨slot, ⟨.right target slot hlive, htransition⟩⟩

/-- Root-aligned left successor-key mirror. -/
theorem
    exists_profiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt_of_leftKeyAt
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (state : CompatibleState A strategy hwin initial)
    (target : SuccessorTarget A strategy hwin initial)
    (hkey :
      ProfiledRawJointHybridPhysicalCompatibleLeftRootAlignedSuccessorKeyAt A
        strategy hwin policy state
          (profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A
            strategy hwin target)
          target.1) :
    ∃ slot : ProfiledRawRightSlot A,
      ProfiledRawJointHybridPhysicalCompatibleRootAlignedSuccessorTargetAt A
        strategy hwin policy state target .right (.inl slot) := by
  rcases hkey with ⟨slot, hlive, htransition⟩
  exact ⟨slot, ⟨.left target slot hlive, htransition⟩⟩

/-! ## Infinite recurrent stream -/

/-- An infinite proof-side audit of successor-decorated physical cuts.

`target_at` is the exact seam: its first field reads the crossed root from the
bare target, and its second field reads the same-policy transition from the
retained key.  `next_state` says that this very key, rather than a freshly
chosen rationalization, is installed at the following cut. -/
structure ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  state : Nat → CompatibleState A strategy hwin initial
  initial_state : state 0 = policy.run []
  initial_code :
    (state 0).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    profiledRawJointHybridCurrentSlots A initialSide (state 0).1.1 () =
      some initialRoot
  target : Nat → SuccessorTarget A strategy hwin initial
  rootAt : Nat → ProfiledRawJointThreadRoot A
  target_at : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (state n) (target n)
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 1))
        (rootAt n)
  next_state : ∀ n : Nat,
    state (n + 1) =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (target n)
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  blockMin_eq_rootPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      profiledRawJointThreadRootPriority A (rootAt k)

/-! ## Honest recurrent tail after the common-root exit -/

/-- The form supplied by a recurrent one-sided carrier.

The first target is separated explicitly because the compatible policy starts
at its common root, whereas sibling-table decoration is available only after
the first one-sided child has been installed.  Thus `state 0` below is the
retained key of `exitTarget`; it is deliberately *not* identified with
`policy.run []`.  The physical cut stream still contains the exit block at
cut zero, followed by the recurrent sibling blocks. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit
    {initial : ProfiledRawJointCommonBaseWorld A strategy}
    (policy : CompatiblePolicy A strategy hwin initial)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂) where
  initial_code :
    (policy.run []).1.1 =
      .common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)
  initialSide : IndexedLineageSide
  initialRoot : ProfiledRawJointThreadRoot A
  initial_live :
    profiledRawJointHybridCurrentSlots A initialSide (policy.run []).1.1 () =
      some initialRoot
  exitTarget : SuccessorTarget A strategy hwin initial
  exitRoot : ProfiledRawJointThreadRoot A
  exit_at :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (policy.run []) exitTarget
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide 1)
        exitRoot
  state : Nat → CompatibleState A strategy hwin initial
  state_zero :
    state 0 =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin exitTarget
  target : Nat → SuccessorTarget A strategy hwin initial
  rootAt : Nat → ProfiledRawJointThreadRoot A
  target_at : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleSuccessorTargetAt A strategy hwin
      policy (state n) (target n)
        (profiledRawJointHybridPhysicalCompatibleSideAfter initialSide (n + 2))
        (rootAt n)
  next_state : ∀ n : Nat,
    state (n + 1) =
      profiledRawJointHybridPhysicalCompatibleSuccessorTargetKey A strategy
        hwin (target n)
  start : Nat
  cuts : Nat → Nat
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  exit_blockMin :
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts 0 =
      profiledRawJointThreadRootPriority A exitRoot
  recurrent_blockMin : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts (k + 1) =
      profiledRawJointThreadRootPriority A (rootAt k)

namespace ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- The retained successor keys of one stream form a single coherent path of
the fixed compatible policy. -/
noncomputable def targetPath
    (stream : ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream A
      strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy where
  state := stream.state
  initial_state := stream.initial_state
  initial_code := stream.initial_code
  initialSide := stream.initialSide
  initialRoot := stream.initialRoot
  initial_live := stream.initial_live
  rootAt := stream.rootAt
  transition := by
    intro n
    have htransition := (stream.target_at n).transition.some
    rw [stream.next_state n]
    exact htransition

/-- The same stream's literal block equations align its finite physical
machine with the coherent path just constructed. -/
noncomputable def machinePathAlignment
    (stream : ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream A
      strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment A strategy
      hwin policy (stream.targetPath A strategy hwin) G outputOne outputTwo env
    where
  start := stream.start
  cuts := stream.cuts
  cuts_strictMono := stream.cuts_strictMono
  cuts_zero := stream.cuts_zero
  blockMin_eq_rootPriority := stream.blockMin_eq_rootPriority

/-- End-to-end positive consumer of an exact successor-decorated cut stream. -/
theorem accepts
    (stream : ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream A
      strategy hwin policy G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (stream.machinePathAlignment A strategy hwin).accepts A strategy hwin

end ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream

namespace
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit

variable {initial : ProfiledRawJointCommonBaseWorld A strategy}
variable {policy : CompatiblePolicy A strategy hwin initial}
variable {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
variable {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
variable {env : EnvironmentSequence In₁ In₂}

/-- Prepend the explicit common-root exit to the genuinely recurrent
one-sided stream.  This is the adapter which prevents the recurrent state at
depth zero from masquerading as `policy.run []`. -/
noncomputable def toSuccessorCutStream
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit
        A strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleSuccessorCutStream A strategy hwin
      policy G outputOne outputTwo env where
  state
    | 0 => policy.run []
    | n + 1 => tail.state n
  initial_state := rfl
  initial_code := tail.initial_code
  initialSide := tail.initialSide
  initialRoot := tail.initialRoot
  initial_live := tail.initial_live
  target
    | 0 => tail.exitTarget
    | n + 1 => tail.target n
  rootAt
    | 0 => tail.exitRoot
    | n + 1 => tail.rootAt n
  target_at := by
    intro n
    cases n with
    | zero => exact tail.exit_at
    | succ n => exact tail.target_at n
  next_state := by
    intro n
    cases n with
    | zero => exact tail.state_zero
    | succ n => exact tail.next_state n
  start := tail.start
  cuts := tail.cuts
  cuts_strictMono := tail.cuts_strictMono
  cuts_zero := tail.cuts_zero
  blockMin_eq_rootPriority := by
    intro k
    cases k with
    | zero => exact tail.exit_blockMin
    | succ k => exact tail.recurrent_blockMin k

/-- The honest initial-exit presentation inherits the complete coherent
target path. -/
noncomputable def targetPath
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit
        A strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleTargetPath A strategy hwin
      policy :=
  (tail.toSuccessorCutStream A strategy hwin).targetPath A strategy hwin

/-- And it inherits the machine/path alignment without any reroot. -/
noncomputable def machinePathAlignment
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit
        A strategy hwin policy G outputOne outputTwo env) :
    ProfiledRawJointHybridPhysicalCompatibleMachinePathAlignment A strategy
      hwin policy (tail.targetPath A strategy hwin) G outputOne outputTwo env :=
  (tail.toSuccessorCutStream A strategy hwin).machinePathAlignment A strategy
    hwin

/-- End-to-end acceptance after the explicit common-to-one-sided exit. -/
theorem accepts
    (tail :
      ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit
        A strategy hwin policy G outputOne outputTwo env) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (tail.toSuccessorCutStream A strategy hwin).accepts A strategy hwin

end
  ProfiledRawJointHybridPhysicalCompatibleSuccessorCutTailAfterInitialExit

end

end DetParityAutomaton

end DistributedSynthesis
