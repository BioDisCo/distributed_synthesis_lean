/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedBridge
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyBankDirectionPath

/-!
# Finite retained-table reinstallation from the marked bank

The marked bank state already contains the two optional literal tables.  This
file turns that annotation into total finite executable data.  A present lane
is installed literally.  An absent lane is filled by the corresponding seed
table of the same finite bank entry; the `..._eq_of_some` lemmas show that this
fallback is definitionally unobserved whenever that lane is live.

The bank state and the two local anchor bits form a finite delivered tag.  Its
two activation functions install the same tag and the canonical roots of the
same retained relay.  They receive no graph, hierarchy orientation, leader
bit, strict-leader bit, semantic source, or history.

Along a concrete allowed bank path, the successor-tag theorem and the exact
literal reinstallation theorems identify this total lookup with the policy's
actual next state and with the transition packet's selected child tables.
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

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev BankPath
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))

private abbrev BankReachable
    (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

/-! ## Total finite table lookup -/

/-- The literal annotation physically stored in a finite marked-bank state. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.literal
    (state : BankControl A strategy hwin) :
    ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A :=
  state.2.1.2.2.2

/-- Right seed used solely to totalize a bank state whose right literal lane
is absent.  It belongs to the same finite common-world bank entry. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.fallbackRightMove
    (state : BankControl A strategy hwin) : RightMove A :=
  profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin state.1).world

/-- Left mirror of `fallbackRightMove`. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.fallbackLeftMove
    (state : BankControl A strategy hwin) : LeftMove A :=
  profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin state.1).world

/-- Total right-table lookup. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove
    (state : BankControl A strategy hwin) : RightMove A :=
  (state.literal A strategy hwin).1.getD
    (state.fallbackRightMove A strategy hwin)

/-- Total left-table lookup. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove
    (state : BankControl A strategy hwin) : LeftMove A :=
  (state.literal A strategy hwin).2.getD
    (state.fallbackLeftMove A strategy hwin)

/-- A present right lane is installed literally; the fallback is not read. -/
@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove_eq_of_some
    (state : BankControl A strategy hwin) (move : RightMove A)
    (hmove : (state.literal A strategy hwin).1 = some move) :
    state.rightMove A strategy hwin = move := by
  simp [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove,
    hmove]

/-- Left mirror. -/
@[simp] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove_eq_of_some
    (state : BankControl A strategy hwin) (move : LeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some move) :
    state.leftMove A strategy hwin = move := by
  simp [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove,
    hmove]

/-! ## One finite delivered installation tag -/

/-- A finite bank state plus the two locally retained anchor bits. -/
abbrev ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag :=
  BankControl A strategy hwin × (Bool × Bool)

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTagFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin) := by
  classical
  infer_instance

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-- The retained carrier roots selected by one total finite tag lookup. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.initial
    (tag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A ×
      ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A :=
  profiledRawJointHybridLiteralPrefixRetainedInitial A
    (tag.1.rightMove A strategy hwin) (tag.1.leftMove A strategy hwin)
    tag.2.1 tag.2.2

/-- Both local runtime banks carry the same finite installation tag. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControl :=
  RetainedTag A strategy hwin ×
    ProfiledRawJointHybridLiteralPrefixRetainedOneControl A

abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControl :=
  RetainedTag A strategy hwin ×
    ProfiledRawJointHybridLiteralPrefixRetainedTwoControl A

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControlFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControl
        A strategy hwin) := by
  classical
  infer_instance

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControlFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControl
        A strategy hwin) := by
  classical
  infer_instance

/-- Local process-one activation from a delivered finite tag. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne
    (tag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControl A
      strategy hwin :=
  (tag, (tag.initial A strategy hwin).1)

/-- Local process-two activation from the same delivered finite tag. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo
    (tag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControl A
      strategy hwin :=
  (tag, (tag.initial A strategy hwin).2)

/-- Proof-side paired activation.  Operationally, each projection is
installed only when that endpoint locally receives the delivered tag. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstall
    (tag : RetainedTag A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedOneControl A
        strategy hwin ×
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTwoControl A
        strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallOne A
      strategy hwin tag,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstallTwo A
      strategy hwin tag)

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstall_keys
    (tag : RetainedTag A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstall A
        strategy hwin tag).1.1 =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedInstall A
        strategy hwin tag).2.1 :=
  rfl

/-- Advance only the finite policy key; anchors are retained. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.successor
    (tag : RetainedTag A strategy hwin) (childCode : LinkedCode A) :
    RetainedTag A strategy hwin :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin tag.1 childCode,
    tag.2)

/-! ## Total finite transition lookup -/

/-- The bank's legal move at a reachable state, totalized at unreachable
finite states by the root move of the same bank entry.  Reachability is a
decidable predicate over a finite type and is compiled into the lookup table;
it is not supplied to an endpoint at runtime. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move
    (state : BankControl A strategy hwin) : LinkedMove A := by
  classical
  exact if hreachable : BankReachable A strategy hwin state then
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
      strategy hwin state.1 state.2 hreachable).move
  else
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin state.1).rootMove

/-- On the reachable invariant, the total move lookup is literally the
finite transition packet selected from that state. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state) :
    state.move A strategy hwin =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable).move := by
  classical
  simp [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move,
    hreachable]

/-- The genuine raw child code requested by one real hybrid direction.  This
is a finite table operation on the bank state and direction. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode
    (state : BankControl A strategy hwin)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) : LinkedCode A :=
  sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
    state.2.1 (state.move A strategy hwin) direction

/-- Total tag transition driven by a real hybrid direction.  The direction
will be reconstructed by the local event dispatch; it is not a leader bit. -/
noncomputable def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.advance
    (tag : RetainedTag A strategy hwin)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    RetainedTag A strategy hwin :=
  tag.successor A strategy hwin
    (tag.1.childCode A strategy hwin direction)

/-- The successor of an arbitrary reachable bank state stores exactly the
replace-only child literal annotation of its selected transition packet. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.successor_literal
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable
    let childCode :=
      sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
        state.2.1 packet.move direction
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
        hwin state childCode).2.1.2.2.2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source state.2.1.2.2.2 direction := by
  dsimp only
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  let childCode :=
    sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
      state.2.1 packet.move direction
  have hsuccessor := packet.successor childCode
  have hfinite :
      sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
          state.2.1 packet.move childCode = childCode := by
    exact sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      state.2.1 packet.move direction
  rw [hfinite] at hsuccessor
  have hann := congrArg (fun nextState ↦ nextState.1.2.2.2) hsuccessor
  have hchildren := congrArg (fun annotation ↦ annotation.2.2)
    (packet.children direction)
  exact hann.trans (by
    simpa [packet, childCode,
      profiledRawJointHybridPhysicalCompatibleExtraAdvance,
      profiledRawJointHybridMarkedLiteralPrefixAdvance] using hchildren.symm)

/-- The same equation for the executable total lookup: unreachable fallbacks
disappear under the reachable invariant. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_literal
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    let packet :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
        hwin state (state.childCode A strategy hwin direction)).2.1.2.2.2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source state.2.1.2.2.2 direction := by
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
      A strategy hwin state hreachable]
  exact
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.successor_literal
      A strategy hwin state hreachable direction

/-- A real-direction lookup preserves the bank reachability invariant. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.advance_reachable
    (tag : RetainedTag A strategy hwin)
    (hreachable : BankReachable A strategy hwin tag.1)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    BankReachable A strategy hwin
      (tag.advance A strategy hwin direction).1 :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_reachable A
    strategy hwin tag.1 hreachable
      (tag.1.childCode A strategy hwin direction)

/-! ## Exact agreement with every concrete bank path -/

/-- Package a concrete path state and the two anchor bits as a runtime tag. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (rightAnchor leftAnchor : Bool) : RetainedTag A strategy hwin :=
  (⟨control, path.state n⟩, (rightAnchor, leftAnchor))

/-- The total finite tag successor follows the path's requested child code
exactly. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag_successor
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (rightAnchor leftAnchor : Bool) :
    (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path n rightAnchor leftAnchor).successor A
          strategy hwin
          (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
            A strategy hwin control path n) =
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path (n + 1) rightAnchor leftAnchor := by
  change
    ((⟨control,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin control).policy.successor (path.state n)
            (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
              A strategy hwin control path n)⟩ :
        BankControl A strategy hwin),
      (rightAnchor, leftAnchor)) =
      ((⟨control, path.state (n + 1)⟩ : BankControl A strategy hwin),
        (rightAnchor, leftAnchor))
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode_spec
    A strategy hwin control path n]

/-- On a live right lane at the next path state, finite tag reinstallation
selects exactly that literal child table. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextRetainedRightMove_eq
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (rightAnchor leftAnchor : Bool) (move : RightMove A)
    (hmove :
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
          A strategy hwin control path n).source
        (path.state n).1.2.2.2
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
          A strategy hwin control path n)).1 = some move) :
    ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path (n + 1) rightAnchor leftAnchor).1.rightMove
          A strategy hwin) = move := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove_eq_of_some
      A strategy hwin
  change (path.state (n + 1)).1.2.2.2.1 = some move
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextLiteral_eq_advance
    A strategy hwin control path n]
  exact hmove

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextRetainedLeftMove_eq
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (rightAnchor leftAnchor : Bool) (move : LeftMove A)
    (hmove :
      (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
          A strategy hwin control path n).source
        (path.state n).1.2.2.2
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
          A strategy hwin control path n)).2 = some move) :
    ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path (n + 1) rightAnchor leftAnchor).1.leftMove
          A strategy hwin) = move := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove_eq_of_some
      A strategy hwin
  change (path.state (n + 1)).1.2.2.2.2 = some move
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextLiteral_eq_advance
    A strategy hwin control path n]
  exact hmove

/-! ## Root and canonical real-direction path corollaries -/

/-- At the bank root the total right lookup installs the canonical seed, so
the fallback branch is not consulted. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.rootRetainedRightMove_eq
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control)
    (rightAnchor leftAnchor : Bool) :
    ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path 0 rightAnchor leftAnchor).1.rightMove A
          strategy hwin) =
      profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove_eq_of_some
      A strategy hwin
  change (path.state 0).1.2.2.2.1 = some _
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_rootLiteral
    A strategy hwin control path]
  rfl

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.rootRetainedLeftMove_eq
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control)
    (rightAnchor leftAnchor : Bool) :
    ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path 0 rightAnchor leftAnchor).1.leftMove A
          strategy hwin) =
      profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world := by
  apply
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove_eq_of_some
      A strategy hwin
  change (path.state 0).1.2.2.2.2 = some _
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_rootLiteral
    A strategy hwin control path]
  rfl

/-- Therefore paired activation at the root is exactly the original retained
seed installation, not merely an extensionally equivalent table choice. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.rootRetainedInitial_eq
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control)
    (rightAnchor leftAnchor : Bool) :
    (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path 0 rightAnchor leftAnchor).initial A
          strategy hwin =
      profiledRawJointHybridLiteralPrefixRetainedInitial A
        (profiledRawJointHybridRightLiteralPrefixSeedMove A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world)
        (profiledRawJointHybridLeftLiteralPrefixSeedMove A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world)
        rightAnchor leftAnchor := by
  unfold
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag.initial
  rw [ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.rootRetainedRightMove_eq
      A strategy hwin control path rightAnchor leftAnchor,
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.rootRetainedLeftMove_eq
      A strategy hwin control path rightAnchor leftAnchor]
  rfl

/-- The finite tag successor on the canonical real-direction path is exactly
the next canonical path tag.  This uses the path's concrete finite child code,
not an arbitrary post-hoc representative. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_retainedTag_successor
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) (rightAnchor leftAnchor : Bool) :
    let path :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
        strategy hwin control direction
    let node :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n
    let child :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt A
        strategy hwin control node (direction n)
    (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path n rightAnchor leftAnchor).successor A
          strategy hwin child =
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
        A strategy hwin control path (n + 1) rightAnchor leftAnchor := by
  dsimp only
  let node :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
      strategy hwin control direction n
  let child :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt A
      strategy hwin control node (direction n)
  change
    ((⟨control,
        (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin control).policy.successor
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank
              A strategy hwin control).policy.run node) child⟩ :
        BankControl A strategy hwin),
      (rightAnchor, leftAnchor)) =
      ((⟨control,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
            strategy hwin control).policy.run (node ++ [child])⟩ :
          BankControl A strategy hwin),
        (rightAnchor, leftAnchor))
  rw [(profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
    strategy hwin control).policy.successor_at node child]

/-- At every canonical direction-path step, total finite reinstallation is
literal on each live next lane.  The two implications are deliberately
separate: an absent lane may use the harmless seed fallback, while the active
lane never does. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_nextRetainedMoves
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) (rightAnchor leftAnchor : Bool) :
    let path :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
        strategy hwin control direction
    let node :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n
    let state :=
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy.run node
    ∃ source : ProfiledRawJointHybridSemanticState A strategy,
      ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
          state.1.2.1 ∧
        ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
          hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world source state.1.2.2 ∧
        (∀ move : RightMove A,
          (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
              source state.1.2.2.2 (direction n)).1 = some move →
            ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
                A strategy hwin control path (n + 1) rightAnchor
                  leftAnchor).1.rightMove A strategy hwin) = move) ∧
        (∀ move : LeftMove A,
          (profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
              source state.1.2.2.2 (direction n)).2 = some move →
            ((ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.retainedTag
                A strategy hwin control path (n + 1) rightAnchor
                  leftAnchor).1.leftMove A strategy hwin) = move) := by
  dsimp only
  obtain ⟨source, _hcode, _hmove, hphysical, hmarked, hliteral⟩ :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_nextLiteral
      A strategy hwin control direction n
  refine ⟨source, hphysical, hmarked, ?_, ?_⟩
  · intro move hmove
    apply
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.rightMove_eq_of_some
        A strategy hwin
    change
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
        strategy hwin control direction).state (n + 1)).1.2.2.2.1 = some move
    rw [hliteral]
    exact hmove
  · intro move hmove
    apply
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.leftMove_eq_of_some
        A strategy hwin
    change
      ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
        strategy hwin control direction).state (n + 1)).1.2.2.2.2 = some move
    rw [hliteral]
    exact hmove

end

end DetParityAutomaton

end DistributedSynthesis
