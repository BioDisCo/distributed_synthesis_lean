/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixRetainedCarrierTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleLiteralPrefixCurrentTailAdapter
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixOperationalAcceptance

/-!
# Current literal tables along the fixed marked bank

This file is the path-to-carrier seam for the canonical marked policy bank.
Every state of a root-started bank path is reachable in the one policy fixed
at its finite `CommonControl` index.  Reachable inversion therefore supplies
one genuine current semantic source, and marked validity projects to the
ordinary current-literal provenance consumed by the retained carrier and its
Tail-facing safety lemmas.

The resulting witnesses are proof-side only.  The executable retained
controller still receives only local inputs and delivered partner controls;
no graph, hierarchy orientation, leader bit, strict-leader bit, semantic
source, or path state is passed to an endpoint transition.

This bridge deliberately stops before *reinstallation*: one retained carrier
advances one fixed pair of literal tables, whereas an infinite bank path
replaces its literal annotation at every policy edge.  The remaining global
controller construction must perform that finite bank lookup at the cut.  No
such lookup is assumed in the statements below.
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

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

private abbrev MarkedExtra :=
  ProfiledRawJointHybridMarkedLiteralPrefixExtra A

private abbrev LiteralAnnotation :=
  ProfiledRawJointHybridLiteralPrefixEdgeAnnotation A

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
        (MarkedExtra A))

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := HybridDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointHybridMove A)
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (MarkedExtra A))

private abbrev Package
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootPackage A strategy
    hwin control

private abbrev BankPath
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A strategy
    hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy

/-! ## Reachability inside the selected bank entry -/

/-- Every state of a root-started path stays reachable in the exact marked
policy selected at its already fixed bank index. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_reachable
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) : ∀ n : Nat,
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixReachable
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world
        (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin control).policy
        (path.state n) := by
  intro n
  induction n with
  | zero =>
      exact ⟨[], path.initial_state.symm⟩
  | succ n ih =>
      rcases path.allowed n with ⟨childCode, hchild⟩
      rcases ih with ⟨node, hnode⟩
      refine ⟨node ++ [childCode], ?_⟩
      rw [← (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank
        A strategy hwin control).policy.successor_at node childCode, hnode,
        hchild]

/-! ## The complete finite-code transition at a path state -/

/-- One reachable bank state together with the exact finite-child-code
transition selected by its fixed rational policy.  Unlike the raw-direction
view, `successor` is quantified over every requested finite child code.  This
is the form needed by an executable finite bank lookup at a cut. -/
structure
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep
    (control : CommonControl A strategy hwin)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world) where
  move : LinkedMove A
  source : HybridState A strategy
  source_code : source.code A = state.1.1
  source_move : source.move A = move.1
  physical_current :
    ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
      state.1.2.1
  marked_current :
    ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world source state.1.2.2
  children : ∀ direction,
    profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
        (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)
        source state.1.2 direction =
      move.2 direction
  successor : ∀ requested : LinkedCode A,
    let childCode :=
      sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
        state.1 move requested
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy.successor state requested =
      (childCode,
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation :=
            ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
              (MarkedExtra A))
          (profiledRawJointHybridCodeParityDPA A
            (.common
              ((profiledRawJointCommonWorldFamily A
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                  A strategy hwin control).world).incidenceCode A)))).step
            state.2 childCode)

/-- Reachable inversion retaining the arbitrary finite-code successor law
instead of only its raw-direction corollary. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep
    (control : CommonControl A strategy hwin)
    (state :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world)
    (hreachable :
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixReachable
        A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world
          (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
            strategy hwin control).policy state) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep
      A strategy hwin control state := by
  let initial :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control).world
  let policy :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).policy
  let D := sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (MarkedExtra A))
    (profiledRawJointHybridCodeParityDPA A
      (.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)))
  let hexists :=
    policy.exists_sourceFreeMove D
      ((.common ((profiledRawJointCommonWorldFamily A initial).incidenceCode A)),
        profiledRawJointHybridPhysicalCompatibleExtraInitial A
          (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
            initial))
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid
          A strategy hwin
            (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A
              strategy hwin initial)
            (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)))
      (sourceFreeBeliefFiniteCodeNext
        (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)))
      state hreachable
  let move := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  rcases hspec with ⟨hvalid, hsuccessor⟩
  rcases hvalid with ⟨_hprovenance, hlink⟩
  let source := Classical.choose hlink
  have hsource := Classical.choose_spec hlink
  rcases hsource with ⟨hcode, hmove, hphysical, hmarked, hchildren⟩
  exact
    { move := move
      source := source
      source_code := hcode
      source_move := hmove
      physical_current := hphysical
      marked_current := hmarked
      children := hchildren
      successor := hsuccessor }

/-- The finite transition packet at one concrete state of a bank path. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep
      A strategy hwin control (path.state n) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
    hwin control (path.state n)
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_reachable
        A strategy hwin control path n)

/-- The finite child-code request followed by the concrete allowed path at
time `n`. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) : LinkedCode A :=
  Classical.choose (path.allowed n)

theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode_spec
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).policy.successor (path.state n)
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
          A strategy hwin control path n) =
      path.state (n + 1) :=
  Classical.choose_spec (path.allowed n)

/-- Raw semantic direction represented by the path's finite child-code
request at time `n`.  It is proof-side reconstruction from the fixed finite
transition packet, not an input to either endpoint. -/
noncomputable def
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  sourceFreeBeliefRawDirectionOfChildCode
    (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
    (path.state n).1
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
        A strategy hwin control path n).move
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
        A strategy hwin control path n)

/-- The next path state is exactly the finite-code image of the selected raw
direction of the current transition packet.  This is the policy-state lookup
equation needed at a physical cut. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextState_eq_selected
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    let packet :=
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
        A strategy hwin control path n
    let direction :=
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
        A strategy hwin control path n
    let childCode := sourceFreeBeliefParentLinkedNext
      (profiledRawJointHybridNext A) (path.state n).1 packet.move direction
    path.state (n + 1) =
      (childCode,
        (sourceFreeBeliefParentLinkedCodeParityDPA
          (Annotation :=
            ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
              (MarkedExtra A))
          (profiledRawJointHybridCodeParityDPA A
            (.common
              ((profiledRawJointCommonWorldFamily A
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
                  A strategy hwin control).world).incidenceCode A)))).step
            (path.state n).2 childCode) := by
  dsimp only
  let packet :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
      A strategy hwin control path n
  let requested :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode
      A strategy hwin control path n
  have hrequested :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.requestedChildCode_spec
      A strategy hwin control path n
  have hfinite := packet.successor requested
  exact hrequested.symm.trans (by
    simpa [packet, requested,
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection,
      sourceFreeBeliefFiniteCodeNext] using hfinite)

/-- Exact replace-only reinstallation equation along the chosen bank path.
The next path state's literal tables are the concrete advance of the current
state's tables along the selected raw semantic direction. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextLiteral_eq_advance
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    let packet :=
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
        A strategy hwin control path n
    let direction :=
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
        A strategy hwin control path n
    (path.state (n + 1)).1.2.2.2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        packet.source (path.state n).1.2.2.2 direction := by
  dsimp only
  let packet :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.finiteStep
      A strategy hwin control path n
  let direction :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.selectedDirection
      A strategy hwin control path n
  have hstate :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath.nextState_eq_selected
      A strategy hwin control path n
  have hann := congrArg (fun state ↦ state.1.2.2.2) hstate
  have hchildren := congrArg (fun annotation ↦ annotation.2.2)
    (packet.children direction)
  exact hann.trans (by
    simpa [packet, direction,
      profiledRawJointHybridPhysicalCompatibleExtraAdvance,
      profiledRawJointHybridMarkedLiteralPrefixAdvance] using hchildren.symm)

/-! ## Concrete current provenance at every path state -/

/-- Reachable inversion, specialized to a state of the fixed bank path.  The
returned source explains the exact literal annotation stored at that state;
it is not reselected from a code-equal representative. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_exists_currentSource
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat) :
    ∃ source : HybridState A strategy,
      source.code A = (path.state n).1.1 ∧
        ProfiledRawJointHybridLiteralPrefixCurrentCompatible A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world
          source (path.state n).1.2.2.2 := by
  obtain ⟨_move, source, hcode, _hmove, _hphysical, hmarked, _hchildren,
      _hsuccessor⟩ :=
    exists_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixSemanticSource
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world
        (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
          strategy hwin control).policy
        (path.state n)
        (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_reachable
          A strategy hwin control path n)
  exact ⟨source, hcode,
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world source (path.state n).1.2.2 hmarked⟩

/-- The path root contains exactly the literal seed of its installed common
world. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_rootLiteral
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) :
    (path.state 0).1.2.2.2 =
      profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world := by
  rw [path.initial_state]
  exact congrArg Prod.snd
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
      A strategy hwin control)

/-! ## Present bank tables are legal retained-carrier tables -/

/-- Any right literal table actually present at a bank-path state is rooted
at its own physical monitor initial state. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_rightWellRooted
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (move : RightMove A)
    (hmove : (path.state n).1.2.2.2.1 = some move) :
    ProfiledRawJointRightLiteralPrefixWellRooted A move := by
  obtain ⟨source, _hcode, hcurrent⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_exists_currentSource
      A strategy hwin control path n
  exact hcurrent.rightWellRooted A strategy hwin hmove

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_leftWellRooted
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (move : LeftMove A)
    (hmove : (path.state n).1.2.2.2.2 = some move) :
    ProfiledRawJointLeftLiteralPrefixWellRooted A move := by
  obtain ⟨source, _hcode, hcurrent⟩ :=
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_exists_currentSource
      A strategy hwin control path n
  exact hcurrent.leftWellRooted A strategy hwin hmove

/-- If both optional lanes are present at a path state, installing those exact
finite values in the retained carrier starts with the authority invariant.
Together with `...globalStateTrace_authority`, this is the complete
bank-state-to-actual-trace bridge for one installed literal block. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_retained_initial
    (control : CommonControl A strategy hwin)
    (path : BankPath A strategy hwin control) (n : Nat)
    (rightMove : RightMove A) (leftMove : LeftMove A)
    (hlanes : (path.state n).1.2.2.2 =
      (some rightMove, some leftMove))
    (rightAnchor leftAnchor : Bool) :
    ProfiledRawJointRightLiteralPrefixWellRooted A rightMove ∧
      ProfiledRawJointLeftLiteralPrefixWellRooted A leftMove ∧
      ProfiledRawJointHybridLiteralPrefixRetainedAuthority A
        (profiledRawJointHybridLiteralPrefixRetainedRelayInitial A rightMove
          leftMove rightAnchor leftAnchor)
        (profiledRawJointHybridLiteralPrefixRetainedInitial A rightMove
          leftMove rightAnchor leftAnchor) := by
  have hright : (path.state n).1.2.2.2.1 = some rightMove := by
    rw [hlanes]
  have hleft : (path.state n).1.2.2.2.2 = some leftMove := by
    rw [hlanes]
  exact
    ⟨ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_rightWellRooted
        A strategy hwin control path n rightMove hright,
      ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_leftWellRooted
        A strategy hwin control path n leftMove hleft,
      profiledRawJointHybridLiteralPrefixRetainedAuthority_initial A rightMove
        leftMove rightAnchor leftAnchor⟩

end

end DetParityAutomaton

end DistributedSynthesis
