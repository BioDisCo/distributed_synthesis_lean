/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyBank
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedExtraPathAdapter

/-!
# Driving the fixed marked policy bank by real hybrid directions

For one bank index and an arbitrary stream of real hybrid directions, this
file constructs the canonical root-started path through the policy already
selected at that index.  At a policy node we choose its one legal linked move
and request the finite child-code tag equal to that move's *actual* raw child
code.  The finite-code image theorem then says that the successor really has
that raw child code.

This is proof-side path selection only.  Neither endpoint is given the hybrid
direction, graph orientation, hierarchy side, leader bit, or semantic source.
The result is the reusable bridge between an actual environment direction
stream and the fixed finite policy bank.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev MarkedExtra :=
  ProfiledRawJointHybridMarkedLiteralPrefixExtra A

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

private abbrev Installed
    (control : CommonControl A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
    hwin control

private abbrev Policy
    (control : CommonControl A strategy hwin) :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
    strategy hwin control).policy

private abbrev PolicyState
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
    A strategy hwin (Installed A strategy hwin control).world

private abbrev LinkedDPA
    (control : CommonControl A strategy hwin) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (MarkedExtra A))
    (profiledRawJointHybridCodeParityDPA A
      (.common
        ((profiledRawJointCommonWorldFamily A
          (Installed A strategy hwin control).world).incidenceCode A)))

private abbrev InitialCode
    (control : CommonControl A strategy hwin) : LinkedCode A :=
  (.common
      ((profiledRawJointCommonWorldFamily A
        (Installed A strategy hwin control).world).incidenceCode A),
    profiledRawJointHybridPhysicalCompatibleExtraInitial A
      (profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
        (Installed A strategy hwin control).world))

private abbrev Valid
    (control : CommonControl A strategy hwin) :=
  sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (ProfiledRawJointHybridPhysicalCompatibleValidatedExtraParentLinkValid A
      strategy hwin
        (ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
          hwin (Installed A strategy hwin control).world)
        (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin))

private abbrev RawNext :=
  sourceFreeBeliefParentLinkedNext
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (MarkedExtra A))
    (profiledRawJointHybridNext A)

private abbrev FiniteNext :=
  sourceFreeBeliefFiniteCodeNext (RawNext A)

/-! ## The legal move and actual child tag at one bank node -/

/-- The legal linked move selected by the already-fixed bank policy at a
literal policy node. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt
    (control : CommonControl A strategy hwin)
    (node : TreeNode (LinkedCode A)) : LinkedMove A :=
  Classical.choose
    ((Policy A strategy hwin control).exists_sourceFreeMove
      (LinkedDPA A strategy hwin control)
      (InitialCode A strategy hwin control)
      (Valid A strategy hwin control)
      (FiniteNext A)
      ((Policy A strategy hwin control).run node)
      ⟨node, rfl⟩)

/-- The chosen move realizes the complete finite successor table at its
literal node. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt_realizes
    (control : CommonControl A strategy hwin)
    (node : TreeNode (LinkedCode A)) :
    (Policy A strategy hwin control).MoveRealizesAt
      (LinkedDPA A strategy hwin control)
      (InitialCode A strategy hwin control)
      (Valid A strategy hwin control)
      (FiniteNext A)
      ((Policy A strategy hwin control).run node)
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
        hwin control node) :=
  Classical.choose_spec
    ((Policy A strategy hwin control).exists_sourceFreeMove
      (LinkedDPA A strategy hwin control)
      (InitialCode A strategy hwin control)
      (Valid A strategy hwin control)
      (FiniteNext A)
      ((Policy A strategy hwin control).run node)
      ⟨node, rfl⟩)

/-- At the marked root the generic legal-move lookup is forced to be the
root move already stored in the bank package.  Thus the direction-driven path
does not silently select a second root implementation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt_zero_eq_rootMove
    (control : CommonControl A strategy hwin) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
        hwin control [] =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
        strategy hwin control).rootMove := by
  let package :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control
  let installed := Installed A strategy hwin control
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
      hwin control []
  have hvalid :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt_realizes A
      strategy hwin control []).1
  rcases hvalid with ⟨_hprovenance, hlink⟩
  rcases hlink with
    ⟨source, _hcode, hmove, _hphysical, hmarked, hchildren⟩
  have hrootExtra :
      ((Policy A strategy hwin control).run []).1.2.2 =
        profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          installed.world := by
    simpa only [Policy, package, installed] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
        A strategy hwin control)
  rw [hrootExtra] at hmarked
  have hsource : source = .common installed.world :=
    (profiledRawJointHybridMarkedLiteralPrefixCurrentCompatible_initial_elim A
      strategy hwin installed.world source hmarked).1
  apply Prod.ext
  · calc
      move.1 = source.move A := hmove.symm
      _ = ((.common installed.world : HybridState A strategy).move A) := by
        rw [hsource]
      _ = some installed.rawMove := congrArg some installed.move_eq
      _ = package.rootMove.1 := package.rootMove_realizes.1.symm
  · funext direction
    have hchosen := hchildren direction
    have hroot := package.rootMove_realizes.2.1 direction
    rw [hsource] at hchosen
    exact hchosen.symm.trans hroot

/-- Request the finite tag equal to the genuine raw child code of `direction`.
This is the canonical embedding of a real direction into the finite child-code
alphabet. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt
    (control : CommonControl A strategy hwin)
    (node : TreeNode (LinkedCode A))
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) : LinkedCode A :=
  RawNext A ((Policy A strategy hwin control).run node).1
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
      hwin control node) direction

/-! ## The canonical node stream and allowed path -/

/-- Recursively follow the actual child-code tag of each real direction. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    Nat → TreeNode (LinkedCode A)
  | 0 => []
  | n + 1 =>
      let node :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode
          control direction n
      node ++
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt
          A strategy hwin control node (direction n)]

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode_zero
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
      strategy hwin control direction 0 = [] :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode_succ
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction (n + 1) =
      let node :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
          strategy hwin control direction n
      node ++
        [profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt
          A strategy hwin control node (direction n)] :=
  rfl

/-- The root-started path in the fixed bank induced by a stream of real
hybrid directions. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A
      strategy hwin (Policy A strategy hwin control) where
  state := fun n ↦
    (Policy A strategy hwin control).run
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n)
  initial_state := rfl
  allowed := fun n ↦ by
    let node :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n
    let child :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankActualChildCodeAt A
        strategy hwin control node (direction n)
    refine ⟨child, ?_⟩
    change
      (Policy A strategy hwin control).successor
          ((Policy A strategy hwin control).run node) child =
        (Policy A strategy hwin control).run (node ++ [child])
    exact (Policy A strategy hwin control).successor_at node child

/-! ## Exact raw-code and replace-only annotation equations -/

/-- At every step, the next path code is exactly the raw linked child code of
the supplied direction, rather than merely the image of an arbitrary finite
tag. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_nextCode
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    let node :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
        hwin control node
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
        strategy hwin control direction).state (n + 1)).1 =
      RawNext A ((Policy A strategy hwin control).run node).1 move
        (direction n) := by
  dsimp only
  let node :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
      strategy hwin control direction n
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
      hwin control node
  let child := RawNext A ((Policy A strategy hwin control).run node).1 move
    (direction n)
  have hsucc :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt_realizes A
      strategy hwin control node).2 child
  have hfinite :
      FiniteNext A ((Policy A strategy hwin control).run node).1 move child =
        child := by
    dsimp only [FiniteNext, child]
    exact sourceFreeBeliefFiniteCodeNext_of_direction (RawNext A)
      ((Policy A strategy hwin control).run node).1 move (direction n)
  rw [hfinite] at hsucc
  have hpath :
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
          strategy hwin control direction).state (n + 1) =
        (Policy A strategy hwin control).successor
          ((Policy A strategy hwin control).run node) child := by
    change
      (Policy A strategy hwin control).run (node ++ [child]) =
        (Policy A strategy hwin control).successor
          ((Policy A strategy hwin control).run node) child
    exact ((Policy A strategy hwin control).successor_at node child).symm
  exact congrArg Prod.fst (hpath.trans hsucc)

/-- Consequently the unmarked literal tables in the next bank state are
exactly the current tables advanced along the supplied real direction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_nextLiteral
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    let node :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
        strategy hwin control direction n
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
        hwin control node
    let state := (Policy A strategy hwin control).run node
    ∃ source : HybridState A strategy,
      source.code A = state.1.1 ∧
        source.move A = move.1 ∧
        ProfiledRawJointHybridPhysicalCurrentCompatible A strategy source
          state.1.2.1 ∧
        ProfiledRawJointHybridMarkedLiteralPrefixCurrentCompatible A strategy
          hwin (Installed A strategy hwin control).world source state.1.2.2 ∧
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath A
            strategy hwin control direction).state (n + 1)).1.2.2.2 =
          profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
            source state.1.2.2.2 (direction n) := by
  dsimp only
  let node :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionNode A
      strategy hwin control direction n
  let move :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt A strategy
      hwin control node
  have hvalid :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankMoveAt_realizes A
      strategy hwin control node).1
  rcases hvalid with ⟨hprovenance, hlink⟩
  rcases hlink with
    ⟨source, hcode, hmove, hphysical, hmarked, hchildren⟩
  have hnext :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankDirectionPath_nextCode
      A strategy hwin control direction n
  have hann := congrArg (fun code ↦ code.2.2.2) hnext
  have hchild := congrArg (fun annotation ↦ annotation.2.2)
    (hchildren (direction n))
  refine ⟨source, hcode, hmove, hphysical, hmarked, ?_⟩
  exact hann.trans (by
    simpa [node, move,
      profiledRawJointHybridPhysicalCompatibleExtraAdvance,
      profiledRawJointHybridMarkedLiteralPrefixAdvance] using hchild.symm)

end

end DetParityAutomaton

end DistributedSynthesis
