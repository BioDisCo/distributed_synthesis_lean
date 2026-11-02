/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialPolicyBank

/-!
# The finite marked literal-policy bank

For every finite leader-free common control, this module selects one marked
validated literal-prefix policy.  The complete function-valued bank is fixed
from `A`, the already fixed winning strategy, and its all-environment winning
proof.  It is therefore outside every later environment, path, root-source,
cut, and hierarchy-case quantifier.

The bank index is the existing finite `CommonControl`.  Its runtime control is
the dependent sum of that index and one state of the selected finite policy.
The selected root package additionally retains the exact root move and its
complete child map.  Semantic sources are used only to prove the package;
they are absent from the controller type.

No graph, hierarchy orientation, leader bit, or strict-leader bit is a bank
argument or controller field.
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

/-! ## One selected marked policy per common control -/

/-- Policy-free literal common occurrence already installed at a finite
common control. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridCommonMoveData A strategy :=
  ProfiledRawJointHybridCommonInstalledMove.toCommonMoveData A
    (profiledRawJointHybridCommonControlInstalled A strategy hwin control)

private abbrev BankPolicy
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world

private abbrev BankPolicyState
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world

/-- One marked rational policy chosen for every finite common-control index.
This function is the bank; later environment behavior only looks up and runs
its already selected entries. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank
    (control : CommonControl A strategy hwin) :
    BankPolicy A strategy hwin control :=
  Classical.choice
    (nonempty_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicy
      A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world)

/-! ## Root package exposed to Tail installation -/

/-- Exact root obligations consumed downstream.  The first conjunct pins the
old raw move already installed at the common controller; the remaining two
conjuncts retain every child annotation and every executable successor. -/
def ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootMoveRealizes
    (control : CommonControl A strategy hwin)
    (policy : BankPolicy A strategy hwin control)
    (move : LinkedMove A) : Prop :=
  let installed :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  move.1 = some installed.rawMove ∧
    (∀ direction,
      profiledRawJointHybridPhysicalCompatibleExtraAdvance A strategy hwin
          (profiledRawJointHybridMarkedLiteralPrefixAdvance A strategy hwin)
          (.common installed.world) (policy.run []).1.2 direction =
        move.2 direction) ∧
    ∀ direction : HybridDirection (In₁ := In₁) (In₂ := In₂),
      policy.successor (policy.run [])
          (sourceFreeBeliefParentLinkedNext
            (profiledRawJointHybridNext A) (policy.run []).1 move direction) =
        let childCode := sourceFreeBeliefParentLinkedNext
          (profiledRawJointHybridNext A) (policy.run []).1 move direction
        (childCode,
          (sourceFreeBeliefParentLinkedCodeParityDPA
            (Annotation :=
              ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
                (MarkedExtra A))
            (profiledRawJointHybridCodeParityDPA A
              (.common ((profiledRawJointCommonWorldFamily A installed.world
                ).incidenceCode A)))).step (policy.run []).2 childCode)

/-- A chosen bank entry together with the one finite root move that supplies
all of its literal children. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootPackage
    (control : CommonControl A strategy hwin) where
  policy : BankPolicy A strategy hwin control
  rootMove : LinkedMove A
  rootMove_realizes :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootMoveRealizes A
      strategy hwin control policy rootMove

/-- The complete root-package bank, selected before any particular
environment or path. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixRootPackage A strategy
      hwin control := by
  let installed :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let policy :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin control
  let hexists :=
    exists_profiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixRootMove
      A strategy hwin installed.world policy
  let move := Classical.choose hexists
  have hrealizes := Classical.choose_spec hexists
  refine
    { policy := policy
      rootMove := move
      rootMove_realizes := ?_ }
  refine ⟨?_, hrealizes.2.1, hrealizes.2.2⟩
  calc
    move.1 =
        ((.common installed.world : HybridState A strategy).move A) :=
      hrealizes.1
    _ = some installed.rawMove := congrArg some installed.move_eq

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_move
    (control : CommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).rootMove.1 =
      some (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).rawMove := by
  exact
    (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).rootMove_realizes.1

/-- The selected bank policy literally starts with the marked seed belonging
to the installed common occurrence. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
    (control : CommonControl A strategy hwin) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).policy.run []).1.2.2 =
      profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin control).world := by
  let package :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control
  exact congrArg (fun state ↦ state.1.2.2) package.policy.accepts.1.1

/-- Every literal child stored in the selected root move is nonfresh.  This
is a controller marker equation, independent of which hierarchy orientation
the proof later associates with `direction`. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_childMarker
    (control : CommonControl A strategy hwin)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).rootMove.2 direction).2.1 = false := by
  let installed :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let package :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control
  have hchild := package.rootMove_realizes.2.1 direction
  have hmarker := congrArg (fun annotation ↦ annotation.2.1) hchild
  exact hmarker.symm

/-- The unmarked table pair stored at a root child is exactly one
replace-only literal advance from the bank entry's seed.  This is the direct
installation equation for the retained Tail carrier. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_childLiteral
    (control : CommonControl A strategy hwin)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control).rootMove.2 direction).2.2 =
      profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (.common
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world)
        (profiledRawJointHybridLiteralPrefixSeedAnnotation A strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
            strategy hwin control).world)
        direction := by
  let installed :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A strategy
      hwin control
  let package :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank A
      strategy hwin control
  have hchild := package.rootMove_realizes.2.1 direction
  have hliteral := congrArg (fun annotation ↦ annotation.2.2) hchild
  change
    profiledRawJointHybridLiteralPrefixAnnotationAdvance A strategy hwin
        (.common installed.world) (package.policy.run []).1.2.2.2 direction =
      (package.rootMove.2 direction).2.2 at hliteral
  have hrootExtra :
      (package.policy.run []).1.2.2 =
        profiledRawJointHybridMarkedLiteralPrefixInitial A strategy hwin
          installed.world := by
    simpa only [package, installed] using
      (profiledRawJointHybridValidatedMarkedLiteralPrefixRootPackageBank_rootExtra
        A strategy hwin control)
  have hrootLiteral := congrArg Prod.snd hrootExtra
  rw [hrootLiteral] at hliteral
  exact hliteral.symm

/-! ## Small finite runtime/path skeleton -/

/-- Runtime control for the marked bank: a finite bank index paired with one
finite state of the policy selected at that index. -/
abbrev ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl :=
  Σ control : CommonControl A strategy hwin,
    BankPolicyState A strategy hwin control

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankControlFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A
        strategy hwin) := by
  classical
  infer_instance

/-- Enter one already selected bank entry at its marked rational root. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
      hwin :=
  ⟨control,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin control).run []⟩

/-- Follow one code transition while retaining the same finite bank index. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor
    (state :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
        hwin)
    (childCode : LinkedCode A) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
      hwin :=
  ⟨state.1,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin state.1).successor state.2 childCode⟩

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_index
    (control : CommonControl A strategy hwin) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
      control).1 = control :=
  rfl

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_index
    (state :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
        hwin)
    (childCode : LinkedCode A) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin state childCode).1 = state.1 :=
  rfl

/-- Reachability is always measured inside the one policy selected at the
stored bank index. -/
abbrev ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable
    (state :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
        hwin) : Prop :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixReachable
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
        hwin state.1) state.2

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot_reachable
    (control : CommonControl A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin control) :=
  ⟨[], rfl⟩

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_reachable
    (state :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy
        hwin)
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (childCode : LinkedCode A) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A
          strategy hwin state childCode) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [childCode], ?_⟩
  change
    (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
      hwin state.1).run (node ++ [childCode]) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
        hwin state.1).successor state.2 childCode
  rw [← (profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A
    strategy hwin state.1).successor_at node childCode, hnode]

end

end DetParityAutomaton

end DistributedSynthesis
