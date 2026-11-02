/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleShadowPhaseLiveTailFibreTypes

/-!
# Seeding one live table on both sides of a tagged tail fibre

At a fixed tail-policy key, the owner fork and the receiver payload are built
from the same optional physical move stored in that key.  This is the upstream
constructor fact needed by the one-live-table simultaneous-close theorem: no
right/left table comparison and no guarded occurrence enrichment is required.

The Boolean fork member changes only the unresolved interpretation.  It does
not alter the tail key, the move identifier, or the initial sender control.
All side names below refer to the finite local carrier type being constructed;
no function receives a graph, hierarchy side, leader bit, or strict-leader
bit.
-/

namespace DistributedSynthesis

universe u v x y s p

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

private abbrev Tag :=
  ProfiledRawJointHybridShadowPhaseLiveTag A strategy hwin

private abbrev TailState (tag : Tag A strategy hwin) :=
  ProfiledRawJointHybridShadowPhaseLiveTailState A strategy hwin tag

private abbrev TailInitial (tag : Tag A strategy hwin) :=
  (profiledRawJointHybridShadowPhaseLiveInstalled A strategy hwin tag.origin
    ).world

/-! ## Right-table seed -/

/-- The right owner fork and right receiver payload selected at one tail key
carry literally the same move. -/
theorem
    exists_profiledRawJointHybridShadowPhaseLiveTailRightSingleTableSeed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove : state.1.2.1 = some move) (row : PairedEntryRow)
    {Payload : Type p} (payload : Payload) (member : Bool) :
    ∃ receiver :
        ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A strategy
          hwin (initial := TailInitial A strategy hwin tag),
      profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow A strategy
          hwin tag state row = some receiver ∧
        receiver.1 = move ∧
        receiver.2.1 = row ∧
        ((profiledRawJointHybridShadowPhaseLiveTailRightForkAt A strategy hwin
          tag state payload).candidate member).1.2.2 =
          .inr ⟨move,
            (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
              A strategy hwin state move false).initial⟩ := by
  obtain ⟨receiver, hreceiver, hreceiverMove, hreceiverRow⟩ :=
    profiledRawJointHybridPhysicalCompatibleRightPayloadAtRow_exact A strategy
      hwin state move hmove row
  refine ⟨receiver, hreceiver, hreceiverMove, hreceiverRow, ?_⟩
  exact profiledRawJointHybridShadowPhaseLiveTailRightForkAt_installed A
    strategy hwin tag state move hmove payload member

/-! ## Left-table mirror -/

theorem
    exists_profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableSeed
    (tag : Tag A strategy hwin) (state : TailState A strategy hwin tag)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove : state.1.2.2 = some move) (row : PairedEntryRow)
    {Payload : Type p} (payload : Payload) (member : Bool) :
    ∃ receiver :
        ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A strategy
          hwin (initial := TailInitial A strategy hwin tag),
      profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow A strategy hwin
          tag state row = some receiver ∧
        receiver.1 = move ∧
        receiver.2.1 = row ∧
        ((profiledRawJointHybridShadowPhaseLiveTailLeftForkAt A strategy hwin
          tag state payload).candidate member).1.2.2 =
          .inr ⟨move,
            (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController
              A strategy hwin state move false).initial⟩ := by
  obtain ⟨receiver, hreceiver, hreceiverMove, hreceiverRow⟩ :=
    profiledRawJointHybridPhysicalCompatibleLeftPayloadAtRow_exact A strategy
      hwin state move hmove row
  refine ⟨receiver, hreceiver, hreceiverMove, hreceiverRow, ?_⟩
  exact profiledRawJointHybridShadowPhaseLiveTailLeftForkAt_installed A strategy
    hwin tag state move hmove payload member

/-! ## Preservation across exact tail successors

The target-transition record already carries the physical move installed in
its successor key.  Consequently the seed construction can be repeated after
every exact transition, without retaining the predecessor table and without
guessing a hierarchy side at run time.
-/

/-- A right-live exact successor immediately seeds one right owner/receiver
pair from the single move stored in the successor key. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.exists_rightSingleTableSeed
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next .right root)
    (row : PairedEntryRow) {Payload : Type p} (payload : Payload)
    (member : Bool) :
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      next.1.2.1 = some move ∧
        ∃ receiver :
            ProfiledRawJointHybridPhysicalCompatibleRightReceiverState A
              strategy hwin (initial := TailInitial A strategy hwin tag),
          profiledRawJointHybridShadowPhaseLiveTailRightPayloadAtRow A strategy
              hwin tag next row = some receiver ∧
            receiver.1 = move ∧
            receiver.2.1 = row ∧
            ((profiledRawJointHybridShadowPhaseLiveTailRightForkAt A strategy
              hwin tag next payload).candidate member).1.2.2 =
              .inr ⟨move,
                (profiledRawJointHybridShadowPhaseLiveTailDecoratedRightMemberController
                  A strategy hwin next move false).initial⟩ := by
  obtain ⟨move, hmove⟩ := transition.child_move
  refine ⟨move, hmove, ?_⟩
  exact exists_profiledRawJointHybridShadowPhaseLiveTailRightSingleTableSeed A
    strategy hwin tag next move hmove row payload member

/-- Left-live mirror of `exists_rightSingleTableSeed`. -/
theorem
    ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt.exists_leftSingleTableSeed
    {tag : Tag A strategy hwin}
    {state next : TailState A strategy hwin tag}
    {root : ProfiledRawJointThreadRoot A}
    (transition :
      ProfiledRawJointHybridShadowPhaseLiveTailTargetTransitionAt A strategy
        hwin tag state next .left root)
    (row : PairedEntryRow) {Payload : Type p} (payload : Payload)
    (member : Bool) :
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      next.1.2.2 = some move ∧
        ∃ receiver :
            ProfiledRawJointHybridPhysicalCompatibleLeftReceiverState A
              strategy hwin (initial := TailInitial A strategy hwin tag),
          profiledRawJointHybridShadowPhaseLiveTailLeftPayloadAtRow A strategy
              hwin tag next row = some receiver ∧
            receiver.1 = move ∧
            receiver.2.1 = row ∧
            ((profiledRawJointHybridShadowPhaseLiveTailLeftForkAt A strategy
              hwin tag next payload).candidate member).1.2.2 =
              .inr ⟨move,
                (profiledRawJointHybridShadowPhaseLiveTailDecoratedLeftMemberController
                  A strategy hwin next move false).initial⟩ := by
  obtain ⟨move, hmove⟩ := transition.child_move
  refine ⟨move, hmove, ?_⟩
  exact exists_profiledRawJointHybridShadowPhaseLiveTailLeftSingleTableSeed A
    strategy hwin tag next move hmove row payload member

end

end DetParityAutomaton

end DistributedSynthesis
