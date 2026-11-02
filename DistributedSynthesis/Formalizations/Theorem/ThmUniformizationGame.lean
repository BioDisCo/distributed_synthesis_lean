/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame
import DistributedSynthesis.Formalizations.Theorem.ThmBlockRestriction

/-!
# The uniformization game

This file defines the countable parity game of step HG-A of the
readback-upgrade plan: the single global game that pays the entire
cross-boundary parity accounting of `prop:journalgivesuniform` through
one application of positional determinacy.

Even is the strategy coalition.  At a boundary atom Even commits a
virtual boundary history, which bakes the subordinate side's behaviour
for the next block into the game's transitions through the sender
restrictions of `ThmBlockRestriction.lean`: within a block the sender
acts on its own input word alone, so its outputs are computable from
the committed history and the recorded sender word.  Every other
output is played by Even at staged positions whose content is exactly
the knowledge of the acting process:

* the shared opening response of a receiver is chosen before the
  environment resolves whether the round is one-sided or
  synchronizing, so the one-bit fringe of `thm:onebitfringe` is a
  structural identity rather than a side condition, exactly as in the
  move shape of `ThmBoundaryGame.lean`;
* within a block the receiver's response is chosen at a position
  carrying the committed history, the sender word, the tracked
  automaton state and the minimal-priority state, before the
  environment decides whether the round continues or closes the
  block, sharing the response between the two outcomes;
* the closing response of the subordinate side, together with its
  hypothetical no-receive response, is chosen at a dedicated position
  ahead of the close-resolve stage, where the environment decides
  whether the closing round synchronizes or directly reverses the
  orientation (the new dominant's fresh one-bit fringe: its response
  is shared between the two outcomes, while the old dominant's two
  table values serve the cases its own receipt tag distinguishes);
* within a directly reversed block no output can be baked (the block
  has no committed boundary), so both processes' lambda-table values
  are staged per round and the environment resolves the round type
  three ways: continue, close to a genuine boundary, or reverse
  again.

Boundary positions carry the atom alone.  A positional Even strategy
therefore commits per atom, which is the cross-boundary uniformization
that every per-block splicing argument fails to deliver; the parity
accounting across the infinitely many boundaries is paid inside the
positional determinacy of this one game.  Priorities follow design D3
of the boundary game: block positions emit the tracked state's
priority and boundary positions emit the closed block's minimum,
which continues across direct reversals.
-/

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  (A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂))

/--
Positions of the uniformization game.  Boundary positions carry the
atom alone; committed positions carry the virtual boundary history;
block positions carry the committed history, the recorded sender
word, the automaton state, and the minimal-priority state since the
boundary; staged positions carry the pending round data.  The
close-resolve positions let the environment decide, after the closing
responses are fixed, whether the round synchronizes or directly
reverses; the reversed-block positions carry no history and stage
both processes' table values per round.
-/
inductive UniformizationPosition where
  | bnd (atom : A.State × A.State)
  | committed (atom : A.State × A.State)
      (h : History In₁ In₂ Graph Out₁ Out₂)
  | opening (atom : A.State × A.State)
      (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂)
  | openingResolve (atom : A.State × A.State)
      (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂)
      (outOne : Out₁) (outTwo : Out₂)
  | blockL (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
      (state minState : A.State)
  | blockEnvL (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
      (state minState : A.State) (revTable : In₁ -> Out₁)
  | recvL (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
      (state minState : A.State) (revTable : In₁ -> Out₁)
      (move : In₁ × In₂)
  | resolveL (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
      (state minState : A.State) (revTable : In₁ -> Out₁)
      (move : In₁ × In₂) (outOne : Out₁)
  | closeL (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
      (state minState : A.State) (revTable : In₁ -> Out₁)
      (move : In₁ × In₂) (outOne : Out₁)
  | closeResolveL (h : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₂) (state minState : A.State)
      (revTable : In₁ -> Out₁) (move : In₁ × In₂)
      (outOne : Out₁) (outTwo : Out₂)
  | blockR (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
      (state minState : A.State)
  | blockEnvR (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
      (state minState : A.State) (revTable : In₂ -> Out₂)
  | recvR (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
      (state minState : A.State) (revTable : In₂ -> Out₂)
      (move : In₁ × In₂)
  | resolveR (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
      (state minState : A.State) (revTable : In₂ -> Out₂)
      (move : In₁ × In₂) (outTwo : Out₂)
  | closeR (h : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
      (state minState : A.State) (revTable : In₂ -> Out₂)
      (move : In₁ × In₂) (outTwo : Out₂)
  | closeResolveR (h : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₁) (state minState : A.State)
      (revTable : In₂ -> Out₂) (move : In₁ × In₂)
      (outTwo : Out₂) (outOne : Out₁)
  | revCommitL (word : List In₂) (entryState entryMin : A.State)
  | revBlockL (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₂) (entryState entryMin state minState : A.State)
  | revEnvL (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₂) (entryState entryMin state minState : A.State)
      (sendTable : In₁ -> Out₁)
  | revRecvL (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₂) (entryState entryMin state minState : A.State)
      (sendTable : In₁ -> Out₁) (move : In₁ × In₂)
  | revResolveL (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₂) (entryState entryMin state minState : A.State)
      (sendTable : In₁ -> Out₁) (move : In₁ × In₂)
      (outOneRecv : Out₁) (outTwoRecv : Out₂)
  | revCommitR (word : List In₁) (entryState entryMin : A.State)
  | revBlockR (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₁) (entryState entryMin state minState : A.State)
  | revEnvR (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₁) (entryState entryMin state minState : A.State)
      (sendTable : In₂ -> Out₂)
  | revRecvR (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₁) (entryState entryMin state minState : A.State)
      (sendTable : In₂ -> Out₂) (move : In₁ × In₂)
  | revResolveR (hc : History In₁ In₂ Graph Out₁ Out₂)
      (word : List In₁) (entryState entryMin state minState : A.State)
      (sendTable : In₂ -> Out₂) (move : In₁ × In₂)
      (outOneRecv : Out₁) (outTwoRecv : Out₂)

namespace UniformizationPosition

variable {A}

/-- Slot-based encoding used for countability: a constructor tag plus
optional component slots. -/
def code (p : UniformizationPosition (In₁ := In₁) A) :
    Nat × Option (A.State × A.State) ×
      Option (History In₁ In₂ Graph Out₁ Out₂) ×
      Option (List In₂) × Option (List In₁) ×
      Option (A.State × A.State) × Option (A.State × A.State) ×
      Option (In₁ × In₂) ×
      Option (In₁ -> Out₁) × Option (In₂ -> Out₂) ×
      Option Out₁ × Option Out₁ × Option Out₂ × Option Out₂ :=
  match p with
  | bnd atom =>
      (0, some atom, none, none, none, none, none, none, none, none,
        none, none, none, none)
  | committed atom h =>
      (1, some atom, some h, none, none, none, none, none, none, none,
        none, none, none, none)
  | opening atom h move =>
      (2, some atom, some h, none, none, none, none, some move, none,
        none, none, none, none, none)
  | openingResolve atom h move outOne outTwo =>
      (3, some atom, some h, none, none, none, none, some move, none,
        none, some outOne, none, some outTwo, none)
  | blockL h word state minState =>
      (4, none, some h, some word, none, some (state, minState), none,
        none, none, none, none, none, none, none)
  | blockEnvL h word state minState revTable =>
      (5, none, some h, some word, none, some (state, minState), none,
        none, some revTable, none, none, none, none, none)
  | recvL h word state minState revTable move =>
      (6, none, some h, some word, none, some (state, minState), none,
        some move, some revTable, none, none, none, none, none)
  | resolveL h word state minState revTable move outOne =>
      (7, none, some h, some word, none, some (state, minState), none,
        some move, some revTable, none, some outOne, none, none, none)
  | closeL h word state minState revTable move outOne =>
      (8, none, some h, some word, none, some (state, minState), none,
        some move, some revTable, none, some outOne, none, none, none)
  | closeResolveL h word state minState revTable move outOne outTwo =>
      (9, none, some h, some word, none, some (state, minState), none,
        some move, some revTable, none, some outOne, none, some outTwo,
        none)
  | blockR h word state minState =>
      (10, none, some h, none, some word, some (state, minState), none,
        none, none, none, none, none, none, none)
  | blockEnvR h word state minState revTable =>
      (11, none, some h, none, some word, some (state, minState), none,
        none, none, some revTable, none, none, none, none)
  | recvR h word state minState revTable move =>
      (12, none, some h, none, some word, some (state, minState), none,
        some move, none, some revTable, none, none, none, none)
  | resolveR h word state minState revTable move outTwo =>
      (13, none, some h, none, some word, some (state, minState), none,
        some move, none, some revTable, none, none, some outTwo, none)
  | closeR h word state minState revTable move outTwo =>
      (14, none, some h, none, some word, some (state, minState), none,
        some move, none, some revTable, none, none, some outTwo, none)
  | closeResolveR h word state minState revTable move outTwo outOne =>
      (15, none, some h, none, some word, some (state, minState), none,
        some move, none, some revTable, some outOne, none, some outTwo,
        none)
  | revCommitL word entryState entryMin =>
      (16, none, none, some word, none, none,
        some (entryState, entryMin), none, none, none, none, none,
        none, none)
  | revBlockL hc word entryState entryMin state minState =>
      (17, none, some hc, some word, none, some (state, minState),
        some (entryState, entryMin), none, none, none, none, none,
        none, none)
  | revEnvL hc word entryState entryMin state minState sendTable =>
      (18, none, some hc, some word, none, some (state, minState),
        some (entryState, entryMin), none, some sendTable, none, none,
        none, none, none)
  | revRecvL hc word entryState entryMin state minState sendTable
      move =>
      (19, none, some hc, some word, none, some (state, minState),
        some (entryState, entryMin), some move, some sendTable, none,
        none, none, none, none)
  | revResolveL hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv =>
      (20, none, some hc, some word, none, some (state, minState),
        some (entryState, entryMin), some move, some sendTable, none,
        some outOneRecv, none, none, some outTwoRecv)
  | revCommitR word entryState entryMin =>
      (21, none, none, none, some word, none,
        some (entryState, entryMin), none, none, none, none, none,
        none, none)
  | revBlockR hc word entryState entryMin state minState =>
      (22, none, some hc, none, some word, some (state, minState),
        some (entryState, entryMin), none, none, none, none, none,
        none, none)
  | revEnvR hc word entryState entryMin state minState sendTable =>
      (23, none, some hc, none, some word, some (state, minState),
        some (entryState, entryMin), none, none, some sendTable, none,
        none, none, none)
  | revRecvR hc word entryState entryMin state minState sendTable
      move =>
      (24, none, some hc, none, some word, some (state, minState),
        some (entryState, entryMin), some move, none, some sendTable,
        none, none, none, none)
  | revResolveR hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv =>
      (25, none, some hc, none, some word, some (state, minState),
        some (entryState, entryMin), some move, none, some sendTable,
        some outOneRecv, none, none, some outTwoRecv)

set_option maxHeartbeats 3200000 in
theorem code_injective :
    Function.Injective
      (code (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        (A := A)) := by
  intro p q hpq
  cases p <;> cases q <;> simp_all [code]

/-- Round records over countable components are countable. -/
instance countableRoundRecord
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂] :
    Countable (RoundRecord In₁ In₂ Graph Out₁ Out₂) := by
  have hinj :
      Function.Injective
        (fun r : RoundRecord In₁ In₂ Graph Out₁ Out₂ =>
          (r.inputOne, r.inputTwo, r.graph, r.outputOne, r.outputTwo)) := by
    intro r r' hrr
    cases r
    cases r'
    simpa using hrr
  exact hinj.countable

instance countable
    [Fintype In₁] [Fintype In₂]
    [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂] :
    Countable (UniformizationPosition (In₁ := In₁) A) := by
  letI hstate : Countable A.State := Finite.to_countable
  letI hatom : Countable (A.State × A.State) := inferInstance
  letI hrecord : Countable (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
    countableRoundRecord
  letI hhistory : Countable (History In₁ In₂ Graph Out₁ Out₂) :=
    inferInstance
  letI hmove : Countable (In₁ × In₂) := inferInstance
  letI hwordL : Countable (List In₂) := inferInstance
  letI hwordR : Countable (List In₁) := inferInstance
  letI htabL : Countable (In₁ -> Out₁) := inferInstance
  letI htabR : Countable (In₂ -> Out₂) := inferInstance
  exact code_injective.countable

end UniformizationPosition

section Arena

variable {A}
variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable [Inhabited In₁] [Inhabited In₂]

open UniformizationPosition

/-- Even commits at boundaries and handoffs, chooses the per-round
reversal tables, and plays the staged responses. -/
def uniformizationOwner :
    UniformizationPosition (In₁ := In₁) A -> ParityPlayer
  | .bnd _ => ParityPlayer.even
  | .opening _ _ _ => ParityPlayer.even
  | .blockL _ _ _ _ => ParityPlayer.even
  | .recvL _ _ _ _ _ _ => ParityPlayer.even
  | .closeL _ _ _ _ _ _ _ => ParityPlayer.even
  | .blockR _ _ _ _ => ParityPlayer.even
  | .recvR _ _ _ _ _ _ => ParityPlayer.even
  | .closeR _ _ _ _ _ _ _ => ParityPlayer.even
  | .revCommitL _ _ _ => ParityPlayer.even
  | .revBlockL _ _ _ _ _ _ => ParityPlayer.even
  | .revRecvL _ _ _ _ _ _ _ _ => ParityPlayer.even
  | .revCommitR _ _ _ => ParityPlayer.even
  | .revBlockR _ _ _ _ _ _ => ParityPlayer.even
  | .revRecvR _ _ _ _ _ _ _ _ => ParityPlayer.even
  | _ => ParityPlayer.odd

/--
Design D3 priorities: boundary positions emit the closed block's
minimum, all other positions emit the tracked automaton state's
priority; handoff commit positions emit the entry state's priority.
-/
def uniformizationPriority :
    UniformizationPosition (In₁ := In₁) A -> Nat
  | .bnd atom => A.priority atom.2
  | .committed atom _ => A.priority atom.1
  | .opening atom _ _ => A.priority atom.1
  | .openingResolve atom _ _ _ _ => A.priority atom.1
  | .blockL _ _ state _ => A.priority state
  | .blockEnvL _ _ state _ _ => A.priority state
  | .recvL _ _ state _ _ _ => A.priority state
  | .resolveL _ _ state _ _ _ _ => A.priority state
  | .closeL _ _ state _ _ _ _ => A.priority state
  | .closeResolveL _ _ state _ _ _ _ _ => A.priority state
  | .blockR _ _ state _ => A.priority state
  | .blockEnvR _ _ state _ _ => A.priority state
  | .recvR _ _ state _ _ _ => A.priority state
  | .resolveR _ _ state _ _ _ _ => A.priority state
  | .closeR _ _ state _ _ _ _ => A.priority state
  | .closeResolveR _ _ state _ _ _ _ _ => A.priority state
  | .revCommitL _ entryState _ => A.priority entryState
  | .revBlockL _ _ _ _ state _ => A.priority state
  | .revEnvL _ _ _ _ state _ _ => A.priority state
  | .revRecvL _ _ _ _ state _ _ _ => A.priority state
  | .revResolveL _ _ _ _ state _ _ _ _ _ => A.priority state
  | .revCommitR _ entryState _ => A.priority entryState
  | .revBlockR _ _ _ _ state _ => A.priority state
  | .revEnvR _ _ _ _ state _ _ => A.priority state
  | .revRecvR _ _ _ _ state _ _ _ => A.priority state
  | .revResolveR _ _ _ _ state _ _ _ _ _ => A.priority state

/-- The target of a synchronizing round played at a boundary. -/
def uOpenBothTarget (atom : A.State × A.State) (move : In₁ × In₂)
    (outOne : Out₁) (outTwo : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  .bnd (A.step atom.1 (bothRoundRecord move outOne outTwo), atom.1)

/--
The target of a left-block opening: the receiver plays the shared
opening response, the sender's output is baked from the committed
history.
-/
def uOpenLeftTarget (atom : A.State × A.State)
    (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂)
    (outOne : Out₁) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step atom.1
      (leftRoundRecord move outOne (blockSenderTwo σ h [] move.2))
  .blockL h [move.2] next (A.minPriorityState atom.1 next)

/-- The target of a right-block opening: the orientation mirror. -/
def uOpenRightTarget (atom : A.State × A.State)
    (h : History In₁ In₂ Graph Out₁ Out₂) (move : In₁ × In₂)
    (outTwo : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step atom.1
      (rightRoundRecord (move.2, move.1)
        (blockSenderOne σ h [] move.1) outTwo)
  .blockR h [move.1] next (A.minPriorityState atom.1 next)

/-- The target of a continuation round inside a left block. -/
def uContinueLTarget (h : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂)
    (outOne : Out₁) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state
      (leftRoundRecord move outOne (blockSenderTwo σ h word move.2))
  .blockL h (word ++ [move.2]) next (A.minPriorityState minState next)

/-- The target of a continuation round inside a right block. -/
def uContinueRTarget (h : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂)
    (outTwo : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (blockSenderOne σ h word move.1) outTwo)
  .blockR h (word ++ [move.1]) next (A.minPriorityState minState next)

/-- The target of a closing round: the block minimum is emitted at
the reached boundary. -/
def uCloseTarget (state minState : A.State) (move : In₁ × In₂)
    (outOne : Out₁) (outTwo : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  .bnd (A.step state (bothRoundRecord move outOne outTwo), minState)

/--
The target of a direct reversal into a right block: the round is a
right round built from the old dominant's tabled no-receive value and
the new dominant's shared response; the reached handoff position asks
Even to commit a virtual view for the process going blind, and
freezes the entry thread.
-/
def uRevReverseRTarget (state minState : A.State) (move : In₁ × In₂)
    (outOneSend : Out₁) (outTwoRecv : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1) outOneSend outTwoRecv)
  .revCommitR [move.1] next (A.minPriorityState minState next)

/-- The target of a direct reversal into a left block: the mirror. -/
def uRevReverseLTarget (state minState : A.State) (move : In₁ × In₂)
    (outOneRecv : Out₁) (outTwoSend : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state (leftRoundRecord move outOneRecv outTwoSend)
  .revCommitL [move.2] next (A.minPriorityState minState next)

/-- The target of a continuation round inside a reversed left block:
the blind side's output is baked from the committed virtual view, the
entry thread is preserved. -/
def uRevContinueLTarget (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState entryMin state minState : A.State)
    (move : In₁ × In₂) (outOneRecv : Out₁) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state
      (leftRoundRecord move outOneRecv
        (blockSenderTwo σ hc (word.drop 1) move.2))
  .revBlockL hc (word ++ [move.2]) entryState entryMin next
    (A.minPriorityState minState next)

/-- The target of a continuation round inside a reversed right
block. -/
def uRevContinueRTarget (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState entryMin state minState : A.State)
    (move : In₁ × In₂) (outTwoRecv : Out₂) :
    UniformizationPosition (In₁ := In₁) A :=
  let next :=
    A.step state
      (rightRoundRecord (move.2, move.1)
        (blockSenderOne σ hc (word.drop 1) move.1) outTwoRecv)
  .revBlockR hc (word ++ [move.1]) entryState entryMin next
    (A.minPriorityState minState next)

/-- The edges of the uniformization game. -/
def uniformizationStep :
    UniformizationPosition (In₁ := In₁) A ->
      UniformizationPosition (In₁ := In₁) A -> Prop
  | .bnd atom, target =>
      ∃ h : History In₁ In₂ Graph Out₁ Out₂,
        target = .committed atom h
  | .committed atom h, target =>
      ∃ move : In₁ × In₂, target = .opening atom h move
  | .opening atom h move, target =>
      ∃ (outOne : Out₁) (outTwo : Out₂),
        target = .openingResolve atom h move outOne outTwo
  | .openingResolve atom h move outOne outTwo, target =>
      target = uOpenBothTarget (A := A) atom move outOne outTwo ∨
      target = uOpenLeftTarget σ atom h move outOne ∨
      target = uOpenRightTarget σ atom h move outTwo
  | .blockL h word state minState, target =>
      ∃ revTable : In₁ -> Out₁,
        target = .blockEnvL h word state minState revTable
  | .blockEnvL h word state minState revTable, target =>
      ∃ move : In₁ × In₂,
        target = .recvL h word state minState revTable move
  | .recvL h word state minState revTable move, target =>
      ∃ outOne : Out₁,
        target = .resolveL h word state minState revTable move outOne
  | .resolveL h word state minState revTable move outOne, target =>
      target = uContinueLTarget σ h word state minState move outOne ∨
      target = .closeL h word state minState revTable move outOne
  | .closeL h word state minState revTable move outOne, target =>
      ∃ outTwo : Out₂,
        target =
          .closeResolveL h word state minState revTable move outOne
            outTwo
  | .closeResolveL _h _word state minState revTable move outOne
      outTwo, target =>
      target = uCloseTarget (A := A) state minState move outOne outTwo ∨
      target = uRevReverseRTarget (A := A) state minState move
        (revTable move.1) outTwo
  | .blockR h word state minState, target =>
      ∃ revTable : In₂ -> Out₂,
        target = .blockEnvR h word state minState revTable
  | .blockEnvR h word state minState revTable, target =>
      ∃ move : In₁ × In₂,
        target = .recvR h word state minState revTable move
  | .recvR h word state minState revTable move, target =>
      ∃ outTwo : Out₂,
        target = .resolveR h word state minState revTable move outTwo
  | .resolveR h word state minState revTable move outTwo, target =>
      target = uContinueRTarget σ h word state minState move outTwo ∨
      target = .closeR h word state minState revTable move outTwo
  | .closeR h word state minState revTable move outTwo, target =>
      ∃ outOne : Out₁,
        target =
          .closeResolveR h word state minState revTable move outTwo
            outOne
  | .closeResolveR _h _word state minState revTable move outTwo
      outOne, target =>
      target = uCloseTarget (A := A) state minState move outOne outTwo ∨
      target = uRevReverseLTarget (A := A) state minState move outOne
        (revTable move.2)
  | .revCommitL word entryState entryMin, target =>
      ∃ hc : History In₁ In₂ Graph Out₁ Out₂,
        target =
          .revBlockL hc word entryState entryMin entryState entryMin
  | .revBlockL hc word entryState entryMin state minState, target =>
      ∃ sendTable : In₁ -> Out₁,
        target =
          .revEnvL hc word entryState entryMin state minState
            sendTable
  | .revEnvL hc word entryState entryMin state minState sendTable,
      target =>
      ∃ move : In₁ × In₂,
        target =
          .revRecvL hc word entryState entryMin state minState
            sendTable move
  | .revRecvL hc word entryState entryMin state minState sendTable
      move, target =>
      ∃ (outOneRecv : Out₁) (outTwoRecv : Out₂),
        target =
          .revResolveL hc word entryState entryMin state minState
            sendTable move outOneRecv outTwoRecv
  | .revResolveL hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv, target =>
      target = uRevContinueLTarget σ hc word entryState entryMin state
          minState move outOneRecv ∨
      target = uCloseTarget (A := A) state minState move outOneRecv
          outTwoRecv ∨
      target = uRevReverseRTarget (A := A) state minState move
          (sendTable move.1) outTwoRecv
  | .revCommitR word entryState entryMin, target =>
      ∃ hc : History In₁ In₂ Graph Out₁ Out₂,
        target =
          .revBlockR hc word entryState entryMin entryState entryMin
  | .revBlockR hc word entryState entryMin state minState, target =>
      ∃ sendTable : In₂ -> Out₂,
        target =
          .revEnvR hc word entryState entryMin state minState
            sendTable
  | .revEnvR hc word entryState entryMin state minState sendTable,
      target =>
      ∃ move : In₁ × In₂,
        target =
          .revRecvR hc word entryState entryMin state minState
            sendTable move
  | .revRecvR hc word entryState entryMin state minState sendTable
      move, target =>
      ∃ (outOneRecv : Out₁) (outTwoRecv : Out₂),
        target =
          .revResolveR hc word entryState entryMin state minState
            sendTable move outOneRecv outTwoRecv
  | .revResolveR hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv, target =>
      target = uRevContinueRTarget σ hc word entryState entryMin state
          minState move outTwoRecv ∨
      target = uCloseTarget (A := A) state minState move outOneRecv
          outTwoRecv ∨
      target = uRevReverseLTarget (A := A) state minState move
          outOneRecv (sendTable move.2)

variable [Inhabited Out₁] [Inhabited Out₂]

theorem uniformizationStep_total
    (position : UniformizationPosition (In₁ := In₁) A) :
    ∃ target : UniformizationPosition (In₁ := In₁) A,
      uniformizationStep σ position target := by
  cases position with
  | bnd atom => exact ⟨_, [], rfl⟩
  | committed atom h => exact ⟨_, default, rfl⟩
  | opening atom h move => exact ⟨_, default, default, rfl⟩
  | openingResolve atom h move outOne outTwo => exact ⟨_, Or.inl rfl⟩
  | blockL h word state minState =>
      exact ⟨_, fun _ => default, rfl⟩
  | blockEnvL h word state minState revTable =>
      exact ⟨_, default, rfl⟩
  | recvL h word state minState revTable move =>
      exact ⟨_, default, rfl⟩
  | resolveL h word state minState revTable move outOne =>
      exact ⟨_, Or.inl rfl⟩
  | closeL h word state minState revTable move outOne =>
      exact ⟨_, default, rfl⟩
  | closeResolveL h word state minState revTable move outOne outTwo =>
      exact ⟨_, Or.inl rfl⟩
  | blockR h word state minState =>
      exact ⟨_, fun _ => default, rfl⟩
  | blockEnvR h word state minState revTable =>
      exact ⟨_, default, rfl⟩
  | recvR h word state minState revTable move =>
      exact ⟨_, default, rfl⟩
  | resolveR h word state minState revTable move outTwo =>
      exact ⟨_, Or.inl rfl⟩
  | closeR h word state minState revTable move outTwo =>
      exact ⟨_, default, rfl⟩
  | closeResolveR h word state minState revTable move outTwo outOne =>
      exact ⟨_, Or.inl rfl⟩
  | revCommitL word entryState entryMin => exact ⟨_, [], rfl⟩
  | revBlockL hc word entryState entryMin state minState =>
      exact ⟨_, fun _ => default, rfl⟩
  | revEnvL hc word entryState entryMin state minState sendTable =>
      exact ⟨_, default, rfl⟩
  | revRecvL hc word entryState entryMin state minState sendTable
      move =>
      exact ⟨_, default, default, rfl⟩
  | revResolveL hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv =>
      exact ⟨_, Or.inl rfl⟩
  | revCommitR word entryState entryMin => exact ⟨_, [], rfl⟩
  | revBlockR hc word entryState entryMin state minState =>
      exact ⟨_, fun _ => default, rfl⟩
  | revEnvR hc word entryState entryMin state minState sendTable =>
      exact ⟨_, default, rfl⟩
  | revRecvR hc word entryState entryMin state minState sendTable
      move =>
      exact ⟨_, default, default, rfl⟩
  | revResolveR hc word entryState entryMin state minState sendTable
      move outOneRecv outTwoRecv =>
      exact ⟨_, Or.inl rfl⟩

variable [Fintype In₁] [Fintype In₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]

variable (A)

/--
The uniformization game: the single countable parity game whose
positional determinacy pays the cross-boundary accounting of the
journal construction.  Even's positional strategies commit one
virtual history per atom, one virtual view per chain handoff, one
reversal table per block round, one blind-send table per chain round,
and answer with staged values in exactly the knowledge of the acting
process.
-/
def uniformizationGame : CountableParityGame.{max u v x y s} where
  Position := UniformizationPosition (In₁ := In₁) A
  positionCountable := UniformizationPosition.countable
  owner := uniformizationOwner
  step := uniformizationStep σ
  step_total := uniformizationStep_total σ
  priority := uniformizationPriority
  priority_finite := by
    have hsub :
        Set.range (uniformizationPriority (In₁ := In₁) (A := A)) ⊆
          Set.range A.priority := by
      rintro p ⟨position, rfl⟩
      cases position <;>
        first
          | exact ⟨_, rfl⟩
    exact Set.Finite.subset (Set.finite_range A.priority) hsub

end Arena

end DetParityAutomaton

end DistributedSynthesis
