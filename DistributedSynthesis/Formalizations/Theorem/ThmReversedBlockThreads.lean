/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmBoundaryGame
import DistributedSynthesis.Formalizations.Theorem.ThmDeterministicBlockAutomaton

/-!
# Thread machinery for directly reversed blocks

The M2/M3 extension of the journal automaton's thread structure, in
information-narrowed form: per reversed-block mode, the receiving
side's tables are thread-indexed and full, while the no-receive
values depend only on data their emitter possesses (the informed
side's re-reversal value is thread-indexed over its own input, the
blind side's continuation value is a plain own-input table, realized
by baking from the virtual chain history committed at the handoff).

This file provides, per orientation of the reversed block:

* the four-value label type and the thread maps for the three round
  types (continue, close to a genuine boundary, reverse again);
* the handoff maps out of a normal block (the reversal round built
  from the normal label's shared closing response and the staged
  no-receive response) and the corresponding handoff subsets;
* the realized-thread subsets within reversed blocks;
* the narrowed thread fold along full environment words and the
  universal thread condition from a handoff thread;
* the set-started checker interfaces, whose `winning_iff` ties a
  deterministic monitor started at a handoff thread set to the
  universal thread condition over every thread of the set.

Everything here is definitional groundwork: the checker instances
come from the narrowed-thread determinization at assembly time, as in
`ThmGlobalJournalChecker.lean`.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

/--
The label of a reversed-left-mode node, in information-narrowed form:
process one (the receiving side of left rounds) has a full
thread-indexed receive table and a thread-indexed no-receive table
over its own input alone (its re-reversal value); process two (the
non-receiving side) has a no-receive table over its own input alone,
realized by baking from the virtual chain history committed at the
handoff, and a full receive table for the closing round.
-/
abbrev RevLeftBlockLabel (Q : Type w) :=
  (Q × Q -> In₁ × In₂ -> Out₁) ×
    (Q × Q -> In₁ -> Out₁) ×
    (Q -> In₂ -> Out₂) ×
    (Q × Q -> In₁ × In₂ -> Out₂)

/-- The label of a reversed-right-mode node: the mirror, with the
thread-indexed no-receive slot on process two's side. -/
abbrev RevRightBlockLabel (Q : Type w) :=
  (Q × Q -> In₁ × In₂ -> Out₁) ×
    (Q -> In₁ -> Out₁) ×
    (Q × Q -> In₂ -> Out₂) ×
    (Q × Q -> In₁ × In₂ -> Out₂)

namespace RevLeftBlockLabel

variable {Q : Type w}

/-- Process one's receive value (left and synchronizing rounds). -/
def oneRecv (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (move : In₁ × In₂) :
    Out₁ :=
  label.1 th move

/-- Process one's no-receive value (the re-reversing right round). -/
def oneSend (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (inputOne : In₁) :
    Out₁ :=
  label.2.1 th inputOne

/-- Process two's no-receive value (left rounds), indexed by the
entry thread of the chain segment. -/
def twoSend (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (entry : Q) (inputTwo : In₂) :
    Out₂ :=
  label.2.2.1 entry inputTwo

/-- Process two's receive value (the synchronizing close). -/
def twoRecv (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (move : In₁ × In₂) :
    Out₂ :=
  label.2.2.2 th move

end RevLeftBlockLabel

namespace RevRightBlockLabel

variable {Q : Type w}

/-- Process one's receive value (the synchronizing close and the
re-reversing left round). -/
def oneRecv (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (move : In₁ × In₂) :
    Out₁ :=
  label.1 th move

/-- Process one's no-receive value (right rounds), indexed by the
entry thread of the chain segment. -/
def oneSend (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (entry : Q) (inputOne : In₁) :
    Out₁ :=
  label.2.1 entry inputOne

/-- Process two's no-receive value (the re-reversing left round). -/
def twoSend (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (inputTwo : In₂) :
    Out₂ :=
  label.2.2.1 th inputTwo

/-- Process two's receive value (right and synchronizing rounds). -/
def twoRecv (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Q) (th : Q × Q) (move : In₁ × In₂) :
    Out₂ :=
  label.2.2.2 th move

end RevRightBlockLabel

variable (A)

/-- A composed chain thread: the thread at entry into the current
reversed segment, and the current thread.  The blind side's tables
are read at the entry component, everything else at the current
component; a re-reversal starts a fresh segment and doubles the
post-round thread. -/
abbrev ChainThread :=
  (A.State × A.State) × (A.State × A.State)

/-! ### Thread maps within reversed blocks

Threads carry the tracked automaton state and the sampled minimum;
the minimum continues across reversals and is emitted only at genuine
boundaries. -/

/-- The thread after a continuation round of a reversed right
block. -/
def revRightThreadStep (th : ChainThread A)
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : ChainThread A :=
  let next :=
    A.step th.2.1
      (rightRoundRecord (inputTwo, inputOne)
        (label.oneSend th.1 inputOne)
        (label.twoRecv th (inputOne, inputTwo)))
  (th.1, next, A.minPriorityState th.2.2 next)

/-- The boundary atom reached by closing a reversed right block with
a synchronizing round. -/
def revRightThreadClose (th : ChainThread A)
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  (A.step th.2.1
      (bothRoundRecord (inputOne, inputTwo)
        (label.oneRecv th (inputOne, inputTwo))
        (label.twoRecv th (inputOne, inputTwo))),
    th.2.2)

/-- The thread after reversing a reversed right block again (a left
round; the minimum continues). -/
def revRightThreadReverse (th : ChainThread A)
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : ChainThread A :=
  let next :=
    A.step th.2.1
      (leftRoundRecord (inputOne, inputTwo)
        (label.oneRecv th (inputOne, inputTwo))
        (label.twoSend th inputTwo))
  ((next, A.minPriorityState th.2.2 next),
    next, A.minPriorityState th.2.2 next)

/-- The thread after a continuation round of a reversed left block. -/
def revLeftThreadStep (th : ChainThread A)
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : ChainThread A :=
  let next :=
    A.step th.2.1
      (leftRoundRecord (inputOne, inputTwo)
        (label.oneRecv th (inputOne, inputTwo))
        (label.twoSend th.1 inputTwo))
  (th.1, next, A.minPriorityState th.2.2 next)

/-- The boundary atom reached by closing a reversed left block with a
synchronizing round. -/
def revLeftThreadClose (th : ChainThread A)
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : A.State × A.State :=
  (A.step th.2.1
      (bothRoundRecord (inputOne, inputTwo)
        (label.oneRecv th (inputOne, inputTwo))
        (label.twoRecv th (inputOne, inputTwo))),
    th.2.2)

/-- The thread after reversing a reversed left block again (a right
round; the minimum continues). -/
def revLeftThreadReverse (th : ChainThread A)
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) (inputTwo : In₂) : ChainThread A :=
  let next :=
    A.step th.2.1
      (rightRoundRecord (inputTwo, inputOne)
        (label.oneSend th inputOne)
        (label.twoRecv th (inputOne, inputTwo)))
  ((next, A.minPriorityState th.2.2 next),
    next, A.minPriorityState th.2.2 next)

/-! ### Handoff maps out of a normal block

The reversal round out of a normal block is built from the normal
label's shared closing response and the staged no-receive response of
the old dominant; the minimum continues. -/

variable {A}

/-- The thread after directly reversing out of a normal left block:
a right round from the old dominant's staged no-receive response and
the shared closing response. -/
def leftThreadReverse (qm : A.State × A.State)
    (close : (A.State × A.State) -> In₁ × In₂ -> Out₂)
    (rev : (A.State × A.State) -> In₁ -> Out₁)
    (inputOne : In₁) (inputTwo : In₂) : ChainThread A :=
  let next :=
    A.step qm.1
      (rightRoundRecord (inputTwo, inputOne)
        (rev qm inputOne) (close qm (inputOne, inputTwo)))
  ((next, A.minPriorityState qm.2 next),
    next, A.minPriorityState qm.2 next)

/-- The thread after directly reversing out of a normal right block:
the mirror. -/
def rightThreadReverse (qm : A.State × A.State)
    (close : (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (rev : (A.State × A.State) -> In₂ -> Out₂)
    (inputTwo : In₂) (inputOne : In₁) : ChainThread A :=
  let next :=
    A.step qm.1
      (leftRoundRecord (inputOne, inputTwo)
        (close qm (inputTwo, inputOne)) (rev qm inputTwo))
  ((next, A.minPriorityState qm.2 next),
    next, A.minPriorityState qm.2 next)

section Subsets

variable [Fintype In₁] [Fintype In₂] [DecidableEq A.State]

/-- The handoff thread set of a direct reversal out of a normal left
block: every realized thread closed through the reversal round, over
the new receiver's private inputs. -/
def leftReverseSubset (threads : Finset (A.State × A.State))
    (close : (A.State × A.State) -> In₁ × In₂ -> Out₂)
    (rev : (A.State × A.State) -> In₁ -> Out₁)
    (inputOne : In₁) : Finset (ChainThread A) :=
  threads.biUnion fun qm =>
    Finset.image
      (fun inputTwo => leftThreadReverse qm close rev inputOne inputTwo)
      Finset.univ

/-- The handoff thread set of a direct reversal out of a normal right
block: the mirror. -/
def rightReverseSubset (threads : Finset (A.State × A.State))
    (close : (A.State × A.State) -> In₂ × In₁ -> Out₁)
    (rev : (A.State × A.State) -> In₂ -> Out₂)
    (inputTwo : In₂) : Finset (ChainThread A) :=
  threads.biUnion fun qm =>
    Finset.image
      (fun inputOne => rightThreadReverse qm close rev inputTwo inputOne)
      Finset.univ

/-- The realized threads after a continuation round of a reversed
right block. -/
def revRightStepSubset (threads : Finset (ChainThread A))
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) : Finset (ChainThread A) :=
  threads.biUnion fun th =>
    Finset.image
      (fun inputTwo => revRightThreadStep A th label inputOne inputTwo)
      Finset.univ

/-- The boundary atoms reachable by closing a reversed right block. -/
def revRightCloseSubset (threads : Finset (ChainThread A))
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State)) :
    Finset (A.State × A.State) :=
  threads.biUnion fun th =>
    Finset.image
      (fun move : In₁ × In₂ =>
        revRightThreadClose A th label move.1 move.2)
      Finset.univ

/-- The handoff thread set of reversing a reversed right block
again. -/
def revRightReverseSubset (threads : Finset (ChainThread A))
    (label : RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputTwo : In₂) : Finset (ChainThread A) :=
  threads.biUnion fun th =>
    Finset.image
      (fun inputOne =>
        revRightThreadReverse A th label inputOne inputTwo)
      Finset.univ

/-- The realized threads after a continuation round of a reversed
left block. -/
def revLeftStepSubset (threads : Finset (ChainThread A))
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputTwo : In₂) : Finset (ChainThread A) :=
  threads.biUnion fun th =>
    Finset.image
      (fun inputOne => revLeftThreadStep A th label inputOne inputTwo)
      Finset.univ

/-- The boundary atoms reachable by closing a reversed left block. -/
def revLeftCloseSubset (threads : Finset (ChainThread A))
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State)) :
    Finset (A.State × A.State) :=
  threads.biUnion fun th =>
    Finset.image
      (fun move : In₁ × In₂ =>
        revLeftThreadClose A th label move.1 move.2)
      Finset.univ

/-- The handoff thread set of reversing a reversed left block
again. -/
def revLeftReverseSubset (threads : Finset (ChainThread A))
    (label : RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State))
    (inputOne : In₁) : Finset (ChainThread A) :=
  threads.biUnion fun th =>
    Finset.image
      (fun inputTwo =>
        revLeftThreadReverse A th label inputOne inputTwo)
      Finset.univ

end Subsets

/-! ### The composed-thread fold of a reversal chain

Across a chain of directly reversed blocks, a left-sorted direction
is a left round (continuing a reversed left block or reversing a
reversed right block) and a right-sorted direction is a right round,
regardless of the current mode: the two step formulas coincide.  The
composed threads therefore fold uniformly over the mixed direction
alphabet, with the sampled minimum continuing throughout. -/

variable (A)

/-- One composed-thread step of a reversal chain: the direction sort
selects the round type, the opposite component of the full move is
the universal receiver input. -/
def chainThreadStep (th : ChainThread A)
    (label :
      RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) (A.State × A.State) ⊕
        RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) (A.State × A.State)) :
    In₂ ⊕ In₁ -> In₁ × In₂ -> ChainThread A
  | Sum.inl inputTwo, move =>
      match label with
      | Sum.inl labL => revLeftThreadStep A th labL move.1 inputTwo
      | Sum.inr labR => revRightThreadReverse A th labR move.1 inputTwo
  | Sum.inr inputOne, move =>
      match label with
      | Sum.inl labL => revLeftThreadReverse A th labL inputOne move.2
      | Sum.inr labR => revRightThreadStep A th labR inputOne move.2

variable (In₁ In₂ Out₁ Out₂) in
/-- The mixed chain alphabet: the mode-typed reversed-block labels. -/
abbrev ChainLabel (Q : Type w) :=
  RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) Q ⊕
    RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) Q

/-- The composed-thread fold along a chain subtree: nodes carry the
mode-typed label of their reversed block, branches are the mixed
directions, the universal dimension is the full move. -/
def chainFold
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    List (In₂ ⊕ In₁) -> ChainThread A ->
      TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)) -> ChainThread A
  | _, th, [] => th
  | word, th, step :: rest =>
      chainFold narrowed (word ++ [step.2])
        (chainThreadStep A th (narrowed word) step.2 step.1) rest

/--
The universal composed-thread condition of a reversal chain from a
handoff thread: along every direction sequence and every sequence of
full moves, the tracked automaton state is min-even.
-/
def ChainAllThreadsWin
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))
    (th₀ : ChainThread A) : Prop :=
  ∀ env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁),
    NatSeqMinEvenParity
      (fun n =>
        A.priority
          (chainFold A narrowed [] th₀ (branchNode env n)).2.1)

/-! ### The chain checker

One deterministic monitor runs across the entire reversal chain: it
starts at the handoff thread set of the first direct reversal and is
stepped, never restarted, through continuations and re-reversals
alike.  Restarting per reversed block would be unsound: on a branch
that alternates reversed blocks forever nothing is emitted below the
priority shift, and finite checker prefixes carry no semantic
content.  The instance comes from the composed-thread determinization
at assembly time. -/

/--
A universal composed-thread checker for reversal chains: a
deterministic monitor over mixed directions and mode-typed
reversed-block labels, started per handoff thread set, whose
branchwise parity decides whether every composed thread from the set
wins.
-/
structure ChainThreadChecker [DecidableEq A.State] where
  monitor :
    DeterministicBlockMonitor.{max u v, max u v x y s, s}
      (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))
  start : Finset (ChainThread A) -> monitor.State
  winning_iff :
    ∀ (threads : Finset (ChainThread A))
      (narrowed :
        LabeledTree (In₂ ⊕ In₁)
          (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))),
      DeterministicBlockMonitor.WinningTree
          { monitor with initial := start threads } narrowed ↔
        ∀ th ∈ threads, ChainAllThreadsWin A narrowed th

end DetParityAutomaton

end DistributedSynthesis
