/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalAutomaton
import DistributedSynthesis.Formalizations.Theorem.ThmUniformizationParity

/-!
# The journal tree of a positional uniformization winner

The tree fed to the global journal automaton: a positional Even
winner of the uniformization game commits one virtual history per
atom, and its staged choices along that history label the journal
tree.  A node parses into its last atom event and the trailing
homogeneous sender segment; the label at an atom node carries the
opening tables (the shared fringe responses and the baked sender
outputs at the empty word), the label at a block node carries the
in-block receiver table, the baked sender map, and the closing table
read off the winner's choices at the corresponding staged positions.
Mixed segments are sink-bound in the automaton, so their labels are
irrelevant defaults.
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

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)

/-- The committed history of an atom. -/
noncomputable def commitmentOf (atom : A.State × A.State) :
    History In₁ In₂ Graph Out₁ Out₂ :=
  (exists_commitment_of_positional σ τ atom).choose

theorem commitmentOf_spec (atom : A.State × A.State) :
    τ.move (.bnd atom) = .committed atom (commitmentOf σ τ atom) :=
  (exists_commitment_of_positional σ τ atom).choose_spec

/-- The shared fringe responses committed at an opening. -/
noncomputable def openingChoice (atom : A.State × A.State)
    (move : In₁ × In₂) : Out₁ × Out₂ :=
  match τ.move (.opening atom (commitmentOf σ τ atom) move) with
  | .openingResolve _ _ _ outOne outTwo => (outOne, outTwo)
  | _ => default

/-- The per-round reversal table committed at a left block: process
one's no-receive responses for a direct reversal out of the block. -/
noncomputable def blockRevTableL (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) : In₁ -> Out₁ :=
  match
    τ.move (.blockL (commitmentOf σ τ atom) word state minState) with
  | .blockEnvL _ _ _ _ tbl => tbl
  | _ => default

/-- The per-round reversal table committed at a right block: the
mirror. -/
noncomputable def blockRevTableR (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) : In₂ -> Out₂ :=
  match
    τ.move (.blockR (commitmentOf σ τ atom) word state minState) with
  | .blockEnvR _ _ _ _ tbl => tbl
  | _ => default

/-- The in-block receiver response of a left block, read at the
receiver stage after the block's reversal table has been committed. -/
noncomputable def recvChoiceL (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂) :
    Out₁ :=
  match
    τ.move
      (.recvL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move) with
  | .resolveL _ _ _ _ _ _ outOne => outOne
  | _ => default

/-- The in-block receiver response of a right block. -/
noncomputable def recvChoiceR (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂) :
    Out₂ :=
  match
    τ.move
      (.recvR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move) with
  | .resolveR _ _ _ _ _ _ outTwo => outTwo
  | _ => default

/-- The closing response of a left block, read off through choice
because the closing output is absorbed into the reached state. -/
noncomputable def closeChoiceL (atom : A.State × A.State)
    (word : List In₂) (state minState : A.State) (move : In₁ × In₂) :
    Out₂ :=
  (τ.legal
      (.closeL (commitmentOf σ τ atom) word state minState
        (blockRevTableL σ τ atom word state minState) move
        (recvChoiceL σ τ atom word state minState move))
      rfl).choose

/-- The closing response of a right block. -/
noncomputable def closeChoiceR (atom : A.State × A.State)
    (word : List In₁) (state minState : A.State) (move : In₁ × In₂) :
    Out₁ :=
  (τ.legal
      (.closeR (commitmentOf σ τ atom) word state minState
        (blockRevTableR σ τ atom word state minState) move
        (recvChoiceR σ τ atom word state minState move))
      rfl).choose

/-- The virtual view committed for the process going blind at a
handoff into a reversed left block. -/
noncomputable def commitmentRevL (word : List In₂)
    (entryState entryMin : A.State) : History In₁ In₂ Graph Out₁ Out₂ :=
  match τ.move (.revCommitL word entryState entryMin) with
  | .revBlockL hc _ _ _ _ _ => hc
  | _ => default

/-- The virtual view committed at a handoff into a reversed right
block. -/
noncomputable def commitmentRevR (word : List In₁)
    (entryState entryMin : A.State) : History In₁ In₂ Graph Out₁ Out₂ :=
  match τ.move (.revCommitR word entryState entryMin) with
  | .revBlockR hc _ _ _ _ _ => hc
  | _ => default

/-- The per-round blind-send table committed inside a reversed left
block: process one's re-reversal responses for a direct reversal back
out of the reversed block. -/
noncomputable def revSendTableL (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₂) (entryState entryMin state minState : A.State) :
    In₁ -> Out₁ :=
  match
    τ.move (.revBlockL hc word entryState entryMin state minState) with
  | .revEnvL _ _ _ _ _ _ tbl => tbl
  | _ => default

/-- The per-round blind-send table committed inside a reversed right
block: the mirror. -/
noncomputable def revSendTableR (hc : History In₁ In₂ Graph Out₁ Out₂)
    (word : List In₁) (entryState entryMin state minState : A.State) :
    In₂ -> Out₂ :=
  match
    τ.move (.revBlockR hc word entryState entryMin state minState) with
  | .revEnvR _ _ _ _ _ _ tbl => tbl
  | _ => default

/-- The shared receive responses staged inside a reversed left block:
process one's and process two's synchronizing outputs. -/
noncomputable def revRecvChoiceL
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₂)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂) :
    Out₁ × Out₂ :=
  match
    τ.move
      (.revRecvL hc word entryState entryMin state minState
        (revSendTableL σ τ hc word entryState entryMin state minState)
        move) with
  | .revResolveL _ _ _ _ _ _ _ _ o1r o2r => (o1r, o2r)
  | _ => default

/-- The shared receive responses staged inside a reversed right
block. -/
noncomputable def revRecvChoiceR
    (hc : History In₁ In₂ Graph Out₁ Out₂) (word : List In₁)
    (entryState entryMin state minState : A.State) (move : In₁ × In₂) :
    Out₁ × Out₂ :=
  match
    τ.move
      (.revRecvR hc word entryState entryMin state minState
        (revSendTableR σ τ hc word entryState entryMin state minState)
        move) with
  | .revResolveR _ _ _ _ _ _ _ _ o1r o2r => (o1r, o2r)
  | _ => default

/-- The opening label of a left block below an atom. -/
noncomputable def tauOpeningLeftLabel (atom : A.State × A.State) :
    NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State) :=
  (fun inputTwo => blockSenderTwo σ (commitmentOf σ τ atom) [] inputTwo,
    fun _ move => (openingChoice σ τ atom move).1)

/-- The opening label of a right block below an atom. -/
noncomputable def tauOpeningRightLabel (atom : A.State × A.State) :
    NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State) :=
  (fun inputOne => blockSenderOne σ (commitmentOf σ τ atom) [] inputOne,
    fun _ move => (openingChoice σ τ atom (move.2, move.1)).2)

/-- The in-block label of a left block node. -/
noncomputable def tauLeftLabel (atom : A.State × A.State)
    (word : List In₂) :
    NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State) :=
  (fun inputTwo => blockSenderTwo σ (commitmentOf σ τ atom) word inputTwo,
    fun qm move => recvChoiceL σ τ atom word qm.1 qm.2 move)

/-- The in-block label of a right block node. -/
noncomputable def tauRightLabel (atom : A.State × A.State)
    (word : List In₁) :
    NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State) :=
  (fun inputOne => blockSenderOne σ (commitmentOf σ τ atom) word inputOne,
    fun qm move =>
      recvChoiceR σ τ atom word qm.1 qm.2 (move.2, move.1))

/-- The closing table of a left block node. -/
noncomputable def tauLeftClose (atom : A.State × A.State)
    (word : List In₂) :
    (A.State × A.State) -> In₁ × In₂ -> Out₂ :=
  fun qm move => closeChoiceL σ τ atom word qm.1 qm.2 move

/-- The closing table of a right block node. -/
noncomputable def tauRightClose (atom : A.State × A.State)
    (word : List In₁) :
    (A.State × A.State) -> In₂ × In₁ -> Out₁ :=
  fun qm move => closeChoiceR σ τ atom word qm.1 qm.2 (move.2, move.1)

/-- The block-level reversal table of a left block node: process one's
committed no-receive responses for the direct reversal out. -/
noncomputable def tauLeftRev (atom : A.State × A.State)
    (word : List In₂) :
    (A.State × A.State) -> In₁ -> Out₁ :=
  fun qm inputOne => blockRevTableL σ τ atom word qm.1 qm.2 inputOne

/-- The block-level reversal table of a right block node: the
mirror. -/
noncomputable def tauRightRev (atom : A.State × A.State)
    (word : List In₁) :
    (A.State × A.State) -> In₂ -> Out₂ :=
  fun qm inputTwo => blockRevTableR σ τ atom word qm.1 qm.2 inputTwo

/-- The label of a reversed left block node, in narrowed form: the
receive slots are staged, process one's re-reversal value is the
committed blind-send table, and process two's no-receive value is
baked from the virtual view committed for it at the segment's
handoff, keyed by the entry thread and the entry direction. -/
noncomputable def tauRevLeftLabel (word : List In₂) :
    RevLeftBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State) :=
  (fun th move =>
      (revRecvChoiceL σ τ
          (commitmentRevL σ τ [word.headD default] th.1.1 th.1.2) word
          th.1.1 th.1.2 th.2.1 th.2.2 move).1,
    fun th inputOne =>
      revSendTableL σ τ
        (commitmentRevL σ τ [word.headD default] th.1.1 th.1.2) word
        th.1.1 th.1.2 th.2.1 th.2.2 inputOne,
    fun entry inputTwo =>
      blockSenderTwo σ (commitmentRevL σ τ [word.headD default] entry.1 entry.2)
        (word.drop 1) inputTwo,
    fun th move =>
      (revRecvChoiceL σ τ
          (commitmentRevL σ τ [word.headD default] th.1.1 th.1.2) word
          th.1.1 th.1.2 th.2.1 th.2.2 move).2)

/-- The label of a reversed right block node, in narrowed form: the
mirror. -/
noncomputable def tauRevRightLabel (word : List In₁) :
    RevRightBlockLabel (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
      (Out₂ := Out₂) (A.State × A.State) :=
  (fun th move =>
      (revRecvChoiceR σ τ
          (commitmentRevR σ τ [word.headD default] th.1.1 th.1.2) word
          th.1.1 th.1.2 th.2.1 th.2.2 move).1,
    fun entry inputOne =>
      blockSenderOne σ (commitmentRevR σ τ [word.headD default] entry.1 entry.2)
        (word.drop 1) inputOne,
    fun th inputTwo =>
      revSendTableR σ τ
        (commitmentRevR σ τ [word.headD default] th.1.1 th.1.2) word
        th.1.1 th.1.2 th.2.1 th.2.2 inputTwo,
    fun th move =>
      (revRecvChoiceR σ τ
          (commitmentRevR σ τ [word.headD default] th.1.1 th.1.2) word
          th.1.1 th.1.2 th.2.1 th.2.2 move).2)

/-- The parse of a tree node: the last atom event, the trailing
homogeneous sender segment, or the reversed segment since the last
orientation switch. -/
inductive TauNodeState where
  | atNode (atom : A.State × A.State)
  | inLeft (atom : A.State × A.State) (word : List In₂)
  | inRight (atom : A.State × A.State) (word : List In₁)
  | inRevLeft (word : List In₂)
  | inRevRight (word : List In₁)
  | junk

/-- One parsing step per tree direction: orientation switches enter
the reversed segments. -/
def tauNodeStep :
    TauNodeState (In₁ := In₁) (In₂ := In₂) (A := A) ->
      GlobalJournalBranch (In₁ := In₁) A ->
      TauNodeState (In₁ := In₁) (In₂ := In₂) (A := A)
  | _, Sum.inl atom' => .atNode atom'
  | .atNode atom, Sum.inr (Sum.inl inputTwo) => .inLeft atom [inputTwo]
  | .atNode atom, Sum.inr (Sum.inr inputOne) => .inRight atom [inputOne]
  | .inLeft atom word, Sum.inr (Sum.inl inputTwo) =>
      .inLeft atom (word ++ [inputTwo])
  | .inLeft _ _, Sum.inr (Sum.inr inputOne) => .inRevRight [inputOne]
  | .inRight atom word, Sum.inr (Sum.inr inputOne) =>
      .inRight atom (word ++ [inputOne])
  | .inRight _ _, Sum.inr (Sum.inl inputTwo) => .inRevLeft [inputTwo]
  | .inRevLeft word, Sum.inr (Sum.inl inputTwo) =>
      .inRevLeft (word ++ [inputTwo])
  | .inRevLeft _, Sum.inr (Sum.inr inputOne) => .inRevRight [inputOne]
  | .inRevRight word, Sum.inr (Sum.inr inputOne) =>
      .inRevRight (word ++ [inputOne])
  | .inRevRight _, Sum.inr (Sum.inl inputTwo) => .inRevLeft [inputTwo]
  | .junk, _ => .junk

/-- The parse of a node. -/
def tauNodeState
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    TauNodeState (In₁ := In₁) (In₂ := In₂) (A := A) :=
  node.foldl tauNodeStep (.atNode (A.initial, A.initial))

/-- The label of a parsed node. -/
noncomputable def tauLabelOf :
    TauNodeState (In₁ := In₁) (In₂ := In₂) (A := A) ->
      GlobalJournalLabel (In₁ := In₁) A
  | .atNode atom =>
      (tauOpeningLeftLabel σ τ atom, default, default,
        tauOpeningRightLabel σ τ atom, default, default, default,
        default)
  | .inLeft atom word =>
      (tauLeftLabel σ τ atom word, tauLeftClose σ τ atom word,
        tauLeftRev σ τ atom word, default, default, default, default,
        default)
  | .inRight atom word =>
      (default, default, default, tauRightLabel σ τ atom word,
        tauRightClose σ τ atom word, tauRightRev σ τ atom word,
        default, default)
  | .inRevLeft word =>
      (default, default, default, default, default, default,
        tauRevLeftLabel σ τ word, default)
  | .inRevRight word =>
      (default, default, default, default, default, default, default,
        tauRevRightLabel σ τ word)
  | .junk => default

/-- The journal tree of the positional uniformization winner. -/
noncomputable def tauTree :
    LabeledTree (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A) :=
  fun node => tauLabelOf σ τ (tauNodeState node)

@[simp]
theorem tauNodeState_nil :
    tauNodeState (In₂ := In₂) (A := A) ([] : TreeNode _) =
      .atNode (A.initial, A.initial) :=
  rfl

theorem tauNodeState_append
    (node : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    tauNodeState (In₂ := In₂) (node ++ [branch]) =
      tauNodeStep (tauNodeState node) branch := by
  simp [tauNodeState, List.foldl_append]

end DetParityAutomaton

end DistributedSynthesis
