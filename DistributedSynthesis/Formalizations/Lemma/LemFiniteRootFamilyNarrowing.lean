/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting
import DistributedSynthesis.Formalizations.Lemma.LemStateControlledTreeRationalization

/-!
# Simultaneous narrowing of a finite family of block roots

The sender of a one-directional block cannot distinguish several hidden
global anchors that represent the same local view.  Rationalizing one block
tree per anchor independently therefore loses a real strategy invariant: the
selected finite trees may emit different sender outputs at the same sender
word.

This file supplies the reusable repair.  A finite family of record monitors
with the same physical alphabets is folded into one monitor.  The hidden
receiver input chooses the family member on the first round and must retain
that choice thereafter; a changed tag enters an accepting sink.  Consequently
one sender tree is checked simultaneously against every family member.

Applying the unconditional universal-thread narrowing theorem once produces
one finite controller.  Its sender table is shared definitionally by all
family members.  No member tag, orientation, or leader bit is exposed to the
sender.
-/

namespace DistributedSynthesis

universe i u v x y w

section

variable {I : Type i} {RIn : Type u} {SIn : Type v}
variable {ROut : Type x} {SOut : Type y}
variable (M : I → BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

namespace BlockRecordMonitor

/-- Restart a block monitor from a state reached inside an earlier block.
Parity is prefix independent, so these restarted monitors are the finite
objects needed to compare a continued anchor with a freshly opened anchor. -/
def restartAt
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (state : base.State) :
    BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut where
  State := base.State
  stateFinite := base.stateFinite
  initial := state
  step := base.step
  priority := base.priority

/-- A restarted run is the corresponding suffix of the original run. -/
theorem restartAt_run_eq_suffix
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) (cut : Nat) :
    ∀ n,
      (base.restartAt (base.run play cut)).run (fun k => play (cut + k)) n =
        base.run play (cut + n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, ih]
      change base.step (base.run play (cut + n)) (play (cut + n)) =
        base.run play (cut + (n + 1))
      rw [show cut + (n + 1) = (cut + n) + 1 by omega,
        BlockRecordMonitor.run]

/-- Every winning play remains winning after rebasing its monitor and play at
an arbitrary finite cut. -/
theorem restartAt_wins_suffix
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) (cut : Nat)
    (hwin : base.WinsPlay play) :
    (base.restartAt (base.run play cut)).WinsPlay
      (fun k => play (cut + k)) := by
  let priorities : Nat → Nat := fun n => base.priority (base.run play n)
  have hshift : NatSeqMinEvenParity (fun n => priorities (cut + n)) :=
    (natSeqMinEvenParity_shift priorities cut).mpr hwin
  change NatSeqMinEvenParity (fun n =>
    base.priority
      ((base.restartAt (base.run play cut)).run
        (fun k => play (cut + k)) n))
  simpa only [priorities, base.restartAt_run_eq_suffix play cut] using hshift

/-- A sticky safety bit can be read back from a winning restarted monitor,
even when the restart state is supplied directly rather than exhibited as a
prefix of a particular play.  This is the generic form needed at a hidden
root-family seam: the proof-side anchor carries the finite monitor state, but
the shared sender controller sees only the continuation. -/
theorem restartAt_safe_of_wins
    (base : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
    (safe : base.State → Bool)
    (hstep : ∀ state round, safe state = false →
      safe (base.step state round) = false)
    (hpriority : ∀ state, safe state = false →
      base.priority state = 1)
    (start : base.State)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut)
    (hwin : (base.restartAt start).WinsPlay play) (n : Nat) :
    safe ((base.restartAt start).run play n) = true := by
  by_contra hnot
  have hfalse : safe ((base.restartAt start).run play n) = false :=
    Bool.eq_false_of_not_eq_true hnot
  have hpersist : ∀ k, n ≤ k →
      safe ((base.restartAt start).run play k) = false := by
    intro k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
    induction m with
    | zero => simpa using hfalse
    | succ m ih =>
        rw [Nat.add_succ, BlockRecordMonitor.run]
        exact hstep _ _ (ih (Nat.le_add_right n m))
  have heventual : ∀ k, n ≤ k →
      (base.restartAt start).priority
        ((base.restartAt start).run play k) = 1 := by
    intro k hk
    exact hpriority _ (hpersist k hk)
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwin

end BlockRecordMonitor

/-- State of the finite-family monitor: before choosing a hidden member,
inside one member, or in the harmless sink reached by an illegal tag change. -/
inductive FiniteRootFamilyState where
  | initial
  | active (index : I) (state : (M index).State)
  | sink

namespace FiniteRootFamilyState

variable [Fintype I]

noncomputable instance : Fintype (FiniteRootFamilyState M) := by
  classical
  letI (index : I) : Fintype (M index).State := (M index).stateFinite
  let Rep := Unit ⊕ (Sigma fun index => (M index).State) ⊕ Unit
  let e : FiniteRootFamilyState M ≃ Rep :=
    { toFun := fun state =>
        match state with
        | .initial => .inl ()
        | .active index state => .inr (.inl ⟨index, state⟩)
        | .sink => .inr (.inr ())
      invFun := fun state =>
        match state with
        | .inl _ => .initial
        | .inr (.inl ⟨index, state⟩) => .active index state
        | .inr (.inr _) => .sink
      left_inv := by intro state; cases state <;> rfl
      right_inv := by
        intro state
        cases state with
        | inl value => cases value; rfl
        | inr tagged =>
            cases tagged with
            | inl sigma => rcases sigma with ⟨index, state⟩; rfl
            | inr value => cases value; rfl }
  exact Fintype.ofEquiv Rep e.symm

end FiniteRootFamilyState

/-- Forget the hidden family tag in a realized round. -/
def finiteRootFamilyRecord
    (letter : RealizedBlockRound (I × RIn) SIn ROut SOut) :
    RealizedBlockRound RIn SIn ROut SOut :=
  ((letter.1.1.2, letter.1.2), letter.2.1, letter.2.2)

/-- The family tag carried by a realized round. -/
def finiteRootFamilyIndex
    (letter : RealizedBlockRound (I × RIn) SIn ROut SOut) : I :=
  letter.1.1.1

/-- One monitor whose valid threads are precisely the constant-tag threads of
the members of `M`.  Tag changes are invalid hidden histories and therefore
move to an even sink. -/
noncomputable def finiteRootFamilyMonitor
    [Fintype I] [DecidableEq I] :
    BlockRecordMonitor (I × RIn) SIn ROut SOut := by
  classical
  exact {
    State := FiniteRootFamilyState M
    stateFinite := inferInstance
    initial := .initial
    step := fun state letter =>
      match state with
      | .initial =>
          .active (finiteRootFamilyIndex letter)
            ((M (finiteRootFamilyIndex letter)).step
              (M (finiteRootFamilyIndex letter)).initial
              (finiteRootFamilyRecord letter))
      | .active index state =>
          if h : finiteRootFamilyIndex letter = index then
            .active index
              ((M index).step state (finiteRootFamilyRecord letter))
          else .sink
      | .sink => .sink
    priority := fun state =>
      match state with
      | .initial => 0
      | .active index state => (M index).priority state
      | .sink => 0
  }

/-- Tag every receiver input by one fixed family member. -/
def tagFiniteRootEnvironment (index : I) (env : Nat → RIn × SIn) :
    Nat → (I × RIn) × SIn :=
  fun n => ((index, (env n).1), (env n).2)

/-- Project a family environment to the physical receiver/sender inputs. -/
def untagFiniteRootEnvironment (env : Nat → (I × RIn) × SIn) :
    Nat → RIn × SIn :=
  fun n => ((env n).1.2, (env n).2)

@[simp] theorem finiteRootFamilyRecord_tagged
    (index : I) (move : RIn × SIn) (receiver : ROut) (sender : SOut) :
    finiteRootFamilyRecord
      (I := I) (((index, move.1), move.2), receiver, sender) =
        (move, receiver, sender) := rfl

@[simp] theorem finiteRootFamilyIndex_tagged
    (index : I) (move : RIn × SIn) (receiver : ROut) (sender : SOut) :
    finiteRootFamilyIndex
      (RIn := RIn) (SIn := SIn) (ROut := ROut) (SOut := SOut)
      (((index, move.1), move.2), receiver, sender) = index := rfl

/-- Tag every realized round of one member by that fixed member. -/
def tagFiniteRootPlay (index : I)
    (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    Nat → RealizedBlockRound (I × RIn) SIn ROut SOut :=
  fun n =>
    (((index, (play n).1.1), (play n).1.2), (play n).2.1, (play n).2.2)

@[simp] theorem finiteRootFamilyRecord_tagFiniteRootPlay
    (index : I) (play : Nat → RealizedBlockRound RIn SIn ROut SOut)
    (n : Nat) :
    finiteRootFamilyRecord (tagFiniteRootPlay index play n) = play n := by
  simp [tagFiniteRootPlay, finiteRootFamilyRecord]

@[simp] theorem finiteRootFamilyIndex_tagFiniteRootPlay
    (index : I) (play : Nat → RealizedBlockRound RIn SIn ROut SOut)
    (n : Nat) :
    finiteRootFamilyIndex (tagFiniteRootPlay index play n) = index := by
  rfl

theorem finiteRootFamilyMonitor_run_tagged_succ
    [Fintype I] [DecidableEq I]
    (index : I) (play : Nat → RealizedBlockRound RIn SIn ROut SOut) :
    ∀ n : Nat,
      (finiteRootFamilyMonitor M).run (tagFiniteRootPlay index play) (n + 1) =
        .active index ((M index).run play (n + 1)) := by
  intro n
  induction n with
  | zero =>
      simp [BlockRecordMonitor.run, finiteRootFamilyMonitor,
        tagFiniteRootPlay, finiteRootFamilyIndex, finiteRootFamilyRecord]
  | succ n ih =>
      change
        (finiteRootFamilyMonitor M).run (tagFiniteRootPlay index play)
            ((n + 1) + 1) =
          .active index ((M index).run play ((n + 1) + 1))
      rw [BlockRecordMonitor.run, ih, BlockRecordMonitor.run]
      simp [finiteRootFamilyMonitor, tagFiniteRootPlay,
        finiteRootFamilyIndex, finiteRootFamilyRecord]
      rw [show n + 1 + 1 = (n + 1) + 1 by omega,
        BlockRecordMonitor.run]
      simp only [BlockRecordMonitor.run]

/-- A winning member play remains winning after the harmless family tag and
the single initial family-selection state. -/
theorem finiteRootFamilyMonitor_wins_tagged
    [Fintype I] [DecidableEq I]
    (index : I) (play : Nat → RealizedBlockRound RIn SIn ROut SOut)
    (hwin : (M index).WinsPlay play) :
    (finiteRootFamilyMonitor M).WinsPlay (tagFiniteRootPlay index play) := by
  let familyPriorities : Nat → Nat := fun n =>
    (finiteRootFamilyMonitor M).priority
      ((finiteRootFamilyMonitor M).run (tagFiniteRootPlay index play) n)
  let memberPriorities : Nat → Nat := fun n =>
    (M index).priority ((M index).run play n)
  have hmember : NatSeqMinEvenParity memberPriorities := hwin
  have hmemberShift :
      NatSeqMinEvenParity (fun n => memberPriorities (1 + n)) :=
    (natSeqMinEvenParity_shift memberPriorities 1).mpr hmember
  have hshift :
      (fun n => familyPriorities (1 + n)) =
        fun n => memberPriorities (1 + n) := by
    funext n
    simp only [familyPriorities, memberPriorities]
    rw [show 1 + n = n + 1 by omega,
      finiteRootFamilyMonitor_run_tagged_succ M index play n]
    rfl
  have hfamilyShift :
      NatSeqMinEvenParity (fun n => familyPriorities (1 + n)) := by
    rw [hshift]
    exact hmemberShift
  exact (natSeqMinEvenParity_shift familyPriorities 1).mp hfamilyShift

theorem finiteRootFamilyMonitor_run_active_or_sink
    [Fintype I] [DecidableEq I]
    (play : Nat → RealizedBlockRound (I × RIn) SIn ROut SOut) :
    ∀ n : Nat,
      (finiteRootFamilyMonitor M).run play (n + 1) = .sink ∨
        ∃ state : (M (finiteRootFamilyIndex (play 0))).State,
          (finiteRootFamilyMonitor M).run play (n + 1) =
            .active (finiteRootFamilyIndex (play 0)) state := by
  intro n
  induction n with
  | zero =>
      right
      refine ⟨(M (finiteRootFamilyIndex (play 0))).step
        (M (finiteRootFamilyIndex (play 0))).initial
        (finiteRootFamilyRecord (play 0)), ?_⟩
      simp [BlockRecordMonitor.run, finiteRootFamilyMonitor]
  | succ n ih =>
      change
        (finiteRootFamilyMonitor M).run play ((n + 1) + 1) = .sink ∨
          ∃ state : (M (finiteRootFamilyIndex (play 0))).State,
            (finiteRootFamilyMonitor M).run play ((n + 1) + 1) =
              .active (finiteRootFamilyIndex (play 0)) state
      rw [BlockRecordMonitor.run]
      rcases ih with hsink | ⟨state, hstate⟩
      · left
        rw [hsink]
        rfl
      · rw [hstate]
        by_cases hindex : finiteRootFamilyIndex (play (n + 1)) =
            finiteRootFamilyIndex (play 0)
        · right
          refine ⟨(M (finiteRootFamilyIndex (play 0))).step state
            (finiteRootFamilyRecord (play (n + 1))), ?_⟩
          simp [finiteRootFamilyMonitor, hindex]
        · left
          simp [finiteRootFamilyMonitor, hindex]

theorem finiteRootFamilyMonitor_run_sink_of_mismatch
    [Fintype I] [DecidableEq I]
    (play : Nat → RealizedBlockRound (I × RIn) SIn ROut SOut)
    {n : Nat}
    (hmismatch : finiteRootFamilyIndex (play n) ≠
      finiteRootFamilyIndex (play 0)) :
    (finiteRootFamilyMonitor M).run play (n + 1) = .sink := by
  cases n with
  | zero => exact absurd rfl hmismatch
  | succ n =>
      rw [BlockRecordMonitor.run]
      rcases finiteRootFamilyMonitor_run_active_or_sink M play n with
        hsink | ⟨state, hstate⟩
      · rw [hsink]
        rfl
      · rw [hstate]
        simp [finiteRootFamilyMonitor, hmismatch]

theorem finiteRootFamilyMonitor_run_sink_persists
    [Fintype I] [DecidableEq I]
    (play : Nat → RealizedBlockRound (I × RIn) SIn ROut SOut)
    {n : Nat}
    (hsink : (finiteRootFamilyMonitor M).run play n = .sink) :
    ∀ k : Nat,
      (finiteRootFamilyMonitor M).run play (n + k) = .sink := by
  intro k
  induction k with
  | zero => simpa using hsink
  | succ k ih =>
      rw [show n + (k + 1) = (n + k) + 1 by omega,
        BlockRecordMonitor.run, ih]
      rfl

theorem natSeqMinEvenParity_eventually_zero
    (priorities : Nat → Nat) (n : Nat)
    (hzero : ∀ k : Nat, priorities (n + k) = 0) :
    NatSeqMinEvenParity priorities := by
  have hshift : NatSeqMinEvenParity (fun k => priorities (n + k)) := by
    refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
    · intro base
      exact ⟨base, le_rfl, hzero base⟩
    · intro q _
      exact Nat.zero_le q
  exact (natSeqMinEvenParity_shift priorities n).mp hshift

/-- Any illegal change of hidden family tag is harmless: the monitor reaches
the even sink and stays there. -/
theorem finiteRootFamilyMonitor_wins_of_mismatch
    [Fintype I] [DecidableEq I]
    (play : Nat → RealizedBlockRound (I × RIn) SIn ROut SOut)
    {n : Nat}
    (hmismatch : finiteRootFamilyIndex (play n) ≠
      finiteRootFamilyIndex (play 0)) :
    (finiteRootFamilyMonitor M).WinsPlay play := by
  let priorities : Nat → Nat := fun k =>
    (finiteRootFamilyMonitor M).priority
      ((finiteRootFamilyMonitor M).run play k)
  apply natSeqMinEvenParity_eventually_zero priorities (n + 1)
  intro k
  have hsink := finiteRootFamilyMonitor_run_sink_persists M play
    (finiteRootFamilyMonitor_run_sink_of_mismatch M play hmismatch) k
  change (finiteRootFamilyMonitor M).priority
    ((finiteRootFamilyMonitor M).run play (n + 1 + k)) = 0
  rw [hsink]
  rfl

/-- If every round carries the initial tag, a family play is literally the
tagged play of the selected member after erasing tags. -/
theorem finiteRootFamilyMonitor_wins_of_constant_index
    [Fintype I] [DecidableEq I]
    (play : Nat → RealizedBlockRound (I × RIn) SIn ROut SOut)
    (hconstant : ∀ n, finiteRootFamilyIndex (play n) =
      finiteRootFamilyIndex (play 0))
    (hmember : (M (finiteRootFamilyIndex (play 0))).WinsPlay
      (fun n => finiteRootFamilyRecord (play n))) :
    (finiteRootFamilyMonitor M).WinsPlay play := by
  let index := finiteRootFamilyIndex (play 0)
  let projected : Nat → RealizedBlockRound RIn SIn ROut SOut :=
    fun n => finiteRootFamilyRecord (play n)
  have hplay : tagFiniteRootPlay index projected = play := by
    funext n
    rcases hletter : play n with
      ⟨⟨⟨letterIndex, receiverInput⟩, senderInput⟩,
        receiverOutput, senderOutput⟩
    have htag : letterIndex = index := by
      simpa [index, finiteRootFamilyIndex, hletter] using hconstant n
    subst letterIndex
    simp [tagFiniteRootPlay, projected, finiteRootFamilyRecord, hletter]
  rw [← hplay]
  exact finiteRootFamilyMonitor_wins_tagged M index projected hmember

/-- Merge the receiver strategies of a finite hidden-root family.  The
current hidden tag selects the receiver table; the sender strategy is not
given the tag. -/
def finiteRootFamilyReceiver
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut) :
    ReceiverBlockStrategy (I × RIn) SIn ROut :=
  fun past move =>
    receiver move.1.1
      (past.map fun old => (old.1.2, old.2))
      (move.1.2, move.2)

theorem map_untag_branchNode
    (index : I) (env : Nat → RIn × SIn) :
    ∀ n : Nat,
      (branchNode (tagFiniteRootEnvironment index env) n).map
          (fun old => (old.1.2, old.2)) =
        branchNode env n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [branchNode, List.map_append, List.map_singleton]
      rw [ih]
      rfl

theorem senderWord_tagFiniteRootEnvironment_branchNode
    (index : I) (env : Nat → RIn × SIn) :
    ∀ n : Nat,
      senderWord (branchNode (tagFiniteRootEnvironment index env) n) =
        senderWord (branchNode env n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change List.map Prod.snd
          (branchNode (tagFiniteRootEnvironment index env) n) =
        List.map Prod.snd (branchNode env n) at ih
      simp only [branchNode, senderWord, List.map_append, List.map_singleton]
      rw [ih]
      rfl

theorem pairPlay_finiteRootFamilyReceiver_tagged
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (index : I) (env : Nat → RIn × SIn) :
    pairPlay (finiteRootFamilyReceiver receiver) sender
        (tagFiniteRootEnvironment index env) =
      tagFiniteRootPlay index (pairPlay (receiver index) sender env) := by
  funext n
  simp only [pairPlay, treePlay, treeOfPair, blockLabelApply,
    finiteRootFamilyReceiver, tagFiniteRootEnvironment, tagFiniteRootPlay]
  rw [map_untag_branchNode index env n]
  rw [senderWord_tagFiniteRootEnvironment_branchNode index env n]

/-- A common (possibly infinite-memory) sender strategy winning every member
of a finite root family realizes the combined monitor. -/
theorem finiteRootFamily_realizable
    [Fintype I] [DecidableEq I]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    ∀ env,
      (finiteRootFamilyMonitor M).WinsPlay
        (pairPlay (finiteRootFamilyReceiver receiver) sender env) := by
  intro env
  by_cases hconstant : ∀ n,
      finiteRootFamilyIndex
          (pairPlay (finiteRootFamilyReceiver receiver) sender env n) =
        finiteRootFamilyIndex
          (pairPlay (finiteRootFamilyReceiver receiver) sender env 0)
  · apply finiteRootFamilyMonitor_wins_of_constant_index M _ hconstant
    let index := (env 0).1.1
    let physicalEnv : Nat → RIn × SIn := fun n => ((env n).1.2, (env n).2)
    have htag : ∀ n, (env n).1.1 = index := by
      intro n
      simpa [finiteRootFamilyIndex, pairPlay, treePlay, blockLabelApply,
        index] using hconstant n
    have henv : env = tagFiniteRootEnvironment index physicalEnv := by
      funext n
      rcases hmove : env n with ⟨⟨tag, receiverInput⟩, senderInput⟩
      have : tag = index := by simpa [hmove] using htag n
      subst tag
      simp [tagFiniteRootEnvironment, physicalEnv, hmove]
    rw [henv]
    rw [pairPlay_finiteRootFamilyReceiver_tagged receiver sender index
      physicalEnv]
    simpa using hwin index physicalEnv
  · push Not at hconstant
    obtain ⟨n, hn⟩ := hconstant
    exact finiteRootFamilyMonitor_wins_of_mismatch M _ hn

/-- End-to-end simultaneous rationalization.  One application of the
unconditional universal-thread theorem returns a finite controller whose
sender table is shared across every hidden member of the family. -/
theorem exists_finiteRootFamilyController
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    ∃ controller :
        TransitionRationalTree.{v, max i u v x y w, max i w} SIn
          (NarrowedBlockLabel (I × RIn) SIn ROut SOut
            (finiteRootFamilyMonitor M).State),
      NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
        controller.labeledTree := by
  apply
    (block_realizable_iff_implementable_controller_unconditional
      (finiteRootFamilyMonitor M)).mp
  exact ⟨finiteRootFamilyReceiver receiver, sender,
    finiteRootFamily_realizable M receiver sender hwin⟩

/-- Canonical simultaneous controller with a fixed, model-independent control
type: the state type of the deterministic universal-thread monitor.  This is
the finite presentation needed when family controllers themselves label a
higher-level parity game. -/
noncomputable def stateControlledFiniteRootFamilyController
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State) := by
  classical
  let familyExists := exists_finiteRootFamilyController M receiver sender hwin
  let family := Classical.choose familyExists
  have hfamily := Classical.choose_spec familyExists
  let combined := finiteRootFamilyMonitor M
  let cert := BlockRecordMonitor.narrowedThreadDPACertificate combined
  have hwinning : cert.monitor.WinningTree family.labeledTree :=
    (cert.winning_iff family.labeledTree).mpr hfamily
  have haccepts : cert.monitor.toRunAutomaton.acceptsTree family.labeledTree :=
    (cert.monitor.acceptsTree_iff_winningTree family.labeledTree).mpr hwinning
  exact cert.monitor.toRunAutomaton.stateControlledAcceptedTree
    ⟨family.labeledTree, haccepts⟩

theorem stateControlledFiniteRootFamilyController_control_eq
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    (stateControlledFiniteRootFamilyController M receiver sender hwin).Control =
      (BlockRecordMonitor.threadBlockMonitor
        (finiteRootFamilyMonitor M)).toRunAutomaton.State := rfl

theorem stateControlledFiniteRootFamilyController_wins
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
      (stateControlledFiniteRootFamilyController M receiver sender hwin).labeledTree := by
  classical
  let familyExists := exists_finiteRootFamilyController M receiver sender hwin
  let family := Classical.choose familyExists
  have hfamily := Classical.choose_spec familyExists
  let combined := finiteRootFamilyMonitor M
  let cert := BlockRecordMonitor.narrowedThreadDPACertificate combined
  have hwinning : cert.monitor.WinningTree family.labeledTree :=
    (cert.winning_iff family.labeledTree).mpr hfamily
  have haccepts : cert.monitor.toRunAutomaton.acceptsTree family.labeledTree :=
    (cert.monitor.acceptsTree_iff_winningTree family.labeledTree).mpr hwinning
  have hcanonical := cert.monitor.toRunAutomaton.stateControlledAcceptedTree_accepts
    ⟨family.labeledTree, haccepts⟩
  exact (cert.winning_iff _).mp
    ((cert.monitor.acceptsTree_iff_winningTree _).mp hcanonical)

/-- The finite move alphabet of simultaneous root-family controllers.  It
depends only on the finite family monitor, not on a semantic strategy or on
an existential controller state type. -/
abbrev FiniteRootFamilyTable
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn] :=
  RunParityTreeAutomaton.StateControlledTreeTable
    (BlockRecordMonitor.threadBlockMonitor (finiteRootFamilyMonitor M)).toRunAutomaton

/-- Choose the simultaneous controller directly in the finite table type. -/
noncomputable def finiteRootFamilyTable
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    FiniteRootFamilyTable M := by
  classical
  let familyExists := exists_finiteRootFamilyController M receiver sender hwin
  let family := Classical.choose familyExists
  have hfamily := Classical.choose_spec familyExists
  let combined := finiteRootFamilyMonitor M
  let cert := BlockRecordMonitor.narrowedThreadDPACertificate combined
  have hwinning : cert.monitor.WinningTree family.labeledTree :=
    (cert.winning_iff family.labeledTree).mpr hfamily
  have haccepts : cert.monitor.toRunAutomaton.acceptsTree family.labeledTree :=
    (cert.monitor.acceptsTree_iff_winningTree family.labeledTree).mpr hwinning
  exact Classical.choose
    (cert.monitor.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨family.labeledTree, haccepts⟩)

theorem finiteRootFamilyTable_wins
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
      (finiteRootFamilyTable M receiver sender hwin).toTransitionRationalTree.labeledTree := by
  classical
  let familyExists := exists_finiteRootFamilyController M receiver sender hwin
  let family := Classical.choose familyExists
  have hfamily := Classical.choose_spec familyExists
  let combined := finiteRootFamilyMonitor M
  let cert := BlockRecordMonitor.narrowedThreadDPACertificate combined
  have hwinning : cert.monitor.WinningTree family.labeledTree :=
    (cert.winning_iff family.labeledTree).mpr hfamily
  have haccepts : cert.monitor.toRunAutomaton.acceptsTree family.labeledTree :=
    (cert.monitor.acceptsTree_iff_winningTree family.labeledTree).mpr hwinning
  have htable := Classical.choose_spec
    (cert.monitor.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨family.labeledTree, haccepts⟩)
  exact (cert.winning_iff _).mp
    ((cert.monitor.acceptsTree_iff_winningTree _).mp htable)

/-- Read one member from a simultaneous family controller.  The extra bit
selects the family monitor's unique pre-selection root state on the empty
word and the active member state afterwards. -/
noncomputable def finiteRootMemberController
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) :
    TransitionRationalTree.{v, max u v x y w, max i w} SIn
      (NarrowedBlockLabel RIn SIn ROut SOut (M index).State) where
  Control := family.Control × Bool
  controlFinite := inferInstance
  initial := (family.initial, false)
  step := fun control input => (family.step control.1 input, true)
  labelOf := fun control =>
    let label := family.labelOf control.1
    (label.1, fun (state : (M index).State) (move : RIn × SIn) =>
      label.2
        (if control.2 then .active index state else .initial)
        ((index, move.1), move.2))

theorem finiteRootMemberController_control_fst
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (word : List SIn) :
    ((finiteRootMemberController M family index).controlAt word).1 =
      family.controlAt word := by
  induction word using List.reverseRecOn with
  | nil => rfl
  | append_singleton word input ih =>
      rw [TransitionRationalTree.controlAt_append,
        TransitionRationalTree.controlAt_append]
      exact congrArg (fun control => family.step control input) ih

/-- Two projections of one simultaneous family controller carry exactly the
same local sender control after every sender-input word.  The member index
occurs only in `labelOf`, where it selects the receiver component; it cannot
affect either the sender transition or its finite control. -/
theorem finiteRootMemberController_control_eq
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (left right : I) (word : List SIn) :
    (finiteRootMemberController M family left).controlAt word =
      (finiteRootMemberController M family right).controlAt word := by
  rfl

/-- All projected members have definitionally the same sender table at every
sender word.  The hidden family index is used only by the receiver table. -/
theorem finiteRootMemberController_sender_eq
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (left right : I) (word : List SIn) :
    ((finiteRootMemberController M family left).labeledTree word).1 =
      ((finiteRootMemberController M family right).labeledTree word).1 := by
  change
    (family.labelOf
      (((finiteRootMemberController M family left).controlAt word).1)).1 =
    (family.labelOf
      (((finiteRootMemberController M family right).controlAt word).1)).1
  rw [finiteRootMemberController_control_fst M family left word,
    finiteRootMemberController_control_fst M family right word]

@[simp] theorem finiteRootMemberController_flag_branchNode
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (env : Nat → RIn × SIn) :
    ∀ n : Nat,
      ((finiteRootMemberController M family index).controlAt
        (senderWord (branchNode env n))).2 = decide (n ≠ 0) := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      rw [show senderWord (branchNode env (n + 1)) =
          senderWord (branchNode env n) ++ [(env n).2] by
        rw [branchNode, senderWord_append]]
      rw [TransitionRationalTree.controlAt_append]
      simp [finiteRootMemberController]

theorem finiteRootMemberController_sender_at_branchNode
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (env : Nat → RIn × SIn) (n : Nat) :
    ((finiteRootMemberController M family index).labeledTree
        (senderWord (branchNode env n))).1 =
      (family.labeledTree (senderWord (branchNode env n))).1 := by
  change
    (family.labelOf
      (((finiteRootMemberController M family index).controlAt
        (senderWord (branchNode env n))).1)).1 =
      (family.labelOf
        (family.controlAt (senderWord (branchNode env n)))).1
  rw [finiteRootMemberController_control_fst M family index]

theorem finiteRootMemberController_receiver_at_positive_branchNode
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (env : Nat → RIn × SIn) (n : Nat)
    (state : (M index).State) (move : RIn × SIn) :
    ((finiteRootMemberController M family index).labeledTree
        (senderWord (branchNode env (n + 1)))).2 state move =
      (family.labeledTree (senderWord (branchNode env (n + 1)))).2
        (.active index state) ((index, move.1), move.2) := by
  change
    (family.labelOf
        (((finiteRootMemberController M family index).controlAt
          (senderWord (branchNode env (n + 1)))).1)).2
      (if ((finiteRootMemberController M family index).controlAt
          (senderWord (branchNode env (n + 1)))).2 then .active index state
        else .initial)
      ((index, move.1), move.2) =
    (family.labelOf
      (family.controlAt (senderWord (branchNode env (n + 1))))).2
      (.active index state) ((index, move.1), move.2)
  rw [finiteRootMemberController_control_fst M family index,
    finiteRootMemberController_flag_branchNode M family index env (n + 1)]
  simp

/-- Along a constant-tag environment, the family narrowed state is the
selected member narrowed state, wrapped in `active`, after the unique root
selection step. -/
theorem finiteRootFamily_narrowedThreadState_tagged_succ
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (env : Nat → RIn × SIn) :
    ∀ n : Nat,
      narrowedThreadState (finiteRootFamilyMonitor M) family.labeledTree
          (tagFiniteRootEnvironment index env) (n + 1) =
        .active index
          (narrowedThreadState (M index)
            (finiteRootMemberController M family index).labeledTree env
            (n + 1)) := by
  intro n
  induction n with
  | zero =>
      simp [narrowedThreadState, branchNode, narrowedControl,
        narrowedControlAux, narrowedRecord, finiteRootFamilyMonitor,
        finiteRootMemberController, TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt, tagFiniteRootEnvironment,
        finiteRootFamilyRecord, finiteRootFamilyIndex]
  | succ n ih =>
      change narrowedControl (finiteRootFamilyMonitor M) family.labeledTree
          (branchNode (tagFiniteRootEnvironment index env) (n + 1) ++
            [tagFiniteRootEnvironment index env (n + 1)]) =
        .active index
          (narrowedControl (M index)
            (finiteRootMemberController M family index).labeledTree
            (branchNode env (n + 1) ++ [env (n + 1)]))
      rw [narrowedControl_append, narrowedControl_append]
      have ih' := ih
      change narrowedControl (finiteRootFamilyMonitor M) family.labeledTree
          (branchNode (tagFiniteRootEnvironment index env) (n + 1)) =
        .active index
          (narrowedControl (M index)
            (finiteRootMemberController M family index).labeledTree
            (branchNode env (n + 1))) at ih'
      rw [ih']
      simp only [finiteRootFamilyMonitor]
      rw [senderWord_tagFiniteRootEnvironment_branchNode index env (n + 1)]
      simp only [narrowedRecord, finiteRootFamilyRecord,
        finiteRootFamilyIndex, tagFiniteRootEnvironment,
        TransitionRationalTree.labeledTree]
      change FiniteRootFamilyState.active index ((M index).step
          (narrowedControl (M index)
            (finiteRootMemberController M family index).labeledTree
            (branchNode env (n + 1)))
          (env (n + 1),
            (family.labeledTree
              (senderWord (branchNode env (n + 1)))).2
              (FiniteRootFamilyState.active index
                (narrowedControl (M index)
                  (finiteRootMemberController M family index).labeledTree
                  (branchNode env (n + 1))))
              ((index, (env (n + 1)).1), (env (n + 1)).2),
            (family.labeledTree
              (senderWord (branchNode env (n + 1)))).1
              (env (n + 1)).2)) =
        FiniteRootFamilyState.active index ((M index).step
          (narrowedControl (M index)
            (finiteRootMemberController M family index).labeledTree
            (branchNode env (n + 1)))
          (env (n + 1),
            ((finiteRootMemberController M family index).labeledTree
              (senderWord (branchNode env (n + 1)))).2
              (narrowedControl (M index)
                (finiteRootMemberController M family index).labeledTree
                (branchNode env (n + 1)))
              (env (n + 1)),
            ((finiteRootMemberController M family index).labeledTree
              (senderWord (branchNode env (n + 1)))).1
              (env (n + 1)).2))
      rw [finiteRootMemberController_receiver_at_positive_branchNode
          M family index env n,
        finiteRootMemberController_sender_at_branchNode
          M family index env (n + 1)]

/-- The projected member controller is not merely winning: its literal play
is exactly the fixed-member projection of the simultaneous family play. -/
theorem finiteRootMemberController_treePlay_tagged
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (index : I) (env : Nat → RIn × SIn) : ∀ n : Nat,
    tagFiniteRootPlay index
        (treePlay
          (narrowedInducedTree (M index)
            (finiteRootMemberController M family index).labeledTree) env) n =
      treePlay
        (narrowedInducedTree (finiteRootFamilyMonitor M) family.labeledTree)
        (tagFiniteRootEnvironment index env) n := by
  intro n
  cases n with
  | zero =>
      simp [tagFiniteRootPlay, treePlay, narrowedInducedTree, blockLabelApply,
        branchNode, senderWord, narrowedControl, narrowedControlAux,
        finiteRootMemberController, finiteRootFamilyMonitor,
        TransitionRationalTree.labeledTree,
        TransitionRationalTree.controlAt, tagFiniteRootEnvironment]
  | succ n =>
      change
        (((index, (env (n + 1)).1), (env (n + 1)).2),
          ((finiteRootMemberController M family index).labeledTree
              (senderWord (branchNode env (n + 1)))).2
            (narrowedControl (M index)
              (finiteRootMemberController M family index).labeledTree
              (branchNode env (n + 1)))
            (env (n + 1)),
          ((finiteRootMemberController M family index).labeledTree
              (senderWord (branchNode env (n + 1)))).1
            (env (n + 1)).2) =
        (((index, (env (n + 1)).1), (env (n + 1)).2),
          (family.labeledTree
              (senderWord
                (branchNode (tagFiniteRootEnvironment index env) (n + 1)))).2
            (narrowedControl (finiteRootFamilyMonitor M) family.labeledTree
              (branchNode (tagFiniteRootEnvironment index env) (n + 1)))
            ((index, (env (n + 1)).1), (env (n + 1)).2),
          (family.labeledTree
              (senderWord
                (branchNode (tagFiniteRootEnvironment index env) (n + 1)))).1
            (env (n + 1)).2)
      rw [senderWord_tagFiniteRootEnvironment_branchNode index env (n + 1)]
      have hstate := finiteRootFamily_narrowedThreadState_tagged_succ M family
        index env n
      change narrowedControl (finiteRootFamilyMonitor M) family.labeledTree
          (branchNode (tagFiniteRootEnvironment index env) (n + 1)) =
        .active index
          (narrowedControl (M index)
            (finiteRootMemberController M family index).labeledTree
            (branchNode env (n + 1))) at hstate
      rw [hstate,
        finiteRootMemberController_receiver_at_positive_branchNode M family
          index env n,
        finiteRootMemberController_sender_at_branchNode M family index env
          (n + 1)]

/-- Projecting a simultaneous winning controller retains the all-thread
parity guarantee of every member monitor. -/
theorem finiteRootMemberController_allThreadsWin
    [Fintype I] [DecidableEq I]
    (family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
      (NarrowedBlockLabel (I × RIn) SIn ROut SOut
        (finiteRootFamilyMonitor M).State))
    (hfamily : NarrowedAllThreadsWin (finiteRootFamilyMonitor M)
      family.labeledTree)
    (index : I) :
    NarrowedAllThreadsWin (M index)
      (finiteRootMemberController M family index).labeledTree := by
  intro env
  let familyPriorities : Nat → Nat := fun n =>
    (finiteRootFamilyMonitor M).priority
      (narrowedThreadState (finiteRootFamilyMonitor M) family.labeledTree
        (tagFiniteRootEnvironment index env) n)
  let memberPriorities : Nat → Nat := fun n =>
    (M index).priority
      (narrowedThreadState (M index)
        (finiteRootMemberController M family index).labeledTree env n)
  have hfamilyWin : NatSeqMinEvenParity familyPriorities :=
    hfamily (tagFiniteRootEnvironment index env)
  have hfamilyShift :
      NatSeqMinEvenParity (fun n => familyPriorities (1 + n)) :=
    (natSeqMinEvenParity_shift familyPriorities 1).mpr hfamilyWin
  have heq : (fun n => familyPriorities (1 + n)) =
      fun n => memberPriorities (1 + n) := by
    funext n
    simp only [familyPriorities, memberPriorities]
    rw [show 1 + n = n + 1 by omega,
      finiteRootFamily_narrowedThreadState_tagged_succ M family index env n]
    rfl
  have hmemberShift :
      NatSeqMinEvenParity (fun n => memberPriorities (1 + n)) := by
    rw [← heq]
    exact hfamilyShift
  exact (natSeqMinEvenParity_shift memberPriorities 1).mp hmemberShift

/-- End-to-end projected form of simultaneous narrowing.  This is the form
used by controller banks: one hidden-family controller exists, every member
projection wins its own monitor, and all member projections share the sender
table pointwise. -/
theorem exists_finiteRootMemberControllerBank
    [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ index env, (M index).WinsPlay
      (pairPlay (receiver index) sender env)) :
    ∃ family : TransitionRationalTree.{v, max i u v x y w, max i w} SIn
        (NarrowedBlockLabel (I × RIn) SIn ROut SOut
          (finiteRootFamilyMonitor M).State),
      (∀ index,
        NarrowedAllThreadsWin (M index)
          (finiteRootMemberController M family index).labeledTree) ∧
      (∀ left right word,
        ((finiteRootMemberController M family left).labeledTree word).1 =
          ((finiteRootMemberController M family right).labeledTree word).1) := by
  obtain ⟨family, hfamily⟩ :=
    exists_finiteRootFamilyController M receiver sender hwin
  exact ⟨family,
    fun index => finiteRootMemberController_allThreadsWin M family hfamily index,
    finiteRootMemberController_sender_eq M family⟩

/-- A finite implementation of two rebased hidden anchors. -/
structure FiniteCrossAnchorPairController
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State) where
  family : TransitionRationalTree.{v, max u v x y w, max w} SIn
    (NarrowedBlockLabel (Bool × RIn) SIn ROut SOut
      (finiteRootFamilyMonitor
        (fun anchor => (base anchor).restartAt (start anchor))).State)
  wins : ∀ anchor,
    NarrowedAllThreadsWin
      ((base anchor).restartAt (start anchor))
      (finiteRootMemberController
        (fun anchor => (base anchor).restartAt (start anchor))
        family anchor).labeledTree
  sender_eq : ∀ left right word,
    ((finiteRootMemberController
      (fun anchor => (base anchor).restartAt (start anchor))
      family left).labeledTree word).1 =
    ((finiteRootMemberController
      (fun anchor => (base anchor).restartAt (start anchor))
      family right).labeledTree word).1

/-- The explicit dangerous-pair extraction theorem.  Two anchors may use
different monitors, different receiver continuations, and different finite
monitor states.  If they are continuations of one semantic sender strategy,
they admit finite winning controllers whose sender tables agree on every
future sender word.  No anchor bit is exposed to that sender. -/
noncomputable def finiteCrossAnchorPairController
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (base : Bool → BlockRecordMonitor.{u, v, x, y, w}
      RIn SIn ROut SOut)
    (start : ∀ anchor, (base anchor).State)
    (receiver : ∀ anchor, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ anchor env,
      ((base anchor).restartAt (start anchor)).WinsPlay
        (pairPlay (receiver anchor) sender env)) :
    FiniteCrossAnchorPairController base start := by
  let hexists :=
    exists_finiteRootMemberControllerBank
      (fun anchor => (base anchor).restartAt (start anchor))
      receiver sender hwin
  let family := Classical.choose hexists
  have hspec := Classical.choose_spec hexists
  exact ⟨family, hspec.1, hspec.2⟩

end

end DistributedSynthesis
