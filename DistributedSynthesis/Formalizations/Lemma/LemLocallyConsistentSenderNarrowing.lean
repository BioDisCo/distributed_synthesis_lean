/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmUniversalThreadDeterminization

/-!
# Locally consistent sender narrowing

The ordinary sender-narrowing theorem folds receiver responses after the
environment has selected its current full move.  For a response component
owned by a process that does not receive in a possible closing round, this
order is too permissive: all hidden-input alternatives must use one
contingent table.

This file supplies the tree-automaton half of the repair.  Any decidable
finite predicate on the complete receiver table is installed as a sticky
label restriction and is therefore preserved by rational-tree extraction.
No node is told which side is the strict leader; the predicate compares the
entries of the single table chosen at that node.
-/

namespace DistributedSynthesis

universe u v x y w

section

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq SIn]
variable [Inhabited SIn]
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- Every monitor-state-indexed receiver table in every tree label obeys
the prescribed information-discipline law. -/
def NarrowedTablesAllowed
    (Allowed : (RIn × SIn -> ROut) -> Prop)
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) : Prop :=
  ∀ word q, Allowed ((narrowed word).2 q)

/-- The corresponding node-label predicate consumed by `restrictLabels`. -/
def NarrowedLabelAllowed
    (Allowed : (RIn × SIn -> ROut) -> Prop)
    (label : NarrowedBlockLabel RIn SIn ROut SOut M.State) : Prop :=
  ∀ q, Allowed (label.2 q)

omit [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [DecidableEq SIn]
    [Inhabited SIn] in
theorem narrowedTablesAllowed_iff_labels
    (Allowed : (RIn × SIn -> ROut) -> Prop)
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    NarrowedTablesAllowed M Allowed narrowed ↔
      ∀ word, NarrowedLabelAllowed M Allowed (narrowed word) := by
  rfl

omit [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [DecidableEq SIn]
    [Inhabited SIn] in
/-- A complete-table law stored in every narrowed label is inherited by the
actual receiver table of the induced full-information tree at every node.
The selected monitor state is the genuine `narrowedControl` of that history,
not an arbitrary restart state. -/
theorem narrowedInducedTree_receiver_allowed
    (Allowed : (RIn × SIn -> ROut) -> Prop)
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hallowed : NarrowedTablesAllowed M Allowed narrowed)
    (node : TreeNode (RIn × SIn)) :
    Allowed (narrowedInducedTree M narrowed node).1 := by
  exact hallowed (senderWord node) (narrowedControl M narrowed node)

/--
Rationalize a narrowed winning tree while preserving an arbitrary decidable
law on its complete receiver tables.  This is the reusable infinite-tree
counterpart of a finite locally-consistent strategy table.
-/
theorem exists_transitionRational_narrowed_of_tablesAllowed
    (Allowed : (RIn × SIn -> ROut) -> Prop)
    [DecidablePred Allowed]
    (narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (hthreads : NarrowedAllThreadsWin M narrowed)
    (hallowed : NarrowedTablesAllowed M Allowed narrowed) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y w, w}
          SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      NarrowedAllThreadsWin M controller.labeledTree ∧
        NarrowedTablesAllowed M Allowed controller.labeledTree := by
  classical
  let base := BlockRecordMonitor.threadBlockMonitor M
  let P := NarrowedLabelAllowed M Allowed
  let restricted := base.restrictLabels P
  have hbase : base.WinningTree narrowed :=
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M narrowed).mpr hthreads
  have hall : ∀ word, P (narrowed word) := hallowed
  have hrestricted : restricted.WinningTree narrowed :=
    base.restrictLabels_winningTree_of P narrowed hbase hall
  rcases restricted.toRunAutomaton.exists_transitionRational_accepted
      ⟨narrowed,
        (restricted.acceptsTree_iff_winningTree narrowed).mpr hrestricted⟩ with
    ⟨controller, haccepts⟩
  have hwin : restricted.WinningTree controller.labeledTree :=
    (restricted.acceptsTree_iff_winningTree controller.labeledTree).mp haccepts
  have hsplit :=
    (base.restrictLabels_winningTree_iff P controller.labeledTree).mp hwin
  exact ⟨controller,
    (BlockRecordMonitor.threadBlockMonitor_winningTree_iff M
      controller.labeledTree).mp hsplit.1,
    hsplit.2⟩

end

/-! ## Table-first folding arena -/

section TableFirst

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

abbrev ReceiverContingencyTable := RIn × SIn -> ROut

local instance : Countable RIn := Finite.to_countable
local instance : Countable SIn := Finite.to_countable
local instance : Countable ROut := Finite.to_countable
local instance : Countable M.State := Finite.to_countable
local instance : Countable
    (ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut)) :=
  Finite.to_countable

/-- Four tiers make the table-before-input order explicit.  The two commit
tiers are deterministic stutters; retaining four copies lets the existing
checked halving parity transfer be used twice. -/
inductive TableFirstFoldPosition where
  | choose (word : List SIn) (q : M.State)
  | table (word : List SIn) (q : M.State)
      (responses : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
  | move (word : List SIn) (q : M.State)
      (responses : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
      (input : RIn × SIn)
  | commit (word : List SIn) (q : M.State)
      (responses : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
      (input : RIn × SIn)

noncomputable instance : Countable (TableFirstFoldPosition M) := by
  classical
  let Table :=
    ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut)
  let Rep :=
    (List SIn × M.State) ⊕
      ((List SIn × M.State × Table) ⊕
        ((List SIn × M.State × Table × (RIn × SIn)) ⊕
          (List SIn × M.State × Table × (RIn × SIn))))
  let encode : TableFirstFoldPosition M -> Rep
    | .choose word q => Sum.inl (word, q)
    | .table word q responses => Sum.inr (Sum.inl (word, q, responses))
    | .move word q responses input =>
        Sum.inr (Sum.inr (Sum.inl (word, q, responses, input)))
    | .commit word q responses input =>
        Sum.inr (Sum.inr (Sum.inr (word, q, responses, input)))
  have hinjective : Function.Injective encode := by
    intro left right h
    cases left <;> cases right <;> simp_all [encode] <;> aesop
  exact hinjective.countable

def tableFirstFoldOwner : TableFirstFoldPosition M -> ParityPlayer
  | .choose _ _ => ParityPlayer.even
  | _ => ParityPlayer.odd

def tableFirstFoldPriority : TableFirstFoldPosition M -> Nat
  | .choose _ q => M.priority q
  | .table _ q _ => M.priority q
  | .move _ q _ _ => M.priority q
  | .commit _ q _ _ => M.priority q

def tableFirstFoldStep
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop) :
    TableFirstFoldPosition M -> TableFirstFoldPosition M -> Prop
  | .choose word q, target =>
      ∃ responses, Allowed responses ∧ target = .table word q responses
  | .table word q responses, target =>
      ∃ input, target = .move word q responses input
  | .move word q responses input, target =>
      target = .commit word q responses input
  | .commit word q responses input, target =>
      target = .choose (word ++ [input.2])
        (M.step q (input, responses input, senderTree word input.2))

omit [Inhabited ROut] [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn] in
theorem tableFirstFoldStep_total
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable) :
    ∀ position, ∃ next, tableFirstFoldStep M senderTree Allowed position next := by
  intro position
  cases position with
  | choose word q => exact ⟨.table word q defaultTable, defaultTable, hdefault, rfl⟩
  | table word q responses =>
      exact ⟨.move word q responses default, default, rfl⟩
  | move word q responses input =>
      exact ⟨.commit word q responses input, rfl⟩
  | commit word q responses input =>
      exact ⟨.choose (word ++ [input.2])
        (M.step q (input, responses input, senderTree word input.2)), rfl⟩

@[reducible] noncomputable def tableFirstFoldGame
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable) : CountableParityGame where
  Position := TableFirstFoldPosition M
  positionCountable := inferInstance
  owner := tableFirstFoldOwner M
  step := tableFirstFoldStep M senderTree Allowed
  step_total := tableFirstFoldStep_total M senderTree Allowed defaultTable hdefault
  priority := tableFirstFoldPriority M
  priority_finite := by
    refine Set.Finite.subset (Set.finite_range M.priority) ?_
    rintro p ⟨position, rfl⟩
    cases position with
    | choose _ q | table _ q _ | move _ q _ _ | commit _ q _ _ =>
        exact ⟨q, rfl⟩

def tableFirstExtractMove : TableFirstFoldPosition M -> Option (RIn × SIn)
  | .move _ _ _ input => some input
  | _ => none

def tableFirstDecode {n : Nat}
    (pref : Fin (n + 1) -> TableFirstFoldPosition M) : List (RIn × SIn) :=
  (List.ofFn pref).filterMap (tableFirstExtractMove M)

def tableFirstMemoryMove
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut))
    (last : TableFirstFoldPosition M) (decoded : List (RIn × SIn)) :
    TableFirstFoldPosition M :=
  match last with
  | .choose word q => .table word q (T decoded).1
  | position => position

def tableFirstMemoryStrategy
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable)
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)) :
    (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).Strategy
      ParityPlayer.even where
  move _ pref := tableFirstMemoryMove M T
    ((tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast pref)
    (tableFirstDecode M pref)

omit [Inhabited ROut] [Fintype SOut] [DecidableEq RIn] [DecidableEq SIn] in
theorem tableFirstMemoryStrategy_legal
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable)
    (T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut))
    (hallowed : ∀ node, Allowed (T node).1) :
    (tableFirstMemoryStrategy M senderTree Allowed defaultTable hdefault T).Legal := by
  intro n pref _ howner
  show tableFirstFoldStep M senderTree Allowed
    ((tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast pref)
    (tableFirstMemoryMove M T
      ((tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast pref)
      (tableFirstDecode M pref))
  cases hlast :
      (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast pref with
  | choose word q =>
      exact ⟨(T (tableFirstDecode M pref)).1,
        hallowed (tableFirstDecode M pref), rfl⟩
  | table word q responses =>
      rw [hlast] at howner
      simp [tableFirstFoldOwner] at howner
  | move word q responses input =>
      rw [hlast] at howner
      simp [tableFirstFoldOwner] at howner
  | commit word q responses input =>
      rw [hlast] at howner
      simp [tableFirstFoldOwner] at howner

def tableFirstMoveAt (position : TableFirstFoldPosition M) : RIn × SIn :=
  match position with
  | .move _ _ _ input => input
  | _ => default

section
omit [Inhabited ROut]

/-- The table-first memory strategy follows the original winning full tree.
The four arena tiers merely stutter each monitor priority four times. -/
theorem tableFirstMemoryStrategy_winningFrom
    (senderTree : List SIn -> SIn -> SOut)
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable)
    {T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)}
    (hoblivious : SenderOblivious T)
    (hsender : ∀ word : List SIn,
      senderTree word =
        (T (word.map (fun sIn => ((default : RIn), sIn)))).2)
    (hallowed : ∀ node, Allowed (T node).1)
    (hwin : M.lift.WinningTree T) :
    CountableParityGame.Strategy.WinningFrom
      (G := tableFirstFoldGame M senderTree Allowed defaultTable hdefault)
      (tableFirstMemoryStrategy M senderTree Allowed defaultTable hdefault T)
      (.choose [] M.initial) := by
  classical
  constructor
  · exact tableFirstMemoryStrategy_legal M senderTree Allowed
      defaultTable hdefault T hallowed
  · intro path hplayfrom hconsistent
    obtain ⟨hzero, hplay⟩ := hplayfrom
    set u : Nat -> List (RIn × SIn) := fun n =>
      (List.ofFn fun i : Fin (4 * n + 1) => path i).filterMap
        (tableFirstExtractMove M) with hu
    set mv : Nat -> RIn × SIn := fun n =>
      tableFirstMoveAt M (path (4 * n + 2)) with hmv
    have hsend : ∀ word : List SIn, ∀ node : TreeNode (RIn × SIn),
        senderWord node = word -> senderTree word = (T node).2 := by
      intro word node hword
      rw [hsender word]
      refine hoblivious _ _ ?_
      rw [senderWord_completion word, hword]
    have hu0 : u 0 = [] := by
      have hofn : (List.ofFn fun i : Fin (4 * 0 + 1) => path i) = [path 0] := by
        simp [List.ofFn_succ]
      simp only [hu, hofn, hzero]
      rfl
    have hstep : ∀ n,
        path (4 * n) = .choose (senderWord (u n)) (M.lift.control T (u n)) ->
          path (4 * n + 1) =
              .table (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 ∧
          path (4 * n + 2) =
              .move (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) ∧
          path (4 * n + 3) =
              .commit (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) ∧
          u (n + 1) = u n ++ [mv n] ∧
          path (4 * n + 4) =
              .choose (senderWord (u n ++ [mv n]))
                (M.lift.control T (u n ++ [mv n])) := by
      intro n hA
      have howner :
          (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).owner
            (path (4 * n)) = ParityPlayer.even := by
        rw [hA]
        rfl
      have hcons := hconsistent (4 * n) howner
      have hlast :
          (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast
              ((tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixOfPath
                path (4 * n)) = path (4 * n) :=
        (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixLast_prefixOfPath
          path (4 * n)
      have hdecode :
          tableFirstDecode M
              ((tableFirstFoldGame M senderTree Allowed defaultTable hdefault).prefixOfPath
                path (4 * n)) = u n := by
        rfl
      have hB : path (4 * n + 1) =
          .table (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 := by
        rw [hcons]
        show tableFirstMemoryMove M T _ _ = _
        rw [hlast, hdecode, hA]
        rfl
      have hBC := hplay (4 * n + 1)
      rw [hB] at hBC
      obtain ⟨input, hCraw⟩ := hBC
      have hmvn : mv n = input := by
        simp [hmv, hCraw, tableFirstMoveAt]
      have hC : path (4 * n + 2) =
          .move (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) := by
        rw [hmvn]
        exact hCraw
      have hCD := hplay (4 * n + 2)
      rw [hC] at hCD
      have hD : path (4 * n + 3) =
          .commit (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) :=
        hCD
      have hDA := hplay (4 * n + 3)
      rw [hD] at hDA
      have hA' : path (4 * n + 4) =
          .choose (senderWord (u n ++ [mv n]))
            (M.lift.control T (u n ++ [mv n])) := by
        rw [hDA]
        show TableFirstFoldPosition.choose (senderWord (u n) ++ [(mv n).2])
            (M.step (M.lift.control T (u n))
              (mv n, (T (u n)).1 (mv n),
                senderTree (senderWord (u n)) (mv n).2)) = _
        rw [hsend (senderWord (u n)) (u n) rfl,
          ← senderWord_append (u n) (mv n),
          M.lift.control_append T (u n) (mv n)]
        rfl
      have huSucc : u (n + 1) = u n ++ [mv n] := by
        show (List.ofFn fun i : Fin (4 * (n + 1) + 1) => path i).filterMap
            (tableFirstExtractMove M) = u n ++ [mv n]
        rw [show 4 * (n + 1) + 1 = (4 * n + 1) + 4 by omega,
          List.ofFn_add (n := 4 * n + 1) (m := 4)
            (f := fun i : Fin ((4 * n + 1) + 4) => path i)]
        simp only [List.filterMap_append]
        have hfirst :
            List.filterMap (tableFirstExtractMove M)
              (List.ofFn fun i : Fin (4 * n + 1) =>
                path ((Fin.castLE (by omega) i : Fin ((4 * n + 1) + 4)) : Nat)) =
              u n := rfl
        rw [hfirst]
        simp [List.ofFn_succ, hB, hC, hD, hA', tableFirstExtractMove]
      exact ⟨hB, hC, hD, huSucc, hA'⟩
    have hA : ∀ n,
        path (4 * n) = .choose (senderWord (u n)) (M.lift.control T (u n)) := by
      intro n
      induction n with
      | zero =>
          rw [hu0]
          simpa [senderWord] using hzero
      | succ n ih =>
          have hs := hstep n ih
          rw [show 4 * (n + 1) = 4 * n + 4 by omega, hs.2.2.2.1]
          exact hs.2.2.2.2
    have hB : ∀ n, path (4 * n + 1) =
        .table (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 :=
      fun n => (hstep n (hA n)).1
    have hC : ∀ n, path (4 * n + 2) =
        .move (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) :=
      fun n => (hstep n (hA n)).2.1
    have hD : ∀ n, path (4 * n + 3) =
        .commit (senderWord (u n)) (M.lift.control T (u n)) (T (u n)).1 (mv n) :=
      fun n => (hstep n (hA n)).2.2.1
    have huSucc : ∀ n, u (n + 1) = u n ++ [mv n] :=
      fun n => (hstep n (hA n)).2.2.2.1
    have huBranch : ∀ n, u n = branchNode mv n := by
      intro n
      induction n with
      | zero => simpa [branchNode] using hu0
      | succ n ih => rw [huSucc n, ih]; rfl
    have hpriority : ∀ k,
        (tableFirstFoldGame M senderTree Allowed defaultTable hdefault).priority
            (path k) = M.priority (M.lift.control T (u (k / 4))) := by
      intro k
      have hmod : k % 4 < 4 := Nat.mod_lt _ (by omega)
      interval_cases hk : k % 4
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n := ⟨k / 4, by omega⟩
        subst k
        rw [hA]
        have hdiv : 4 * n / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 1 := ⟨k / 4, by omega⟩
        subst k
        rw [hB]
        have hdiv : (4 * n + 1) / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 2 := ⟨k / 4, by omega⟩
        subst k
        rw [hC]
        have hdiv : (4 * n + 2) / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 3 := ⟨k / 4, by omega⟩
        subst k
        rw [hD]
        have hdiv : (4 * n + 3) / 4 = n := by omega
        rw [hdiv]
        rfl
    have htree := hwin mv
    have hbase : NatSeqMinEvenParity
        (fun n => M.priority (M.lift.control T (u n))) := by
      have heq :
          (fun n => M.lift.priority (M.lift.control T (branchNode mv n))) =
            fun n => M.priority (M.lift.control T (u n)) := by
        funext n
        rw [← huBranch n]
        rfl
      rw [heq] at htree
      exact htree
    exact (natSeqMinEvenParity_quartered hpriority).mpr hbase

/--
Constrained completeness of sender narrowing.  The receiver's whole table is
chosen before the current input, so positional determinacy preserves
`Allowed`; the resulting narrowed tree satisfies the law at every node and
monitor state.
-/
theorem exists_narrowed_tablesAllowed_of_senderOblivious_winningTree
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable)
    {T : LabeledTree (RIn × SIn) (BlockLambdaLabel RIn SIn ROut SOut)}
    (hoblivious : SenderOblivious T)
    (hallowed : ∀ node, Allowed (T node).1)
    (hwin : M.lift.WinningTree T) :
    ∃ narrowed :
        LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      NarrowedAllThreadsWin M narrowed ∧
        NarrowedTablesAllowed M Allowed narrowed := by
  classical
  set senderTree : List SIn -> SIn -> SOut := fun word =>
    (T (word.map (fun sIn => ((default : RIn), sIn)))).2 with hsdef
  let game := tableFirstFoldGame M senderTree Allowed defaultTable hdefault
  let memory := tableFirstMemoryStrategy M senderTree Allowed defaultTable hdefault T
  have hmemory : CountableParityGame.Strategy.WinningFrom (G := game) memory
      (.choose [] M.initial) :=
    tableFirstMemoryStrategy_winningFrom M senderTree Allowed defaultTable hdefault
      hoblivious (fun _ => rfl) hallowed hwin
  have hmem : (.choose [] M.initial : game.Position) ∈
      game.WinningRegion ParityPlayer.even := ⟨memory, hmemory⟩
  obtain ⟨σ, hσ⟩ := game.positionalDeterminacy ParityPlayer.even _ hmem
  have hout : ∀ (word : List SIn) (q : M.State),
      ∃ responses, Allowed responses ∧
        σ.move (.choose word q) = .table word q responses := by
    intro word q
    have hlegal := σ.legal (.choose word q) (by rfl)
    simpa [game, tableFirstFoldGame, tableFirstFoldStep] using hlegal
  choose responses hresponsesAllowed hresponses using hout
  let narrowed :
      LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State) :=
    fun word => (senderTree word, fun q => responses word q)
  refine ⟨narrowed, ?_, ?_⟩
  · intro env
    let sw : Nat -> List SIn := fun n => senderWord (branchNode env n)
    let qs : Nat -> M.State := fun n =>
      narrowedControl M narrowed (branchNode env n)
    let tables : Nat -> ReceiverContingencyTable := fun n => responses (sw n) (qs n)
    let evenTier : Nat -> TableFirstFoldPosition M :=
      interleavePlay
        (fun n => .choose (sw n) (qs n))
        (fun n => .move (sw n) (qs n) (tables n) (env n))
    let oddTier : Nat -> TableFirstFoldPosition M :=
      interleavePlay
        (fun n => .table (sw n) (qs n) (tables n))
        (fun n => .commit (sw n) (qs n) (tables n) (env n))
    let path : Nat -> TableFirstFoldPosition M := interleavePlay evenTier oddTier
    have hswSucc : ∀ n, sw (n + 1) = sw n ++ [(env n).2] := by
      intro n
      show senderWord (branchNode env n ++ [env n]) = _
      rw [senderWord_append]
    have hqsSucc : ∀ n, qs (n + 1) =
        M.step (qs n) (env n, tables n (env n), senderTree (sw n) (env n).2) := by
      intro n
      show narrowedControl M narrowed (branchNode env n ++ [env n]) = _
      rw [narrowedControl_append]
      rfl
    have hA : ∀ n, path (4 * n) = .choose (sw n) (qs n) := by
      intro n
      change interleavePlay evenTier oddTier (4 * n) = _
      rw [interleavePlay_of_mod_eq_zero evenTier oddTier (by omega)]
      have hhalf : 4 * n / 2 = 2 * n := by omega
      rw [hhalf]
      dsimp only [evenTier]
      rw [interleavePlay_of_mod_eq_zero _ _ (by omega)]
      have hquarter : 2 * n / 2 = n := by omega
      rw [hquarter]
    have hB : ∀ n, path (4 * n + 1) = .table (sw n) (qs n) (tables n) := by
      intro n
      change interleavePlay evenTier oddTier (4 * n + 1) = _
      rw [interleavePlay_of_mod_eq_one evenTier oddTier (by omega)]
      have hhalf : (4 * n + 1) / 2 = 2 * n := by omega
      rw [hhalf]
      dsimp only [oddTier]
      rw [interleavePlay_of_mod_eq_zero _ _ (by omega)]
      have hquarter : 2 * n / 2 = n := by omega
      rw [hquarter]
    have hC : ∀ n, path (4 * n + 2) = .move (sw n) (qs n) (tables n) (env n) := by
      intro n
      change interleavePlay evenTier oddTier (4 * n + 2) = _
      rw [interleavePlay_of_mod_eq_zero evenTier oddTier (by omega)]
      have hhalf : (4 * n + 2) / 2 = 2 * n + 1 := by omega
      rw [hhalf]
      dsimp only [evenTier]
      rw [interleavePlay_of_mod_eq_one _ _ (by omega)]
      have hquarter : (2 * n + 1) / 2 = n := by omega
      rw [hquarter]
    have hD : ∀ n, path (4 * n + 3) = .commit (sw n) (qs n) (tables n) (env n) := by
      intro n
      change interleavePlay evenTier oddTier (4 * n + 3) = _
      rw [interleavePlay_of_mod_eq_one evenTier oddTier (by omega)]
      have hhalf : (4 * n + 3) / 2 = 2 * n + 1 := by omega
      rw [hhalf]
      dsimp only [oddTier]
      rw [interleavePlay_of_mod_eq_one _ _ (by omega)]
      have hquarter : (2 * n + 1) / 2 = n := by omega
      rw [hquarter]
    have hplay : game.Play path := by
      intro k
      have hmod : k % 4 < 4 := Nat.mod_lt _ (by omega)
      interval_cases hk : k % 4
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n := ⟨k / 4, by omega⟩
        subst k
        rw [hA, hB]
        exact ⟨tables n, hresponsesAllowed (sw n) (qs n), rfl⟩
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 1 := ⟨k / 4, by omega⟩
        subst k
        rw [hB, hC]
        exact ⟨env n, rfl⟩
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 2 := ⟨k / 4, by omega⟩
        subst k
        rw [hC, hD]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 3 := ⟨k / 4, by omega⟩
        subst k
        rw [hD, show 4 * n + 3 + 1 = 4 * (n + 1) by omega, hA,
          hswSucc, hqsSucc]
        rfl
    have hstart : path 0 = (.choose [] M.initial : game.Position) := by
      rw [hA 0]
      rfl
    have hconsistent : CountableParityGame.PositionalStrategy.Consistent
        (G := game) σ path := by
      intro k howner
      have hmod : k % 4 < 4 := Nat.mod_lt _ (by omega)
      interval_cases hk : k % 4
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n := ⟨k / 4, by omega⟩
        subst k
        rw [hA, hB, hresponses]
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 1 := ⟨k / 4, by omega⟩
        subst k
        rw [hB] at howner
        simp [game, tableFirstFoldGame, tableFirstFoldOwner] at howner
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 2 := ⟨k / 4, by omega⟩
        subst k
        rw [hC] at howner
        simp [game, tableFirstFoldGame, tableFirstFoldOwner] at howner
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 3 := ⟨k / 4, by omega⟩
        subst k
        rw [hD] at howner
        simp [game, tableFirstFoldGame, tableFirstFoldOwner] at howner
    have hwins := hσ path ⟨hstart, hplay⟩ hconsistent
    have hpriority : ∀ k, game.priority (path k) = M.priority (qs (k / 4)) := by
      intro k
      have hmod : k % 4 < 4 := Nat.mod_lt _ (by omega)
      interval_cases hk : k % 4
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n := ⟨k / 4, by omega⟩
        subst k
        rw [hA]
        have hdiv : 4 * n / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 1 := ⟨k / 4, by omega⟩
        subst k
        rw [hB]
        have hdiv : (4 * n + 1) / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 2 := ⟨k / 4, by omega⟩
        subst k
        rw [hC]
        have hdiv : (4 * n + 2) / 4 = n := by omega
        rw [hdiv]
        rfl
      · obtain ⟨n, hn⟩ : ∃ n, k = 4 * n + 3 := ⟨k / 4, by omega⟩
        subst k
        rw [hD]
        have hdiv : (4 * n + 3) / 4 = n := by omega
        rw [hdiv]
        rfl
    exact (natSeqMinEvenParity_quartered hpriority).mp hwins
  · intro word q
    exact hresponsesAllowed word q

/-- End-to-end constrained narrowing and rationalization. -/
theorem exists_implementable_controller_of_block_realizable_tablesAllowed
    (Allowed : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut) -> Prop)
    [DecidablePred Allowed]
    (defaultTable : ReceiverContingencyTable (RIn := RIn) (SIn := SIn) (ROut := ROut))
    (hdefault : Allowed defaultTable)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hwin : ∀ env : Nat -> RIn × SIn,
      M.WinsPlay (pairPlay receiver sender env))
    (hallowed : ∀ past, Allowed (receiver past)) :
    ∃ controller :
        TransitionRationalTree.{v, max u v x y w, w}
          SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
      NarrowedAllThreadsWin M controller.labeledTree ∧
        NarrowedTablesAllowed M Allowed controller.labeledTree := by
  classical
  let tree := treeOfPair (SOut := SOut) receiver sender
  have hoblivious : SenderOblivious tree :=
    senderOblivious_treeOfPair receiver sender
  have htree : M.lift.WinningTree tree := by
    apply (M.lift_winningTree_iff tree).mpr
    simpa [tree, pairPlay] using hwin
  have htreeAllowed : ∀ node, Allowed (tree node).1 := by
    intro node
    exact hallowed node
  rcases exists_narrowed_tablesAllowed_of_senderOblivious_winningTree M
      Allowed defaultTable hdefault hoblivious htreeAllowed htree with
    ⟨narrowed, hthreads, hnarrowedAllowed⟩
  exact exists_transitionRational_narrowed_of_tablesAllowed M Allowed narrowed
    hthreads hnarrowedAllowed

end

end TableFirst

end DistributedSynthesis
