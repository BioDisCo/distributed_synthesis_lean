/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlockRecordMonitorFirstLetterGuard
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing

/-!
# A reusable two-letter safety guard for block monitors

The first pending cross-anchor needs one finite piece of coherence beyond a
root pin: the record selected one round later must be compatible with the
literal first record.  This wrapper remembers that first realized record in
the objective monitor, checks a Boolean relation on the second record, and
then becomes inert.  Neither local strategy receives the remembered record or
the guard phase; they remain proof-monitor state only.

As for `firstLetterGuard`, failure receives sticky odd priority one.  Hence
unconditional tree narrowing preserves both finite prefix tests.
-/

namespace DistributedSynthesis

universe i u v x y w z

namespace BlockRecordMonitor

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}
variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- The three proof-monitor phases of a two-letter prefix test. -/
inductive FirstTwoLetterGuardPhase
  | first
  | second
  | done
  deriving DecidableEq, Fintype

/-- Product state of the base monitor and the finite two-letter test. -/
structure FirstTwoLetterGuardState where
  base : M.State
  phase : FirstTwoLetterGuardPhase
  anchor : Option (RealizedBlockRound RIn SIn ROut SOut)
  safe : Bool

noncomputable instance [Fintype RIn] [Fintype SIn] [Fintype ROut]
    [Fintype SOut] : Fintype (FirstTwoLetterGuardState M) := by
  classical
  let Letter := RealizedBlockRound RIn SIn ROut SOut
  let Rep := M.State × FirstTwoLetterGuardPhase × Option Letter × Bool
  let equiv : FirstTwoLetterGuardState M ≃ Rep := {
      toFun := fun state =>
        (state.base, state.phase, state.anchor, state.safe)
      invFun := fun state =>
        ⟨state.1, state.2.1, state.2.2.1, state.2.2.2⟩
      left_inv := by intro state; cases state; rfl
      right_inv := by intro state; cases state; rfl
    }
  exact Fintype.ofEquiv Rep equiv.symm

section Finite

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]

/-- Add sticky tests on the first record and on the ordered pair consisting
of the first two records. -/
noncomputable def firstTwoLetterGuard
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool) :
    BlockRecordMonitor RIn SIn ROut SOut := by
  classical
  exact {
    State := FirstTwoLetterGuardState M
    stateFinite := inferInstance
    initial := ⟨M.initial, .first, none, true⟩
    step := fun state letter =>
      match state.phase with
      | .first =>
          ⟨M.step state.base letter, .second, some letter,
            state.safe && firstAllowed letter⟩
      | .second =>
          ⟨M.step state.base letter, .done, state.anchor,
            state.safe &&
              (match state.anchor with
              | some first => secondAllowed first letter
              | none => false)⟩
      | .done =>
          ⟨M.step state.base letter, .done, state.anchor, state.safe⟩
    priority := fun state =>
      if state.safe then M.priority state.base + 2 else 1
  }

@[simp] theorem firstTwoLetterGuard_initial
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool) :
    (M.firstTwoLetterGuard firstAllowed secondAllowed).initial =
      ⟨M.initial, .first, none, true⟩ := rfl

@[simp] theorem firstTwoLetterGuard_step_base
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstTwoLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut) :
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).step state letter).base =
      M.step state.base letter := by
  rcases state with ⟨base, phase, anchor, safe⟩
  cases phase <;> rfl

/-- The base component remains exactly the underlying monitor run. -/
theorem firstTwoLetterGuard_run_base
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut)) : ∀ n,
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).base =
      M.run word n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [BlockRecordMonitor.run, BlockRecordMonitor.run,
        firstTwoLetterGuard_step_base, ih]

@[simp] theorem firstTwoLetterGuard_step_safe_false
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstTwoLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut)
    (hfalse : state.safe = false) :
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).step state letter).safe =
      false := by
  rcases state with ⟨base, phase, anchor, safe⟩
  change safe = false at hfalse
  cases phase <;> simp [firstTwoLetterGuard, hfalse]

@[simp] theorem firstTwoLetterGuard_step_phase_done
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstTwoLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut)
    (hdone : state.phase = .done) :
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).step state letter).phase =
      .done := by
  rcases state with ⟨base, phase, anchor, safe⟩
  cases phase <;> simp at hdone
  rfl

@[simp] theorem firstTwoLetterGuard_step_safe_of_done
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (state : FirstTwoLetterGuardState M)
    (letter : RealizedBlockRound RIn SIn ROut SOut)
    (hdone : state.phase = .done) (hsafe : state.safe = true) :
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).step state letter).safe =
      true := by
  rcases state with ⟨base, phase, anchor, safe⟩
  cases phase <;> simp at hdone
  simpa [firstTwoLetterGuard] using hsafe

/-- Once either prefix test fails, the failure persists forever. -/
theorem firstTwoLetterGuard_safe_false_persists
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (n : Nat)
    (hfalse :
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe =
        false) : ∀ k,
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word (n + k)).safe =
      false := by
  intro k
  induction k with
  | zero => simpa using hfalse
  | succ k ih =>
      rw [Nat.add_succ, BlockRecordMonitor.run]
      exact firstTwoLetterGuard_step_safe_false M firstAllowed secondAllowed _ _
        ih

/-- Winning forces the sticky prefix-safety bit to remain true. -/
theorem firstTwoLetterGuard_safe_of_wins
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.firstTwoLetterGuard firstAllowed secondAllowed).WinsPlay word)
    (n : Nat) :
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe =
      true := by
  by_contra hnot
  have hfalse :
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe =
        false := Bool.eq_false_of_not_eq_true hnot
  have hpersist := M.firstTwoLetterGuard_safe_false_persists firstAllowed
    secondAllowed word n hfalse
  have heventual : ∀ k, n ≤ k →
      (M.firstTwoLetterGuard firstAllowed secondAllowed).priority
        ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word k) = 1 := by
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    change (if
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word
        (n + j)).safe then _ else 1) = 1
    rw [hpersist j]
    rfl
  exact not_natSeqMinEvenParity_of_eventually_one _ n heventual hwins

/-- Every winning play satisfies both finite prefix predicates. -/
theorem firstTwoLetterGuard_allowed_of_wins
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.firstTwoLetterGuard firstAllowed secondAllowed).WinsPlay word) :
    firstAllowed (word 0) = true ∧
      secondAllowed (word 0) (word 1) = true := by
  have hone := M.firstTwoLetterGuard_safe_of_wins firstAllowed secondAllowed
    word hwins 1
  have htwo := M.firstTwoLetterGuard_safe_of_wins firstAllowed secondAllowed
    word hwins 2
  constructor
  · simpa [BlockRecordMonitor.run, firstTwoLetterGuard] using hone
  · have hpair : firstAllowed (word 0) = true ∧
        secondAllowed (word 0) (word 1) = true := by
      simpa [BlockRecordMonitor.run, firstTwoLetterGuard] using htwo
    exact hpair.2

/-- After two successful prefix tests, the safety bit stays true. -/
theorem firstTwoLetterGuard_run_safe_of_allowed
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hfirst : firstAllowed (word 0) = true)
    (hsecond : secondAllowed (word 0) (word 1) = true) : ∀ n,
    ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe =
      true := by
  have htwo :
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word 2).safe =
        true := by
    simp [BlockRecordMonitor.run, firstTwoLetterGuard, hfirst, hsecond]
  have hphase : ∀ k,
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word
        (2 + k)).phase = .done := by
    intro k
    induction k with
    | zero => simp [BlockRecordMonitor.run, firstTwoLetterGuard]
    | succ k ih =>
        rw [Nat.add_succ, BlockRecordMonitor.run]
        exact firstTwoLetterGuard_step_phase_done M firstAllowed secondAllowed
          _ _ ih
  have hpersist : ∀ k,
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word
        (2 + k)).safe = true := by
    intro k
    induction k with
    | zero => simpa using htwo
    | succ k ih =>
        rw [Nat.add_succ, BlockRecordMonitor.run]
        exact firstTwoLetterGuard_step_safe_of_done M firstAllowed secondAllowed
          _ _ (hphase k) ih
  intro n
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero =>
          simpa [BlockRecordMonitor.run, firstTwoLetterGuard, hfirst]
      | succ n =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hpersist n

/-- Forgetting the finite two-letter test preserves base winning. -/
theorem firstTwoLetterGuard_base_wins_of_wins
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (word : OmegaWord (RealizedBlockRound RIn SIn ROut SOut))
    (hwins : (M.firstTwoLetterGuard firstAllowed secondAllowed).WinsPlay word) :
    M.WinsPlay word := by
  unfold BlockRecordMonitor.WinsPlay at hwins ⊢
  have heq :
      (fun n => (M.firstTwoLetterGuard firstAllowed secondAllowed).priority
        ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change (if
      ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe
      then M.priority
        ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).base + 2
      else 1) = M.priority (M.run word n) + 2
    rw [M.firstTwoLetterGuard_safe_of_wins firstAllowed secondAllowed word hwins
      n, if_pos rfl,
      M.firstTwoLetterGuard_run_base firstAllowed secondAllowed word n]
  rw [heq] at hwins
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mp hwins

/-- A base-realizing strategy satisfying both finite prefix tests realizes the
strengthened monitor. -/
theorem firstTwoLetterGuard_realizable
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (receiver : ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ env : Nat → RIn × SIn,
      M.WinsPlay (pairPlay receiver sender env))
    (hfirst : ∀ env : Nat → RIn × SIn,
      firstAllowed (pairPlay receiver sender env 0) = true)
    (hsecond : ∀ env : Nat → RIn × SIn,
      secondAllowed (pairPlay receiver sender env 0)
        (pairPlay receiver sender env 1) = true) :
    ∀ env : Nat → RIn × SIn,
      (M.firstTwoLetterGuard firstAllowed secondAllowed).WinsPlay
        (pairPlay receiver sender env) := by
  intro env
  let word := pairPlay receiver sender env
  have hsafe := M.firstTwoLetterGuard_run_safe_of_allowed firstAllowed
    secondAllowed word (hfirst env) (hsecond env)
  have hparity := hbase env
  unfold BlockRecordMonitor.WinsPlay at hparity ⊢
  have heq :
      (fun n => (M.firstTwoLetterGuard firstAllowed secondAllowed).priority
        ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n)) =
        fun n => M.priority (M.run word n) + 2 := by
    funext n
    change
      (if ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).safe
        then M.priority
          ((M.firstTwoLetterGuard firstAllowed secondAllowed).run word n).base +
            2
        else 1) = M.priority (M.run word n) + 2
    rw [hsafe n, if_pos rfl,
      M.firstTwoLetterGuard_run_base firstAllowed secondAllowed word n]
  rw [heq]
  exact (natSeqMinEvenParity_add_const (d := 2) ⟨1, rfl⟩).mpr hparity

section Narrowing

variable [DecidableEq RIn] [DecidableEq SIn]

/-- Rationalization-facing form: every branch of a universally winning
narrowed controller satisfies both prefix predicates.  The branch is exposed
only as its induced physical play, so consumers need not unfold the narrowed
controller representation. -/
theorem firstTwoLetterGuard_narrowed_play_allowed
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (narrowed : LabeledTree SIn
      (NarrowedBlockLabel RIn SIn ROut SOut
        (M.firstTwoLetterGuard firstAllowed secondAllowed).State))
    (hthreads : NarrowedAllThreadsWin
      (M.firstTwoLetterGuard firstAllowed secondAllowed) narrowed)
    (env : Nat → RIn × SIn) :
    let play := treePlay
      (narrowedInducedTree
        (M.firstTwoLetterGuard firstAllowed secondAllowed) narrowed) env
    firstAllowed (play 0) = true ∧
      secondAllowed (play 0) (play 1) = true := by
  let guard := M.firstTwoLetterGuard firstAllowed secondAllowed
  let tree := narrowedInducedTree guard narrowed
  let play := treePlay tree env
  have htree : guard.lift.WinningTree tree :=
    narrowedInducedTree_winningTree_of_allThreadsWin guard hthreads
  have hwins : guard.WinsPlay play :=
    (guard.lift_winningTree_iff tree).mp htree env
  exact M.firstTwoLetterGuard_allowed_of_wins firstAllowed secondAllowed play
    hwins

/-- Concrete two-node form used by finite controller tables.  The second
record is read at the controller node selected by the sender component of the
first move and at the exact guarded monitor state reached after that record. -/
theorem firstTwoLetterGuard_narrowed_records_allowed
    (firstAllowed : RealizedBlockRound RIn SIn ROut SOut → Bool)
    (secondAllowed : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)
    (narrowed : LabeledTree SIn
      (NarrowedBlockLabel RIn SIn ROut SOut
        (M.firstTwoLetterGuard firstAllowed secondAllowed).State))
    (hthreads : NarrowedAllThreadsWin
      (M.firstTwoLetterGuard firstAllowed secondAllowed) narrowed)
    (firstMove secondMove : RIn × SIn) :
    let guard := M.firstTwoLetterGuard firstAllowed secondAllowed
    let firstRecord := narrowedRecord guard (narrowed []) guard.initial
      firstMove
    let secondRecord := narrowedRecord guard (narrowed [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    firstAllowed firstRecord = true ∧
      secondAllowed firstRecord secondRecord = true := by
  let env : Nat → RIn × SIn
    | 0 => firstMove
    | _ + 1 => secondMove
  have h := M.firstTwoLetterGuard_narrowed_play_allowed firstAllowed
    secondAllowed narrowed hthreads env
  simpa [env, treePlay, narrowedInducedTree, branchNode, narrowedControl,
    narrowedControlAux, narrowedRecord, senderWord] using h

/-- Equality-specialized second-record relation.  This is the minimal shape
used by pending cross anchors: the second local physical output is forced to
the output prescribed by the first-record anchor and the second input. -/
noncomputable def secondOutputAllowed
    {Output : Type*} [DecidableEq Output]
    (actual : RealizedBlockRound RIn SIn ROut SOut → Output)
    (expected : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Output)
    (first second : RealizedBlockRound RIn SIn ROut SOut) : Bool :=
  decide (actual second = expected first second)

omit [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [DecidableEq RIn]
    [DecidableEq SIn] in
theorem secondOutputAllowed_eq
    {Output : Type*} [DecidableEq Output]
    (actual : RealizedBlockRound RIn SIn ROut SOut → Output)
    (expected : RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Output)
    (first second : RealizedBlockRound RIn SIn ROut SOut)
    (hallowed : secondOutputAllowed actual expected first second = true) :
    actual second = expected first second := by
  exact of_decide_eq_true hallowed

end Narrowing

end Finite

/-! ## Simultaneous finite-family rationalization -/

section Family

variable {I : Type i}
variable [Inhabited I] [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable [Fintype I] [Fintype RIn] [Fintype SIn] [Fintype ROut]
  [Fintype SOut]
variable [DecidableEq I] [DecidableEq RIn] [DecidableEq SIn]

variable
  (family : I → BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)
  (firstAllowed : ∀ index : I,
    RealizedBlockRound RIn SIn ROut SOut → Bool)
  (secondAllowed : ∀ index : I,
    RealizedBlockRound RIn SIn ROut SOut →
      RealizedBlockRound RIn SIn ROut SOut → Bool)

/-- The monitor family obtained by adding the two finite prefix tests member
by member. -/
noncomputable abbrev firstTwoLetterGuardFamily (index : I) :=
  (family index).firstTwoLetterGuard (firstAllowed index)
    (secondAllowed index)

/-- A simultaneous finite table obtained only after both prefix conditions
have been inserted into the objective. -/
noncomputable def firstTwoLetterGuardedFiniteRootFamilyTable
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ index env,
      (family index).WinsPlay (pairPlay (receiver index) sender env))
    (hfirst : ∀ index env,
      firstAllowed index (pairPlay (receiver index) sender env 0) = true)
    (hsecond : ∀ index env,
      secondAllowed index (pairPlay (receiver index) sender env 0)
        (pairPlay (receiver index) sender env 1) = true) :
    FiniteRootFamilyTable
      (firstTwoLetterGuardFamily family firstAllowed secondAllowed) := by
  let hguard : ∀ index env,
      (firstTwoLetterGuardFamily family firstAllowed secondAllowed index
        ).WinsPlay (pairPlay (receiver index) sender env) := by
    intro index
    exact (family index).firstTwoLetterGuard_realizable
      (firstAllowed index) (secondAllowed index) (receiver index) sender
      (hbase index) (hfirst index) (hsecond index)
  exact finiteRootFamilyTable
    (firstTwoLetterGuardFamily family firstAllowed secondAllowed) receiver sender
      hguard

/-- Read one member of the simultaneously rationalized guarded table. -/
noncomputable def firstTwoLetterGuardedFiniteRootMemberController
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ index env,
      (family index).WinsPlay (pairPlay (receiver index) sender env))
    (hfirst : ∀ index env,
      firstAllowed index (pairPlay (receiver index) sender env 0) = true)
    (hsecond : ∀ index env,
      secondAllowed index (pairPlay (receiver index) sender env 0)
        (pairPlay (receiver index) sender env 1) = true)
    (index : I) :=
  finiteRootMemberController
    (firstTwoLetterGuardFamily family firstAllowed secondAllowed)
    (firstTwoLetterGuardedFiniteRootFamilyTable family firstAllowed
      secondAllowed receiver sender hbase hfirst hsecond
      ).toTransitionRationalTree index

/-- Every projected member still satisfies its own first- and second-record
relations.  This is the rationalization-facing interface needed by the
pending cross-anchor construction. -/
theorem firstTwoLetterGuardedFiniteRootMemberController_records_allowed
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ index env,
      (family index).WinsPlay (pairPlay (receiver index) sender env))
    (hfirst : ∀ index env,
      firstAllowed index (pairPlay (receiver index) sender env 0) = true)
    (hsecond : ∀ index env,
      secondAllowed index (pairPlay (receiver index) sender env 0)
        (pairPlay (receiver index) sender env 1) = true)
    (index : I) (firstMove secondMove : RIn × SIn) :
    let guard := firstTwoLetterGuardFamily family firstAllowed secondAllowed
      index
    let controller := firstTwoLetterGuardedFiniteRootMemberController family
      firstAllowed secondAllowed receiver sender hbase hfirst hsecond index
    let firstRecord := narrowedRecord guard (controller.labeledTree [])
      guard.initial firstMove
    let secondRecord := narrowedRecord guard
      (controller.labeledTree [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    firstAllowed index firstRecord = true ∧
      secondAllowed index firstRecord secondRecord = true := by
  let guardFamily := firstTwoLetterGuardFamily family firstAllowed secondAllowed
  let hguard : ∀ member env,
      (guardFamily member).WinsPlay (pairPlay (receiver member) sender env) := by
    intro member
    exact (family member).firstTwoLetterGuard_realizable
      (firstAllowed member) (secondAllowed member) (receiver member) sender
      (hbase member) (hfirst member) (hsecond member)
  let table := firstTwoLetterGuardedFiniteRootFamilyTable family firstAllowed
    secondAllowed receiver sender hbase hfirst hsecond
  have htable : NarrowedAllThreadsWin (finiteRootFamilyMonitor guardFamily)
      table.toTransitionRationalTree.labeledTree := by
    exact finiteRootFamilyTable_wins guardFamily receiver sender hguard
  have hmember := finiteRootMemberController_allThreadsWin guardFamily
    table.toTransitionRationalTree htable index
  exact (family index).firstTwoLetterGuard_narrowed_records_allowed
    (firstAllowed index) (secondAllowed index)
    (finiteRootMemberController guardFamily table.toTransitionRationalTree
      index).labeledTree hmember firstMove secondMove

/-! ### Equality-valued pending-output specialization -/

variable {Output : Type z} [DecidableEq Output]

/-- The projected controller obtained when the second guard is exactly an
output-equality test. -/
noncomputable def secondOutputGuardedFiniteRootMemberController
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ index env,
      (family index).WinsPlay (pairPlay (receiver index) sender env))
    (hfirst : ∀ index env,
      firstAllowed index (pairPlay (receiver index) sender env 0) = true)
    (actual : ∀ index : I,
      RealizedBlockRound RIn SIn ROut SOut → Output)
    (expected : ∀ index : I,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Output)
    (hsemantic : ∀ index env,
      actual index (pairPlay (receiver index) sender env 1) =
        expected index (pairPlay (receiver index) sender env 0)
          (pairPlay (receiver index) sender env 1))
    (index : I) :=
  firstTwoLetterGuardedFiniteRootMemberController family firstAllowed
    (fun member => secondOutputAllowed (actual member) (expected member))
    receiver sender hbase hfirst
    (fun member env => decide_eq_true (hsemantic member env)) index

/-- The equality checked on the semantic strategy survives simultaneous
finite-family rationalization.  This is the abstract pending cross-anchor
law: after one transition, the old controller's physical output is still the
one prescribed by the first-record anchor. -/
theorem secondOutputGuardedFiniteRootMemberController_output_eq
    (receiver : ∀ index : I, ReceiverBlockStrategy RIn SIn ROut)
    (sender : SenderBlockStrategy SIn SOut)
    (hbase : ∀ index env,
      (family index).WinsPlay (pairPlay (receiver index) sender env))
    (hfirst : ∀ index env,
      firstAllowed index (pairPlay (receiver index) sender env 0) = true)
    (actual : ∀ index : I,
      RealizedBlockRound RIn SIn ROut SOut → Output)
    (expected : ∀ index : I,
      RealizedBlockRound RIn SIn ROut SOut →
        RealizedBlockRound RIn SIn ROut SOut → Output)
    (hsemantic : ∀ index env,
      actual index (pairPlay (receiver index) sender env 1) =
        expected index (pairPlay (receiver index) sender env 0)
          (pairPlay (receiver index) sender env 1))
    (index : I) (firstMove secondMove : RIn × SIn) :
    let secondAllowed := fun member =>
      secondOutputAllowed (actual member) (expected member)
    let guard := firstTwoLetterGuardFamily family firstAllowed secondAllowed
      index
    let controller := secondOutputGuardedFiniteRootMemberController family
      firstAllowed receiver sender hbase hfirst actual expected hsemantic index
    let firstRecord := narrowedRecord guard (controller.labeledTree [])
      guard.initial firstMove
    let secondRecord := narrowedRecord guard
      (controller.labeledTree [firstMove.2])
      (guard.step guard.initial firstRecord) secondMove
    actual index secondRecord = expected index firstRecord secondRecord := by
  let secondAllowed := fun member =>
    secondOutputAllowed (actual member) (expected member)
  have hrecords :=
    firstTwoLetterGuardedFiniteRootMemberController_records_allowed family
      firstAllowed secondAllowed receiver sender hbase hfirst
      (fun member env => decide_eq_true (hsemantic member env)) index firstMove
        secondMove
  exact secondOutputAllowed_eq (actual index) (expected index) _ _ hrecords.2

end Family

end BlockRecordMonitor

end DistributedSynthesis
