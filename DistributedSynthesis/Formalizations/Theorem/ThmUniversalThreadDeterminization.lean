/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Automata.SequenceParity
import DistributedSynthesis.Formalizations.Lemma.LemSendernarrowing
import DistributedSynthesis.Formalizations.Theorem.ThmPitermanDeterminization
import DistributedSynthesis.Formalizations.Theorem.ThmDPACombinators

/-!
# Universal thread determinization

This file discharges `NarrowedThreadDPACertificate` unconditionally.

The universal thread condition of `LemSendernarrowing` says: along every
sender branch of a narrowed tree, every monitor thread — one thread per
choice of receiver inputs — satisfies the min-even parity condition.  Read
along one branch this is acceptance by a universal parity word automaton
over the narrowed labels, with state space the block monitor states and
one transition per receiver input.

The determinization is by complementation:

1. `threadBuchi` is a nondeterministic Büchi automaton accepting exactly
   the words along which *some* thread has min-odd parity.  It guesses the
   thread, an odd priority threshold from the finite monitor priority
   range, and a point after which no smaller priority occurs; acceptance
   visits are the threshold hits after the guess.
2. The checked Piterman compiler determinizes `threadBuchi` to a DPA.
3. Shifting priorities by one complements the DPA
   (`shiftPriority_one_accepts_iff_not_accepts`), giving `threadDPA`,
   which accepts exactly the words on which every thread is min-even.

`BlockRecordMonitor.narrowedThreadDPACertificate` packages `threadDPA` as
the deterministic block monitor over the sender branching required by
`NarrowedThreadDPACertificate`.  Combined with
`block_realizable_iff_implementable_controller`, block realizability is
now unconditionally equivalent to the existence of a finite-state
implementable controller
(`block_realizable_iff_implementable_controller_unconditional`).
-/

namespace DistributedSynthesis

universe u v x y w

/-- Deterministic parity acceptance is the min-even condition on run priorities. -/
theorem DetParityAutomaton.accepts_iff_natSeqMinEvenParity
    {Alphabet : Type u}
    (A : DetParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    A.Accepts word ↔
      NatSeqMinEvenParity (fun n => A.priority (A.run word n)) :=
  Iff.rfl

section UniversalThread

variable {RIn : Type u} {SIn : Type v} {ROut : Type x} {SOut : Type y}

namespace BlockRecordMonitor

variable (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut)

/-- The finite range of monitor priorities. -/
noncomputable def priorityRange : Finset Nat :=
  Finset.image M.priority Finset.univ

/-- One letter of the narrowed-label word read along a sender branch. -/
abbrev ThreadLetter :=
  NarrowedBlockLabel RIn SIn ROut SOut M.State × SIn

/-- The word read along a sender branch of a narrowed tree. -/
def branchWord
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (branch : Nat -> SIn) (n : Nat) : ThreadLetter M :=
  (narrowed (branchNode branch n), branch n)

/--
A monitor thread of a narrowed-label word: an evolution of the block
monitor under some sequence of receiver inputs.
-/
def IsThread (word : Nat -> ThreadLetter M) (q : Nat -> M.State) : Prop :=
  q 0 = M.initial ∧
    ∀ n : Nat, ∃ r : RIn,
      q (n + 1) = M.step (q n) (narrowedRecord M (word n).1 (q n) (r, (word n).2))

/-- State priority sequences live inside the finite monitor priority range. -/
theorem priority_range_finite (q : Nat -> M.State) :
    (Set.range (fun n => M.priority (q n))).Finite := by
  refine (M.priorityRange : Finset Nat).finite_toSet.subset ?_
  rintro p ⟨n, rfl⟩
  rw [Finset.mem_coe, priorityRange]
  exact Finset.mem_image_of_mem M.priority (Finset.mem_univ (q n))

/-- States of the min-odd thread guess automaton. -/
abbrev ThreadGuessState :=
  M.State × Option {p : Nat // p ∈ M.priorityRange}

/--
The nondeterministic Büchi automaton accepting words with a min-odd
thread.  The `none` phase tracks a guessed thread; the `some t` phase
additionally asserts that every later priority is at least the odd
threshold `t`, with Büchi visits at threshold hits.
-/
noncomputable def threadBuchi :
    NondetBuchiAutomaton.{max u v x y w, w} (ThreadLetter M) where
  State := ThreadGuessState M
  stateFinite := by
    classical
    infer_instance
  initial := (M.initial, none)
  step := fun source letter target =>
    (∃ r : RIn,
      target.1 = M.step source.1
        (narrowedRecord M letter.1 source.1 (r, letter.2))) ∧
      ((source.2 = none ∧
          (target.2 = none ∨
            ∃ t : {p : Nat // p ∈ M.priorityRange},
              target.2 = some t ∧
                ¬ DetParityAutomaton.NatEven t.1 ∧
                  t.1 ≤ M.priority target.1)) ∨
        (∃ t : {p : Nat // p ∈ M.priorityRange},
          source.2 = some t ∧ target.2 = some t ∧
            t.1 ≤ M.priority target.1))
  accepting := fun state =>
    ∃ t : {p : Nat // p ∈ M.priorityRange},
      state.2 = some t ∧ M.priority state.1 = t.1

/-- Once the threshold is guessed, the tag persists. -/
theorem threadBuchi_tag_persists
    {word : OmegaWord (ThreadLetter M)}
    (run : (threadBuchi M).RunFrom (threadBuchi M).initial word)
    {m : Nat} {t : {p : Nat // p ∈ M.priorityRange}}
    (hm : (run.path m).2 = some t) :
    ∀ k : Nat, m ≤ k -> (run.path k).2 = some t := by
  intro k hk
  induction k with
  | zero =>
      have hzero : m = 0 := Nat.le_zero.mp hk
      rw [← hzero]
      exact hm
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · have hkk : (run.path k).2 = some t := ih (by omega)
        rcases run.step_valid k with ⟨_, hnone | ⟨t', hsrc, htgt, _⟩⟩
        · rw [hkk] at hnone
          exact absurd hnone.1 (by simp)
        · rw [hkk] at hsrc
          rw [htgt, Option.some.inj hsrc]
      · have heq : m = k + 1 := by omega
        rw [← heq]
        exact hm

/-- Every tagged state carries an odd threshold below its own priority. -/
theorem threadBuchi_tag_sound
    {word : OmegaWord (ThreadLetter M)}
    (run : (threadBuchi M).RunFrom (threadBuchi M).initial word) :
    ∀ k : Nat, ∀ t : {p : Nat // p ∈ M.priorityRange},
      (run.path k).2 = some t ->
        ¬ DetParityAutomaton.NatEven t.1 ∧
          t.1 ≤ M.priority (run.path k).1 := by
  intro k
  induction k with
  | zero =>
      intro t ht
      have h2 : (run.path 0).2 = none :=
        congrArg Prod.snd run.initial_state
      rw [ht] at h2
      exact absurd h2 (by simp)
  | succ k ih =>
      intro t ht
      rcases run.step_valid k with ⟨_, ⟨_, hnone | ⟨t', htgt, hodd, hle⟩⟩ | ⟨t', hsrc, htgt, hle⟩⟩
      · rw [ht] at hnone
        exact absurd hnone (by simp)
      · rw [ht] at htgt
        rw [Option.some.inj htgt]
        exact ⟨hodd, hle⟩
      · rw [ht] at htgt
        have htt : t = t' := Option.some.inj htgt
        rcases ih t' hsrc with ⟨hodd, _⟩
        rw [htt]
        exact ⟨hodd, hle⟩

/-- The guess automaton accepts exactly the words with a min-odd thread. -/
theorem threadBuchi_accepts_iff
    (word : OmegaWord (ThreadLetter M)) :
    (threadBuchi M).Accepts word ↔
      ∃ q : Nat -> M.State,
        IsThread M word q ∧
          NatSeqMinOddParity (fun n => M.priority (q n)) := by
  constructor
  · rintro ⟨run, haccepts⟩
    refine ⟨fun n => (run.path n).1, ⟨congrArg Prod.fst run.initial_state, ?_⟩, ?_⟩
    · intro n
      exact (run.step_valid n).1
    · rcases haccepts 0 with ⟨m, _, ⟨t, hmtag, _⟩⟩
      have hpersist := threadBuchi_tag_persists M run hmtag
      have hsound := threadBuchi_tag_sound M run
      refine ⟨t.1, (hsound m t hmtag).1, ?_, ?_⟩
      · intro n
        rcases haccepts (max n m) with ⟨k, hk, ⟨t', hktag, hkprio⟩⟩
        have hktag' : (run.path k).2 = some t :=
          hpersist k (le_trans (le_max_right n m) hk)
        rw [hktag'] at hktag
        rw [← Option.some.inj hktag] at hkprio
        exact ⟨k, le_trans (le_max_left n m) hk, hkprio⟩
      · intro p hp
        rcases hp m with ⟨k, hk, hkprio⟩
        have hktag : (run.path k).2 = some t := hpersist k hk
        have hle := (hsound k t hktag).2
        have hkprio' : M.priority (run.path k).1 = p := hkprio
        omega
  · rintro ⟨q, ⟨hinit, hstep⟩, ⟨p, hodd, hseen, hmin⟩⟩
    have hpmem : p ∈ M.priorityRange := by
      rcases hseen 0 with ⟨k, _, hk⟩
      have hk' : M.priority (q k) = p := hk
      rw [priorityRange, ← hk']
      exact Finset.mem_image_of_mem M.priority (Finset.mem_univ (q k))
    rcases natSeq_eventually_ge_of_min_recurring
        (fun n => M.priority (q n))
        (priority_range_finite M q) hmin with ⟨N, hN⟩
    classical
    set path : Nat -> ThreadGuessState M :=
      fun k => (q k, if k ≤ N then none else some ⟨p, hpmem⟩) with hpathdef
    have hpathLe : ∀ k : Nat, k ≤ N -> (path k).2 = none := by
      intro k hk
      simp only [hpathdef, if_pos hk]
    have hpathGt : ∀ k : Nat, ¬ k ≤ N -> (path k).2 = some ⟨p, hpmem⟩ := by
      intro k hk
      simp only [hpathdef, if_neg hk]
    refine ⟨⟨path, ?_, ?_⟩, ?_⟩
    · show path 0 = (M.initial, none)
      simp only [hpathdef, if_pos (Nat.zero_le N), hinit]
    · intro n
      refine ⟨hstep n, ?_⟩
      by_cases hn : n ≤ N
      · by_cases hn1 : n + 1 ≤ N
        · exact Or.inl ⟨hpathLe n hn, Or.inl (hpathLe (n + 1) hn1)⟩
        · exact Or.inl ⟨hpathLe n hn,
            Or.inr ⟨⟨p, hpmem⟩, hpathGt (n + 1) hn1, hodd,
              hN (n + 1) (by omega)⟩⟩
      · have hn1 : ¬ n + 1 ≤ N := by omega
        exact Or.inr ⟨⟨p, hpmem⟩, hpathGt n hn, hpathGt (n + 1) hn1,
          hN (n + 1) (by omega)⟩
    · intro n
      rcases hseen (max n (N + 1)) with ⟨k, hk, hkprio⟩
      have hkN : ¬ k ≤ N := by
        have hge := le_trans (le_max_right n (N + 1)) hk
        omega
      exact ⟨k, le_trans (le_max_left n (N + 1)) hk,
        ⟨⟨p, hpmem⟩, hpathGt k hkN, hkprio⟩⟩

/--
The deterministic parity automaton for the universal thread condition:
Piterman determinization of the guess automaton, complemented by the
priority shift.
-/
noncomputable def threadDPA :
    DetParityAutomaton.{max u v x y w, w} (ThreadLetter M) :=
  (((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
      (ThreadLetter M)).compile (threadBuchi M)).dpa).shiftPriority 1

/-- The thread DPA accepts exactly the words on which every thread wins. -/
theorem threadDPA_accepts_iff
    (word : OmegaWord (ThreadLetter M)) :
    (threadDPA M).Accepts word ↔
      ∀ q : Nat -> M.State,
        IsThread M word q ->
          NatSeqMinEvenParity (fun n => M.priority (q n)) := by
  rw [threadDPA,
    DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts,
    ((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
      (ThreadLetter M)).compile (threadBuchi M)).correct word,
    threadBuchi_accepts_iff]
  constructor
  · intro hnot q hthread
    rcases natSeqMinEvenParity_or_minOddParity
        (fun n => M.priority (q n)) (priority_range_finite M q) with
      heven | hodd
    · exact heven
    · exact absurd ⟨q, hthread, hodd⟩ hnot
  · rintro hall ⟨q, hthread, hodd⟩
    exact not_natSeqMinEvenParity_and_natSeqMinOddParity _
      ⟨hall q hthread, hodd⟩

/-- Sender words of environment branch nodes are sender branch nodes. -/
theorem senderWord_branchNode
    (env : Nat -> RIn × SIn) (branch : Nat -> SIn)
    (hbranch : ∀ k : Nat, (env k).2 = branch k) :
    ∀ n : Nat, senderWord (branchNode env n) = branchNode branch n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show senderWord (branchNode env n ++ [env n]) = _
      rw [senderWord_append, ih, hbranch n]
      rfl

/-- The narrowed thread states of an environment word form a thread. -/
theorem isThread_narrowedThreadState
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (env : Nat -> RIn × SIn) :
    IsThread M (branchWord M narrowed (fun k => (env k).2))
      (fun n => narrowedThreadState M narrowed env n) := by
  refine ⟨rfl, ?_⟩
  intro n
  refine ⟨(env n).1, ?_⟩
  show narrowedControl M narrowed (branchNode env n ++ [env n]) = _
  rw [narrowedControl_append M narrowed (branchNode env n) (env n),
    senderWord_branchNode env (fun k => (env k).2) (fun _ => rfl) n]
  rfl

/-- Every thread of a branch word is realized by an environment word. -/
theorem exists_env_of_isThread
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (branch : Nat -> SIn)
    {q : Nat -> M.State}
    (hthread : IsThread M (branchWord M narrowed branch) q) :
    ∃ env : Nat -> RIn × SIn,
      (∀ k : Nat, (env k).2 = branch k) ∧
        ∀ n : Nat, narrowedThreadState M narrowed env n = q n := by
  classical
  obtain ⟨hinit, hstep⟩ := hthread
  choose choice hchoice using hstep
  refine ⟨fun n => (choice n, branch n), fun _ => rfl, ?_⟩
  intro n
  induction n with
  | zero => exact hinit.symm ▸ rfl
  | succ n ih =>
      show narrowedControl M narrowed
          (branchNode (fun k => (choice k, branch k)) n ++
            [(choice n, branch n)]) = q (n + 1)
      rw [narrowedControl_append,
        senderWord_branchNode (fun k => (choice k, branch k)) branch
          (fun _ => rfl) n]
      have ih' : narrowedControl M narrowed
          (branchNode (fun k => (choice k, branch k)) n) = q n := ih
      rw [ih', hchoice n]
      rfl

section Certificate

variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq SIn]

/-- The thread DPA packaged as a deterministic block monitor over sender branching. -/
noncomputable def threadBlockMonitor :
    DeterministicBlockMonitor.{v, max u v x y w, w}
      SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State) where
  branchFinite := inferInstance
  alphabetFinite := by
    classical
    infer_instance
  State := (threadDPA M).State
  stateFinite := (threadDPA M).stateFinite
  initial := (threadDPA M).initial
  step := fun state label branch => (threadDPA M).step state (label, branch)
  priority := (threadDPA M).priority

/-- The block-monitor control along a branch is the thread-DPA run on the branch word. -/
theorem threadBlockMonitor_control_eq_run
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State))
    (branch : Nat -> SIn) :
    ∀ n : Nat,
      (threadBlockMonitor M).control narrowed (branchNode branch n) =
        (threadDPA M).run (branchWord M narrowed branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      show (threadBlockMonitor M).control narrowed
          (branchNode branch n ++ [branch n]) = _
      rw [(threadBlockMonitor M).control_append narrowed
        (branchNode branch n) (branch n), ih]
      rfl

/-- The winning trees of the thread block monitor are the all-threads-winning trees. -/
theorem threadBlockMonitor_winningTree_iff
    (narrowed : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    (threadBlockMonitor M).WinningTree narrowed ↔
      NarrowedAllThreadsWin M narrowed := by
  constructor
  · intro hwin env
    have hbranch := hwin (fun k => (env k).2)
    have heq :
        (fun n =>
            (threadBlockMonitor M).priority
              ((threadBlockMonitor M).control narrowed
                (branchNode (fun k => (env k).2) n))) =
          fun n =>
            (threadDPA M).priority
              ((threadDPA M).run
                (branchWord M narrowed (fun k => (env k).2)) n) := by
      funext n
      rw [threadBlockMonitor_control_eq_run M narrowed (fun k => (env k).2) n]
      rfl
    rw [heq] at hbranch
    have haccepts :
        (threadDPA M).Accepts (branchWord M narrowed (fun k => (env k).2)) :=
      (DetParityAutomaton.accepts_iff_natSeqMinEvenParity _ _).mpr hbranch
    exact (threadDPA_accepts_iff M _).mp haccepts
      (fun n => narrowedThreadState M narrowed env n)
      (isThread_narrowedThreadState M narrowed env)
  · intro hthreads branch
    have haccepts :
        (threadDPA M).Accepts (branchWord M narrowed branch) := by
      rw [threadDPA_accepts_iff]
      intro q hthread
      rcases exists_env_of_isThread M narrowed branch hthread with
        ⟨env, _, hstate⟩
      have hwin := hthreads env
      have heq :
          (fun n => M.priority (narrowedThreadState M narrowed env n)) =
            fun n => M.priority (q n) := by
        funext n
        rw [hstate n]
      rw [heq] at hwin
      exact hwin
    have hbranch :=
      (DetParityAutomaton.accepts_iff_natSeqMinEvenParity _ _).mp haccepts
    have heq :
        (fun n =>
            (threadDPA M).priority
              ((threadDPA M).run (branchWord M narrowed branch) n)) =
          fun n =>
            (threadBlockMonitor M).priority
              ((threadBlockMonitor M).control narrowed
                (branchNode branch n)) := by
      funext n
      rw [threadBlockMonitor_control_eq_run M narrowed branch n]
      rfl
    rw [heq] at hbranch
    exact hbranch

/-- The unconditional narrowed-thread determinization certificate. -/
noncomputable def narrowedThreadDPACertificate :
    NarrowedThreadDPACertificate RIn SIn ROut SOut M where
  monitor := threadBlockMonitor M
  winning_iff := threadBlockMonitor_winningTree_iff M

end Certificate

end BlockRecordMonitor

/--
Unconditional sender-narrowing equivalence: block realizability by a local
receiver/sender pair is equivalent to the existence of a finite-state
implementable controller over the sender branching.  All certificates are
discharged: the receiver folding is the checked Zielonka positional
determinacy, and the universal thread determinization is the checked
Piterman construction complemented by the parity shift.
-/
theorem block_realizable_iff_implementable_controller_unconditional
    [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
    [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
    [DecidableEq RIn] [DecidableEq SIn]
    (M : BlockRecordMonitor.{u, v, x, y, w} RIn SIn ROut SOut) :
    (∃ receiver : ReceiverBlockStrategy RIn SIn ROut,
      ∃ sender : SenderBlockStrategy SIn SOut,
        ∀ env : Nat -> RIn × SIn,
          M.WinsPlay (pairPlay receiver sender env)) ↔
      ∃ controller :
          TransitionRationalTree.{v, max u v x y w, w}
            SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State),
        NarrowedAllThreadsWin M controller.labeledTree :=
  block_realizable_iff_implementable_controller M
    (BlockRecordMonitor.narrowedThreadDPACertificate M)

end UniversalThread

end DistributedSynthesis
