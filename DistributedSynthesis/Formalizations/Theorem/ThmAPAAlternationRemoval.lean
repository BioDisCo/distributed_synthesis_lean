/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPitermanDeterminization

/-!
# APA alternation-removal backend adapters

This file contains checked adapters around APA run-tree semantics.  In
particular, an explicitly supplied APA-to-Buchi compiler can be composed with
the checked Piterman Buchi-to-DPA construction.  The file no longer declares a
cited alternation-removal axiom.

The intended internal replacement is the Miyano-Hayashi breakpoint construction
for a finite Streett chain obtained from Lean's min-even parity convention.  It
must track timed progress obligations through the actual chosen macro-step
supports.  A raw recurring-edge graph is not enough: recurring edges can occur
at unrelated levels and form abstract paths that are not realized by one
branch.

The `mhBuchi` skeleton below is intentionally kept with a checked
counterexample: always propagating every odd request is too strong, because
parity/Streett acceptance does not require finite one-shot odd requests to be
answered by a lower priority.  The final internal construction must replace
this skeleton, not prove it correct.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton

/-- The finite set of priorities that occur in an APA. -/
noncomputable def priorityFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Finset Nat := by
  classical
  exact Finset.univ.image A.priority

@[simp]
theorem mem_priorityFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (p : Nat) :
    p ∈ A.priorityFinset ↔ ∃ state : A.State, A.priority state = p := by
  classical
  simp [priorityFinset]

/-- The finite set of odd priorities that can generate Streett requests. -/
noncomputable def oddPriorityFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Finset Nat := by
  classical
  exact A.priorityFinset.filter (fun p => ¬ DetParityAutomaton.NatEven p)

@[simp]
theorem mem_oddPriorityFinset
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (p : Nat) :
    p ∈ A.oddPriorityFinset ↔
      (∃ state : A.State, A.priority state = p) ∧
        ¬ DetParityAutomaton.NatEven p := by
  classical
  simp [oddPriorityFinset]

/-- The request set for one odd-priority Streett pair. -/
def streettOddPriorityRequest
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (oddPriority : Nat)
    (state : A.State) :
    Prop :=
  A.priority state = oddPriority

/-- The grant set for one odd-priority Streett pair. -/
def streettOddPriorityGrant
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (oddPriority : Nat)
    (state : A.State) :
    Prop :=
  A.priority state < oddPriority

namespace Run

/--
Streett-chain presentation of Lean's min-even parity condition on one branch.

Every recurring odd priority must be answered by some recurring strictly lower
priority.  This is the parity-normalized condition used by the
Miyano-Hayashi breakpoint construction.
-/
def StreettOddPriorityChain
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    Prop :=
  ∀ oddPriority : Nat,
    ¬ DetParityAutomaton.NatEven oddPriority ->
      run.PrioritySeenInfinitelyOften branch oddPriority ->
        ∃ grantPriority : Nat,
          grantPriority < oddPriority ∧
            run.PrioritySeenInfinitelyOften branch grantPriority

/--
The min-even parity condition on a branch is equivalent to the odd-priority
Streett chain.
-/
theorem branchAccepts_iff_streettOddPriorityChain
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    run.BranchAccepts branch ↔ run.StreettOddPriorityChain branch := by
  constructor
  · intro hbranch oddPriority hodd hseenOdd
    rcases hbranch with ⟨p, hpEven, hpSeen, hpMin⟩
    have hp_le_odd : p ≤ oddPriority := hpMin oddPriority hseenOdd
    have hp_ne_odd : p ≠ oddPriority := by
      intro hp_eq
      exact hodd (by simpa [hp_eq] using hpEven)
    exact ⟨p, lt_of_le_of_ne hp_le_odd hp_ne_odd, hpSeen⟩
  · intro hstreett
    rcases run.exists_min_prioritySeenInfinitelyOften branch with
      ⟨p, hpSeen, hpMin⟩
    have hpEven : DetParityAutomaton.NatEven p := by
      by_contra hpOdd
      rcases hstreett p hpOdd hpSeen with ⟨q, hq_lt_p, hqSeen⟩
      have hp_le_q : p ≤ q := hpMin q hqSeen
      exact (Nat.not_lt_of_ge hp_le_q) hq_lt_p
    exact ⟨p, hpEven, hpSeen, hpMin⟩

/--
Run-tree acceptance is equivalent to the Streett-chain condition on every
active branch.
-/
theorem accepting_iff_all_branches_streettOddPriorityChain
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    run.Accepting ↔
      ∀ branch : Nat -> Nat,
        run.ActiveBranch branch -> run.StreettOddPriorityChain branch := by
  constructor
  · intro hacc branch hactive
    exact (run.branchAccepts_iff_streettOddPriorityChain branch).mp
      (hacc branch hactive)
  · intro hstreett branch hactive
    exact (run.branchAccepts_iff_streettOddPriorityChain branch).mpr
      (hstreett branch hactive)

/-- Every recurring branch priority is in the finite priority carrier of `A`. -/
theorem prioritySeenInfinitelyOften_mem_priorityFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    {branch : Nat -> Nat}
    {p : Nat}
    (hseen : run.PrioritySeenInfinitelyOften branch p) :
    p ∈ A.priorityFinset := by
  rcases hseen 0 with ⟨k, _hk, hkprio⟩
  exact (A.mem_priorityFinset p).mpr
    ⟨run.stateAt (branchPrefix branch k), hkprio⟩

/--
The Streett-chain condition can be checked over the finite odd-priority carrier
of `A`.
-/
theorem streettOddPriorityChain_iff_oddPriorityFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    run.StreettOddPriorityChain branch ↔
      ∀ oddPriority : Nat,
        oddPriority ∈ A.oddPriorityFinset ->
          run.PrioritySeenInfinitelyOften branch oddPriority ->
            ∃ grantPriority : Nat,
              grantPriority < oddPriority ∧
                run.PrioritySeenInfinitelyOften branch grantPriority := by
  constructor
  · intro hstreett oddPriority hoddMem hseen
    exact hstreett oddPriority
      ((A.mem_oddPriorityFinset oddPriority).mp hoddMem).2 hseen
  · intro hfinite oddPriority hodd hseen
    have hoddMem : oddPriority ∈ A.oddPriorityFinset := by
      exact (A.mem_oddPriorityFinset oddPriority).mpr
        ⟨(A.mem_priorityFinset oddPriority).mp
          (run.prioritySeenInfinitelyOften_mem_priorityFinset hseen),
          hodd⟩
    exact hfinite oddPriority hoddMem hseen

/--
Paper-facing finite-Streett form of branch acceptance: it is enough to check
the finitely many odd priorities that occur in the APA.
-/
theorem branchAccepts_iff_oddPriorityFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word)
    (branch : Nat -> Nat) :
    run.BranchAccepts branch ↔
      ∀ oddPriority : Nat,
        oddPriority ∈ A.oddPriorityFinset ->
          run.PrioritySeenInfinitelyOften branch oddPriority ->
            ∃ grantPriority : Nat,
              grantPriority < oddPriority ∧
                run.PrioritySeenInfinitelyOften branch grantPriority := by
  rw [run.branchAccepts_iff_streettOddPriorityChain branch,
    run.streettOddPriorityChain_iff_oddPriorityFinset branch]

/--
Run-tree acceptance in the finite-Streett presentation used by the cited
Miyano-Hayashi/Vardi-Wolper backend.
-/
theorem accepting_iff_all_branches_oddPriorityFinset
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {word : OmegaWord Alphabet}
    (run : A.Run word) :
    run.Accepting ↔
      ∀ branch : Nat -> Nat,
        run.ActiveBranch branch ->
          ∀ oddPriority : Nat,
            oddPriority ∈ A.oddPriorityFinset ->
              run.PrioritySeenInfinitelyOften branch oddPriority ->
                ∃ grantPriority : Nat,
                  grantPriority < oddPriority ∧
                    run.PrioritySeenInfinitelyOften branch grantPriority := by
  constructor
  · intro hacc branch hactive
    exact (run.branchAccepts_iff_oddPriorityFinset branch).mp
      (hacc branch hactive)
  · intro hfinite branch hactive
    exact (run.branchAccepts_iff_oddPriorityFinset branch).mpr
      (hfinite branch hactive)

end Run

/--
Odd request states are the finite request indices used by the checked
breakpoint skeleton below.  Indexing by states, rather than raw priorities,
keeps the construction in the APA state universe while still representing the
finite Streett chain: a recurring odd priority has a recurring state that
carries that priority.
-/
abbrev OddRequestState
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :=
  { state : A.State // ¬ DetParityAutomaton.NatEven (A.priority state) }

noncomputable instance oddRequestStateFintype
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype A.OddRequestState := by
  classical
  infer_instance

/--
A pending breakpoint obligation.  The first component records the odd request
state whose priority must be answered; the second component records the current
frontier state carrying that still-unanswered request along the actual timed
support transition.
-/
abbrev MHObligation
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :=
  A.OddRequestState × A.State

/--
Finite state for a naive always-propagating breakpoint attempt.

`frontier` is the current finite set of APA states in the guessed alternating
run.  `pending` is the finite set of timed request obligations that have been
created on concrete support edges and have not yet reached a lower-priority
grant state.  The counterexample below shows that this is not yet the correct
Miyano-Hayashi state discipline.
-/
structure MHState
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) where
  frontier : Finset A.State
  pending : Finset A.MHObligation

namespace MHState

noncomputable instance fintype
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Fintype A.MHState := by
  classical
  exact
    Fintype.ofInjective
      (fun state : A.MHState => (state.frontier, state.pending))
      (by
        intro left right h
        cases left
        cases right
        cases h
        rfl)

end MHState

/-- The initial breakpoint state starts from the singleton APA initial frontier. -/
noncomputable def mhInitialState
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    A.MHState := by
  classical
  exact
    { frontier := {A.initial}
      pending := ∅ }

/-- A target state grants an obligation when it reaches a lower priority. -/
def mhObligationGrant
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (request : A.OddRequestState)
    (target : A.State) :
    Prop :=
  A.priority target < A.priority request.1

/--
One timed breakpoint transition.

The transition first chooses one concrete APA macro-step support from the
current frontier.  Pending obligations at the next time are exactly those
propagated across an actual chosen support edge, plus new obligations generated
by odd-priority source states on such an edge, with obligations dropped
precisely when the target grants them by visiting a lower priority.
-/
def mhStep
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (current : A.MHState)
    (letter : Alphabet)
    (next : A.MHState) :
    Prop :=
  ∃ supportChoice : A.MacroStepSupport current.frontier letter,
    supportChoice.support = next.frontier ∧
      ∀ obligation : A.MHObligation,
        obligation ∈ next.pending ↔
          ∃ source : A.State,
            ∃ hsource : source ∈ current.frontier,
              obligation.2 ∈
                  (supportChoice.choice ⟨source, hsource⟩).support ∧
                (((obligation.1, source) ∈ current.pending) ∨
                    obligation.1.1 = source) ∧
                  ¬ A.mhObligationGrant obligation.1 obligation.2

/-- A breakpoint state is Büchi-accepting when all timed obligations have cleared. -/
def mhAccepting
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    (state : A.MHState) :
    Prop :=
  state.pending = ∅

/--
The nondeterministic Büchi automaton induced by the naive breakpoint state
space.  See `MHNaiveCounterexample.oneShot_mhBuchi_not_equivalent`: this
automaton is a checked failed candidate, not the final APA alternation-removal
construction.
-/
noncomputable def mhBuchi
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    NondetBuchiAutomaton.{u, v} Alphabet where
  State := A.MHState
  stateFinite := MHState.fintype A
  initial := A.mhInitialState
  step := A.mhStep
  accepting := mhAccepting

theorem mhStep_frontier_transition
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {current next : A.MHState}
    {letter : Alphabet}
    (hstep : A.mhStep current letter next) :
    A.MacroTransition current.frontier letter next.frontier := by
  rcases hstep with ⟨supportChoice, hfrontier, _hpending⟩
  exact ⟨supportChoice, hfrontier⟩

theorem mhStep_pending_iff
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {current next : A.MHState}
    {letter : Alphabet}
    (hstep : A.mhStep current letter next) :
    ∃ supportChoice : A.MacroStepSupport current.frontier letter,
      supportChoice.support = next.frontier ∧
        ∀ obligation : A.MHObligation,
          obligation ∈ next.pending ↔
            ∃ source : A.State,
              ∃ hsource : source ∈ current.frontier,
                obligation.2 ∈
                    (supportChoice.choice ⟨source, hsource⟩).support ∧
                  (((obligation.1, source) ∈ current.pending) ∨
                      obligation.1.1 = source) ∧
                    ¬ A.mhObligationGrant obligation.1 obligation.2 := by
  exact hstep

/--
Every pending obligation after an MH step is carried by a target state in the
next frontier.  This is the basic timedness invariant missing from the rejected
raw recurring-edge-graph route.
-/
theorem mhStep_pending_target_mem_frontier
    {Alphabet : Type u}
    {A : AlternatingParityAutomaton.{u, v} Alphabet}
    {current next : A.MHState}
    {letter : Alphabet}
    (hstep : A.mhStep current letter next)
    {obligation : A.MHObligation}
    (hobligation : obligation ∈ next.pending) :
    obligation.2 ∈ next.frontier := by
  rcases hstep with ⟨supportChoice, hfrontier, hpending⟩
  rcases (hpending obligation).mp hobligation with
    ⟨source, hsource, htarget, _hcreated, _hnotGrant⟩
  rw [← hfrontier]
  exact
    (MacroStepSupport.mem_support
      (supportChoice := supportChoice)
      (nextState := obligation.2)).mpr
      ⟨⟨source, hsource⟩, htarget⟩

/--
Project a concrete run of the breakpoint Büchi automaton to the underlying APA
macro-run of frontiers.
-/
noncomputable def mhRunFrontierMacroRun
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (run : (A.mhBuchi).RunFrom (A.mhBuchi).initial word) :
    A.MacroRun ({A.initial} : Finset A.State) word where
  states n := (run.path n).frontier
  initial_states := by
    have hinitial := congrArg
      (fun state : A.MHState => state.frontier)
      run.initial_state
    simpa [mhBuchi, mhInitialState] using hinitial
  step_transition := by
    intro n
    have hstep : A.mhStep (run.path n) (word n) (run.path (n + 1)) := by
      simpa [mhBuchi] using run.step_valid n
    exact A.mhStep_frontier_transition hstep

/--
In every reachable breakpoint run state, a pending obligation is attached to a
state in the current frontier.
-/
theorem mhRun_pending_target_mem_frontier
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    {word : OmegaWord Alphabet}
    (run : (A.mhBuchi).RunFrom (A.mhBuchi).initial word)
    (n : Nat)
    {obligation : A.MHObligation}
    (hobligation : obligation ∈ (run.path n).pending) :
    obligation.2 ∈ (run.path n).frontier := by
  cases n with
  | zero =>
      have hpath0 := congrArg
        (fun state : A.MHState => state.pending)
        run.initial_state
      have hpendingEmpty :
          (run.path 0).pending = ∅ := by
        simpa [mhBuchi, mhInitialState] using hpath0
      rw [hpendingEmpty] at hobligation
      simp at hobligation
  | succ n =>
      have hstep :
          A.mhStep (run.path n) (word n) (run.path (n + 1)) := by
        simpa [mhBuchi] using run.step_valid n
      exact A.mhStep_pending_target_mem_frontier hstep hobligation

@[simp]
theorem mhBuchi_initial
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    (A.mhBuchi).initial = A.mhInitialState :=
  rfl

@[simp]
theorem mhBuchi_step
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (current : A.mhBuchi.State)
    (letter : Alphabet)
    (next : A.mhBuchi.State) :
    (A.mhBuchi).step current letter next = A.mhStep current letter next :=
  rfl

@[simp]
theorem mhBuchi_accepting
    {Alphabet : Type u}
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (state : A.mhBuchi.State) :
    (A.mhBuchi).accepting state = mhAccepting state :=
  rfl

namespace MHNaiveCounterexample

/--
A two-state APA exposing why the current always-propagating breakpoint skeleton
is not yet the Miyano-Hayashi construction.

The initial odd priority is visited only once.  The unique branch then remains
forever in an even state of higher priority.  This is parity-accepting because
the only recurring priority is `2`, but an obligation construction that requires
every finite odd request to receive a lower-priority grant will reject it.
-/
inductive OneShotState where
  | initialOdd
  | stableEven
deriving DecidableEq, Fintype

open OneShotState

def oneShotWord : OmegaWord Unit :=
  fun _ => ()

def oneShotPriority : OneShotState -> Nat
  | initialOdd => 1
  | stableEven => 2

def oneShotStep : OneShotState -> Unit -> PosBool OneShotState
  | initialOdd, _ => PosBool.atom stableEven
  | stableEven, _ => PosBool.atom stableEven

def oneShotAPA : AlternatingParityAutomaton Unit where
  State := OneShotState
  stateFinite := inferInstance
  initial := initialOdd
  step := oneShotStep
  priority := oneShotPriority

def oneShotStateAt : Node -> OneShotState
  | [] => initialOdd
  | _ :: _ => stableEven

@[simp]
theorem oneShotStateAt_nil :
    oneShotStateAt [] = initialOdd :=
  rfl

@[simp]
theorem oneShotStateAt_cons (child : Nat) (node : Node) :
    oneShotStateAt (child :: node) = stableEven :=
  rfl

def oneShotRun : oneShotAPA.Run oneShotWord where
  active := fun _ => True
  stateAt := oneShotStateAt
  root_active := True.intro
  root_state := rfl
  step_satisfied := by
    intro node _hactive
    change
      PosBool.Eval
        (fun nextState =>
          ∃ child : Nat, True ∧ oneShotStateAt (child :: node) = nextState)
        (oneShotStep (oneShotStateAt node) ())
    cases node with
    | nil =>
        exact ⟨0, True.intro, rfl⟩
    | cons child node =>
        exact ⟨0, True.intro, rfl⟩

theorem oneShotAPA_accepts :
    oneShotAPA.Accepts oneShotWord := by
  refine ⟨oneShotRun, ?_⟩
  intro branch _hactive
  refine
    oneShotRun.branchAccepts_of_eventually_priority branch 2 ?_ ?_
  · exact ⟨1, by norm_num⟩
  · refine ⟨1, ?_⟩
    intro n hn
    cases n with
    | zero => omega
    | succ n =>
        simp [oneShotRun, oneShotStateAt, oneShotAPA, oneShotPriority]

def oneShotOddRequest :
    oneShotAPA.OddRequestState :=
  ⟨initialOdd, by
    change ¬ DetParityAutomaton.NatEven 1
    rintro ⟨m, hm⟩
    cases m with
    | zero =>
        norm_num at hm
    | succ m =>
        omega⟩

@[simp]
theorem oneShotPriority_initialOdd :
    oneShotAPA.priority initialOdd = 1 :=
  rfl

@[simp]
theorem oneShotPriority_stableEven :
    oneShotAPA.priority stableEven = 2 :=
  rfl

theorem oneShot_not_grant :
    ¬ oneShotAPA.mhObligationGrant oneShotOddRequest stableEven := by
  intro h
  change 2 < 1 at h
  omega

theorem oneShot_stepSupport_stableEven_mem
    {state : OneShotState}
    {support : oneShotAPA.StepSupport state ()} :
    stableEven ∈ support.support := by
  cases state <;> simpa [oneShotAPA, oneShotStep, PosBool.Eval]
    using support.support_satisfies

theorem oneShot_mhStep_obligation_next
    {current next : oneShotAPA.MHState}
    (hfrontier : stableEven ∈ current.frontier)
    (hpending :
      (oneShotOddRequest, stableEven) ∈ current.pending)
    (hstep : oneShotAPA.mhStep current () next) :
    (oneShotOddRequest, stableEven) ∈ next.pending := by
  rcases hstep with ⟨supportChoice, _hfrontierNext, hpendingNext⟩
  exact (hpendingNext (oneShotOddRequest, stableEven)).mpr
    ⟨stableEven, hfrontier,
      oneShot_stepSupport_stableEven_mem,
      Or.inl hpending,
      oneShot_not_grant⟩

theorem oneShot_mhStep_initial_obligation
    {next : oneShotAPA.MHState}
    (hstep :
      oneShotAPA.mhStep oneShotAPA.mhInitialState () next) :
    (oneShotOddRequest, stableEven) ∈ next.pending := by
  rcases hstep with ⟨supportChoice, _hfrontierNext, hpendingNext⟩
  exact (hpendingNext (oneShotOddRequest, stableEven)).mpr
    ⟨initialOdd, by
      change initialOdd ∈ ({initialOdd} : Finset OneShotState)
      simp,
      oneShot_stepSupport_stableEven_mem,
      Or.inr rfl,
      oneShot_not_grant⟩

theorem oneShot_mhRun_obligation_after_zero
    (run :
      (oneShotAPA.mhBuchi).RunFrom (oneShotAPA.mhBuchi).initial
        oneShotWord) :
    ∀ n : Nat,
      1 ≤ n ->
        (oneShotOddRequest, stableEven) ∈ (run.path n).pending := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
      cases n with
      | zero =>
          have hpath0 : run.path 0 = oneShotAPA.mhInitialState := by
            simpa [mhBuchi] using run.initial_state
          have hstep :
              oneShotAPA.mhStep oneShotAPA.mhInitialState ()
                (run.path 1) := by
            simpa [mhBuchi, oneShotWord, hpath0] using run.step_valid 0
          exact oneShot_mhStep_initial_obligation hstep
      | succ n =>
          have hobligation :
              (oneShotOddRequest, stableEven) ∈
                (run.path (n + 1)).pending :=
            ih (by omega)
          have hfrontier :
              stableEven ∈ (run.path (n + 1)).frontier :=
            oneShotAPA.mhRun_pending_target_mem_frontier run (n + 1)
              hobligation
          have hstep :
              oneShotAPA.mhStep (run.path (n + 1)) ()
                (run.path (n + 1 + 1)) := by
            simpa [mhBuchi, oneShotWord, Nat.add_comm, Nat.add_left_comm,
              Nat.add_assoc] using run.step_valid (n + 1)
          simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
            using
              oneShot_mhStep_obligation_next hfrontier hobligation hstep

theorem oneShot_mhBuchi_not_accepts :
    ¬ (oneShotAPA.mhBuchi).Accepts oneShotWord := by
  intro haccepts
  rcases haccepts with ⟨run, hrunAccepts⟩
  rcases hrunAccepts 1 with ⟨k, hk, hkaccepting⟩
  have hobligation :
      (oneShotOddRequest, stableEven) ∈ (run.path k).pending :=
    oneShot_mhRun_obligation_after_zero run k hk
  have hpendingEmpty : (run.path k).pending = ∅ := hkaccepting
  rw [hpendingEmpty] at hobligation
  exact Finset.notMem_empty _ hobligation

/--
Therefore the checked `mhBuchi` skeleton above cannot be the final
alternation-removal construction: its equivalence statement is false.
-/
theorem oneShot_mhBuchi_not_equivalent :
    ¬ (∀ word : OmegaWord Unit,
        (oneShotAPA.mhBuchi).Accepts word ↔ oneShotAPA.Accepts word) := by
  intro hcorrect
  exact oneShot_mhBuchi_not_accepts
    ((hcorrect oneShotWord).mpr oneShotAPA_accepts)

end MHNaiveCounterexample

end AlternatingParityAutomaton

namespace APARunToNondetBuchiCompiler

/--
Correctness of a supplied APA-to-Buchi compiler for a fixed automaton.
-/
theorem compiler_correct
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (((compiler.compile A).buchi.Accepts word) ↔
      A.Accepts word) :=
  (compiler.compile A).correct word

/--
Existential Buchi form supplied by an explicit APA-to-Buchi compiler.
-/
theorem exists_buchi_of_compiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ B : NondetBuchiAutomaton.{u, w} Alphabet,
      ∀ word : OmegaWord Alphabet, B.Accepts word ↔ A.Accepts word := by
  refine ⟨(compiler.compile A).buchi, ?_⟩
  intro word
  exact compiler_correct compiler A word

end APARunToNondetBuchiCompiler

namespace APARunToDPACompiler

/--
An explicit APA-to-Buchi compiler followed by the checked Piterman
nondeterministic-Buchi-to-DPA compiler.
-/
noncomputable def ofNondetBuchiCompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet) :
    APARunToDPACompiler.{u, v, w} Alphabet :=
  compiler.toDPACompiler
    (NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler Alphabet)

/-- Correctness of the explicit APA-to-DPA backend for a fixed automaton. -/
theorem ofNondetBuchiCompiler_correct
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    (((ofNondetBuchiCompiler compiler).compile A).dpa.Accepts word ↔
      A.Accepts word) :=
  ((ofNondetBuchiCompiler compiler).compile A).correct word

/--
Existential DPA form supplied by an explicit APA-to-Buchi compiler.
-/
theorem exists_dpa_of_nondetBuchiCompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, w} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word := by
  refine ⟨((ofNondetBuchiCompiler compiler).compile A).dpa, ?_⟩
  intro word
  exact ofNondetBuchiCompiler_correct compiler A word

/--
Paper-facing factorization: a supplied APA-to-Büchi backend followed by the
checked Piterman Büchi-to-DPA compiler yields the deterministic parity backend.
-/
theorem exists_buchi_piterman_dpa_of_nondetBuchiCompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ B : NondetBuchiAutomaton.{u, w} Alphabet,
      ∃ D : DetParityAutomaton.{u, w} Alphabet,
        (∀ word : OmegaWord Alphabet, B.Accepts word ↔ A.Accepts word) ∧
          (∀ word : OmegaWord Alphabet, D.Accepts word ↔ B.Accepts word) ∧
            (∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word) := by
  let bcomp := compiler.compile A
  let det :=
    (NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
      Alphabet).compile bcomp.buchi
  refine ⟨bcomp.buchi, det.dpa, ?_, ?_, ?_⟩
  · intro word
    exact bcomp.correct word
  · intro word
    exact det.correct word
  · intro word
    trans bcomp.buchi.Accepts word
    · exact det.correct word
    · exact bcomp.correct word

end APARunToDPACompiler

/--
Lean endpoint corresponding to the old Buchi-factorized backend, stated without
an axiom: once an APA-to-Buchi compiler is supplied, Piterman gives a DPA.
-/
theorem standardAPABackend_of_nondetBuchiCompiler
    {Alphabet : Type u}
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, w} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  APARunToDPACompiler.exists_dpa_of_nondetBuchiCompiler compiler A

/--
Finite-alphabet specialization of
`standardAPABackend_of_nondetBuchiCompiler`.  The compiler interface itself is
slightly more general and does not need the alphabet finiteness assumption.
-/
theorem standardAPABackend_finiteAlphabet_of_nondetBuchiCompiler
    {Alphabet : Type u}
    [Fintype Alphabet]
    (compiler : APARunToNondetBuchiCompiler.{u, v, w} Alphabet)
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    ∃ D : DetParityAutomaton.{u, w} Alphabet,
      ∀ word : OmegaWord Alphabet, D.Accepts word ↔ A.Accepts word :=
  standardAPABackend_of_nondetBuchiCompiler compiler A

end DistributedSynthesis
