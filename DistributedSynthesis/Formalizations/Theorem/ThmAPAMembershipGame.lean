/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefAlternatingAutomata
import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity
import DistributedSynthesis.Formalizations.Theorem.ThmParityTreeEmptinessGame

/-!
# The APA membership game and memoryless run DAGs

This file proves the memoryless-run theorem for alternating parity automata:
a word is accepted by an APA if and only if it admits a *positional run DAG*
— a per-level family of macro support choices, depending only on the state
and the level, all of whose threads satisfy the min-even parity condition.

This is the mathematically load-bearing step of alternation removal.  The
run-tree semantics allows two tree nodes carrying the same state to behave
differently, so per-level merging of a run tree is unsound (the recurring
edge graph mistake).  The correct route is game-theoretic: the membership
game of the automaton on the word is a countable parity game (positions are
level-indexed states and support choices, plus two sinks), and the checked
Zielonka theorem `CountableParityGame.positionalDeterminacy` converts the
history strategy induced by an accepting run tree into a positional
strategy, whose reachable moves form the positional run DAG.

Contents:

* `PositionalRunDAG`, its thread semantics, and `toRun`: a positional run
  DAG induces an accepting run tree, with child indices given by encoding
  the child state (so the state at a node depends only on the last child
  index and the tree is well defined).
* `membershipGame`: the countable parity acceptance game.
* `mem_winningRegion_of_accepts`: an accepting run tree yields a winning
  history strategy tracking the tree node decoded from the play prefix.
* `positionalRunDAG_of_positionalWinning`: a positional winning strategy
  yields a positional run DAG on its reachable states.
* `nonempty_positionalRunDAG_iff_accepts`: the memoryless-run theorem.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton

variable {Alphabet : Type u}
variable (A : AlternatingParityAutomaton.{u, v} Alphabet)
variable (word : OmegaWord Alphabet)

/--
A positional run DAG: per-level macro support choices whose threads all
satisfy the min-even parity condition.  This is the memoryless normal form
of an accepting run.
-/
structure PositionalRunDAG where
  frontier : Nat -> Finset A.State
  choice : ∀ n : Nat, A.MacroStepSupport (frontier n) (word n)
  initial_mem : frontier 0 = {A.initial}
  frontier_succ : ∀ n : Nat, frontier (n + 1) = (choice n).support
  threads_accept :
    ∀ s : Nat -> A.State,
      s 0 = A.initial ->
      (∀ n : Nat, ∃ h : s n ∈ frontier n,
        s (n + 1) ∈ ((choice n).choice ⟨s n, h⟩).support) ->
      NatSeqMinEvenParity (fun n => A.priority (s n))

namespace PositionalRunDAG

variable {A word}
variable (D : A.PositionalRunDAG word)

/-- A thread of the DAG: a state evolution through the support choices. -/
def IsThread (s : Nat -> A.State) : Prop :=
  s 0 = A.initial ∧
    ∀ n : Nat, ∃ h : s n ∈ D.frontier n,
      s (n + 1) ∈ ((D.choice n).choice ⟨s n, h⟩).support

/-- Restated acceptance of all threads. -/
theorem isThread_accepts
    {s : Nat -> A.State} (hthread : D.IsThread s) :
    NatSeqMinEvenParity (fun n => A.priority (s n)) :=
  D.threads_accept s hthread.1 hthread.2

section ToRun

/-- Encoding of states as child indices. -/
noncomputable def encode (state : A.State) : Nat :=
  (Fintype.equivFin A.State state).val

/-- Decoding of child indices, defaulting to the initial state. -/
noncomputable def decode (child : Nat) : A.State := by
  classical
  exact
    if h : child < Fintype.card A.State then
      (Fintype.equivFin A.State).symm ⟨child, h⟩
    else A.initial

@[simp]
theorem decode_encode (state : A.State) :
    decode (A := A) (encode (A := A) state) = state := by
  have hlt : encode (A := A) state < Fintype.card A.State :=
    (Fintype.equivFin A.State state).isLt
  simp [decode, encode]

/-- The state carried by a tree node: decoded from the last child index. -/
noncomputable def dagStateAt : Node -> A.State
  | [] => A.initial
  | child :: _ => decode (A := A) child

/-- Active nodes of the induced run tree. -/
def dagActive : Node -> Prop
  | [] => True
  | child :: node =>
      dagActive node ∧
        ∃ h : dagStateAt (A := A) node ∈ D.frontier node.length,
          dagStateAt (A := A) (child :: node) ∈
            ((D.choice node.length).choice
              ⟨dagStateAt (A := A) node, h⟩).support ∧
            child < Fintype.card A.State

/-- Active node states lie in the frontier of their level. -/
theorem dagActive_state_mem_frontier :
    ∀ node : Node, D.dagActive node ->
      dagStateAt (A := A) node ∈ D.frontier node.length := by
  intro node
  induction node with
  | nil =>
      intro _
      show A.initial ∈ D.frontier 0
      rw [D.initial_mem]
      exact Finset.mem_singleton_self A.initial
  | cons child node _ih =>
      rintro ⟨hnode, hmem, hchild, _⟩
      show dagStateAt (A := A) (child :: node) ∈ D.frontier (node.length + 1)
      rw [D.frontier_succ node.length]
      exact
        (MacroStepSupport.mem_support).mpr
          ⟨⟨dagStateAt (A := A) node, hmem⟩, hchild⟩

/-- The run tree induced by a positional run DAG. -/
noncomputable def toRun : A.Run word where
  active := D.dagActive
  stateAt := dagStateAt (A := A)
  root_active := trivial
  root_state := rfl
  step_satisfied := by
    intro node hactive
    have hmem := D.dagActive_state_mem_frontier node hactive
    have heval :=
      ((D.choice node.length).choice
        ⟨dagStateAt (A := A) node, hmem⟩).support_satisfies
    refine PosBool.eval_mono ?_ _ heval
    intro nextState hnext
    refine ⟨encode (A := A) nextState, ⟨hactive, hmem, ?_, ?_⟩, ?_⟩
    · show dagStateAt (A := A) (encode (A := A) nextState :: node) ∈ _
      show decode (A := A) (encode (A := A) nextState) ∈ _
      rw [decode_encode]
      exact hnext
    · exact (Fintype.equivFin A.State nextState).isLt
    · show decode (A := A) (encode (A := A) nextState) = nextState
      rw [decode_encode]

/-- Branch states of the induced run are DAG threads. -/
theorem toRun_branch_isThread
    {branch : Nat -> Nat}
    (hbranch : D.toRun.ActiveBranch branch) :
    D.IsThread (fun n => D.toRun.stateAt (branchPrefix branch n)) := by
  have hlen : ∀ n : Nat, (branchPrefix branch n).length = n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [branchPrefix, ih]
  refine ⟨rfl, ?_⟩
  intro n
  have hactive : D.dagActive (branchPrefix branch (n + 1)) := hbranch (n + 1)
  obtain ⟨_, hmem, hchild, _⟩ := hactive
  revert hmem hchild
  rw [hlen n]
  intro hmem hchild
  exact ⟨hmem, hchild⟩

/-- The induced run tree is accepting. -/
theorem toRun_accepting : D.toRun.Accepting := by
  intro branch hbranch
  have hthread := D.toRun_branch_isThread hbranch
  have haccept := D.isThread_accepts hthread
  rcases haccept with ⟨p, hpEven, hpSeen, hpMin⟩
  exact ⟨p, hpEven, hpSeen, hpMin⟩

/-- A positional run DAG certifies acceptance. -/
theorem accepts (D' : A.PositionalRunDAG word) : A.Accepts word :=
  ⟨D'.toRun, D'.toRun_accepting⟩

end ToRun

end PositionalRunDAG

section MembershipGame

/--
Positions of the membership game: level-indexed automaton states (Even to
move), level-indexed support choices (Odd to move), and two absorbing
sinks — `true` wins for Even (empty support, no obligations), `false`
loses for Even (no satisfiable support).
-/
abbrev MemPosition :=
  ((Nat × A.State) ⊕ (Nat × A.State × Finset A.State)) ⊕ Bool

variable {A word} in
/-- The state-tier position. -/
@[reducible] def statePos (n : Nat) (s : A.State) : MemPosition A :=
  Sum.inl (Sum.inl (n, s))

variable {A word} in
/-- The support-tier position. -/
@[reducible] def supportPos (n : Nat) (s : A.State) (S : Finset A.State) :
    MemPosition A :=
  Sum.inl (Sum.inr (n, s, S))

/-- Owners: Odd moves at support positions, Even everywhere else. -/
def memOwner : MemPosition A -> ParityPlayer
  | Sum.inl (Sum.inr _) => ParityPlayer.odd
  | _ => ParityPlayer.even

/-- Priorities: both tiers carry the source-state priority; sinks decide. -/
def memPriority : MemPosition A -> Nat
  | Sum.inl (Sum.inl (_, s)) => A.priority s
  | Sum.inl (Sum.inr (_, s, _)) => A.priority s
  | Sum.inr true => 0
  | Sum.inr false => 1

/-- Edges of the membership game. -/
def memStep (A : AlternatingParityAutomaton.{u, v} Alphabet)
    (word : OmegaWord Alphabet) :
    MemPosition A -> MemPosition A -> Prop
  | Sum.inr b, target => target = Sum.inr b
  | Sum.inl (Sum.inl (n, s)), target =>
      (∃ S : Finset A.State,
        PosBool.Eval (· ∈ S) (A.step s (word n)) ∧
          target = supportPos n s S) ∨
        ((¬ ∃ S : Finset A.State,
            PosBool.Eval (· ∈ S) (A.step s (word n))) ∧
          target = Sum.inr false)
  | Sum.inl (Sum.inr (n, _, S)), target =>
      (∃ s' ∈ S, target = statePos (n + 1) s') ∨
        (S = ∅ ∧ target = Sum.inr true)

theorem memStep_total :
    ∀ position : MemPosition A,
      ∃ next : MemPosition A, memStep A word position next := by
  classical
  intro position
  match position with
  | Sum.inr b => exact ⟨Sum.inr b, rfl⟩
  | Sum.inl (Sum.inl (n, s)) =>
      by_cases h : ∃ S : Finset A.State,
        PosBool.Eval (· ∈ S) (A.step s (word n))
      · rcases h with ⟨S, hS⟩
        exact ⟨supportPos n s S, Or.inl ⟨S, hS, rfl⟩⟩
      · exact ⟨Sum.inr false, Or.inr ⟨h, rfl⟩⟩
  | Sum.inl (Sum.inr (n, s, S)) =>
      rcases Finset.eq_empty_or_nonempty S with hS | ⟨s', hs'⟩
      · exact ⟨Sum.inr true, Or.inr ⟨hS, rfl⟩⟩
      · exact ⟨statePos (n + 1) s', Or.inl ⟨s', hs', rfl⟩⟩

/-- The membership game of an APA on a word. -/
@[reducible] noncomputable def membershipGame : CountableParityGame.{v} where
  Position := MemPosition A
  positionCountable := by
    haveI : Countable A.State := Finite.to_countable
    haveI : Countable (Finset A.State) := Finite.to_countable
    exact inferInstance
  owner := memOwner A
  step := memStep A word
  step_total := memStep_total A word
  priority := memPriority A
  priority_finite := by
    classical
    refine Set.Finite.subset
      ((insert 0 (insert 1
        (Finset.image A.priority Finset.univ))) : Finset Nat).finite_toSet ?_
    rintro p ⟨position, rfl⟩
    match position with
    | Sum.inl (Sum.inl (n, s)) =>
        simp [memPriority]
    | Sum.inl (Sum.inr (n, s, S)) =>
        simp [memPriority]
    | Sum.inr true => simp [memPriority]
    | Sum.inr false => simp [memPriority]

/-- Game parity acceptance is min-even parity of the position priorities. -/
theorem membershipGame_minPriorityEven_iff
    (path : Nat -> MemPosition A) :
    (membershipGame A word).MinPriorityEven path ↔
      NatSeqMinEvenParity (fun k => memPriority A (path k)) :=
  Iff.rfl

end MembershipGame

section TreeStrategy

variable {A word}
variable (run : A.Run word)

/-- The child valuation of a tree node. -/
def nodeValuation (node : Node) (s' : A.State) : Prop :=
  ∃ child : Nat,
    run.active (child :: node) ∧ run.stateAt (child :: node) = s'

/-- A finite support of the transition at an active node, from the run tree. -/
noncomputable def treeSupport (node : Node) : Finset A.State := by
  classical
  exact
    if h : run.active node then
      (Classical.choose
        ((PosBool.eval_iff_exists_support
          (nodeValuation run node)
          (A.step (run.stateAt node) (word node.length))).mp
          (run.step_satisfied node h))).toFinset
    else ∅

theorem treeSupport_spec {node : Node} (h : run.active node) :
    PosBool.Eval (· ∈ treeSupport run node)
        (A.step (run.stateAt node) (word node.length)) ∧
      ∀ s' ∈ treeSupport run node, nodeValuation run node s' := by
  classical
  have hspec :=
    Classical.choose_spec
      ((PosBool.eval_iff_exists_support
        (nodeValuation run node)
        (A.step (run.stateAt node) (word node.length))).mp
        (run.step_satisfied node h))
  constructor
  · rw [treeSupport, dif_pos h]
    refine PosBool.eval_mono ?_ _ hspec.2
    intro s' hs'
    exact List.mem_toFinset.mpr hs'
  · intro s' hs'
    rw [treeSupport, dif_pos h] at hs'
    exact hspec.1 s' (List.mem_toFinset.mp hs')

/-- The child selected for a next state, when the valuation holds. -/
noncomputable def nodeStep (node : Node) (s' : A.State) : Node := by
  classical
  exact
    if h : nodeValuation run node s' then
      Classical.choose h :: node
    else node

theorem nodeStep_spec {node : Node} {s' : A.State}
    (h : nodeValuation run node s') :
    run.active (nodeStep run node s') ∧
      run.stateAt (nodeStep run node s') = s' ∧
      nodeStep run node s' = Classical.choose h :: node := by
  classical
  have hspec := Classical.choose_spec h
  rw [nodeStep, dif_pos h]
  exact ⟨hspec.1, hspec.2, rfl⟩

/-- Reconstruct the tracked tree node from the reversed state trace. -/
noncomputable def nodeOfRev : List A.State -> Node
  | [] => []
  | [_] => []
  | s' :: rest => nodeStep run (nodeOfRev rest) s'

/-- The tracked tree node of a state trace. -/
noncomputable def nodeOf (trace : List A.State) : Node :=
  nodeOfRev run trace.reverse

theorem nodeOf_append (trace : List A.State) (s' : A.State)
    (hne : trace ≠ []) :
    nodeOf run (trace ++ [s']) = nodeStep run (nodeOf run trace) s' := by
  rw [nodeOf, List.reverse_append]
  match htrace : trace.reverse with
  | [] =>
      exact absurd (by simpa using htrace) hne
  | head :: tail =>
      show nodeOfRev run (s' :: head :: tail) = _
      rw [nodeOf, htrace]
      rfl

/-- Extract the state carried by a state-tier position. -/
def extractState : MemPosition A -> Option A.State
  | Sum.inl (Sum.inl (_, s)) => some s
  | _ => none

/-- The state trace of a game prefix. -/
noncomputable def traceOf {m : Nat}
    (pref : Fin (m + 1) -> MemPosition A) : List A.State :=
  (List.ofFn pref).filterMap (extractState (A := A))

/-- The move of the tree-tracking strategy at a last position and trace. -/
noncomputable def treeMove (last : MemPosition A) (trace : List A.State) :
    MemPosition A := by
  classical
  exact
    match last with
    | Sum.inl (Sum.inl (n, s)) =>
        if h : run.active (nodeOf run trace) ∧
            run.stateAt (nodeOf run trace) = s ∧
            (nodeOf run trace).length = n then
          supportPos n s (treeSupport run (nodeOf run trace))
        else if hfall : ∃ S : Finset A.State,
            PosBool.Eval (· ∈ S) (A.step s (word n)) then
          supportPos n s (Classical.choose hfall)
        else Sum.inr false
    | other => other

/-- The history strategy tracking the run-tree node. -/
noncomputable def treeStrategy :
    (membershipGame A word).Strategy ParityPlayer.even where
  move _n pref :=
    treeMove run ((membershipGame A word).prefixLast pref) (traceOf pref)

theorem treeStrategy_legal : (treeStrategy run).Legal := by
  classical
  intro n pref _hlegal howner
  show memStep A word ((membershipGame A word).prefixLast pref)
    (treeMove run ((membershipGame A word).prefixLast pref) (traceOf pref))
  match hlast : (membershipGame A word).prefixLast pref with
  | Sum.inl (Sum.inl (m, s)) =>
      show memStep A word _ (treeMove run (Sum.inl (Sum.inl (m, s))) _)
      rw [treeMove]
      by_cases h : run.active (nodeOf run (traceOf pref)) ∧
          run.stateAt (nodeOf run (traceOf pref)) = s ∧
          (nodeOf run (traceOf pref)).length = m
      · simp only [dif_pos h]
        refine Or.inl ⟨treeSupport run (nodeOf run (traceOf pref)), ?_, rfl⟩
        have heval := (treeSupport_spec run h.1).1
        rw [h.2.1, h.2.2] at heval
        exact heval
      · simp only [dif_neg h]
        by_cases hfall : ∃ S : Finset A.State,
            PosBool.Eval (· ∈ S) (A.step s (word m))
        · simp only [dif_pos hfall]
          exact Or.inl ⟨Classical.choose hfall,
            Classical.choose_spec hfall, rfl⟩
        · simp only [dif_neg hfall]
          exact Or.inr ⟨hfall, rfl⟩
  | Sum.inl (Sum.inr triple) =>
      rw [hlast] at howner
      exact absurd howner (by simp [memOwner])
  | Sum.inr b =>
      show memStep A word (Sum.inr b) (Sum.inr b)
      rfl

/-- Total state extractor with a default at non-state positions. -/
def stateAtIndex : MemPosition A -> A.State
  | Sum.inl (Sum.inl (_, s)) => s
  | _ => A.initial

/-- One-step trace evolution along a path. -/
theorem traceOf_succ (path : Nat -> MemPosition A) (k : Nat) :
    traceOf (fun i : Fin (k + 1 + 1) => path i) =
      traceOf (fun i : Fin (k + 1) => path i) ++
        (extractState (A := A) (path (k + 1))).toList := by
  rw [traceOf, List.ofFn_add (n := k + 1) (m := 1)
    (f := fun i : Fin (k + 1 + 1) => path i)]
  simp only [List.filterMap_append]
  congr 1

theorem traceOf_zero (path : Nat -> MemPosition A)
    {s : A.State} {n : Nat} (hzero : path 0 = statePos n s) :
    traceOf (fun i : Fin 1 => path i) = [s] := by
  have hofn : (List.ofFn fun i : Fin 1 => path i) = [path 0] := by
    simp [List.ofFn_succ]
  rw [traceOf, hofn, hzero]
  rfl

/-- The tree-tracking strategy wins from the root for accepting runs. -/
theorem treeStrategy_winningFrom
    (haccepting : run.Accepting) :
    CountableParityGame.Strategy.WinningFrom (G := membershipGame A word)
      (treeStrategy run) (statePos 0 A.initial) := by
  classical
  constructor
  · exact treeStrategy_legal run
  · intro path hplayfrom hconsistent
    obtain ⟨hzero, hplay⟩ := hplayfrom
    by_cases hsinkTrue : ∃ k : Nat, path k = Sum.inr true
    · rcases hsinkTrue with ⟨k, hk⟩
      have habsorb : ∀ j : Nat, k ≤ j -> path j = Sum.inr true := by
        intro j hj
        induction j with
        | zero =>
            rw [← Nat.le_zero.mp hj]
            exact hk
        | succ j ih =>
            rcases Nat.lt_or_ge k (j + 1) with hlt | hge
            · have hjj : path j = Sum.inr true := ih (by omega)
              have hstep := hplay j
              rw [hjj] at hstep
              exact hstep
            · rw [← (by omega : k = j + 1)]
              exact hk
      refine ⟨0, ⟨0, rfl⟩, ?_, ?_⟩
      · intro n
        refine ⟨max n k, le_max_left n k, ?_⟩
        rw [habsorb (max n k) (le_max_right n k)]
        rfl
      · intro p _hp
        exact Nat.zero_le p
    · set t : Nat -> List A.State :=
        fun k => traceOf (fun i : Fin (k + 1) => path i) with ht
      set q : Nat -> A.State := fun n => stateAtIndex (A := A) (path (2 * n)) with hq
      set ν : Nat -> Node := fun n => nodeOf run (t (2 * n)) with hν
      have ht0 : t 0 = [A.initial] := traceOf_zero path hzero
      have htsucc : ∀ k : Nat,
          t (k + 1) = t k ++ (extractState (A := A) (path (k + 1))).toList := by
        intro k
        exact traceOf_succ path k
      have htne : ∀ k : Nat, t k ≠ [] := by
        intro k
        induction k with
        | zero => rw [ht0]; simp
        | succ k ih =>
            rw [htsucc k]
            intro hcontra
            exact ih (List.append_eq_nil_iff.mp hcontra).1
      have hq0 : q 0 = A.initial := by
        show stateAtIndex (A := A) (path 0) = A.initial
        rw [hzero]
        rfl
      have hν0 : ν 0 = [] := by
        show nodeOf run (t 0) = []
        rw [ht0]
        rfl
      have hSucc : ∀ n : Nat,
          (path (2 * n) = statePos n (q n) ∧
            run.active (ν n) ∧
              run.stateAt (ν n) = q n ∧ (ν n).length = n) ->
          ((path (2 * (n + 1)) = statePos (n + 1) (q (n + 1)) ∧
            run.active (ν (n + 1)) ∧
              run.stateAt (ν (n + 1)) = q (n + 1) ∧
                (ν (n + 1)).length = n + 1) ∧
            path (2 * n + 1) = supportPos n (q n) (treeSupport run (ν n)) ∧
              ∃ hval : nodeValuation run (ν n) (q (n + 1)),
                ν (n + 1) = Classical.choose hval :: ν n) := by
        intro n hInvN
        obtain ⟨hpos, hactive, hstate, hlen⟩ := hInvN
        have howner :
            (membershipGame A word).owner (path (2 * n)) =
              ParityPlayer.even := by
          rw [hpos]
          rfl
        have hmove := hconsistent (2 * n) howner
        have hmove' :
            path (2 * n + 1) =
              supportPos n (q n) (treeSupport run (ν n)) := by
          rw [hmove]
          show treeMove run
              ((membershipGame A word).prefixLast
                ((membershipGame A word).prefixOfPath path (2 * n)))
              (traceOf ((membershipGame A word).prefixOfPath path (2 * n))) = _
          rw [(membershipGame A word).prefixLast_prefixOfPath path (2 * n), hpos]
          show treeMove run (statePos n (q n)) (t (2 * n)) = _
          rw [treeMove]
          split
          · rfl
          next hneg => exact absurd ⟨hactive, hstate, hlen⟩ hneg
        have hstep := hplay (2 * n + 1)
        rw [hmove'] at hstep
        rcases hstep with ⟨s', hs'mem, hs'pos⟩ | ⟨_, hsink⟩
        · have hs'pos' : path (2 * n + 1 + 1) = statePos (n + 1) s' := hs'pos
          have htrace1 : t (2 * n + 1) = t (2 * n) := by
            rw [htsucc (2 * n), hmove']
            simp [extractState]
          have htrace2 : t (2 * n + 1 + 1) = t (2 * n) ++ [s'] := by
            rw [htsucc (2 * n + 1), htrace1, hs'pos']
            rfl
          have hval : nodeValuation run (ν n) s' :=
            (treeSupport_spec run hactive).2 s' hs'mem
          have hq1 : q (n + 1) = s' := by
            show stateAtIndex (A := A) (path (2 * (n + 1))) = s'
            rw [(by omega : 2 * (n + 1) = 2 * n + 1 + 1), hs'pos']
            rfl
          have hν1 : ν (n + 1) = nodeStep run (ν n) s' := by
            show nodeOf run (t (2 * (n + 1))) = nodeStep run (nodeOf run (t (2 * n))) s'
            rw [(by omega : 2 * (n + 1) = 2 * n + 1 + 1), htrace2]
            exact nodeOf_append run (t (2 * n)) s' (htne (2 * n))
          have hspec := nodeStep_spec run hval
          refine ⟨⟨?_, ?_, ?_, ?_⟩, hmove', ?_⟩
          · rw [(by omega : 2 * (n + 1) = 2 * n + 1 + 1), hs'pos', hq1]
          · rw [hν1]
            exact hspec.1
          · rw [hν1, hspec.2.1, hq1]
          · rw [hν1, hspec.2.2]
            show (Classical.choose hval :: ν n).length = n + 1
            simp [hlen]
          · rw [hq1]
            exact ⟨hval, by rw [hν1, hspec.2.2]⟩
        · exact absurd ⟨2 * n + 1 + 1, hsink⟩ hsinkTrue
      have hInvAll : ∀ n : Nat,
          path (2 * n) = statePos n (q n) ∧
            run.active (ν n) ∧
              run.stateAt (ν n) = q n ∧ (ν n).length = n := by
        intro n
        induction n with
        | zero =>
            refine ⟨?_, ?_, ?_, ?_⟩
            · show path (2 * 0) = statePos 0 (q 0)
              rw [hq0]
              exact hzero
            · rw [hν0]
              exact run.root_active
            · rw [hν0, hq0]
              exact run.root_state
            · rw [hν0]
              rfl
        | succ n ih =>
            exact (hSucc n ih).1
      have hcons : ∀ n : Nat, ∃ c : Nat, ν (n + 1) = c :: ν n := by
        intro n
        rcases (hSucc n (hInvAll n)).2.2 with ⟨hval, hchoose⟩
        exact ⟨Classical.choose hval, hchoose⟩
      set br : Nat -> Nat := fun n => (ν (n + 1)).headI with hbr
      have hbp : ∀ n : Nat, branchPrefix br n = ν n := by
        intro n
        induction n with
        | zero =>
            rw [hν0]
            rfl
        | succ n ih =>
            show br n :: branchPrefix br n = ν (n + 1)
            rcases hcons n with ⟨c, hc⟩
            rw [ih, hbr]
            show (ν (n + 1)).headI :: ν n = ν (n + 1)
            rw [hc]
            rfl
      have hactiveBr : run.ActiveBranch br := by
        intro n
        rw [hbp n]
        exact (hInvAll n).2.1
      have hstateBr : ∀ n : Nat,
          run.stateAt (branchPrefix br n) = q n := by
        intro n
        rw [hbp n]
        exact (hInvAll n).2.2.1
      have hbranchAccepts := haccepting br hactiveBr
      rcases hbranchAccepts with ⟨p, hpEven, hpSeen, hpMin⟩
      have hpri : ∀ k : Nat,
          (membershipGame A word).priority (path k) =
            A.priority (q (k / 2)) := by
        intro k
        rcases Nat.mod_two_eq_zero_or_one k with hk | hk
        · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j := ⟨k / 2, by omega⟩
          rw [(hInvAll j).1, (by omega : 2 * j / 2 = j)]
          rfl
        · obtain ⟨j, rfl⟩ : ∃ j : Nat, k = 2 * j + 1 := ⟨k / 2, by omega⟩
          rw [(hSucc j (hInvAll j)).2.1, (by omega : (2 * j + 1) / 2 = j)]
          rfl
      have hbranchSeq :
          NatSeqMinEvenParity (fun n => A.priority (q n)) := by
        refine ⟨p, hpEven, ?_, ?_⟩
        · intro n
          rcases hpSeen n with ⟨k, hk, hkp⟩
          refine ⟨k, hk, ?_⟩
          show A.priority (q k) = p
          rw [← hstateBr k]
          exact hkp
        · intro p' hp'
          refine hpMin p' ?_
          intro n
          rcases hp' n with ⟨k, hk, hkp⟩
          have hkp' : A.priority (q k) = p' := hkp
          rw [← hstateBr k] at hkp'
          exact ⟨k, hk, hkp'⟩
      exact (natSeqMinEvenParity_halved hpri).mpr hbranchSeq

/-- An accepting run puts the root position in the Even winning region. -/
theorem mem_winningRegion_of_accepts
    (haccepts : A.Accepts word) :
    (statePos 0 A.initial : MemPosition A) ∈
      (membershipGame A word).WinningRegion ParityPlayer.even := by
  rcases haccepts with ⟨run, haccepting⟩
  exact ⟨treeStrategy run, treeStrategy_winningFrom run haccepting⟩


end TreeStrategy

section PositionalToDAG

variable {A word}
variable (σ : (membershipGame A word).PositionalStrategy ParityPlayer.even)

/-- The support stored in a positional strategy's move at a state position. -/
noncomputable def sigmaRawSupport (n : Nat) (s : A.State) : Finset A.State :=
  match σ.move (statePos n s) with
  | Sum.inl (Sum.inr (_, _, S)) => S
  | _ => ∅

/-- The strategy plays a genuine satisfiable support at a state position. -/
def SigmaGood (n : Nat) (s : A.State) : Prop :=
  σ.move (statePos n s) = supportPos n s (sigmaRawSupport σ n s) ∧
    PosBool.Eval (· ∈ sigmaRawSupport σ n s) (A.step s (word n))

/-- Legality dichotomy at a state position. -/
theorem sigmaMove_cases (n : Nat) (s : A.State) :
    SigmaGood σ n s ∨
      ((¬ ∃ S : Finset A.State,
          PosBool.Eval (· ∈ S) (A.step s (word n))) ∧
        σ.move (statePos n s) = Sum.inr false) := by
  have hlegal : memStep A word (statePos n s) (σ.move (statePos n s)) :=
    σ.legal (statePos n s) rfl
  rcases hlegal with ⟨S, hS, htgt⟩ | ⟨hno, htgt⟩
  · left
    have hraw : sigmaRawSupport σ n s = S := by
      rw [sigmaRawSupport, htgt]
    constructor
    · rw [htgt, hraw]
    · rw [hraw]
      exact hS
  · exact Or.inr ⟨hno, htgt⟩

/-- The default continuation following the strategy at Even positions. -/
noncomputable def sigmaTail (P : MemPosition A) : Nat -> MemPosition A
  | 0 => P
  | k + 1 =>
      if (membershipGame A word).owner (sigmaTail P k) = ParityPlayer.even then
        σ.move (sigmaTail P k)
      else
        Classical.choose
          ((membershipGame A word).step_total (sigmaTail P k))

theorem sigmaTail_playFrom (P : MemPosition A) :
    (membershipGame A word).PlayFrom P (sigmaTail σ P) := by
  refine ⟨rfl, ?_⟩
  intro k
  show (membershipGame A word).step (sigmaTail σ P k) (sigmaTail σ P (k + 1))
  by_cases howner :
      (membershipGame A word).owner (sigmaTail σ P k) = ParityPlayer.even
  · show (membershipGame A word).step _ (if _ then _ else _)
    rw [if_pos howner]
    exact σ.legal (sigmaTail σ P k) howner
  · show (membershipGame A word).step _ (if _ then _ else _)
    rw [if_neg howner]
    exact Classical.choose_spec
      ((membershipGame A word).step_total (sigmaTail σ P k))

theorem sigmaTail_consistent (P : MemPosition A) :
    CountableParityGame.PositionalStrategy.Consistent
      (G := membershipGame A word) σ (sigmaTail σ P) := by
  intro k howner
  show (if _ then _ else _) = σ.move (sigmaTail σ P k)
  rw [if_pos howner]

/-- A winning position is never a stuck state position. -/
theorem sigmaGood_of_winningFrom {n : Nat} {s : A.State}
    (hwin : CountableParityGame.PositionalStrategy.WinningFrom
      (G := membershipGame A word) σ (statePos n s)) :
    SigmaGood σ n s := by
  rcases sigmaMove_cases σ n s with hgood | ⟨_, hmove⟩
  · exact hgood
  · exfalso
    have hwins :=
      hwin (sigmaTail σ (statePos n s))
        (sigmaTail_playFrom σ (statePos n s))
        (sigmaTail_consistent σ (statePos n s))
    have habs : ∀ k : Nat, 1 ≤ k ->
        sigmaTail σ (statePos n s) k = Sum.inr false := by
      intro k hk
      induction k with
      | zero => omega
      | succ k ih =>
          by_cases hk1 : 1 ≤ k
          · have hkk := ih hk1
            show (if _ then _ else _) = Sum.inr false
            rw [if_pos (by rw [hkk]; rfl :
              (membershipGame A word).owner (sigmaTail σ (statePos n s) k) =
                ParityPlayer.even), hkk]
            have hlegal : memStep A word (Sum.inr false)
                (σ.move (Sum.inr false)) :=
              σ.legal (Sum.inr false) rfl
            exact hlegal
          · have hk0 : k = 0 := by omega
            subst hk0
            have howner0 :
                (membershipGame A word).owner
                  (sigmaTail σ (statePos n s) 0) = ParityPlayer.even := rfl
            show (if _ then _ else _) = Sum.inr false
            rw [if_pos howner0]
            exact hmove
    rcases hwins with ⟨p, hpEven, hpSeen, _⟩
    rcases hpSeen 1 with ⟨k, hk1, hkp⟩
    have hp1 : p = 1 := by
      have hks := habs k hk1
      rw [show (membershipGame A word).priority
            (sigmaTail σ (statePos n s) k) =
          memPriority A (sigmaTail σ (statePos n s) k) from rfl,
        hks] at hkp
      exact hkp.symm
    rcases hpEven with ⟨m, hm⟩
    omega

/-- The shrunk support: inside the raw support and the transition atoms. -/
noncomputable def sigmaShrunk (n : Nat) (s : A.State) : Finset A.State := by
  classical
  exact
    if hgood : SigmaGood σ n s then
      (Classical.choose
        ((PosBool.eval_iff_exists_support_subset_atoms
          (· ∈ sigmaRawSupport σ n s) (A.step s (word n))).mp hgood.2)).toFinset
    else ∅

theorem sigmaShrunk_spec {n : Nat} {s : A.State} (hgood : SigmaGood σ n s) :
    (∀ x ∈ sigmaShrunk σ n s, x ∈ sigmaRawSupport σ n s) ∧
      (∀ x ∈ sigmaShrunk σ n s, x ∈ (A.step s (word n)).atoms) ∧
        PosBool.Eval (· ∈ sigmaShrunk σ n s) (A.step s (word n)) := by
  classical
  have hspec :=
    Classical.choose_spec
      ((PosBool.eval_iff_exists_support_subset_atoms
        (· ∈ sigmaRawSupport σ n s) (A.step s (word n))).mp hgood.2)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [sigmaShrunk, dif_pos hgood] at hx
    exact hspec.1 x (List.mem_toFinset.mp hx)
  · intro x hx
    rw [sigmaShrunk, dif_pos hgood] at hx
    exact hspec.2.1 x (List.mem_toFinset.mp hx)
  · rw [sigmaShrunk, dif_pos hgood]
    refine PosBool.eval_mono ?_ _ hspec.2.2
    intro x hx
    exact List.mem_toFinset.mpr hx

/-- States reached by the strategy's shrunk supports. -/
inductive SigmaReached : Nat -> A.State -> Prop where
  | zero : SigmaReached 0 A.initial
  | succ {n : Nat} {s s' : A.State} :
      SigmaReached n s -> s' ∈ sigmaShrunk σ n s -> SigmaReached (n + 1) s'

/-- Winning propagates from the root to all reached state positions. -/
theorem winningFrom_of_sigmaReached
    (hwin0 : CountableParityGame.PositionalStrategy.WinningFrom
      (G := membershipGame A word) σ (statePos 0 A.initial)) :
    ∀ {n : Nat} {s : A.State}, SigmaReached σ n s ->
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := membershipGame A word) σ (statePos n s) := by
  intro n s hreach
  induction hreach with
  | zero => exact hwin0
  | @succ n s s' hreach hmem ih =>
      have hgood := sigmaGood_of_winningFrom σ ih
      have hwin1 :
          CountableParityGame.PositionalStrategy.WinningFrom
            (G := membershipGame A word) σ
            (supportPos n s (sigmaRawSupport σ n s)) := by
        refine CountableParityGame.PositionalStrategy.winningFrom_successor
          ih ?_ (fun _ => hgood.1.symm)
        show memStep A word (statePos n s)
          (supportPos n s (sigmaRawSupport σ n s))
        exact Or.inl ⟨sigmaRawSupport σ n s, hgood.2, rfl⟩
      refine CountableParityGame.PositionalStrategy.winningFrom_successor
        hwin1 ?_ (fun howner => absurd howner (by simp [memOwner]))
      show memStep A word (supportPos n s (sigmaRawSupport σ n s))
        (statePos (n + 1) s')
      exact Or.inl ⟨s', (sigmaShrunk_spec σ hgood).1 s' hmem, rfl⟩

/-- The reached frontier at a level. -/
noncomputable def sigmaFrontier (n : Nat) : Finset A.State := by
  classical
  exact Finset.univ.filter (fun s => SigmaReached σ n s)

theorem mem_sigmaFrontier {n : Nat} {s : A.State} :
    s ∈ sigmaFrontier σ n ↔ SigmaReached σ n s := by
  classical
  rw [sigmaFrontier]
  simp

/-- The macro support choice at a level, on the reached frontier. -/
noncomputable def sigmaChoice
    (hwin0 : CountableParityGame.PositionalStrategy.WinningFrom
      (G := membershipGame A word) σ (statePos 0 A.initial))
    (n : Nat) :
    A.MacroStepSupport (sigmaFrontier σ n) (word n) where
  choice := fun state =>
    { support := sigmaShrunk σ n state.1
      support_satisfies :=
        (sigmaShrunk_spec σ
          (sigmaGood_of_winningFrom σ
            (winningFrom_of_sigmaReached σ hwin0
              ((mem_sigmaFrontier σ).mp state.2)))).2.2
      support_atoms :=
        (sigmaShrunk_spec σ
          (sigmaGood_of_winningFrom σ
            (winningFrom_of_sigmaReached σ hwin0
              ((mem_sigmaFrontier σ).mp state.2)))).2.1 }

/-- The positional run DAG extracted from a winning positional strategy. -/
noncomputable def dagOfWinning
    (hwin0 : CountableParityGame.PositionalStrategy.WinningFrom
      (G := membershipGame A word) σ (statePos 0 A.initial)) :
    A.PositionalRunDAG word where
  frontier := sigmaFrontier σ
  choice := sigmaChoice σ hwin0
  initial_mem := by
    ext s
    rw [mem_sigmaFrontier, Finset.mem_singleton]
    constructor
    · intro hreach
      cases hreach
      rfl
    · intro heq
      rw [heq]
      exact SigmaReached.zero
  frontier_succ := by
    intro n
    ext s'
    rw [mem_sigmaFrontier, MacroStepSupport.mem_support]
    constructor
    · intro hreach
      cases hreach with
      | succ hreach' hmem =>
          exact ⟨⟨_, (mem_sigmaFrontier σ).mpr hreach'⟩, hmem⟩
    · rintro ⟨⟨s, hs⟩, hmem⟩
      exact SigmaReached.succ ((mem_sigmaFrontier σ).mp hs) hmem
  threads_accept := by
    intro s hzero hstep
    have hreach : ∀ n : Nat, SigmaReached σ n (s n) := by
      intro n
      induction n with
      | zero =>
          rw [hzero]
          exact SigmaReached.zero
      | succ n ih =>
          rcases hstep n with ⟨hmemF, hsupp⟩
          exact SigmaReached.succ ((mem_sigmaFrontier σ).mp hmemF) hsupp
    have hgood : ∀ n : Nat, SigmaGood σ n (s n) := fun n =>
      sigmaGood_of_winningFrom σ
        (winningFrom_of_sigmaReached σ hwin0 (hreach n))
    set play : Nat -> MemPosition A :=
      interleavePlay
        (fun j => statePos j (s j))
        (fun j => supportPos j (s j) (sigmaRawSupport σ j (s j)))
      with hplaydef
    have hplay : (membershipGame A word).Play play := by
      refine interleavePlay_play _ _ _ ?_ ?_
      · intro j
        exact Or.inl ⟨sigmaRawSupport σ j (s j), (hgood j).2, rfl⟩
      · intro j
        refine Or.inl ⟨s (j + 1), ?_, rfl⟩
        rcases hstep j with ⟨hmemF, hsupp⟩
        exact (sigmaShrunk_spec σ (hgood j)).1 (s (j + 1)) hsupp
    have hstart : play 0 = statePos 0 A.initial := by
      rw [hplaydef, interleavePlay_zero, hzero]
    have hcons :
        CountableParityGame.PositionalStrategy.Consistent
          (G := membershipGame A word) σ play := by
      intro k howner
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hplaydef, interleavePlay_of_mod_eq_zero _ _ hk,
          interleavePlay_of_mod_eq_one _ _ (by omega : (k + 1) % 2 = 1),
          (by omega : (k + 1) / 2 = k / 2)]
        exact (hgood (k / 2)).1.symm
      · rw [hplaydef, interleavePlay_of_mod_eq_one _ _ hk] at howner
        simp [memOwner] at howner
    have hwins := hwin0 play ⟨hstart, hplay⟩ hcons
    have hpri : ∀ k : Nat,
        (membershipGame A word).priority (play k) =
          A.priority (s (k / 2)) := by
      intro k
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hplaydef, interleavePlay_of_mod_eq_zero _ _ hk]
        rfl
      · rw [hplaydef, interleavePlay_of_mod_eq_one _ _ hk]
        rfl
    exact (natSeqMinEvenParity_halved hpri).mp hwins

end PositionalToDAG

variable {A word}

/-- The memoryless-run theorem: acceptance yields a positional run DAG. -/
theorem exists_positionalRunDAG_of_accepts
    (haccepts : A.Accepts word) :
    Nonempty (A.PositionalRunDAG word) := by
  have hmem := mem_winningRegion_of_accepts haccepts
  rcases (membershipGame A word).positionalDeterminacy
      ParityPlayer.even _ hmem with ⟨σ, hσ⟩
  exact ⟨dagOfWinning σ hσ⟩

/-- Acceptance is equivalent to the existence of a positional run DAG. -/
theorem nonempty_positionalRunDAG_iff_accepts :
    Nonempty (A.PositionalRunDAG word) ↔ A.Accepts word := by
  constructor
  · rintro ⟨D⟩
    exact PositionalRunDAG.accepts D
  · exact exists_positionalRunDAG_of_accepts

end AlternatingParityAutomaton

end DistributedSynthesis
