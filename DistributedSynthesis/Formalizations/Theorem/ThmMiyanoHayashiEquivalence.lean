/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmAPAMembershipGame
import DistributedSynthesis.Formalizations.Theorem.ThmMiyanoHayashiAlternationRemoval
import Mathlib.Order.KonigLemma

/-!
# Miyano-Hayashi breakpoint equivalence for Büchi-shaped automata

This file proves that the Miyano-Hayashi breakpoint automaton `buchiCore`
recognizes exactly the language of a Büchi-shaped alternating automaton —
one whose priorities all lie in `{0, 1}`.

Both directions factor through `PositionalRunDAG` from the membership-game
file, which is what makes per-level reasoning sound:

* Soundness (`accepts_of_buchiCore_accepts`): an accepting breakpoint run
  yields per-level support choices; the resulting DAG's threads must clear
  through the pending sets, so a thread avoiding priority `0` forever
  would be stuck pending after a breakpoint, contradicting infinitely many
  clears.  The DAG then accepts by `PositionalRunDAG.accepts`.
* Completeness (`buchiCore_accepts_of_positionalRunDAG`): running the
  breakpoint construction along the DAG's own choices, an eternally
  nonempty pending sequence yields, by the inverse-limit compactness
  lemma over backward pending chains, an infinite DAG thread that is
  eventually always pending, hence eventually always priority `1` —
  contradicting `threads_accept`.

`buchiCore_accepts_iff_accepts` is the paper-facing equivalence.  The
alternation-removal compiler for weak automata is obtained downstream by
recoloring priorities to their parity, which preserves thread acceptance.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton

namespace MiyanoHayashi

variable {Alphabet : Type u}
variable {A : AlternatingParityAutomaton.{u, v} Alphabet}
variable {word : OmegaWord Alphabet}

/-- A Büchi-shaped priority map: every priority is `0` or `1`. -/
def BuchiShaped (A : AlternatingParityAutomaton.{u, v} Alphabet) : Prop :=
  ∀ s : A.State, A.priority s = 0 ∨ A.priority s = 1

section Soundness

variable (run : (buchiCore A).RunFrom (buchiCore A).initial word)

/-- The support choice taken by one breakpoint step. -/
noncomputable def runChoice (n : Nat) :
    A.MacroStepSupport (run.path n).frontier (word n) :=
  Classical.choose
    (show buchiStep A (run.path n) (word n) (run.path (n + 1)) from
      run.step_valid n)

theorem runChoice_frontier (n : Nat) :
    (run.path (n + 1)).frontier = (runChoice run n).support :=
  (Classical.choose_spec
    (show buchiStep A (run.path n) (word n) (run.path (n + 1)) from
      run.step_valid n)).1

theorem runChoice_pending (n : Nat) :
    (run.path (n + 1)).pending =
      nextPending (runChoice run n) (run.path n).pending :=
  (Classical.choose_spec
    (show buchiStep A (run.path n) (word n) (run.path (n + 1)) from
      run.step_valid n)).2

/--
Pending stickiness: a thread through the breakpoint run whose states are
never Büchi-accepting after a clear time stays pending forever after it.
-/
theorem thread_pending_of_never_accepting
    {s : Nat -> A.State}
    (hthread : ∀ n : Nat, ∃ h : s n ∈ (run.path n).frontier,
      s (n + 1) ∈ ((runChoice run n).choice ⟨s n, h⟩).support)
    {N : Nat}
    (hodd : ∀ k : Nat, N ≤ k -> ¬ buchiAcceptingState A (s k))
    {N₁ : Nat} (hN₁ : N ≤ N₁)
    (hclear : (run.path N₁).pending = ∅) :
    ∀ k : Nat, N₁ < k -> s k ∈ (run.path k).pending := by
  classical
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.lt_or_ge N₁ k with hlt | hge
      · have hkpend : s k ∈ (run.path k).pending := ih hlt
        rw [runChoice_pending run k]
        have hne : (run.path k).pending ≠ ∅ :=
          Finset.ne_empty_of_mem hkpend
        rcases hthread k with ⟨hfr, hsup⟩
        refine Finset.mem_filter.mpr ⟨?_, hodd (k + 1) (by omega)⟩
        rw [rawNextPending, if_neg hne]
        exact (mem_pendingSuccessors (runChoice run k) (s (k + 1))).mpr
          ⟨s k, hkpend, hfr, hsup⟩
      · have hkeq : k = N₁ := by omega
        subst hkeq
        rw [runChoice_pending run k]
        rcases hthread k with ⟨hfr, hsup⟩
        refine Finset.mem_filter.mpr ⟨?_, hodd (k + 1) (by omega)⟩
        rw [rawNextPending, if_pos hclear]
        exact (MacroStepSupport.mem_support).mpr ⟨⟨s k, hfr⟩, hsup⟩

/-- The positional run DAG extracted from an accepting breakpoint run. -/
noncomputable def dagOfBuchiRun
    (haccepts : run.Accepts) :
    A.PositionalRunDAG word where
  frontier := fun n => (run.path n).frontier
  choice := runChoice run
  initial_mem := by
    have h0 := run.initial_state
    have := congrArg BuchiState.frontier h0
    exact this
  frontier_succ := runChoice_frontier run
  threads_accept := by
    intro s _hzero hstep
    by_cases hzeroSeen :
        ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ A.priority (s k) = 0
    · refine ⟨0, ⟨0, rfl⟩, hzeroSeen, ?_⟩
      intro q _hq
      exact Nat.zero_le q
    · exfalso
      push Not at hzeroSeen
      rcases hzeroSeen with ⟨N, hN⟩
      have hodd : ∀ k : Nat, N ≤ k -> ¬ buchiAcceptingState A (s k) := by
        intro k hk hacc
        exact hN k hk hacc
      rcases pending_clears_infinitely_often haccepts N with
        ⟨N₁, hN₁, hclear⟩
      have hsticky :=
        thread_pending_of_never_accepting run hstep hodd hN₁ hclear
      rcases pending_clears_infinitely_often haccepts (N₁ + 1) with
        ⟨k, hk, hkclear⟩
      have hkpend : s k ∈ (run.path k).pending := hsticky k (by omega)
      rw [hkclear] at hkpend
      exact absurd hkpend (Finset.notMem_empty (s k))

/-- Soundness: the breakpoint automaton only accepts accepted words. -/
theorem accepts_of_buchiCore_accepts
    (haccepts : (buchiCore A).Accepts word) :
    A.Accepts word := by
  rcases haccepts with ⟨run, hrun⟩
  exact PositionalRunDAG.accepts (dagOfBuchiRun run hrun)

end Soundness

section Completeness

variable (D : A.PositionalRunDAG word)

/-- The pending sets of the breakpoint run along the DAG's choices. -/
noncomputable def dagPending : Nat -> Finset A.State
  | 0 => ∅
  | n + 1 => nextPending (D.choice n) (dagPending n)

/-- The breakpoint run along the DAG's choices. -/
noncomputable def dagBuchiRun :
    (buchiCore A).RunFrom (buchiCore A).initial word where
  path := fun n => ⟨D.frontier n, dagPending D n⟩
  initial_state := by
    show (⟨D.frontier 0, dagPending D 0⟩ : BuchiState A) =
      buchiInitialState A
    rw [buchiInitialState, D.initial_mem]
    rfl
  step_valid := by
    intro n
    exact ⟨D.choice n, D.frontier_succ n, rfl⟩

/-- Pending states sit inside the frontier. -/
theorem dagPending_subset_frontier :
    ∀ n : Nat, dagPending D n ⊆ D.frontier n := by
  intro n
  match n with
  | 0 =>
      intro x hx
      exact absurd hx (Finset.notMem_empty x)
  | n + 1 =>
      intro x hx
      rw [D.frontier_succ n]
      exact nextPending_subset_support (D.choice n) hx

/-- Pending states are never Büchi-accepting. -/
theorem dagPending_not_accepting
    {n : Nat} {x : A.State} (hx : x ∈ dagPending D (n + 1)) :
    ¬ buchiAcceptingState A x := by
  classical
  exact (Finset.mem_filter.mp hx).2

/-- Frontier predecessors along the DAG. -/
theorem frontier_pred
    {k : Nat} {x : A.State} (hx : x ∈ D.frontier (k + 1)) :
    ∃ y : A.State, ∃ h : y ∈ D.frontier k,
      x ∈ ((D.choice k).choice ⟨y, h⟩).support := by
  rw [D.frontier_succ k] at hx
  rcases (MacroStepSupport.mem_support).mp hx with ⟨⟨y, hy⟩, hsup⟩
  exact ⟨y, hy, hsup⟩

/-- Pending predecessors along the DAG, when the previous pending is live. -/
theorem pending_pred
    {k : Nat} {x : A.State}
    (hne : dagPending D k ≠ ∅)
    (hx : x ∈ dagPending D (k + 1)) :
    ∃ y : A.State, y ∈ dagPending D k ∧
      ∃ h : y ∈ D.frontier k,
        x ∈ ((D.choice k).choice ⟨y, h⟩).support := by
  classical
  have hraw := (Finset.mem_filter.mp hx).1
  rw [rawNextPending, if_neg hne] at hraw
  rcases (mem_pendingSuccessors (D.choice k) x).mp hraw with
    ⟨y, hyp, hyf, hsup⟩
  exact ⟨y, hyp, hyf, hsup⟩

/-- Backward chain property: a rooted DAG-thread prefix, pending past `N`. -/
def ChainProp (N m : Nat) (c : Fin (m + 1) -> A.State) : Prop :=
  c ⟨0, by omega⟩ = A.initial ∧
    (∀ i : Nat, (hi : i < m) ->
      ∃ h : c ⟨i, by omega⟩ ∈ D.frontier i,
        c ⟨i + 1, by omega⟩ ∈
          ((D.choice i).choice ⟨c ⟨i, by omega⟩, h⟩).support) ∧
    ∀ i : Nat, (hi : i ≤ m) -> N < i ->
      c ⟨i, by omega⟩ ∈ dagPending D i

/-- Backward construction of rooted chains ending at a given state. -/
theorem exists_chain_to
    (N : Nat)
    (hne : ∀ j : Nat, N < j -> dagPending D j ≠ ∅) :
    ∀ (k : Nat) (x : A.State), x ∈ D.frontier k ->
      (N < k -> x ∈ dagPending D k) ->
      ∃ c : Fin (k + 1) -> A.State,
        ChainProp D N k c ∧ c ⟨k, by omega⟩ = x := by
  intro k
  induction k with
  | zero =>
      intro x hx _hpend
      have hinit : x = A.initial := by
        rw [D.initial_mem] at hx
        exact Finset.mem_singleton.mp hx
      refine ⟨fun _ => A.initial, ⟨rfl, ?_, ?_⟩, hinit.symm⟩
      · intro i hi
        omega
      · intro i hi hNi
        omega
  | succ k ih =>
      intro x hx hpend
      have hstep : ∃ y : A.State,
          (N < k -> y ∈ dagPending D k) ∧
            ∃ h : y ∈ D.frontier k,
              x ∈ ((D.choice k).choice ⟨y, h⟩).support := by
        by_cases hNk : N < k
        · rcases pending_pred D (hne k hNk) (hpend (by omega)) with
            ⟨y, hyp, hyf, hsup⟩
          exact ⟨y, fun _ => hyp, hyf, hsup⟩
        · rcases frontier_pred D hx with ⟨y, hyf, hsup⟩
          exact ⟨y, fun hNk' => absurd hNk' hNk, hyf, hsup⟩
      rcases hstep with ⟨y, hyp, hyf, hsup⟩
      rcases ih y hyf hyp with ⟨c', ⟨hc0, hedges, hpends⟩, hlast⟩
      have hsnoc_lt : ∀ (i : Nat) (hi : i < k + 1),
          (Fin.snoc c' x : Fin (k + 2) -> A.State) ⟨i, by omega⟩ =
            c' ⟨i, hi⟩ := by
        intro i hi
        have hcast : (⟨i, by omega⟩ : Fin (k + 2)) =
            Fin.castSucc ⟨i, hi⟩ := by
          ext
          rfl
        rw [hcast, Fin.snoc_castSucc]
      have hsnoc_last :
          (Fin.snoc c' x : Fin (k + 2) -> A.State) ⟨k + 1, by omega⟩ = x := by
        have hcast : (⟨k + 1, by omega⟩ : Fin (k + 2)) = Fin.last (k + 1) := by
          ext
          rfl
        rw [hcast, Fin.snoc_last]
      refine ⟨Fin.snoc c' x, ⟨?_, ?_, ?_⟩, hsnoc_last⟩
      · rw [hsnoc_lt 0 (by omega)]
        exact hc0
      · intro i hi
        rcases Nat.lt_or_ge i k with hik | hik
        · rw [hsnoc_lt i (by omega), hsnoc_lt (i + 1) (by omega)]
          exact hedges i hik
        · have hieq : i = k := by omega
          subst hieq
          rw [hsnoc_lt i (by omega), hsnoc_last, hlast]
          exact ⟨hyf, hsup⟩
      · intro i hi hNi
        rcases Nat.lt_or_ge i (k + 1) with hik | hik
        · rw [hsnoc_lt i hik]
          exact hpends i (by omega) hNi
        · have hieq : i = k + 1 := by omega
          subst hieq
          rw [hsnoc_last]
          exact hpend hNi

/-- Chains truncate. -/
theorem chainProp_trunc
    {N m m' : Nat} (hm : m ≤ m')
    {c : Fin (m' + 1) -> A.State}
    (hc : ChainProp D N m' c) :
    ChainProp D N m
      (fun i => c (Fin.castLE (by omega) i)) := by
  obtain ⟨hc0, hedges, hpends⟩ := hc
  refine ⟨hc0, ?_, ?_⟩
  · intro i hi
    exact hedges i (by omega)
  · intro i hi hNi
    exact hpends i (by omega) hNi

end Completeness

/-- Completeness: the breakpoint automaton accepts every accepted word. -/
theorem buchiCore_accepts_of_positionalRunDAG
    (D : A.PositionalRunDAG word)
    (hshape : BuchiShaped A) :
    (buchiCore A).Accepts word := by
  classical
  refine ⟨dagBuchiRun D, ?_⟩
  by_contra hnot
  rw [NondetBuchiAutomaton.RunFrom.Accepts,
    NondetBuchiAutomaton.SeenInfinitelyOftenOn] at hnot
  push Not at hnot
  rcases hnot with ⟨N, hN⟩
  have hne : ∀ j : Nat, N < j -> dagPending D j ≠ ∅ := by
    intro j hj hempty
    refine hN j (by omega) ?_
    show ((dagBuchiRun D).path j).pending = ∅
    exact hempty
  let Chain : Nat -> Type v :=
    fun m => {c : Fin (m + 1) -> A.State // ChainProp D N m c}
  haveI hfinite : ∀ m : Nat, Finite (Chain m) := fun _ => Subtype.finite
  haveI hnonempty : ∀ m : Nat, Nonempty (Chain m) := by
    intro m
    have hklarge : N < max m (N + 1) := by omega
    rcases Finset.nonempty_iff_ne_empty.mpr (hne _ hklarge) with ⟨x, hx⟩
    rcases exists_chain_to D N hne (max m (N + 1)) x
        (dagPending_subset_frontier D _ hx) (fun _ => hx) with
      ⟨c, hc, _⟩
    exact ⟨⟨fun i => c (Fin.castLE (by omega) i),
      chainProp_trunc D (le_max_left m (N + 1)) hc⟩⟩
  let proj : {i j : Nat} -> i ≤ j -> Chain j -> Chain i :=
    fun {i j} hij c =>
      ⟨fun idx => c.1 (Fin.castLE (Nat.succ_le_succ hij) idx),
        chainProp_trunc D hij c.2⟩
  have hproj_refl : ∀ ⦃i : Nat⦄ (c : Chain i), proj rfl.le c = c := by
    intro i c
    apply Subtype.ext
    funext idx
    rfl
  have hproj_trans :
      ∀ ⦃i j k : Nat⦄ (hij : i ≤ j) (hjk : j ≤ k) (c : Chain k),
        proj hij (proj hjk c) = proj (hij.trans hjk) c := by
    intro i j k hij hjk c
    apply Subtype.ext
    funext idx
    rfl
  have hfib : ∀ (i : Nat) (c : Chain i),
      {b : Chain (i + 1) | proj (Nat.le_add_right i 1) b = c}.Finite := by
    intro i c
    exact Set.toFinite _
  obtain ⟨f, hf⟩ :=
    exists_seq_forall_proj_of_forall_finite
      (α := Chain) proj hproj_refl hproj_trans hfib
  have hagree : ∀ (n i : Nat) (hi : i ≤ n),
      (f n).1 ⟨i, Nat.lt_succ_of_le hi⟩ =
        (f i).1 ⟨i, Nat.lt_succ_self i⟩ := by
    intro n i hi
    have hcoh := hf hi
    exact congrArg (fun c => c.1 ⟨i, Nat.lt_succ_self i⟩) hcoh
  set s : Nat -> A.State :=
    fun n => (f n).1 ⟨n, Nat.lt_succ_self n⟩ with hs
  have hzero : s 0 = A.initial := (f 0).2.1
  have hedges : ∀ n : Nat,
      ∃ h : s n ∈ D.frontier n,
        s (n + 1) ∈ ((D.choice n).choice ⟨s n, h⟩).support := by
    intro n
    have hedge := (f (n + 1)).2.2.1 n (Nat.lt_succ_self n)
    rw [hagree (n + 1) n (Nat.le_succ n)] at hedge
    exact hedge
  have hpend : ∀ k : Nat, N < k -> s k ∈ dagPending D k := by
    intro k hk
    exact (f k).2.2.2 k (le_refl k) hk
  have haccept := D.threads_accept s hzero hedges
  rcases haccept with ⟨p, hpEven, hpSeen, _⟩
  rcases hpSeen (N + 1) with ⟨k, hk, hkp⟩
  obtain ⟨k', rfl⟩ : ∃ k' : Nat, k = k' + 1 := ⟨k - 1, by omega⟩
  set k : Nat := k' + 1 with hkdef
  have hkpend : s k ∈ dagPending D k := hpend k (by omega)
  have hknotacc : ¬ buchiAcceptingState A (s k) :=
    dagPending_not_accepting D hkpend
  have hkone : A.priority (s k) = 1 := by
    rcases hshape (s k) with h0 | h1
    · exact absurd h0 hknotacc
    · exact h1
  have hp1 : p = 1 := by
    have hkp' : A.priority (s k) = p := hkp
    omega
  rcases hpEven with ⟨m, hm⟩
  omega

/-- The Miyano-Hayashi breakpoint equivalence for Büchi-shaped automata. -/
theorem buchiCore_accepts_iff_accepts
    (hshape : BuchiShaped A) :
    (buchiCore A).Accepts word ↔ A.Accepts word := by
  constructor
  · exact accepts_of_buchiCore_accepts
  · intro haccepts
    rcases exists_positionalRunDAG_of_accepts haccepts with ⟨D⟩
    exact buchiCore_accepts_of_positionalRunDAG D hshape

end MiyanoHayashi

end AlternatingParityAutomaton

end DistributedSynthesis
