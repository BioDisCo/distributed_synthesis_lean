/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Library.Automata.SequenceParity
import DistributedSynthesis.Formalizations.Theorem.ThmPitermanDeterminization

/-!
# Universal-run bundle determinization

This file constructs a deterministic parity automaton accepting precisely
the words on which every run of a finite thread system satisfies parity.

A `FiniteThreadSystem` is an arbitrary finite-state transition system over a
word alphabet whose steps are resolved by a hidden `Resolution` input: the
runs of the system over a fixed word form the *bundle* of resolutions
consistent with that word.  The belief-lifting engine needs a deterministic
parity automaton reading only the word and accepting exactly when **every**
run of the bundle satisfies min-even parity -- the universal parity objective.

The construction generalizes the proven `BlockRecordMonitor` universal
thread determinization (`ThmUniversalThreadDeterminization.lean`) verbatim:

1. `violationBuchi` is a nondeterministic Buchi automaton accepting exactly
   the words along which *some* run has min-odd parity.  It guesses the run,
   an odd priority threshold from the finite priority range, and a point
   after which no smaller priority occurs; acceptance visits are the
   threshold hits after the guess.
2. The checked Piterman compiler determinizes `violationBuchi` to a DPA.
3. Shifting priorities by one complements the DPA
   (`shiftPriority_one_accepts_iff_not_accepts`), giving `universalRunDPA`,
   which accepts exactly the words on which every run is min-even
   (`universalRunDPA_accepts_iff`).

The blind-letter instantiation -- threads carrying the objective-automaton
state and the informed-side annotation over the blind observation alphabet --
is an instance of this parametric construction.
-/

namespace DistributedSynthesis

universe u v x

/--
A finite-state transition system over the alphabet `L` whose steps are
resolved by a hidden input.  For a fixed word the runs over all resolution
sequences form the bundle the universal determinization quantifies over.
-/
structure FiniteThreadSystem (L : Type u) where
  State : Type v
  stateFinite : Fintype State
  initial : State
  Resolution : Type x
  step : State -> L -> Resolution -> State
  priority : State -> Nat

attribute [instance] FiniteThreadSystem.stateFinite

namespace FiniteThreadSystem

variable {L : Type u} (S : FiniteThreadSystem.{u, v, x} L)

/-- A run of the thread system on a word: an evolution of the state under
some sequence of resolutions. -/
def IsRun (word : OmegaWord L) (q : Nat -> S.State) : Prop :=
  q 0 = S.initial ∧
    ∀ n : Nat, ∃ r : S.Resolution, q (n + 1) = S.step (q n) (word n) r

/-- The finite range of thread priorities. -/
noncomputable def priorityRange : Finset Nat :=
  Finset.image S.priority Finset.univ

/-- State priority sequences live inside the finite priority range. -/
theorem priority_range_finite (q : Nat -> S.State) :
    (Set.range (fun n => S.priority (q n))).Finite := by
  refine (S.priorityRange : Finset Nat).finite_toSet.subset ?_
  rintro p ⟨n, rfl⟩
  rw [Finset.mem_coe, priorityRange]
  exact Finset.mem_image_of_mem S.priority (Finset.mem_univ (q n))

/-- States of the min-odd run guess automaton. -/
abbrev RunGuessState :=
  S.State × Option {p : Nat // p ∈ S.priorityRange}

/--
The nondeterministic Buchi automaton accepting words with a min-odd run.
The `none` phase tracks a guessed run; the `some t` phase additionally
asserts that every later priority is at least the odd threshold `t`, with
Buchi visits at threshold hits.
-/
noncomputable def violationBuchi : NondetBuchiAutomaton.{u, v} L where
  State := S.RunGuessState
  stateFinite := by
    classical
    infer_instance
  initial := (S.initial, none)
  step := fun source letter target =>
    (∃ r : S.Resolution, target.1 = S.step source.1 letter r) ∧
      ((source.2 = none ∧
          (target.2 = none ∨
            ∃ t : {p : Nat // p ∈ S.priorityRange},
              target.2 = some t ∧
                ¬ DetParityAutomaton.NatEven t.1 ∧
                  t.1 ≤ S.priority target.1)) ∨
        (∃ t : {p : Nat // p ∈ S.priorityRange},
          source.2 = some t ∧ target.2 = some t ∧
            t.1 ≤ S.priority target.1))
  accepting := fun state =>
    ∃ t : {p : Nat // p ∈ S.priorityRange},
      state.2 = some t ∧ S.priority state.1 = t.1

/-- Once the threshold is guessed, the tag persists. -/
theorem violationBuchi_tag_persists
    {word : OmegaWord L}
    (run : S.violationBuchi.RunFrom S.violationBuchi.initial word)
    {m : Nat} {t : {p : Nat // p ∈ S.priorityRange}}
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
theorem violationBuchi_tag_sound
    {word : OmegaWord L}
    (run : S.violationBuchi.RunFrom S.violationBuchi.initial word) :
    ∀ k : Nat, ∀ t : {p : Nat // p ∈ S.priorityRange},
      (run.path k).2 = some t ->
        ¬ DetParityAutomaton.NatEven t.1 ∧
          t.1 ≤ S.priority (run.path k).1 := by
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
      rcases run.step_valid k with
        ⟨_, ⟨_, hnone | ⟨t', htgt, hodd, hle⟩⟩ | ⟨t', hsrc, htgt, hle⟩⟩
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

/-- The guess automaton accepts exactly the words with a min-odd run. -/
theorem violationBuchi_accepts_iff (word : OmegaWord L) :
    S.violationBuchi.Accepts word ↔
      ∃ q : Nat -> S.State,
        S.IsRun word q ∧
          NatSeqMinOddParity (fun n => S.priority (q n)) := by
  constructor
  · rintro ⟨run, haccepts⟩
    refine
      ⟨fun n => (run.path n).1,
        ⟨congrArg Prod.fst run.initial_state, ?_⟩, ?_⟩
    · intro n
      exact (run.step_valid n).1
    · rcases haccepts 0 with ⟨m, _, ⟨t, hmtag, _⟩⟩
      have hpersist := S.violationBuchi_tag_persists run hmtag
      have hsound := S.violationBuchi_tag_sound run
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
        have hkprio' : S.priority (run.path k).1 = p := hkprio
        omega
  · rintro ⟨q, ⟨hinit, hstep⟩, ⟨p, hodd, hseen, hmin⟩⟩
    have hpmem : p ∈ S.priorityRange := by
      rcases hseen 0 with ⟨k, _, hk⟩
      have hk' : S.priority (q k) = p := hk
      rw [priorityRange, ← hk']
      exact Finset.mem_image_of_mem S.priority (Finset.mem_univ (q k))
    rcases natSeq_eventually_ge_of_min_recurring
        (fun n => S.priority (q n))
        (S.priority_range_finite q) hmin with ⟨N, hN⟩
    classical
    set path : Nat -> S.RunGuessState :=
      fun k => (q k, if k ≤ N then none else some ⟨p, hpmem⟩) with hpathdef
    have hpathLe : ∀ k : Nat, k ≤ N -> (path k).2 = none := by
      intro k hk
      simp only [hpathdef, if_pos hk]
    have hpathGt : ∀ k : Nat, ¬ k ≤ N -> (path k).2 = some ⟨p, hpmem⟩ := by
      intro k hk
      simp only [hpathdef, if_neg hk]
    refine ⟨⟨path, ?_, ?_⟩, ?_⟩
    · show path 0 = (S.initial, none)
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
The deterministic parity automaton for the universal run condition:
Piterman determinization of the guess automaton, complemented by the
priority shift.
-/
noncomputable def universalRunDPA : DetParityAutomaton.{u, v} L :=
  (((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
      L).compile S.violationBuchi).dpa).shiftPriority 1

/-- **The bundle DPA is universally correct**: it accepts exactly the words
on which every run of the thread system satisfies min-even parity.  This is
the objective-visibility fix of the route-delta belief game: the conjunction
of parity conditions over the bundle is recognized by a single deterministic
parity automaton on the word. -/
theorem universalRunDPA_accepts_iff (word : OmegaWord L) :
    S.universalRunDPA.Accepts word ↔
      ∀ q : Nat -> S.State,
        S.IsRun word q ->
          NatSeqMinEvenParity (fun n => S.priority (q n)) := by
  rw [universalRunDPA,
    DetParityAutomaton.shiftPriority_one_accepts_iff_not_accepts,
    ((NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
      L).compile S.violationBuchi).correct word,
    violationBuchi_accepts_iff]
  constructor
  · intro hnot q hrun
    rcases natSeqMinEvenParity_or_minOddParity
        (fun n => S.priority (q n)) (S.priority_range_finite q) with
      heven | hodd
    · exact heven
    · exact absurd ⟨q, hrun, hodd⟩ hnot
  · rintro hall ⟨q, hrun, hodd⟩
    exact not_natSeqMinEvenParity_and_natSeqMinOddParity _
      ⟨hall q hrun, hodd⟩

end FiniteThreadSystem

end DistributedSynthesis
