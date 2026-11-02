/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalBeliefPhysicalAcceptanceSplit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenGlobalRecutStream
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceAllBothPath

/-!
# Recurrent-environment extraction for the global delayed recut

This file turns the graph-theoretic recurrent regimes into the productive
physical decompositions consumed by `LemPairedProfiledOpenGlobalRecutStream`.
The first split is essential: recurrent `.both` rounds may coexist with
unbounded strict rounds, or the environment may become all-`.both`.  The
latter has its own coherent zero-open path and must not be forced through a
strict-gap interface.

Everything here is proof-side graph combinatorics.  No side, row, cut, or
strict-leader bit is exposed to either process, and no acceptance or fixed
code-lineage claim is made.
-/

namespace DistributedSynthesis

universe u v

/-- Strict rounds occur at arbitrarily late positions. -/
def GraphStrictRecurrent (graphs : Nat → Graph) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start ≤ n ∧ graphs n ≠ .both

/-- After a finite prefix every round is simultaneous. -/
def EventuallyAllBoth (graphs : Nat → Graph) : Prop :=
  ∃ start : Nat, ∀ n : Nat, start ≤ n → graphs n = .both

/-- Every graph sequence either has unbounded strict rounds or an
all-simultaneous tail. -/
theorem graphStrictRecurrent_or_eventuallyAllBoth (graphs : Nat → Graph) :
    GraphStrictRecurrent graphs ∨ EventuallyAllBoth graphs := by
  classical
  by_cases hstrict : GraphStrictRecurrent graphs
  · exact Or.inl hstrict
  · right
    unfold GraphStrictRecurrent at hstrict
    push Not at hstrict
    rcases hstrict with ⟨start, hstart⟩
    refine ⟨start, fun n hn ↦ ?_⟩
    have hnotStrict := hstart n hn
    cases hgraph : graphs n <;> simp_all

/-- A strict group begins at a strict round whose predecessor (if any) has a
different graph.  Thus it begins after a `.both` gap or at a direct strict
reversal. -/
def StrictGroupStart (graphs : Nat → Graph) (n : Nat) : Prop :=
  graphs n ≠ .both ∧ (n = 0 ∨ graphs (n - 1) ≠ graphs n)

noncomputable instance strictGroupStart_decidable (graphs : Nat → Graph) :
    DecidablePred (StrictGroupStart graphs) := fun n ↦ by
  classical
  exact inferInstance

/-- Strict-group starts occur arbitrarily far out. -/
def StrictGroupStartsRecurrent (graphs : Nat → Graph) : Prop :=
  ∀ start : Nat, ∃ n : Nat, start < n ∧ StrictGroupStart graphs n

/-- Convert the non-strict recurrence convention into the strict inequality
used by `nextMarked`. -/
theorem graphStrictRecurrent_strict
    {graphs : Nat → Graph} (hstrict : GraphStrictRecurrent graphs) :
    ∀ start : Nat, ∃ n : Nat, start < n ∧ graphs n ≠ .both := by
  intro start
  rcases hstrict (start + 1) with ⟨n, hn, hgraph⟩
  exact ⟨n, by omega, hgraph⟩

/-- If both simultaneous and strict rounds recur, then maximal strict-group
starts recur.  Pick a `.both` round and then the least later strict round;
its immediate predecessor is still `.both`, so it is a group start. -/
theorem strictGroupStartsRecurrent_of_both_of_strict
    {graphs : Nat → Graph}
    (hboth : GraphBothRecurrent graphs)
    (hstrict : GraphStrictRecurrent graphs) :
    StrictGroupStartsRecurrent graphs := by
  classical
  let hstrict' : ∀ start : Nat,
      ∃ n : Nat, start < n ∧ graphs n ≠ .both :=
    graphStrictRecurrent_strict hstrict
  intro start
  rcases hboth start with ⟨bothAt, hstart, hbothAt⟩
  let strictAt := nextMarked (B := fun n ↦ graphs n ≠ .both)
    hstrict' bothAt
  have hlt : bothAt < strictAt := lt_nextMarked hstrict' bothAt
  have hstrictAt : graphs strictAt ≠ .both :=
    marked_nextMarked hstrict' bothAt
  have hprev : graphs (strictAt - 1) = .both := by
    by_cases heq : strictAt - 1 = bothAt
    · simpa [heq] using hbothAt
    · have hinterior : bothAt < strictAt - 1 := by omega
      have hbefore : strictAt - 1 < strictAt := by omega
      have hnot := not_marked_of_lt_nextMarked hstrict'
        hinterior hbefore
      by_contra hne
      exact hnot hne
  refine ⟨strictAt, Nat.lt_of_le_of_lt hstart hlt, hstrictAt, ?_⟩
  right
  rw [hprev]
  exact fun heq ↦ hstrictAt heq.symm

/-- The all-`.both` alternative obtained from the graph split gives an exact
coherent paired branch on the corresponding physical tail. -/
theorem exists_allBothTail_pairedBranch
    {In₁ : Type u} {In₂ : Type v}
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hall : EventuallyAllBoth (fun n ↦ (env n).graph)) :
    ∃ start : Nat,
      ∀ initialSide : DetParityAutomaton.IndexedLineageSide,
      DetParityAutomaton.pairedBranchEnvironment
          (DetParityAutomaton.profiledOpenAllBothDirection
            (OmegaWord.drop env start) initialSide) =
        OmegaWord.drop env start := by
  rcases hall with ⟨start, hstart⟩
  refine ⟨start, fun initialSide ↦ ?_⟩
  apply DetParityAutomaton.pairedBranchEnvironment_profiledOpenAllBothDirection
  intro n
  exact hstart (start + n) (Nat.le_add_right start n)

/-- Recurrent `.both` environments split cleanly into the all-`.both` tail
case or the complementary case with unbounded strict-group starts. -/
theorem graphBothRecurrent_split
    (graphs : Nat → Graph) (hboth : GraphBothRecurrent graphs) :
    EventuallyAllBoth graphs ∨
      (GraphStrictRecurrent graphs ∧ StrictGroupStartsRecurrent graphs) := by
  rcases graphStrictRecurrent_or_eventuallyAllBoth graphs with
      hstrict | hall
  · exact Or.inr ⟨hstrict,
      strictGroupStartsRecurrent_of_both_of_strict hboth hstrict⟩
  · exact Or.inl hall

/-! ## Shifting to, and enumerating, strict-group boundaries -/

/-- At the beginning of a suffix, being strict is already enough to be a
strict-group start: there is no predecessor inside the suffix. -/
theorem strictGroupStart_drop_zero_of_strict
    (graphs : Nat → Graph) (shift : Nat)
    (hstrict : graphs shift ≠ .both) :
    StrictGroupStart (fun n ↦ graphs (shift + n)) 0 := by
  exact ⟨by simpa using hstrict, Or.inl rfl⟩

/-- Away from zero, strict-group starts are invariant under dropping a finite
prefix. -/
theorem strictGroupStart_drop_iff
    (graphs : Nat → Graph) (shift n : Nat) (hn : 0 < n) :
    StrictGroupStart (fun j ↦ graphs (shift + j)) n ↔
      StrictGroupStart graphs (shift + n) := by
  unfold StrictGroupStart
  have hpos : shift + n ≠ 0 := by omega
  have hpred : shift + (n - 1) = shift + n - 1 := by omega
  simp only [hn.ne', hpos, false_or, hpred]

/-- Recurrence of strict-group starts survives every finite suffix shift. -/
theorem strictGroupStartsRecurrent_drop
    {graphs : Nat → Graph}
    (hstarts : StrictGroupStartsRecurrent graphs) (shift : Nat) :
    StrictGroupStartsRecurrent (fun n ↦ graphs (shift + n)) := by
  intro start
  rcases hstarts (shift + start) with ⟨m, hm, hgroup⟩
  refine ⟨m - shift, by omega, ?_⟩
  have hpositive : 0 < m - shift := by omega
  rw [strictGroupStart_drop_iff graphs shift (m - shift) hpositive]
  simpa [Nat.add_sub_of_le (Nat.le_trans (Nat.le_add_right shift start)
    hm.le)] using hgroup

/-- Choose one finite shift after which round zero is a strict-group start and
strict-group starts remain unbounded.  The shift is proof-side data only. -/
theorem exists_drop_strictGroupStart_zero_and_recurrent
    {graphs : Nat → Graph}
    (hstarts : StrictGroupStartsRecurrent graphs) :
    ∃ shift : Nat,
      StrictGroupStart (fun n ↦ graphs (shift + n)) 0 ∧
        StrictGroupStartsRecurrent (fun n ↦ graphs (shift + n)) := by
  rcases hstarts 0 with ⟨shift, hshift, hgroup⟩
  refine ⟨shift, strictGroupStart_drop_zero_of_strict graphs shift
    hgroup.1, strictGroupStartsRecurrent_drop hstarts shift⟩

/-- Enumeration of all successive strict-group starts after a suffix has been
shifted so that zero itself is a group start. -/
noncomputable def strictGroupCuts
    (graphs : Nat → Graph) (hstarts : StrictGroupStartsRecurrent graphs) :
    Nat → Nat :=
  cutSeq hstarts

@[simp] theorem strictGroupCuts_zero
    (graphs : Nat → Graph) (hstarts : StrictGroupStartsRecurrent graphs) :
    strictGroupCuts graphs hstarts 0 = 0 :=
  rfl

theorem strictGroupCuts_strictMono
    (graphs : Nat → Graph) (hstarts : StrictGroupStartsRecurrent graphs) :
    StrictMono (strictGroupCuts graphs hstarts) :=
  cutSeq_strictMono hstarts

/-- Every enumerated cut is a strict-group start, including the explicitly
shifted cut zero. -/
theorem strictGroupStart_strictGroupCuts
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k : Nat) :
    StrictGroupStart graphs (strictGroupCuts graphs hstarts k) := by
  cases k with
  | zero => simpa using hzero
  | succ k => exact marked_cutSeq_succ hstarts k

/-- Consecutive strict-group cuts contain no further group start in their
open interior. -/
theorem not_strictGroupStart_between_strictGroupCuts
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    {k n : Nat}
    (hlower : strictGroupCuts graphs hstarts k < n)
    (hupper : n < strictGroupCuts graphs hstarts (k + 1)) :
    ¬ StrictGroupStart graphs n :=
  not_marked_between hstarts hlower hupper

/-- Between consecutive strict-group cuts there is a unique *shape*: a
nonempty constant strict block followed by a (possibly empty) block of
simultaneous rounds.  `split` is the first position after the cut whose graph
differs from the current strict graph.  This is the exact group-slice fact
needed to instantiate the right/left signed recuts. -/
theorem exists_strictGroupCut_split
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k : Nat) :
    ∃ split : Nat,
      strictGroupCuts graphs hstarts k < split ∧
      split ≤ strictGroupCuts graphs hstarts (k + 1) ∧
      (∀ n : Nat,
        strictGroupCuts graphs hstarts k ≤ n → n < split →
          graphs n = graphs (strictGroupCuts graphs hstarts k)) ∧
      (∀ n : Nat,
        split ≤ n → n < strictGroupCuts graphs hstarts (k + 1) →
          graphs n = .both) := by
  classical
  let c := strictGroupCuts graphs hstarts k
  let d := strictGroupCuts graphs hstarts (k + 1)
  have hcd : c < d := strictGroupCuts_strictMono graphs hstarts
    (Nat.lt_succ_self k)
  have hc : StrictGroupStart graphs c :=
    strictGroupStart_strictGroupCuts hstarts hzero k
  have hd : StrictGroupStart graphs d :=
    strictGroupStart_strictGroupCuts hstarts hzero (k + 1)
  have hchange : ∃ n : Nat, c < n ∧ n ≤ d ∧ graphs n ≠ graphs c := by
    by_cases hdc : graphs d = graphs c
    · have hdpos : d ≠ 0 := by omega
      have hpredDiff : graphs (d - 1) ≠ graphs d :=
        (hd.2.resolve_left hdpos)
      refine ⟨d - 1, ?_, by omega, ?_⟩
      · by_contra hnot
        have heq : d - 1 = c := by omega
        rw [heq, hdc] at hpredDiff
        exact hpredDiff rfl
      · simpa [hdc] using hpredDiff
    · exact ⟨d, hcd, le_rfl, hdc⟩
  let split := Nat.find hchange
  have hsplitSpec : c < split ∧ split ≤ d ∧
      graphs split ≠ graphs c :=
    Nat.find_spec hchange
  have hconstant : ∀ n : Nat, c ≤ n → n < split →
      graphs n = graphs c := by
    intro n hcn hnSplit
    rcases hcn.eq_or_lt with rfl | hcn'
    · rfl
    · by_contra hne
      exact Nat.find_min hchange hnSplit ⟨hcn', hnSplit.le.trans
        hsplitSpec.2.1, hne⟩
  have hnoInterior : ∀ n : Nat, c < n → n < d →
      ¬ StrictGroupStart graphs n := by
    intro n hcn hnd
    exact not_strictGroupStart_between_strictGroupCuts hstarts hcn hnd
  have hsplitBoth : split < d → graphs split = .both := by
    intro hsplitD
    by_contra hnotBoth
    have hpredBounds : c ≤ split - 1 ∧ split - 1 < split := by
      omega
    have hpred : graphs (split - 1) = graphs c :=
      hconstant (split - 1) hpredBounds.1 hpredBounds.2
    have hprevDiff : graphs (split - 1) ≠ graphs split := by
      rw [hpred]
      exact fun heq ↦ hsplitSpec.2.2 heq.symm
    exact hnoInterior split hsplitSpec.1 hsplitD
      ⟨hnotBoth, Or.inr hprevDiff⟩
  have hbothAfter : ∀ n : Nat, split ≤ n → n < d →
      graphs n = .both := by
    intro n hsplitN hnD
    have hindexed : ∀ t : Nat, split + t < d →
        graphs (split + t) = .both := by
      intro t
      induction t with
      | zero =>
          intro hlt
          simpa using hsplitBoth hlt
      | succ t ih =>
          intro hlt
          have hprev : graphs (split + t) = .both := ih (by omega)
          by_contra hnotBoth
          have hpredIndex : split + (t + 1) - 1 = split + t := by omega
          have hgroup : StrictGroupStart graphs (split + (t + 1)) := by
            refine ⟨hnotBoth, Or.inr ?_⟩
            rw [hpredIndex, hprev]
            exact fun heq ↦ hnotBoth heq.symm
          exact hnoInterior (split + (t + 1)) (by omega) hlt hgroup
    have hn : split + (n - split) = n := by omega
    rw [← hn]
    exact hindexed (n - split) (by omega)
  exact ⟨split, hsplitSpec.1, hsplitSpec.2.1, hconstant, hbothAfter⟩

/-! ## Literal finite slices -/

/-- The half-open finite slice `[start, stop)` of an omega environment. -/
def environmentSlice {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) :
    List (EnvironmentRound In₁ In₂) :=
  List.ofFn (fun i : Fin (stop - start) ↦ env (start + i))

@[simp] theorem environmentSlice_length
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) :
    (environmentSlice env start stop).length = stop - start := by
  simp [environmentSlice]

@[simp] theorem environmentSlice_getElem
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (start stop i : Nat)
    (hi : i < (environmentSlice env start stop).length) :
    (environmentSlice env start stop)[i] = env (start + i) := by
  simp [environmentSlice]

/-- Slices concatenate exactly at every intermediate boundary. -/
theorem environmentSlice_append
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) {start split stop : Nat}
    (hstart : start ≤ split) (hstop : split ≤ stop) :
    environmentSlice env start stop =
      environmentSlice env start split ++ environmentSlice env split stop := by
  apply List.ext_getElem
  · simp only [environmentSlice_length, List.length_append]
    omega
  · intro i hiLeft hiRight
    rw [environmentSlice_getElem]
    rw [List.getElem_append]
    split
    next hfirst =>
      rw [environmentSlice_getElem]
    next hsecond =>
      rw [environmentSlice_getElem]
      congr 1
      simp only [environmentSlice_length] at hsecond ⊢
      omega

/-- Prefixes are literal slices from zero. -/
theorem environmentSlice_zero_eq_omegaPrefix
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂) (stop : Nat) :
    environmentSlice env 0 stop = DetParityAutomaton.omegaPrefix env stop := by
  simp [environmentSlice, DetParityAutomaton.omegaPrefix]

/-- Receiver-first input pairs carried by a left-strict environment word. -/
def leftMovesOfRounds {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂)) : List (In₁ × In₂) :=
  rounds.map fun round ↦ (round.inputOne, round.inputTwo)

/-- Receiver-first input pairs carried by a right-strict environment word. -/
def rightMovesOfRounds {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂)) : List (In₂ × In₁) :=
  rounds.map fun round ↦ (round.inputTwo, round.inputOne)

/-- Rebuilding a uniformly left-strict finite word from its input pairs is
literal identity. -/
theorem map_leftEnvironment_leftMovesOfRounds
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂))
    (hleft : ∀ round ∈ rounds, round.graph = .left) :
    (leftMovesOfRounds rounds).map leftEnvironment = rounds := by
  induction rounds with
  | nil => rfl
  | cons round rest ih =>
      have hround := hleft round (by simp)
      have hrest : ∀ next ∈ rest, next.graph = .left := by
        intro next hnext
        exact hleft next (by simp [hnext])
      cases round
      simp_all [leftMovesOfRounds, leftEnvironment]

/-- Right mirror of `map_leftEnvironment_leftMovesOfRounds`. -/
theorem map_rightEnvironment_rightMovesOfRounds
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂))
    (hright : ∀ round ∈ rounds, round.graph = .right) :
    (rightMovesOfRounds rounds).map rightEnvironment = rounds := by
  induction rounds with
  | nil => rfl
  | cons round rest ih =>
      have hround := hright round (by simp)
      have hrest : ∀ next ∈ rest, next.graph = .right := by
        intro next hnext
        exact hright next (by simp [hnext])
      cases round
      simp_all [rightMovesOfRounds, rightEnvironment]

/-- The input-pair word of a nonempty environment word is nonempty. -/
theorem leftMovesOfRounds_ne_nil
    {In₁ : Type u} {In₂ : Type v}
    {rounds : List (EnvironmentRound In₁ In₂)}
    (hne : rounds ≠ []) : leftMovesOfRounds rounds ≠ [] := by
  simpa [leftMovesOfRounds] using hne

theorem rightMovesOfRounds_ne_nil
    {In₁ : Type u} {In₂ : Type v}
    {rounds : List (EnvironmentRound In₁ In₂)}
    (hne : rounds ≠ []) : rightMovesOfRounds rounds ≠ [] := by
  simpa [rightMovesOfRounds] using hne

/-- Splitting off the final strict move before rebuilding preserves the whole
left-strict environment word. -/
theorem map_leftEnvironment_dropLast_append_getLast
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂)) (hne : rounds ≠ [])
    (hleft : ∀ round ∈ rounds, round.graph = .left) :
    (leftMovesOfRounds rounds).dropLast.map leftEnvironment ++
        [leftEnvironment
          ((leftMovesOfRounds rounds).getLast
            (leftMovesOfRounds_ne_nil hne))] = rounds := by
  change (leftMovesOfRounds rounds).dropLast.map leftEnvironment ++
      [((leftMovesOfRounds rounds).getLast
        (leftMovesOfRounds_ne_nil hne))].map leftEnvironment = rounds
  rw [← List.map_append]
  rw [List.dropLast_append_getLast]
  exact map_leftEnvironment_leftMovesOfRounds rounds hleft

/-- Right mirror of the final-move split lemma. -/
theorem map_rightEnvironment_dropLast_append_getLast
    {In₁ : Type u} {In₂ : Type v}
    (rounds : List (EnvironmentRound In₁ In₂)) (hne : rounds ≠ [])
    (hright : ∀ round ∈ rounds, round.graph = .right) :
    (rightMovesOfRounds rounds).dropLast.map rightEnvironment ++
        [rightEnvironment
          ((rightMovesOfRounds rounds).getLast
            (rightMovesOfRounds_ne_nil hne))] = rounds := by
  change (rightMovesOfRounds rounds).dropLast.map rightEnvironment ++
      [((rightMovesOfRounds rounds).getLast
        (rightMovesOfRounds_ne_nil hne))].map rightEnvironment = rounds
  rw [← List.map_append]
  rw [List.dropLast_append_getLast]
  exact map_rightEnvironment_rightMovesOfRounds rounds hright

/-! ## Chosen strict/both slices at every recurrent cut -/

/-- The canonical split supplied by `exists_strictGroupCut_split`. -/
noncomputable def strictGroupSplit
    (graphs : Nat → Graph) (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k : Nat) : Nat :=
  (exists_strictGroupCut_split hstarts hzero k).choose

theorem strictGroupCut_lt_split
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k : Nat) :
    strictGroupCuts graphs hstarts k <
      strictGroupSplit graphs hstarts hzero k :=
  (exists_strictGroupCut_split hstarts hzero k).choose_spec.1

theorem strictGroupSplit_le_nextCut
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k : Nat) :
    strictGroupSplit graphs hstarts hzero k ≤
      strictGroupCuts graphs hstarts (k + 1) :=
  (exists_strictGroupCut_split hstarts hzero k).choose_spec.2.1

theorem graph_eq_cutGraph_before_strictGroupSplit
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k n : Nat)
    (hlower : strictGroupCuts graphs hstarts k ≤ n)
    (hupper : n < strictGroupSplit graphs hstarts hzero k) :
    graphs n = graphs (strictGroupCuts graphs hstarts k) :=
  (exists_strictGroupCut_split hstarts hzero k).choose_spec.2.2.1
    n hlower hupper

theorem graph_eq_both_after_strictGroupSplit
    {graphs : Nat → Graph} (hstarts : StrictGroupStartsRecurrent graphs)
    (hzero : StrictGroupStart graphs 0) (k n : Nat)
    (hlower : strictGroupSplit graphs hstarts hzero k ≤ n)
    (hupper : n < strictGroupCuts graphs hstarts (k + 1)) :
    graphs n = .both :=
  (exists_strictGroupCut_split hstarts hzero k).choose_spec.2.2.2
    n hlower hupper

/-- Literal nonempty strict prefix of group `k`. -/
noncomputable def strictGroupStrictRounds
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    List (EnvironmentRound In₁ In₂) :=
  environmentSlice env
    (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)
    (strictGroupSplit (fun n ↦ (env n).graph) hstarts hzero k)

/-- Literal simultaneous suffix of group `k`. -/
noncomputable def strictGroupBothRounds
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    List (EnvironmentRound In₁ In₂) :=
  environmentSlice env
    (strictGroupSplit (fun n ↦ (env n).graph) hstarts hzero k)
    (strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1))

theorem strictGroupStrictRounds_ne_nil
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    strictGroupStrictRounds env hstarts hzero k ≠ [] := by
  intro hempty
  have hlength := congrArg List.length hempty
  simp only [strictGroupStrictRounds, environmentSlice_length,
    List.length_nil] at hlength
  have := strictGroupCut_lt_split hstarts hzero k
  omega

theorem strictGroupStrictRounds_graph
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat)
    (round : EnvironmentRound In₁ In₂)
    (hmem : round ∈ strictGroupStrictRounds env hstarts hzero k) :
    round.graph =
      (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)).graph := by
  simp only [strictGroupStrictRounds, environmentSlice, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  exact graph_eq_cutGraph_before_strictGroupSplit hstarts hzero k
    _ (by omega) (by omega)

theorem strictGroupBothRounds_graph
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat)
    (round : EnvironmentRound In₁ In₂)
    (hmem : round ∈ strictGroupBothRounds env hstarts hzero k) :
    round.graph = .both := by
  simp only [strictGroupBothRounds, environmentSlice, List.mem_ofFn] at hmem
  rcases hmem with ⟨i, rfl⟩
  exact graph_eq_both_after_strictGroupSplit hstarts hzero k
    _ (by omega) (by omega)

/-- Proof-side orientation associated with a strict graph.  The `.both` value
is irrelevant and is never used at a recurrent strict-group cut. -/
def strictGraphSide : Graph → DetParityAutomaton.IndexedLineageSide
  | .left => .left
  | .right => .right
  | .both => .left

theorem strictGraphSide_other_of_strict_ne
    {current next : Graph} (hcurrent : current ≠ .both)
    (hnext : next ≠ .both) (hne : next ≠ current) :
    strictGraphSide next = (strictGraphSide current).other := by
  cases current <;> cases next <;>
    simp_all [strictGraphSide,
      DetParityAutomaton.IndexedLineageSide.other]

/-- An empty simultaneous suffix means the next strict group is a direct
reversal, hence its proof-side orientation is opposite. -/
theorem strictGraphSide_nextCut_of_bothRounds_nil
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat)
    (hempty : strictGroupBothRounds env hstarts hzero k = []) :
    strictGraphSide
        (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1))).graph =
      (strictGraphSide
        (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)).graph).other := by
  let graphs := fun n ↦ (env n).graph
  let c := strictGroupCuts graphs hstarts k
  let d := strictGroupCuts graphs hstarts (k + 1)
  let split := strictGroupSplit graphs hstarts hzero k
  have hsplitEq : split = d := by
    have hlength := congrArg List.length hempty
    simp only [strictGroupBothRounds, environmentSlice_length,
      List.length_nil] at hlength
    have hle := strictGroupSplit_le_nextCut hstarts hzero k
    dsimp only [graphs, split, d] at hlength hle ⊢
    omega
  have hcStart : StrictGroupStart graphs c :=
    strictGroupStart_strictGroupCuts hstarts hzero k
  have hdStart : StrictGroupStart graphs d :=
    strictGroupStart_strictGroupCuts hstarts hzero (k + 1)
  have hcd : c < d := strictGroupCuts_strictMono graphs hstarts
    (Nat.lt_succ_self k)
  have hpred : graphs (d - 1) = graphs c := by
    apply graph_eq_cutGraph_before_strictGroupSplit hstarts hzero k
    · dsimp only [graphs, c, d, split] at hcd hsplitEq ⊢
      omega
    · dsimp only [graphs, c, d, split] at hcd hsplitEq ⊢
      omega
  have hdne : graphs d ≠ graphs c := by
    have hdzero : d ≠ 0 := by omega
    have hprevDiff := hdStart.2.resolve_left hdzero
    rw [hpred] at hprevDiff
    exact fun heq ↦ hprevDiff heq.symm
  exact strictGraphSide_other_of_strict_ne hcStart.1 hdStart.1 hdne

/-! ## Automatic signed recuts -/

namespace DetParityAutomaton

/-- Boundary row propagated by the simultaneous suffix of the preceding
strict group. -/
noncomputable def recurrentStrictGroupRow
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) :
    Nat → PairedEntryRow
  | 0 => .first
  | k + 1 => pairedGapNextRow (strictGroupBothRounds env hstarts hzero k)

@[simp] theorem recurrentStrictGroupRow_zero
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) :
    recurrentStrictGroupRow env hstarts hzero 0 = .first :=
  rfl

@[simp] theorem recurrentStrictGroupRow_succ
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    recurrentStrictGroupRow env hstarts hzero (k + 1) =
      pairedGapNextRow (strictGroupBothRounds env hstarts hzero k) :=
  rfl

/-- The concrete signed recut attached to one automatically extracted strict
group.  Its side is proof-side metadata read from the actual strict graph;
neither process is asked to know it. -/
noncomputable def recurrentStrictSignedGap
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    PairedSignedFiniteRecut In₁ In₂ := by
  let graphs := fun n ↦ (env n).graph
  let c := strictGroupCuts graphs hstarts k
  let d := strictGroupCuts graphs hstarts (k + 1)
  let strictRounds := strictGroupStrictRounds env hstarts hzero k
  let boths := strictGroupBothRounds env hstarts hzero k
  let nextSide := strictGraphSide (env d).graph
  have hne : strictRounds ≠ [] :=
    strictGroupStrictRounds_ne_nil env hstarts hzero k
  have hboth : ∀ round ∈ boths, round.graph = .both := by
    intro round hround
    exact strictGroupBothRounds_graph env hstarts hzero k round hround
  have hcurrent : graphs c ≠ .both :=
    (strictGroupStart_strictGroupCuts hstarts hzero k).1
  by_cases hleft : graphs c = .left
  · exact pairedSignedLeftGapRecut
        (recurrentStrictGroupRow env hstarts hzero k)
        (leftMovesOfRounds strictRounds).dropLast
        ((leftMovesOfRounds strictRounds).getLast
          (leftMovesOfRounds_ne_nil hne))
        boths (env d) nextSide
        (by
          intro hempty
          have hside := strictGraphSide_nextCut_of_bothRounds_nil
            env hstarts hzero k hempty
          simpa [graphs, c, d, nextSide, hleft, strictGraphSide,
            IndexedLineageSide.other] using hside)
        hboth
  · have hright : graphs c = .right := by
      cases hgraph : graphs c <;> simp_all
    exact pairedSignedRightGapRecut
        (recurrentStrictGroupRow env hstarts hzero k)
        (rightMovesOfRounds strictRounds).dropLast
        ((rightMovesOfRounds strictRounds).getLast
          (rightMovesOfRounds_ne_nil hne))
        boths (env d) nextSide
        (by
          intro hempty
          have hside := strictGraphSide_nextCut_of_bothRounds_nil
            env hstarts hzero k hempty
          simpa [graphs, c, d, nextSide, hright, strictGraphSide,
            IndexedLineageSide.other] using hside)
        hboth

/-- Starting signature of an automatically extracted recut. -/
theorem recurrentStrictSignedGap_currentSignature
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    (recurrentStrictSignedGap env hstarts hzero k).currentSignature =
      (strictGraphSide
          (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)).graph,
        recurrentStrictGroupRow env hstarts hzero k) := by
  let graphs := fun n ↦ (env n).graph
  let c := strictGroupCuts graphs hstarts k
  have hcurrent : graphs c ≠ .both :=
    (strictGroupStart_strictGroupCuts hstarts hzero k).1
  by_cases hleft : graphs c = .left
  · simp [recurrentStrictSignedGap, graphs, c, hleft, strictGraphSide,
      pairedSignedLeftGapRecut]
  · have hright : graphs c = .right := by
      cases hgraph : graphs c <;> simp_all
    simp [recurrentStrictSignedGap, graphs, c, hleft, hright,
      strictGraphSide, pairedSignedRightGapRecut]

/-- Ending signature is exactly the next cut's side and recursively propagated
row. -/
theorem recurrentStrictSignedGap_nextSignature
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    (recurrentStrictSignedGap env hstarts hzero k).nextSignature =
      (strictGraphSide
          (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1))).graph,
        recurrentStrictGroupRow env hstarts hzero (k + 1)) := by
  let graphs := fun n ↦ (env n).graph
  let c := strictGroupCuts graphs hstarts k
  have hcurrent : graphs c ≠ .both :=
    (strictGroupStart_strictGroupCuts hstarts hzero k).1
  by_cases hleft : graphs c = .left
  · simp [recurrentStrictSignedGap, graphs, c, hleft,
      recurrentStrictGroupRow, pairedSignedLeftGapRecut]
  · have hright : graphs c = .right := by
      cases hgraph : graphs c <;> simp_all
    simp [recurrentStrictSignedGap, graphs, c, hleft, hright,
      recurrentStrictGroupRow, pairedSignedRightGapRecut]

/-- The physical word stored by the automatic signed recut is exactly the
half-open environment slice between consecutive strict-group cuts. -/
theorem recurrentStrictSignedGap_physicalWord
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    (recurrentStrictSignedGap env hstarts hzero k).physicalWord =
      environmentSlice env
        (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)
        (strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1)) := by
  let graphs := fun n ↦ (env n).graph
  let c := strictGroupCuts graphs hstarts k
  let d := strictGroupCuts graphs hstarts (k + 1)
  let split := strictGroupSplit graphs hstarts hzero k
  let strictRounds := strictGroupStrictRounds env hstarts hzero k
  let boths := strictGroupBothRounds env hstarts hzero k
  have hne : strictRounds ≠ [] :=
    strictGroupStrictRounds_ne_nil env hstarts hzero k
  have hstartSplit : c ≤ split :=
    (strictGroupCut_lt_split hstarts hzero k).le
  have hsplitStop : split ≤ d :=
    strictGroupSplit_le_nextCut hstarts hzero k
  have happend : environmentSlice env c d = strictRounds ++ boths := by
    simpa [strictRounds, boths, c, d, split, graphs] using
      environmentSlice_append env hstartSplit hsplitStop
  have hcurrent : graphs c ≠ .both :=
    (strictGroupStart_strictGroupCuts hstarts hzero k).1
  by_cases hleft : graphs c = .left
  · have hleftRounds : ∀ round ∈ strictRounds,
        round.graph = .left := by
      intro round hround
      rw [strictGroupStrictRounds_graph env hstarts hzero k round hround]
      exact hleft
    have hrebuild := map_leftEnvironment_dropLast_append_getLast
      strictRounds hne hleftRounds
    have hleft' :
        (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)).graph =
          .left := by
      simpa [graphs, c] using hleft
    simp only [recurrentStrictSignedGap]
    rw [dif_pos hleft']
    change (leftMovesOfRounds strictRounds).dropLast.map leftEnvironment ++
        [leftEnvironment ((leftMovesOfRounds strictRounds).getLast
          (leftMovesOfRounds_ne_nil hne))] ++ boths =
      environmentSlice env c d
    rw [hrebuild]
    exact happend.symm
  · have hright : graphs c = .right := by
      cases hgraph : graphs c <;> simp_all
    have hrightRounds : ∀ round ∈ strictRounds,
        round.graph = .right := by
      intro round hround
      rw [strictGroupStrictRounds_graph env hstarts hzero k round hround]
      exact hright
    have hrebuild := map_rightEnvironment_dropLast_append_getLast
      strictRounds hne hrightRounds
    have hleft' : ¬
        (env (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)).graph =
          .left := by
      simpa [graphs, c] using hleft
    simp only [recurrentStrictSignedGap]
    rw [dif_neg hleft']
    change (rightMovesOfRounds strictRounds).dropLast.map rightEnvironment ++
        [rightEnvironment ((rightMovesOfRounds strictRounds).getLast
          (rightMovesOfRounds_ne_nil hne))] ++ boths =
      environmentSlice env c d
    rw [hrebuild]
    exact happend.symm

/-- All automatically extracted strict groups form one signature-coherent
productive signed stream. -/
noncomputable def recurrentStrictSignedRecutStream
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) :
    PairedSignedRecutStream In₁ In₂ where
  gap k := recurrentStrictSignedGap env hstarts hzero k
  signature_overlap k := by
    rw [recurrentStrictSignedGap_nextSignature,
      recurrentStrictSignedGap_currentSignature]

@[simp] theorem recurrentStrictSignedRecutStream_gap
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    (recurrentStrictSignedRecutStream env hstarts hzero).gap k =
      recurrentStrictSignedGap env hstarts hzero k :=
  rfl

/-- The finite stream segment stores exactly the corresponding original
environment slice. -/
theorem recurrentStrictFiniteRecutStream_segment_physicalWord
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) (k : Nat) :
    (((recurrentStrictSignedRecutStream env hstarts hzero).toFiniteRecutStream).segment k).physicalWord =
      environmentSlice env
        (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)
        (strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1)) := by
  exact recurrentStrictSignedGap_physicalWord env hstarts hzero k

/-- Real-round cuts generated by flattening the signed recuts are exactly the
original strict-group cuts. -/
theorem recurrentStrictFiniteRecutStream_physicalCuts
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) : ∀ k : Nat,
    ((recurrentStrictSignedRecutStream env hstarts hzero).toFiniteRecutStream).physicalCuts
        k =
      strictGroupCuts (fun n ↦ (env n).graph) hstarts k
  | 0 => rfl
  | k + 1 => by
      rw [PairedFiniteRecutStream.physicalCuts_succ]
      rw [recurrentStrictFiniteRecutStream_physicalCuts env hstarts hzero k]
      rw [recurrentStrictFiniteRecutStream_segment_physicalWord]
      simp only [environmentSlice_length]
      have hmono :
          strictGroupCuts (fun n ↦ (env n).graph) hstarts k <
            strictGroupCuts (fun n ↦ (env n).graph) hstarts (k + 1) := by
        simpa only [Nat.succ_eq_add_one] using
          strictGroupCuts_strictMono
            (fun n ↦ (env n).graph) hstarts (Nat.lt_succ_self k)
      omega

/-- Concatenating the first `k` automatic segment words gives precisely the
original environment prefix ending at strict-group cut `k`. -/
theorem recurrentStrictFiniteRecutStream_physicalWordsPrefix
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) : ∀ k : Nat,
    ((recurrentStrictSignedRecutStream env hstarts hzero).toFiniteRecutStream).physicalWordsPrefix
        k =
      environmentSlice env 0
        (strictGroupCuts (fun n ↦ (env n).graph) hstarts k)
  | 0 => rfl
  | k + 1 => by
      rw [PairedFiniteRecutStream.physicalWordsPrefix_succ]
      rw [recurrentStrictFiniteRecutStream_physicalWordsPrefix
        env hstarts hzero k]
      rw [recurrentStrictFiniteRecutStream_segment_physicalWord]
      rw [← environmentSlice_append env]
      · exact Nat.zero_le _
      · exact (strictGroupCuts_strictMono
          (fun n ↦ (env n).graph) hstarts (Nat.lt_succ_self k)).le

/-- Automatic productive decomposition for any environment whose zero round
is a strict-group start and whose later strict-group starts are recurrent. -/
noncomputable def recurrentProductiveStrictGapDecomposition
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) :
    PairedSignedRecutStream.ProductiveStrictGapDecomposition In₁ In₂ where
  recuts := recurrentStrictSignedRecutStream env hstarts hzero
  environment := env
  exact_prefix k := by
    rw [recurrentStrictFiniteRecutStream_physicalCuts env hstarts hzero k]
    rw [recurrentStrictFiniteRecutStream_physicalWordsPrefix env hstarts hzero k]
    exact (environmentSlice_zero_eq_omegaPrefix env _).symm

/-- Flattening the automatically extracted recurrent recuts recovers the
original environment literally. -/
theorem recurrentStrict_pairedBranchEnvironment_eq_original
    {In₁ : Type u} {In₂ : Type v}
    (env : EnvironmentSequence In₁ In₂)
    (hstarts : StrictGroupStartsRecurrent (fun n ↦ (env n).graph))
    (hzero : StrictGroupStart (fun n ↦ (env n).graph) 0) :
    pairedBranchEnvironment
        (((recurrentStrictSignedRecutStream env hstarts hzero).toFiniteRecutStream).branch) =
      env :=
  PairedSignedRecutStream.ProductiveStrictGapDecomposition.pairedBranchEnvironment_eq_original
    (recurrentProductiveStrictGapDecomposition env hstarts hzero)

/-- Complete automatic extraction in the recurrent-`.both` regime.  After an
explicit finite prefix shift, either the suffix is all simultaneous and uses
the existing all-both branch, or it has a fully automatic productive strict
gap decomposition whose flattened branch is literally that suffix. -/
theorem graphBothRecurrent_automatic_recut
    {In₁ : Type u} {In₂ : Type v}
    [Fintype In₁] [Fintype In₂]
    [Inhabited In₁] [Inhabited In₂]
    [DecidableEq In₁] [DecidableEq In₂]
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    ∃ start : Nat,
      (∀ initialSide : IndexedLineageSide,
        pairedBranchEnvironment
            (profiledOpenAllBothDirection (OmegaWord.drop env start)
              initialSide) =
          OmegaWord.drop env start) ∨
      (∃ decomposition :
          PairedSignedRecutStream.ProductiveStrictGapDecomposition In₁ In₂,
        decomposition.environment = OmegaWord.drop env start ∧
          pairedBranchEnvironment decomposition.recuts.toFiniteRecutStream.branch =
            OmegaWord.drop env start) := by
  rcases graphBothRecurrent_split (fun n ↦ (env n).graph) hboth with
      hall | ⟨_, hstarts⟩
  · rcases exists_allBothTail_pairedBranch env hall with ⟨start, htail⟩
    exact ⟨start, Or.inl htail⟩
  · rcases exists_drop_strictGroupStart_zero_and_recurrent hstarts with
      ⟨start, hzero, hstartsTail⟩
    let tail : EnvironmentSequence In₁ In₂ := OmegaWord.drop env start
    have hzero' : StrictGroupStart (fun n ↦ (tail n).graph) 0 := by
      simpa [tail, OmegaWord.drop] using hzero
    have hstarts' :
        StrictGroupStartsRecurrent (fun n ↦ (tail n).graph) := by
      simpa [tail, OmegaWord.drop] using hstartsTail
    let decomposition :=
      recurrentProductiveStrictGapDecomposition tail hstarts' hzero'
    refine ⟨start, Or.inr ⟨decomposition, rfl, ?_⟩⟩
    exact recurrentStrict_pairedBranchEnvironment_eq_original
      tail hstarts' hzero'

end DetParityAutomaton

end DistributedSynthesis
