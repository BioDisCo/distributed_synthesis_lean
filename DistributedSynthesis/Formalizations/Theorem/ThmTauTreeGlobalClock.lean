/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeGlobalPlay
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRegimeA
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeRegimeC
import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeChainSegment
import DistributedSynthesis.Formalizations.Theorem.ThmTreeToReadback
import DistributedSynthesis.Formalizations.Theorem.ThmRouteBAcceptance

/-!
# The global play: extraction, clock, and the regime (a) endpoint

Between two consecutive boundaries of a never-sinking branch, the
branch is a synchronizing round or a block closed by an atom
direction; the segment extraction turns each shape into a
`SegmentSpec` via the subset-membership inversions and the
thread-trace inversions.  The clock concatenates the segments into one
infinite winner-consistent play from the initial boundary, whose
min-even parity (the winner is winning) transfers to the boundary-atom
priority subsequence: boundary priorities recur in the play at the
segment starts, and every interior play priority dominates the next
boundary's.  Together with the shift-domination reduction of
`ThmTauTreeRegimeA.lean` and the trapped regimes of
`ThmTauTreeRegimeB.lean`, this closes the tau-tree acceptance.
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
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
variable (σ : StrategyPair In₁ In₂ Out₁ Out₂)
variable
  (τ :
    (uniformizationGame A σ).PositionalStrategy ParityPlayer.even)
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/-! ### Segment extraction between consecutive boundaries -/

/-! ### The boundary atoms and the segment clock -/

section Clock

variable (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
variable
  (hns :
    ∀ m, branchRun σ τ CL CR CC branch m ≠
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
variable
  (hinf : ∀ N, ∃ n, N ≤ n ∧ IsBranchBoundary σ τ CL CR CC branch n)

/-- The atom at the `k`-th boundary. -/
noncomputable def atomAt (k : Nat) : A.State × A.State :=
  (isBranchBoundary_branchBoundaryIndex σ τ CL CR CC branch hinf k).choose

theorem atomAt_spec (k : Nat) :
    branchRun σ τ CL CR CC branch
        (branchBoundaryIndex σ τ CL CR CC branch hinf k) =
      Sum.inl (atomAt σ τ CL CR CC branch hinf k) :=
  (isBranchBoundary_branchBoundaryIndex σ τ CL CR CC branch hinf k).choose_spec

theorem atomAt_zero :
    atomAt σ τ CL CR CC branch hinf 0 = (A.initial, A.initial) := by
  have h := atomAt_spec σ τ CL CR CC branch hinf 0
  have h0 :
      branchRun σ τ CL CR CC branch
          (branchBoundaryIndex σ τ CL CR CC branch hinf 0) =
        Sum.inl ((A.initial, A.initial) : A.State × A.State) :=
    rfl
  exact (Sum.inl.inj (h0.symm.trans h)).symm

theorem branchBoundaryPriority_eq_atomAt (k : Nat) :
    branchBoundaryPriority σ τ CL CR CC branch hinf k =
      A.priority (atomAt σ τ CL CR CC branch hinf k).2 := by
  unfold branchBoundaryPriority
  rw [atomAt_spec σ τ CL CR CC branch hinf k]
  rfl

theorem no_boundary_between (k : Nat) :
    ∀ m, branchBoundaryIndex σ τ CL CR CC branch hinf k < m ->
      m < branchBoundaryIndex σ τ CL CR CC branch hinf (k + 1) ->
      ∀ atom, branchRun σ τ CL CR CC branch m ≠ Sum.inl atom := by
  intro m h1 h2 atom hcon
  have hle :
      branchBoundaryIndex σ τ CL CR CC branch hinf (k + 1) ≤ m :=
    nextBranchBoundary_le σ τ CL CR CC branch hinf h1 ⟨atom, hcon⟩
  omega

/-- The chosen segment between consecutive boundaries. -/
noncomputable def segAt (k : Nat) :
    SegmentSpec σ τ (atomAt σ τ CL CR CC branch hinf k)
      (atomAt σ τ CL CR CC branch hinf (k + 1)) :=
  (exists_segmentSpec_of_boundary_pair CL CR CC σ τ branch hns
      (branchBoundaryIndex σ τ CL CR CC branch hinf k)
      (branchBoundaryIndex σ τ CL CR CC branch hinf (k + 1))
      (atomAt σ τ CL CR CC branch hinf k)
      (atomAt σ τ CL CR CC branch hinf (k + 1))
      (atomAt_spec σ τ CL CR CC branch hinf k)
      (atomAt_spec σ τ CL CR CC branch hinf (k + 1))
      (branchBoundaryIndex_lt_succ σ τ CL CR CC branch hinf k)
      (no_boundary_between σ τ CL CR CC branch hinf k)).some

/-- The cumulative segment clock. -/
noncomputable def cum : Nat -> Nat
  | 0 => 0
  | k + 1 => cum k + (segAt σ τ CL CR CC branch hns hinf k).len

theorem cum_lt_succ (k : Nat) :
    cum σ τ CL CR CC branch hns hinf k <
      cum σ τ CL CR CC branch hns hinf (k + 1) := by
  have h := (segAt σ τ CL CR CC branch hns hinf k).len_pos
  show
    cum σ τ CL CR CC branch hns hinf k <
      cum σ τ CL CR CC branch hns hinf k +
        (segAt σ τ CL CR CC branch hns hinf k).len
  omega

theorem le_cum (k : Nat) : k ≤ cum σ τ CL CR CC branch hns hinf k := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih =>
      have h := cum_lt_succ σ τ CL CR CC branch hns hinf k
      omega

theorem cum_le_cum {j k : Nat} (h : j ≤ k) :
    cum σ τ CL CR CC branch hns hinf j ≤
      cum σ τ CL CR CC branch hns hinf k := by
  induction k with
  | zero =>
      rw [Nat.le_zero.mp h]
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · have h1 := ih (by omega)
        have h2 := cum_lt_succ σ τ CL CR CC branch hns hinf k
        omega
      · rw [Nat.le_antisymm h hge]

/-- The segment index of a play round. -/
noncomputable def segIdx (m : Nat) : Nat :=
  letI :
      DecidablePred fun k => cum σ τ CL CR CC branch hns hinf k ≤ m :=
    fun _ => Classical.propDecidable _
  Nat.findGreatest (fun k => cum σ τ CL CR CC branch hns hinf k ≤ m) m

theorem cum_segIdx_le (m : Nat) :
    cum σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m) ≤
      m := by
  letI :
      DecidablePred fun k => cum σ τ CL CR CC branch hns hinf k ≤ m :=
    fun _ => Classical.propDecidable _
  unfold segIdx
  exact
    Nat.findGreatest_spec
      (P := fun k => cum σ τ CL CR CC branch hns hinf k ≤ m)
      (Nat.zero_le m)
      (show cum σ τ CL CR CC branch hns hinf 0 ≤ m from Nat.zero_le m)

theorem lt_cum_segIdx_succ (m : Nat) :
    m <
      cum σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m + 1) := by
  letI :
      DecidablePred fun k => cum σ τ CL CR CC branch hns hinf k ≤ m :=
    fun _ => Classical.propDecidable _
  by_contra hcon
  push Not at hcon
  have hb :
      segIdx σ τ CL CR CC branch hns hinf m + 1 ≤ m := by
    have := le_cum σ τ CL CR CC branch hns hinf
      (segIdx σ τ CL CR CC branch hns hinf m + 1)
    omega
  have hng :
      ¬ cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m + 1) ≤
        m := by
    unfold segIdx
    unfold segIdx at hb
    exact
      Nat.findGreatest_is_greatest
        (P := fun k => cum σ τ CL CR CC branch hns hinf k ≤ m)
        (Nat.lt_succ_self _) hb
  exact hng hcon

theorem le_segIdx {k m : Nat}
    (h : cum σ τ CL CR CC branch hns hinf k ≤ m) :
    k ≤ segIdx σ τ CL CR CC branch hns hinf m := by
  letI :
      DecidablePred fun j => cum σ τ CL CR CC branch hns hinf j ≤ m :=
    fun _ => Classical.propDecidable _
  unfold segIdx
  exact
    Nat.le_findGreatest
      (Nat.le_trans (le_cum σ τ CL CR CC branch hns hinf k) h) h

theorem segIdx_le {k m : Nat}
    (h : m < cum σ τ CL CR CC branch hns hinf (k + 1)) :
    segIdx σ τ CL CR CC branch hns hinf m ≤ k := by
  by_contra hcon
  push Not at hcon
  have h1 :
      cum σ τ CL CR CC branch hns hinf (k + 1) ≤
        cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m) :=
    cum_le_cum σ τ CL CR CC branch hns hinf (by omega)
  have h2 := cum_segIdx_le σ τ CL CR CC branch hns hinf m
  omega

theorem segIdx_cum (k : Nat) :
    segIdx σ τ CL CR CC branch hns hinf
        (cum σ τ CL CR CC branch hns hinf k) =
      k :=
  Nat.le_antisymm
    (segIdx_le σ τ CL CR CC branch hns hinf
      (cum_lt_succ σ τ CL CR CC branch hns hinf k))
    (le_segIdx σ τ CL CR CC branch hns hinf (Nat.le_refl _))

/-- The global play: the concatenation of the per-boundary segments. -/
noncomputable def gPlay (m : Nat) :
    UniformizationPosition (In₁ := In₁) A :=
  (segAt σ τ CL CR CC branch hns hinf
      (segIdx σ τ CL CR CC branch hns hinf m)).play
    (m - cum σ τ CL CR CC branch hns hinf
      (segIdx σ τ CL CR CC branch hns hinf m))

theorem gPlay_cum (k : Nat) :
    gPlay σ τ CL CR CC branch hns hinf
        (cum σ τ CL CR CC branch hns hinf k) =
      .bnd (atomAt σ τ CL CR CC branch hinf k) := by
  unfold gPlay
  rw [segIdx_cum σ τ CL CR CC branch hns hinf k, Nat.sub_self]
  exact (segAt σ τ CL CR CC branch hns hinf k).play_zero

/-- One step of the clock: the next play position is the current
segment's next position (through the glue at segment ends). -/
theorem gPlay_succ (m : Nat) :
    gPlay σ τ CL CR CC branch hns hinf (m + 1) =
      (segAt σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m)).play
        (m - cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m) + 1) := by
  have h1 := cum_segIdx_le σ τ CL CR CC branch hns hinf m
  have h2 := lt_cum_segIdx_succ σ τ CL CR CC branch hns hinf m
  have hlen :
      cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m + 1) =
        cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m) +
          (segAt σ τ CL CR CC branch hns hinf
              (segIdx σ τ CL CR CC branch hns hinf m)).len :=
    rfl
  by_cases hc :
      m + 1 <
        cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m + 1)
  · have hidx :
        segIdx σ τ CL CR CC branch hns hinf (m + 1) =
          segIdx σ τ CL CR CC branch hns hinf m :=
      Nat.le_antisymm
        (segIdx_le σ τ CL CR CC branch hns hinf hc)
        (le_segIdx σ τ CL CR CC branch hns hinf (by omega))
    show
      (segAt σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf (m + 1))).play
        (m + 1 - cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf (m + 1))) =
        _
    rw [hidx]
    congr 1
    omega
  · have hce :
        m + 1 =
          cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m + 1) := by
      omega
    have hidx :
        segIdx σ τ CL CR CC branch hns hinf (m + 1) =
          segIdx σ τ CL CR CC branch hns hinf m + 1 := by
      rw [hce, segIdx_cum]
    show
      (segAt σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf (m + 1))).play
        (m + 1 - cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf (m + 1))) =
        _
    rw [hidx,
      show
        m + 1 - cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m + 1) =
          0 from by omega,
      (segAt σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m + 1)).play_zero,
      show
        m - cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m) + 1 =
          (segAt σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m)).len from by omega,
      (segAt σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m)).play_len]

theorem gPlay_playFrom :
    (uniformizationGame A σ).PlayFrom (.bnd (A.initial, A.initial))
      (gPlay σ τ CL CR CC branch hns hinf) := by
  constructor
  · have h := gPlay_cum σ τ CL CR CC branch hns hinf 0
    rw [atomAt_zero σ τ CL CR CC branch hinf] at h
    exact h
  · intro m
    rw [gPlay_succ σ τ CL CR CC branch hns hinf m]
    exact
      (segAt σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m)).step
        (m - cum σ τ CL CR CC branch hns hinf
          (segIdx σ τ CL CR CC branch hns hinf m))
        (by
          have h1 := cum_segIdx_le σ τ CL CR CC branch hns hinf m
          have h2 := lt_cum_segIdx_succ σ τ CL CR CC branch hns hinf m
          have hlen :
              cum σ τ CL CR CC branch hns hinf
                  (segIdx σ τ CL CR CC branch hns hinf m + 1) =
                cum σ τ CL CR CC branch hns hinf
                    (segIdx σ τ CL CR CC branch hns hinf m) +
                  (segAt σ τ CL CR CC branch hns hinf
                      (segIdx σ τ CL CR CC branch hns hinf m)).len :=
            rfl
          omega)

theorem gPlay_consistent :
    CountableParityGame.PositionalStrategy.Consistent
      (G := uniformizationGame A σ) τ
      (gPlay σ τ CL CR CC branch hns hinf) := by
  intro m howner
  rw [gPlay_succ σ τ CL CR CC branch hns hinf m]
  exact
    (segAt σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m)).consistent
      (m - cum σ τ CL CR CC branch hns hinf
        (segIdx σ τ CL CR CC branch hns hinf m))
      (by
        have h1 := cum_segIdx_le σ τ CL CR CC branch hns hinf m
        have h2 := lt_cum_segIdx_succ σ τ CL CR CC branch hns hinf m
        have hlen :
            cum σ τ CL CR CC branch hns hinf
                (segIdx σ τ CL CR CC branch hns hinf m + 1) =
              cum σ τ CL CR CC branch hns hinf
                  (segIdx σ τ CL CR CC branch hns hinf m) +
                (segAt σ τ CL CR CC branch hns hinf
                    (segIdx σ τ CL CR CC branch hns hinf m)).len :=
          rfl
        omega)
      howner

/-! ### The parity transfer to the boundary subsequence -/

include hns in
/-- The boundary-atom priority subsequence of a never-sinking branch
with recurring boundaries is min-even: the global play is winning, its
priorities dominate the following boundary within each segment, and
each boundary priority recurs at the segment starts. -/
theorem boundary_priorities_min_even
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (branchBoundaryPriority σ τ CL CR CC branch hinf) := by
  have hplay :
      (uniformizationGame A σ).MinPriorityEven
        (gPlay σ τ CL CR CC branch hns hinf) :=
    hwin _ (gPlay_playFrom σ τ CL CR CC branch hns hinf)
      (gPlay_consistent σ τ CL CR CC branch hns hinf)
  have hs :
      NatSeqMinEvenParity
        (fun m =>
          (uniformizationGame A σ).priority
            (gPlay σ τ CL CR CC branch hns hinf m)) :=
    hplay
  refine
    (natSeqMinEvenParity_iff_of_recurring_transfer
      (branchBoundaryPriority σ τ CL CR CC branch hinf)
      (fun m =>
        (uniformizationGame A σ).priority
          (gPlay σ τ CL CR CC branch hns hinf m))
      ?_ ?_).mpr hs
  · -- boundary priorities recur at segment starts
    intro w hw m0
    obtain ⟨k, hk, hval⟩ := hw m0
    refine
      ⟨cum σ τ CL CR CC branch hns hinf k,
        Nat.le_trans hk (le_cum σ τ CL CR CC branch hns hinf k), ?_⟩
    show
      (uniformizationGame A σ).priority
          (gPlay σ τ CL CR CC branch hns hinf
            (cum σ τ CL CR CC branch hns hinf k)) =
        w
    rw [gPlay_cum σ τ CL CR CC branch hns hinf k]
    show A.priority (atomAt σ τ CL CR CC branch hinf k).2 = w
    rw [← branchBoundaryPriority_eq_atomAt σ τ CL CR CC branch hinf k]
    exact hval
  · -- recurring play priorities dominate a later boundary
    intro v hv m0
    obtain ⟨m, hm, hval⟩ :=
      hv (cum σ τ CL CR CC branch hns hinf (m0 + 1))
    have hk0 : m0 + 1 ≤ segIdx σ τ CL CR CC branch hns hinf m :=
      le_segIdx σ τ CL CR CC branch hns hinf hm
    have h1 := cum_segIdx_le σ τ CL CR CC branch hns hinf m
    have h2 := lt_cum_segIdx_succ σ τ CL CR CC branch hns hinf m
    have hlen :
        cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m + 1) =
          cum σ τ CL CR CC branch hns hinf
              (segIdx σ τ CL CR CC branch hns hinf m) +
            (segAt σ τ CL CR CC branch hns hinf
                (segIdx σ τ CL CR CC branch hns hinf m)).len :=
      rfl
    have hval' :
        (uniformizationGame A σ).priority
            (gPlay σ τ CL CR CC branch hns hinf m) =
          v :=
      hval
    by_cases ht :
        m - cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m) =
          0
    · refine ⟨segIdx σ τ CL CR CC branch hns hinf m, by omega, ?_⟩
      have hmc :
          m =
            cum σ τ CL CR CC branch hns hinf
              (segIdx σ τ CL CR CC branch hns hinf m) := by
        omega
      rw [branchBoundaryPriority_eq_atomAt]
      have hpm :
          (uniformizationGame A σ).priority
              (gPlay σ τ CL CR CC branch hns hinf m) =
            A.priority
              (atomAt σ τ CL CR CC branch hinf
                (segIdx σ τ CL CR CC branch hns hinf m)).2 := by
        conv_lhs =>
          rw [hmc,
            gPlay_cum σ τ CL CR CC branch hns hinf
              (segIdx σ τ CL CR CC branch hns hinf m)]
        rfl
      exact Nat.le_of_eq (hpm.symm.trans hval')
    · refine
        ⟨segIdx σ τ CL CR CC branch hns hinf m + 1, by omega, ?_⟩
      rw [branchBoundaryPriority_eq_atomAt]
      have hb :
          A.priority
              (atomAt σ τ CL CR CC branch hinf
                (segIdx σ τ CL CR CC branch hns hinf m + 1)).2 ≤
            (uniformizationGame A σ).priority
              (gPlay σ τ CL CR CC branch hns hinf m) :=
        (segAt σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m)).bound
          (m - cum σ τ CL CR CC branch hns hinf
            (segIdx σ τ CL CR CC branch hns hinf m))
          (by omega) (by omega)
      exact Nat.le_trans hb (Nat.le_of_eq hval')

include hns hinf in
/-- Regime (a) closed: a never-sinking branch with recurring
boundaries has min-even run priorities. -/
theorem tauTree_priorities_min_even_of_recurring
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC (tauTree σ τ)
            (Sum.inl (A.initial, A.initial)) (branchNode branch n))) :=
  branch_min_even_of_boundary_subseq σ τ CL CR CC branch hinf hns
    (boundary_priorities_min_even σ τ CL CR CC branch hns hinf hwin)

end Clock

/-! ### The acceptance -/

/-- The global journal automaton accepts the winner's tree: the sink
regime is even by construction, the recurring-boundary regime is paid
by the global play through the segment extraction
(`ThmTauTreeChainSegment.lean`), the trapped regimes by the checker
verdicts, and the chain tail by the chain checker's verdict at the
first handoff set (`ThmTauTreeRegimeC.lean`). -/
theorem tauTree_acceptsTree
    (hwin :
      CountableParityGame.PositionalStrategy.WinningFrom
        (G := uniformizationGame A σ) τ
        (.bnd (A.initial, A.initial))) :
    (globalJournalAutomaton A CL CR CC).acceptsTree (tauTree σ τ) := by
  refine tauTree_acceptsTree_of_neverSink σ τ CL CR CC ?_
  intro branch hns
  rcases neverSink_classification σ τ CL CR CC branch hns with
    hinf | ⟨M, atom₀, leftInput, hrunM, htail⟩ |
    ⟨M, atom₀, rightInput, hrunM, htail⟩ | ⟨S, htail⟩
  · exact
      tauTree_priorities_min_even_of_recurring σ τ CL CR CC branch hns hinf
        hwin
  · exact
      tauTree_priorities_min_even_of_trapped_left CL CR CC σ τ branch M
        atom₀ leftInput hrunM htail hwin
  · exact
      tauTree_priorities_min_even_of_trapped_right CL CR CC σ τ branch M
        atom₀ rightInput hrunM htail hwin
  · exact
      tauTree_priorities_min_even_of_chain_tail CL CR CC σ τ branch S
        htail hwin

end DetParityAutomaton

/-! ### The fragment readback upgrade -/

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Countable In₁] [Countable In₂] [Countable Out₁] [Countable Out₂]
variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/--
A committed plan family whose journal readback wins the no-direct
fragment, packaged with the finite-control instances the readback
needs.
-/
structure JournalReadbackWitness where
  Control : Type s
  [controlFintype : Fintype Control]
  [controlDecEq : DecidableEq Control]
  [controlInhabited : Inhabited Control]
  plans :
    PlanFamily (In₁ := In₁) A (ULift.{max u v x y, s} Control)
      (ULift.{max u v x y, s} Control)
      (ULift.{max u v x y, s} Control)
  accepts :
    ∀ env : EnvironmentSequence In₁ In₂,
      NoDirectReversalSequence env ->
        A.Accepts (execution (journalStrategy plans) env)

include CL CR CC in
/--
The readback upgrade in dominance form, with the fragment conclusion
and no remaining acceptance obligations.  The chain: the tracking
strategy wins the reversal-extended uniformization game, positional
determinacy yields a positional winner, its journal tree is accepted
(`tauTree_acceptsTree`, now unconditional), the Rabin basis supplies
a transition-rational accepted tree, and the HG-C/H4 composition
turns it into the readback strategy.  Extending the conclusion to all
environment sequences is the remaining M2 work (M2-4/5).
-/
theorem journal_fragment_readback_upgrade
    (hex :
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env)) :
    Nonempty (JournalReadbackWitness (In₁ := In₁) (A := A)) := by
  obtain ⟨σ, hσ⟩ := hex
  obtain ⟨τ, hτ⟩ := exists_positional_uniformization_winner σ hσ
  have hacc := tauTree_acceptsTree σ τ CL CR CC hτ
  letI := globalJournalLabelFintype (A := A)
  obtain ⟨t, hacct⟩ :=
    (globalJournalAutomaton A CL CR CC).exists_transitionRational_accepted
      ⟨tauTree σ τ, hacc⟩
  letI : DecidableEq t.Control := Classical.decEq _
  letI : Inhabited t.Control := ⟨t.initial⟩
  obtain ⟨plans, hplans⟩ :=
    journal_readback_accepts_of_accepts t CL CR CC hacct
  exact ⟨⟨t.Control, plans, hplans⟩⟩

/--
A committed plan family whose journal readback wins on *every* environment
(including direct reversals), packaged with the finite-control instances the
readback needs.  The full-model analogue of `JournalReadbackWitness`.
-/
structure JournalReadbackWitnessFull where
  Control : Type s
  [controlFintype : Fintype Control]
  [controlDecEq : DecidableEq Control]
  [controlInhabited : Inhabited Control]
  plans :
    PlanFamily (In₁ := In₁) A (ULift.{max u v x y, s} Control)
      (ULift.{max u v x y, s} Control)
      (ULift.{max u v x y, s} Control)
  accepts :
    ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution (journalStrategy plans) env)

include CL CR CC in
/--
The full-model readback upgrade: from full realizability of the objective, the
same winning chain produces a committed plan family whose readback is accepted
on *every* environment, given the entry-indexed measurability certificate
`hcert` for the boundary-game plan families.  Identical to
`journal_fragment_readback_upgrade` except the conclusion drops
`NoDirectReversalSequence`, discharged through `journal_readback_accepts_of_accepts_full`.
-/
theorem journal_fragment_readback_upgrade_full
    (hex :
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env))
    (hcert :
      ∀ (C : Type s) [Fintype C] [DecidableEq C] [Inhabited C]
        (τ :
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} C)
              (ULift.{max u v x y, s} C)
              (ULift.{max u v x y, s} C)).PositionalStrategy
            ParityPlayer.even),
        CountableParityGame.PositionalStrategy.WinningFrom
            (G :=
              DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} C)
                (ULift.{max u v x y, s} C)
                (ULift.{max u v x y, s} C))
            τ (Sum.inl (A.initial, A.initial)) ->
          ∃ τ' :
              (DetParityAutomaton.boundaryGame A
                  (ULift.{max u v x y, s} C)
                  (ULift.{max u v x y, s} C)
                  (ULift.{max u v x y, s} C)).PositionalStrategy
                ParityPlayer.even,
            CountableParityGame.PositionalStrategy.WinningFrom
                (G :=
                  DetParityAutomaton.boundaryGame A
                    (ULift.{max u v x y, s} C)
                    (ULift.{max u v x y, s} C)
                    (ULift.{max u v x y, s} C))
                τ' (Sum.inl (A.initial, A.initial)) ∧
              ReversalMeasurable (plansOf τ')) :
    Nonempty (JournalReadbackWitnessFull (In₁ := In₁) (A := A)) := by
  obtain ⟨σ, hσ⟩ := hex
  obtain ⟨τ, hτ⟩ := exists_positional_uniformization_winner σ hσ
  have hacc := tauTree_acceptsTree σ τ CL CR CC hτ
  letI := globalJournalLabelFintype (A := A)
  obtain ⟨t, hacct⟩ :=
    (globalJournalAutomaton A CL CR CC).exists_transitionRational_accepted
      ⟨tauTree σ τ, hacc⟩
  letI : DecidableEq t.Control := Classical.decEq _
  letI : Inhabited t.Control := ⟨t.initial⟩
  obtain ⟨plans, hplans⟩ :=
    journal_readback_accepts_of_accepts_full t CL CR CC hacct (hcert t.Control)
  exact ⟨⟨t.Control, plans, hplans⟩⟩

include CL CR CC in
/--
The **Route B** full-model readback upgrade: from full realizability, a committed
plan family whose readback is accepted on *every* environment, given the
summary-soundness certificate `SummarySoundnessCertificate` in place of the
entry-indexed certificate.  Identical chain to
`journal_fragment_readback_upgrade_full`, but the direct-reversal case is
discharged through `journal_readback_accepts_of_accepts_route_b`
(fringe elimination) rather than `ReversalMeasurable`.
-/
theorem journal_fragment_readback_upgrade_route_b
    (hex :
      ∃ σ : StrategyPair In₁ In₂ Out₁ Out₂,
        ∀ env : EnvironmentSequence In₁ In₂,
          A.Accepts (execution σ env))
    (hcert : SummarySoundnessCertificate (In₁ := In₁) (A := A)) :
    Nonempty (JournalReadbackWitnessFull (In₁ := In₁) (A := A)) := by
  obtain ⟨σ, hσ⟩ := hex
  obtain ⟨τ, hτ⟩ := exists_positional_uniformization_winner σ hσ
  have hacc := tauTree_acceptsTree σ τ CL CR CC hτ
  letI := globalJournalLabelFintype (A := A)
  obtain ⟨t, hacct⟩ :=
    (globalJournalAutomaton A CL CR CC).exists_transitionRational_accepted
      ⟨tauTree σ τ, hacc⟩
  letI : DecidableEq t.Control := Classical.decEq _
  letI : Inhabited t.Control := ⟨t.initial⟩
  obtain ⟨plans, hplans⟩ :=
    journal_readback_accepts_of_accepts_route_b t CL CR CC hacct (hcert t.Control)
  exact ⟨⟨t.Control, plans, hplans⟩⟩

end DetParityAutomaton

end DistributedSynthesis
