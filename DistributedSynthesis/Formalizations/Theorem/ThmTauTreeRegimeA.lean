/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeDichotomy
import DistributedSynthesis.Formalizations.Theorem.ThmParityBlockPasting

/-!
# Regime (a): infinitely many boundaries

A never-sinking branch that visits a boundary infinitely often has
min-even run priorities, provided its boundary-atom priority
subsequence is min-even.  Block priorities are the checker priority
plus the even global shift, so they sit strictly above every atom
priority; since atoms recur, the min recurring branch priority is the
min recurring atom priority.  This file proves that shift-domination
reduction; the atom subsequence's parity comes from the global play.
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

/-- A boundary of the branch's run. -/
def IsBranchBoundary
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (n : Nat) : Prop :=
  ∃ atom : A.State × A.State,
    branchRun σ τ CL CR CC branch n = Sum.inl atom

/-- The branch priority at a boundary is an atom priority, below the
shift. -/
theorem branchPriority_lt_shift_of_boundary
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) {n : Nat}
    (h : IsBranchBoundary σ τ CL CR CC branch n) :
    globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch n) <
      globalShift (In₁ := In₁) A := by
  obtain ⟨atom, hatom⟩ := h
  rw [hatom]
  exact priority_lt_globalShift (In₁ := In₁) A atom.2

/-- The branch priority at a non-boundary, non-sink round is at least
the shift. -/
theorem shift_le_branchPriority_of_not_boundary
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (n : Nat)
    (hns :
      branchRun σ τ CL CR CC branch n ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
    (hnb : ¬ IsBranchBoundary σ τ CL CR CC branch n) :
    globalShift (In₁ := In₁) A ≤
      globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch n) := by
  rcases branchRun_shape σ τ CL CR CC branch n hns with
    ⟨atom, h⟩ | ⟨c, t, h⟩ | ⟨c, t, h⟩ | ⟨c, t, h⟩ | ⟨c, t, h⟩
  · exact absurd ⟨atom, h⟩ hnb
  · rw [h]
    show globalShift (In₁ := In₁) A ≤
      CL.monitor.priority c + globalShift (In₁ := In₁) A
    omega
  · rw [h]
    show globalShift (In₁ := In₁) A ≤
      CR.monitor.priority c + globalShift (In₁ := In₁) A
    omega
  · rw [h]
    show globalShift (In₁ := In₁) A ≤
      CC.monitor.priority c + globalShift (In₁ := In₁) A
    omega
  · rw [h]
    show globalShift (In₁ := In₁) A ≤
      CC.monitor.priority c + globalShift (In₁ := In₁) A
    omega

/-! ### The boundary enumeration -/

section Enumeration

variable
  (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
  (hinf : ∀ N, ∃ n, N ≤ n ∧ IsBranchBoundary σ τ CL CR CC branch n)

include hinf in
theorem exists_gt_branchBoundary (n : Nat) :
    ∃ m, n < m ∧ IsBranchBoundary σ τ CL CR CC branch m := by
  obtain ⟨m, hm, h⟩ := hinf (n + 1)
  exact ⟨m, by omega, h⟩

/-- The first boundary strictly after a round. -/
noncomputable def nextBranchBoundary (n : Nat) : Nat :=
  letI : DecidablePred fun m => n < m ∧ IsBranchBoundary σ τ CL CR CC branch m :=
    fun _ => Classical.propDecidable _
  Nat.find (exists_gt_branchBoundary σ τ CL CR CC branch hinf n)

theorem nextBranchBoundary_spec (n : Nat) :
    n < nextBranchBoundary σ τ CL CR CC branch hinf n ∧
      IsBranchBoundary σ τ CL CR CC branch
        (nextBranchBoundary σ τ CL CR CC branch hinf n) := by
  letI : DecidablePred fun m => n < m ∧ IsBranchBoundary σ τ CL CR CC branch m :=
    fun _ => Classical.propDecidable _
  unfold nextBranchBoundary
  exact Nat.find_spec (exists_gt_branchBoundary σ τ CL CR CC branch hinf n)

theorem nextBranchBoundary_le {n m : Nat} (hm : n < m)
    (hb : IsBranchBoundary σ τ CL CR CC branch m) :
    nextBranchBoundary σ τ CL CR CC branch hinf n ≤ m := by
  letI : DecidablePred fun m => n < m ∧ IsBranchBoundary σ τ CL CR CC branch m :=
    fun _ => Classical.propDecidable _
  unfold nextBranchBoundary
  exact
    Nat.find_min' (exists_gt_branchBoundary σ τ CL CR CC branch hinf n)
      ⟨hm, hb⟩

/-- The increasing enumeration of the branch's boundaries. -/
noncomputable def branchBoundaryIndex : Nat -> Nat
  | 0 => 0
  | k + 1 => nextBranchBoundary σ τ CL CR CC branch hinf
      (branchBoundaryIndex k)

theorem branchBoundaryIndex_lt_succ (k : Nat) :
    branchBoundaryIndex σ τ CL CR CC branch hinf k <
      branchBoundaryIndex σ τ CL CR CC branch hinf (k + 1) :=
  (nextBranchBoundary_spec σ τ CL CR CC branch hinf
      (branchBoundaryIndex σ τ CL CR CC branch hinf k)).1

theorem branchBoundaryIndex_strictMono :
    StrictMono (branchBoundaryIndex σ τ CL CR CC branch hinf) :=
  strictMono_nat_of_lt_succ (branchBoundaryIndex_lt_succ σ τ CL CR CC branch hinf)

theorem le_branchBoundaryIndex (k : Nat) :
    k ≤ branchBoundaryIndex σ τ CL CR CC branch hinf k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have := branchBoundaryIndex_lt_succ σ τ CL CR CC branch hinf k
      omega

theorem isBranchBoundary_branchBoundaryIndex (k : Nat) :
    IsBranchBoundary σ τ CL CR CC branch
      (branchBoundaryIndex σ τ CL CR CC branch hinf k) := by
  match k with
  | 0 => exact ⟨(A.initial, A.initial), rfl⟩
  | k + 1 =>
      exact
        (nextBranchBoundary_spec σ τ CL CR CC branch hinf
          (branchBoundaryIndex σ τ CL CR CC branch hinf k)).2

/-- The enumeration is exhaustive. -/
theorem exists_branchBoundaryIndex_eq {m : Nat}
    (hb : IsBranchBoundary σ τ CL CR CC branch m) :
    ∃ k, branchBoundaryIndex σ τ CL CR CC branch hinf k = m := by
  have hex : ∃ k, m ≤ branchBoundaryIndex σ τ CL CR CC branch hinf k :=
    ⟨m, le_branchBoundaryIndex σ τ CL CR CC branch hinf m⟩
  have hspec := Nat.find_spec hex
  rcases Nat.eq_or_lt_of_le hspec with heq | hlt
  · exact ⟨Nat.find hex, heq.symm⟩
  · exfalso
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
    · rw [hzero] at hlt
      exact absurd hlt (by simp [branchBoundaryIndex])
    · have hprev :
          ¬ m ≤ branchBoundaryIndex σ τ CL CR CC branch hinf (Nat.find hex - 1) :=
        Nat.find_min hex (by omega)
      have hle :
          branchBoundaryIndex σ τ CL CR CC branch hinf (Nat.find hex - 1 + 1) ≤
            m := by
        show nextBranchBoundary σ τ CL CR CC branch hinf _ ≤ m
        exact nextBranchBoundary_le σ τ CL CR CC branch hinf (by omega) hb
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hle
      omega

/-! ### The shift-domination reduction -/

/-- The branch priority at the `k`-th boundary. -/
noncomputable def branchBoundaryPriority (k : Nat) : Nat :=
  globalJournalPriority A CL CR CC
    (branchRun σ τ CL CR CC branch
      (branchBoundaryIndex σ τ CL CR CC branch hinf k))

/--
Regime (a) reduced: if the boundary-atom priority subsequence is
min-even and the run never sinks, the branch priorities are min-even.
-/
theorem branch_min_even_of_boundary_subseq
    (hns :
      ∀ n, branchRun σ τ CL CR CC branch n ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
    (hsub :
      NatSeqMinEvenParity (branchBoundaryPriority σ τ CL CR CC branch hinf)) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch n)) := by
  refine
    (natSeqMinEvenParity_iff_of_recurring_transfer
      (branchBoundaryPriority σ τ CL CR CC branch hinf)
      (fun n =>
        globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch n))
      ?_ ?_).mp hsub
  · -- boundary priorities recur among the branch priorities
    intro w hw n
    obtain ⟨k, hk, hval⟩ := hw n
    exact
      ⟨branchBoundaryIndex σ τ CL CR CC branch hinf k,
        Nat.le_trans hk (le_branchBoundaryIndex σ τ CL CR CC branch hinf k),
        hval⟩
  · -- recurring branch priorities dominate the boundary priorities
    intro v hv n
    by_cases hge : globalShift (In₁ := In₁) A ≤ v
    · refine ⟨n, Nat.le_refl n, ?_⟩
      have hlt :
          branchBoundaryPriority σ τ CL CR CC branch hinf n <
            globalShift (In₁ := In₁) A :=
        branchPriority_lt_shift_of_boundary σ τ CL CR CC branch
          (isBranchBoundary_branchBoundaryIndex σ τ CL CR CC branch hinf n)
      omega
    · push Not at hge
      obtain ⟨m, hm, hvm⟩ :=
        hv (branchBoundaryIndex σ τ CL CR CC branch hinf n)
      have hvm' :
          globalJournalPriority A CL CR CC (branchRun σ τ CL CR CC branch m) = v :=
        hvm
      have hbm : IsBranchBoundary σ τ CL CR CC branch m := by
        by_contra hnb
        have hge' :=
          shift_le_branchPriority_of_not_boundary σ τ CL CR CC branch m
            (hns m) hnb
        rw [hvm'] at hge'
        omega
      obtain ⟨km, hkm⟩ :=
        exists_branchBoundaryIndex_eq σ τ CL CR CC branch hinf hbm
      refine ⟨km, ?_, ?_⟩
      · by_contra hlt
        push Not at hlt
        have hstrict :=
          branchBoundaryIndex_strictMono σ τ CL CR CC branch hinf
            (show km < n by omega)
        rw [hkm] at hstrict
        omega
      · have heq :
            branchBoundaryPriority σ τ CL CR CC branch hinf km = v := by
          unfold branchBoundaryPriority
          rw [hkm]
          exact hvm'
        omega

end Enumeration

end DetParityAutomaton

end DistributedSynthesis
