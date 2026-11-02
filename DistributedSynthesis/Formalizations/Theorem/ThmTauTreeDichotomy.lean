/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmTauTreeAccepts

/-!
# The never-sink dichotomy

A branch of the winner's journal tree whose deterministic run never
sinks either visits an atom infinitely often, or is eventually trapped
in a single block orientation.  The run stays in a block on sender
inputs and leaves it only by an atom close (which would be a fresh
boundary) or an orientation switch (which would sink); so once
boundaries stop, all remaining directions are same-orientation sender
inputs.
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

/-- The deterministic run of the winner's tree along a branch. -/
noncomputable def branchRun
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (n : Nat) :
    GlobalJournalState (In₁ := In₁) A CL CR CC :=
  globalRunIn CL CR CC (tauTree σ τ) (Sum.inl (A.initial, A.initial))
    (branchNode branch n)

theorem branchRun_succ
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (n : Nat) :
    branchRun σ τ CL CR CC branch (n + 1) =
      globalJournalStep A CL CR CC (branchRun σ τ CL CR CC branch n)
        (tauTree σ τ (branchNode branch n)) (branch n) :=
  globalRunIn_append CL CR CC (tauTree σ τ)
    (Sum.inl (A.initial, A.initial)) (branchNode branch n) (branch n)

/-- A non-sinking run is an atom, a block mode, or a reversed mode. -/
theorem branchRun_shape
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A) (n : Nat)
    (hns :
      branchRun σ τ CL CR CC branch n ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) :
    (∃ atom : A.State × A.State,
      branchRun σ τ CL CR CC branch n = Sum.inl atom) ∨
    (∃ (checker : CL.monitor.State)
        (threads : Finset (A.State × A.State)),
      branchRun σ τ CL CR CC branch n = Sum.inr (Sum.inl (checker, threads))) ∨
    (∃ (checker : CR.monitor.State)
        (threads : Finset (A.State × A.State)),
      branchRun σ τ CL CR CC branch n =
        Sum.inr (Sum.inr (Sum.inl (checker, threads)))) ∨
    (∃ (checker : CC.monitor.State)
        (threads : Finset (ChainThread A)),
      branchRun σ τ CL CR CC branch n =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))) ∨
    (∃ (checker : CC.monitor.State)
        (threads : Finset (ChainThread A)),
      branchRun σ τ CL CR CC branch n =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))))) := by
  rcases h : branchRun σ τ CL CR CC branch n with atom | ⟨c, t⟩ | ⟨c, t⟩ |
    ⟨c, t⟩ | ⟨c, t⟩ | u
  · exact Or.inl ⟨atom, rfl⟩
  · exact Or.inr (Or.inl ⟨c, t, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, t, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨c, t, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨c, t, rfl⟩)))
  · exact absurd (by rw [h]) hns

/-! ### Step shapes of the extended automaton -/

/-- From a left-block state, a step is a close-or-sink, a left
continuation, or a direct reversal into a reversed right block. -/
theorem step_of_inLeft_cases
    (checker : CL.monitor.State)
    (threads : Finset (A.State × A.State))
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    (∃ atom' : A.State × A.State,
      branch = Sum.inl atom' ∧
        (globalJournalStep A CL CR CC
            (Sum.inr (Sum.inl (checker, threads))) label branch =
          Sum.inl atom' ∨
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inl (checker, threads))) label branch =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))) ∨
    (∃ (inputTwo : In₂) (c' : CL.monitor.State)
        (t' : Finset (A.State × A.State)),
      branch = Sum.inr (Sum.inl inputTwo) ∧
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inl (checker, threads))) label branch =
          Sum.inr (Sum.inl (c', t'))) ∨
    (∃ (inputOne : In₁) (c' : CC.monitor.State)
        (t' : Finset (ChainThread A)),
      branch = Sum.inr (Sum.inr inputOne) ∧
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inl (checker, threads))) label branch =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c', t')))))) := by
  rcases branch with atom' | inputTwo | inputOne
  · refine Or.inl ⟨atom', rfl, ?_⟩
    simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr (Or.inl ⟨inputTwo, _, _, rfl, rfl⟩)
  · exact Or.inr (Or.inr ⟨inputOne, _, _, rfl, rfl⟩)

/-- From a right-block state, a step is a close-or-sink, a right
continuation, or a direct reversal into a reversed left block. -/
theorem step_of_inRight_cases
    (checker : CR.monitor.State)
    (threads : Finset (A.State × A.State))
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    (∃ atom' : A.State × A.State,
      branch = Sum.inl atom' ∧
        (globalJournalStep A CL CR CC
            (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) label
            branch =
          Sum.inl atom' ∨
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) label
            branch =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))) ∨
    (∃ (inputOne : In₁) (c' : CR.monitor.State)
        (t' : Finset (A.State × A.State)),
      branch = Sum.inr (Sum.inr inputOne) ∧
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) label
            branch =
          Sum.inr (Sum.inr (Sum.inl (c', t')))) ∨
    (∃ (inputTwo : In₂) (c' : CC.monitor.State)
        (t' : Finset (ChainThread A)),
      branch = Sum.inr (Sum.inl inputTwo) ∧
        globalJournalStep A CL CR CC
            (Sum.inr (Sum.inr (Sum.inl (checker, threads)))) label
            branch =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (c', t'))))) := by
  rcases branch with atom' | inputTwo | inputOne
  · refine Or.inl ⟨atom', rfl, ?_⟩
    simp only [globalJournalStep]
    split
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact Or.inr (Or.inr ⟨inputTwo, _, _, rfl, rfl⟩)
  · exact Or.inr (Or.inl ⟨inputOne, _, _, rfl, rfl⟩)

/-- A reversed-mode state steps to an atom, the sink, or a reversed
mode. -/
theorem step_of_rev_cases
    (state : GlobalJournalState (In₁ := In₁) A CL CR CC)
    (hrev :
      (∃ (c : CC.monitor.State) (t : Finset (ChainThread A)),
        state = Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
      ∃ (c : CC.monitor.State) (t : Finset (ChainThread A)),
        state = Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))))
    (label : GlobalJournalLabel (In₁ := In₁) A)
    (branch : GlobalJournalBranch (In₁ := In₁) A) :
    (∃ atom' : A.State × A.State,
      globalJournalStep A CL CR CC state label branch = Sum.inl atom') ∨
    globalJournalStep A CL CR CC state label branch =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))) ∨
    (∃ (c : CC.monitor.State) (t : Finset (ChainThread A)),
      globalJournalStep A CL CR CC state label branch =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
    (∃ (c : CC.monitor.State) (t : Finset (ChainThread A)),
      globalJournalStep A CL CR CC state label branch =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))) := by
  rcases hrev with ⟨c, t, hstate⟩ | ⟨c, t, hstate⟩ <;> subst hstate <;>
    rcases branch with atom' | inputTwo | inputOne
  · simp only [globalJournalStep]
    split
    · exact Or.inl ⟨atom', rfl⟩
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))
  · simp only [globalJournalStep]
    split
    · exact Or.inl ⟨atom', rfl⟩
    · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨_, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨_, _, rfl⟩))

/-- A step into a left-block state comes from a left-sender input. -/
theorem inLeft_of_step
    {state : GlobalJournalState (In₁ := In₁) A CL CR CC}
    {label : GlobalJournalLabel (In₁ := In₁) A}
    {branch : GlobalJournalBranch (In₁ := In₁) A}
    {checker : CL.monitor.State}
    {threads : Finset (A.State × A.State)}
    (h :
      globalJournalStep A CL CR CC state label branch =
        Sum.inr (Sum.inl (checker, threads))) :
    ∃ inputTwo : In₂, branch = Sum.inr (Sum.inl inputTwo) := by
  rcases state with atom | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | u <;>
    rcases branch with atom' | inputTwo | inputOne <;>
    first
      | exact ⟨_, rfl⟩
      | (exact
          absurd h (by simp only [globalJournalStep]; split <;> simp))
      | exact absurd h (by simp [globalJournalStep])

/-- A step into a right-block state comes from a right-sender
input. -/
theorem inRight_of_step
    {state : GlobalJournalState (In₁ := In₁) A CL CR CC}
    {label : GlobalJournalLabel (In₁ := In₁) A}
    {branch : GlobalJournalBranch (In₁ := In₁) A}
    {checker : CR.monitor.State}
    {threads : Finset (A.State × A.State)}
    (h :
      globalJournalStep A CL CR CC state label branch =
        Sum.inr (Sum.inr (Sum.inl (checker, threads)))) :
    ∃ inputOne : In₁, branch = Sum.inr (Sum.inr inputOne) := by
  rcases state with atom | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | u <;>
    rcases branch with atom' | inputTwo | inputOne <;>
    first
      | exact ⟨_, rfl⟩
      | (exact
          absurd h (by simp only [globalJournalStep]; split <;> simp))
      | exact absurd h (by simp [globalJournalStep])

/-! ### The never-sink classification -/

/-- Once the run is in a reversed mode it stays reversed, closes to
an atom, or sinks. -/
theorem rev_forever
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    (hns :
      ∀ n, branchRun σ τ CL CR CC branch n ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit)))))
    (S : Nat)
    (hnoatom :
      ∀ m, S ≤ m ->
        ¬ ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom)
    (hrevS :
      (∃ c t, branchRun σ τ CL CR CC branch S =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
      ∃ c t, branchRun σ τ CL CR CC branch S =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))) :
    ∀ k,
      (∃ c t, branchRun σ τ CL CR CC branch (S + k) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
      ∃ c t, branchRun σ τ CL CR CC branch (S + k) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) := by
  intro k
  induction k with
  | zero => exact hrevS
  | succ k ih =>
      have hstep := branchRun_succ σ τ CL CR CC branch (S + k)
      rcases
        step_of_rev_cases CL CR CC (branchRun σ τ CL CR CC branch (S + k))
          ih (tauTree σ τ (branchNode branch (S + k))) (branch (S + k)) with
        ⟨atom', hat⟩ | hsink | ⟨c, t, hc⟩ | ⟨c, t, hc⟩
      · exact
          absurd ⟨atom', by rw [hstep, hat]⟩
            (hnoatom (S + k + 1) (by omega))
      · exact absurd (by rw [hstep, hsink]) (hns (S + k + 1))
      · exact
          Or.inl ⟨c, t, by
            show branchRun σ τ CL CR CC branch (S + k + 1) = _
            rw [hstep, hc]⟩
      · exact
          Or.inr ⟨c, t, by
            show branchRun σ τ CL CR CC branch (S + k + 1) = _
            rw [hstep, hc]⟩

/--
The never-sink classification: a branch whose run never sinks either
visits a boundary infinitely often, is eventually trapped in a single
normal block orientation with no reversal, or eventually enters the
reversal chain and stays reversed forever.
-/
theorem neverSink_classification
    (branch : Nat -> GlobalJournalBranch (In₁ := In₁) A)
    (hns :
      ∀ n, branchRun σ τ CL CR CC branch n ≠
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr PUnit.unit))))) :
    (∀ N, ∃ n, N ≤ n ∧
      ∃ atom, branchRun σ τ CL CR CC branch n = Sum.inl atom) ∨
    (∃ (M : Nat) (atom₀ : A.State × A.State) (leftInput : Nat -> In₂),
      branchRun σ τ CL CR CC branch M = Sum.inl atom₀ ∧
        ∀ j, branch (M + j) = Sum.inr (Sum.inl (leftInput j))) ∨
    (∃ (M : Nat) (atom₀ : A.State × A.State) (rightInput : Nat -> In₁),
      branchRun σ τ CL CR CC branch M = Sum.inl atom₀ ∧
        ∀ j, branch (M + j) = Sum.inr (Sum.inr (rightInput j))) ∨
    (∃ S : Nat,
      ∀ k,
        (∃ c t, branchRun σ τ CL CR CC branch (S + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
        ∃ c t, branchRun σ τ CL CR CC branch (S + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))) := by
  by_cases hinf :
      ∀ N, ∃ n, N ≤ n ∧
        ∃ atom, branchRun σ τ CL CR CC branch n = Sum.inl atom
  · exact Or.inl hinf
  · refine Or.inr ?_
    push Not at hinf
    obtain ⟨N, hN⟩ := hinf
    letI :
        DecidablePred fun m =>
          ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom :=
      fun _ => Classical.propDecidable _
    have hzero :
        ∃ atom, branchRun σ τ CL CR CC branch 0 = Sum.inl atom :=
      ⟨(A.initial, A.initial), rfl⟩
    set M :=
      Nat.findGreatest
        (fun m => ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom)
        N with hMdef
    have hMspec :
        ∃ atom, branchRun σ τ CL CR CC branch M = Sum.inl atom :=
      Nat.findGreatest_spec (m := 0)
        (P := fun m => ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom)
        (n := N) (Nat.zero_le N) hzero
    obtain ⟨atom₀, hatom₀⟩ := hMspec
    have hnobnd :
        ∀ m, M < m ->
          ¬ ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom := by
      intro m hm hbnd
      rcases Nat.le_total m N with hle | hge
      · exact
          Nat.findGreatest_is_greatest
            (P := fun m => ∃ atom, branchRun σ τ CL CR CC branch m = Sum.inl atom)
            (by rw [← hMdef]; exact hm) hle hbnd
      · obtain ⟨atom', hbnd'⟩ := hbnd
        exact hN m hge atom' hbnd'
    -- helper: a reversed mode at any point past M yields the chain tail
    have hchain :
        ∀ S, M < S ->
          ((∃ c t, branchRun σ τ CL CR CC branch S =
            Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
          ∃ c t, branchRun σ τ CL CR CC branch S =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))) ->
          (∃ S' : Nat,
            ∀ k,
              (∃ c t, branchRun σ τ CL CR CC branch (S' + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t))))) ∨
              ∃ c t, branchRun σ τ CL CR CC branch (S' + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (c, t)))))) :=
      fun S hMS hrev =>
        ⟨S,
          rev_forever σ τ CL CR CC branch hns S
            (fun m hm => hnobnd m (by omega)) hrev⟩
    -- classify the mode at M + 1
    rcases hshape : branchRun σ τ CL CR CC branch (M + 1) with
      atom | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | ⟨c, t⟩ | u
    · exact absurd ⟨atom, hshape⟩ (hnobnd (M + 1) (by omega))
    · -- left block at M + 1
      by_cases htrap :
          ∀ j, ∃ c' t',
            branchRun σ τ CL CR CC branch (M + j + 1) =
              Sum.inr (Sum.inl (c', t'))
      · -- trapped left forever: every direction is a left-sender input
        refine Or.inl ?_
        have hdir :
            ∀ j, ∃ i2, branch (M + j) = Sum.inr (Sum.inl i2) := by
          intro j
          obtain ⟨c', t', hj⟩ := htrap j
          have hstep := branchRun_succ σ τ CL CR CC branch (M + j)
          rw [show M + j + 1 = M + j + 1 from rfl] at hj
          rw [hj] at hstep
          exact inLeft_of_step CL CR CC hstep.symm
        exact
          ⟨M, atom₀, fun j => (hdir j).choose, hatom₀, fun j =>
            (hdir j).choose_spec⟩
      · -- a reversal occurs: find it and enter the chain tail
        push Not at htrap
        obtain ⟨j₀, hj₀⟩ := htrap
        letI :
            DecidablePred fun j =>
              ¬ ∃ c' t',
                branchRun σ τ CL CR CC branch (M + j + 1) =
                  Sum.inr (Sum.inl (c', t')) :=
          fun _ => Classical.propDecidable _
        have hex : ∃ j, ¬ ∃ c' t',
            branchRun σ τ CL CR CC branch (M + j + 1) =
              Sum.inr (Sum.inl (c', t')) :=
          ⟨j₀, by push Not; exact hj₀⟩
        have hspec := Nat.find_spec hex
        have hpos : Nat.find hex ≠ 0 := by
          intro h0
          rw [h0] at hspec
          exact hspec ⟨c, t, hshape⟩
        obtain ⟨j₂, hj₂⟩ := Nat.exists_eq_succ_of_ne_zero hpos
        have hprev :
            ∃ c' t',
              branchRun σ τ CL CR CC branch (M + j₂ + 1) =
                Sum.inr (Sum.inl (c', t')) := by
          have := Nat.find_min hex (show j₂ < Nat.find hex by omega)
          exact not_not.mp this
        obtain ⟨c', t', hprev⟩ := hprev
        have hstep := branchRun_succ σ τ CL CR CC branch (M + j₂ + 1)
        rw [hprev] at hstep
        rcases
          step_of_inLeft_cases CL CR CC c' t'
            (tauTree σ τ (branchNode branch (M + j₂ + 1)))
            (branch (M + j₂ + 1)) with
          ⟨atom', -, hclose | hsink⟩ | ⟨i2, c'', t'', -, hcont⟩ |
          ⟨i1, c'', t'', -, hrev⟩
        · rw [hclose] at hstep
          exact
            absurd ⟨atom', hstep⟩ (hnobnd (M + j₂ + 1 + 1) (by omega))
        · rw [hsink] at hstep
          exact absurd hstep (hns (M + j₂ + 1 + 1))
        · rw [hcont] at hstep
          exact
            absurd ⟨c'', t'', by
              rw [show M + Nat.find hex + 1 = M + j₂ + 1 + 1 by omega]
              exact hstep⟩ hspec
        · rw [hrev] at hstep
          exact
            Or.inr (Or.inr
              (hchain (M + j₂ + 1 + 1) (by omega)
                (Or.inr ⟨c'', t'', hstep⟩)))
    · -- right block at M + 1: the mirror
      by_cases htrap :
          ∀ j, ∃ c' t',
            branchRun σ τ CL CR CC branch (M + j + 1) =
              Sum.inr (Sum.inr (Sum.inl (c', t')))
      · refine Or.inr (Or.inl ?_)
        have hdir :
            ∀ j, ∃ i1, branch (M + j) = Sum.inr (Sum.inr i1) := by
          intro j
          obtain ⟨c', t', hj⟩ := htrap j
          have hstep := branchRun_succ σ τ CL CR CC branch (M + j)
          rw [hj] at hstep
          exact inRight_of_step CL CR CC hstep.symm
        exact
          ⟨M, atom₀, fun j => (hdir j).choose, hatom₀, fun j =>
            (hdir j).choose_spec⟩
      · push Not at htrap
        obtain ⟨j₀, hj₀⟩ := htrap
        letI :
            DecidablePred fun j =>
              ¬ ∃ c' t',
                branchRun σ τ CL CR CC branch (M + j + 1) =
                  Sum.inr (Sum.inr (Sum.inl (c', t'))) :=
          fun _ => Classical.propDecidable _
        have hex : ∃ j, ¬ ∃ c' t',
            branchRun σ τ CL CR CC branch (M + j + 1) =
              Sum.inr (Sum.inr (Sum.inl (c', t'))) :=
          ⟨j₀, by push Not; exact hj₀⟩
        have hspec := Nat.find_spec hex
        have hpos : Nat.find hex ≠ 0 := by
          intro h0
          rw [h0] at hspec
          exact hspec ⟨c, t, hshape⟩
        obtain ⟨j₂, hj₂⟩ := Nat.exists_eq_succ_of_ne_zero hpos
        have hprev :
            ∃ c' t',
              branchRun σ τ CL CR CC branch (M + j₂ + 1) =
                Sum.inr (Sum.inr (Sum.inl (c', t'))) := by
          have := Nat.find_min hex (show j₂ < Nat.find hex by omega)
          exact not_not.mp this
        obtain ⟨c', t', hprev⟩ := hprev
        have hstep := branchRun_succ σ τ CL CR CC branch (M + j₂ + 1)
        rw [hprev] at hstep
        rcases
          step_of_inRight_cases CL CR CC c' t'
            (tauTree σ τ (branchNode branch (M + j₂ + 1)))
            (branch (M + j₂ + 1)) with
          ⟨atom', -, hclose | hsink⟩ | ⟨i1, c'', t'', -, hcont⟩ |
          ⟨i2, c'', t'', -, hrev⟩
        · rw [hclose] at hstep
          exact
            absurd ⟨atom', hstep⟩ (hnobnd (M + j₂ + 1 + 1) (by omega))
        · rw [hsink] at hstep
          exact absurd hstep (hns (M + j₂ + 1 + 1))
        · rw [hcont] at hstep
          exact
            absurd ⟨c'', t'', by
              rw [show M + Nat.find hex + 1 = M + j₂ + 1 + 1 by omega]
              exact hstep⟩ hspec
        · rw [hrev] at hstep
          exact
            Or.inr (Or.inr
              (hchain (M + j₂ + 1 + 1) (by omega)
                (Or.inl ⟨c'', t'', hstep⟩)))
    · -- already reversed at M + 1
      exact
        Or.inr (Or.inr
          (hchain (M + 1) (by omega) (Or.inl ⟨c, t, hshape⟩)))
    · exact
        Or.inr (Or.inr
          (hchain (M + 1) (by omega) (Or.inr ⟨c, t, hshape⟩)))
    · exact absurd hshape (hns (M + 1))

end DetParityAutomaton

end DistributedSynthesis
