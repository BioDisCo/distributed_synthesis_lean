/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankAuthorityPath
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOperationalCloseCuts

/-!
# Exact bank paths at operational cuts

The linked relay is not restarted after every strict receive.  A maximal
homogeneous strict block is therefore one bank transition, not one transition
per physical round.  A change of strict side begins the next block, while a
simultaneous round is a singleton block.

This file keeps the remaining operational seam explicit.  A cut schedule
records the graph-theoretic blocks and their proof-side bank directions.  If
the concrete controller proves one exact `BankChildren` equation at every
completed cut, the cut-indexed controls are definitionally the states of one
allowed marked-bank path.  Both finite cut prefixes and an infinite cut
schedule are provided.  An eventually homogeneous last block simply has no
finite closing cut and is handled by its retained-table tail proof.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

private abbrev CommonControl :=
  ProfiledRawJointHybridCommonControl A strategy hwin

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-! ## Graph-theoretic operational cuts -/

/-- `[start, stop)` is one maximal strict-right block.  Maximality is stated
at both finite boundaries; an eventually-right suffix has no finite `stop`
and hence is intentionally not represented as a completed cut. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalRightBlock
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) : Prop :=
  start < stop ∧
    (∀ j : Nat, start ≤ j → j < stop → (env j).graph = .right) ∧
    (env stop).graph ≠ .right

/-- Maximal strict-left mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalLeftBlock
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat) : Prop :=
  start < stop ∧
    (∀ j : Nat, start ≤ j → j < stop → (env j).graph = .left) ∧
    (env stop).graph ≠ .left

/-- One completed operational cut.  Strict blocks carry one proof-side strict
direction of the matching physical side.  A BOTH block is forced to be the
single physical round at `start`, with its literal simultaneous input. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep
    (env : EnvironmentSequence In₁ In₂) (start stop : Nat)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) : Prop :=
  match (env start).graph with
  | .right =>
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalRightBlock
          env start stop ∧
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          actual.side = .right ∧ direction = .strict actual
  | .left =>
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalLeftBlock
          env start stop ∧
        ∃ actual : ProfiledRawJointActualDirection
            (I := Unit) (In₁ := In₁) (In₂ := In₂),
          actual.side = .left ∧ direction = .strict actual
  | .both =>
      stop = start + 1 ∧
        direction = .simultaneous ((env start).inputOne, (env start).inputTwo)

omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂] in
/-- Every operational cut has positive physical length. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep.lt
    {env : EnvironmentSequence In₁ In₂} {start stop : Nat}
    {direction : HybridDirection (In₁ := In₁) (In₂ := In₂)}
    (hstep :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep
        env start stop direction) :
    start < stop := by
  cases hgraph : (env start).graph with
  | right =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hgraph] at hstep
      exact hstep.1.1
  | left =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hgraph] at hstep
      exact hstep.1.1
  | both =>
      rw [
        ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
        hgraph] at hstep
      omega

/-! ## Finite and infinite schedules -/

/-- A prefix of `count` completed operational cuts.  Values of `cut` and
`direction` above `count` are harmless total extensions. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutPrefix
    (env : EnvironmentSequence In₁ In₂) (count : Nat) where
  cut : Nat → Nat
  direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)
  initial : cut 0 = 0
  step : ∀ k : Nat, k < count →
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep
      env (cut k) (cut (k + 1)) (direction k)

/-- An infinite sequence of completed cuts.  This is the branch with
infinitely many strict-side changes or BOTH rounds. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
    (env : EnvironmentSequence In₁ In₂) where
  cut : Nat → Nat
  direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)
  initial : cut 0 = 0
  step : ∀ k : Nat,
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep
      env (cut k) (cut (k + 1)) (direction k)

/-! ## Canonical schedule from the operational-close clock -/

/-- Right-oriented physical inputs beginning at an absolute cut. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalRightInputs
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Nat → In₂ × In₁ :=
  fun j ↦ ((env (start + j)).inputTwo, (env (start + j)).inputOne)

/-- Left-oriented physical inputs. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalLeftInputs
    (env : EnvironmentSequence In₁ In₂) (start : Nat) : Nat → In₁ × In₂ :=
  fun j ↦ ((env (start + j)).inputOne, (env (start + j)).inputTwo)

/-- The proof-side bank direction represented by operational block `k`.
For a strict block, `openLength` inputs form the retained prefix and the next
input is its closing receive.  `rowAt` is deliberately supplied by the linked
acknowledgement trace; it is not inferred from the graph. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutDirection
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (rowAt : Nat → PairedEntryRow) (k : Nat) :
    HybridDirection (In₁ := In₁) (In₂ := In₂) :=
  let start := cuts.cuts k
  let length := cuts.openLength k
  match (env start).graph with
  | .right =>
      let inputs :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalRightInputs
          env start
      .strict
        (profiledRawJointUnitRightActualDirection
          (In₁ := In₁) (In₂ := In₂) (rowAt k)
            (DetParityAutomaton.omegaPrefix inputs length) (inputs length))
  | .left =>
      let inputs :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalLeftInputs
          env start
      .strict
        (profiledRawJointUnitLeftActualDirection
          (In₁ := In₁) (In₂ := In₂) (rowAt k)
            (DetParityAutomaton.omegaPrefix inputs length) (inputs length))
  | .both => .simultaneous ((env start).inputOne, (env start).inputTwo)

/-- Every operational-close package canonically supplies the graph/physical-
input part of an infinite bank cut schedule. -/
noncomputable def
    OperationalCloseCutPackage.toBankOperationalCutSchedule
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph))
    (rowAt : Nat → PairedEntryRow) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
      (In₁ := In₁) (In₂ := In₂) env where
  cut := cuts.cuts
  direction :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutDirection
      env cuts rowAt
  initial := cuts.cuts_zero
  step := by
    intro k
    let start := cuts.cuts k
    let stop := cuts.cuts (k + 1)
    have hlt : start < stop := cuts.cuts_strictMono (Nat.lt_succ_self k)
    cases hgraph : (env start).graph with
    | right =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph]
        refine ⟨?_, ?_⟩
        · unfold
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalRightBlock
          refine ⟨hlt, ?_, ?_⟩
          · intro j hjLower hjUpper
            have hstep := cuts.step_eq k
            have hjClosing : j ≤ start + cuts.openLength k := by
              dsimp only [start, stop] at hjLower hjUpper hstep ⊢
              omega
            rcases hjClosing.eq_or_lt with hclose | hopen
            · have hclosing := cuts.closing_graph_eq k
              have hindex : cuts.cuts (k + 1) - 1 =
                  start + cuts.openLength k := by
                dsimp only [start]
                rw [cuts.step_eq]
                omega
              rw [hindex] at hclosing
              rw [hclose, hclosing]
              exact hgraph
            · have hoffset : j = start + (j - start) := by omega
              rw [hoffset,
                cuts.homogeneous k (j - start) (by omega)]
              exact hgraph
          · have hstrict : (env start).graph ≠ .both := by
              rw [hgraph]
              exact Graph.noConfusion
            have hmax := cuts.maximal_of_strict k hstrict
            intro hstop
            exact hmax (hstop.trans hgraph.symm)
        · refine ⟨
            profiledRawJointUnitRightActualDirection
              (In₁ := In₁) (In₂ := In₂) (rowAt k)
              (DetParityAutomaton.omegaPrefix
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalRightInputs
                  env start) (cuts.openLength k))
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalRightInputs
                env start (cuts.openLength k)), rfl, ?_⟩
          simp [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutDirection,
            start, hgraph]
    | left =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph]
        refine ⟨?_, ?_⟩
        · unfold
            ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankIsMaximalLeftBlock
          refine ⟨hlt, ?_, ?_⟩
          · intro j hjLower hjUpper
            have hstep := cuts.step_eq k
            have hjClosing : j ≤ start + cuts.openLength k := by
              dsimp only [start, stop] at hjLower hjUpper hstep ⊢
              omega
            rcases hjClosing.eq_or_lt with hclose | hopen
            · have hclosing := cuts.closing_graph_eq k
              have hindex : cuts.cuts (k + 1) - 1 =
                  start + cuts.openLength k := by
                dsimp only [start]
                rw [cuts.step_eq]
                omega
              rw [hindex] at hclosing
              rw [hclose, hclosing]
              exact hgraph
            · have hoffset : j = start + (j - start) := by omega
              rw [hoffset,
                cuts.homogeneous k (j - start) (by omega)]
              exact hgraph
          · have hstrict : (env start).graph ≠ .both := by
              rw [hgraph]
              exact Graph.noConfusion
            have hmax := cuts.maximal_of_strict k hstrict
            intro hstop
            exact hmax (hstop.trans hgraph.symm)
        · refine ⟨
            profiledRawJointUnitLeftActualDirection
              (In₁ := In₁) (In₂ := In₂) (rowAt k)
              (DetParityAutomaton.omegaPrefix
                (profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalLeftInputs
                  env start) (cuts.openLength k))
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalLeftInputs
                env start (cuts.openLength k)), rfl, ?_⟩
          simp [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutDirection,
            start, hgraph]
    | both =>
        rw [
          ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutStep,
          hgraph]
        refine ⟨?_, ?_⟩
        · dsimp only [start, stop]
          rw [cuts.step_eq, cuts.zero_open_of_both k hgraph]
        · simp [
            profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutDirection,
            start, hgraph]

/-- The row of the closing receive of a maximal strict block.  A singleton
block is the first receive in its phase; every longer homogeneous block closes
after at least one same-side receive. -/
def
    OperationalCloseCutPackage.bankOperationalRowAt
    {graphs : Nat → Graph} (cuts : OperationalCloseCutPackage graphs)
    (k : Nat) : PairedEntryRow :=
  if cuts.openLength k = 0 then .first else .both

/-- Fully canonical bank cut schedule of an operational-close package. -/
noncomputable def
    OperationalCloseCutPackage.toCanonicalBankOperationalCutSchedule
    (env : EnvironmentSequence In₁ In₂)
    (cuts : OperationalCloseCutPackage (fun n ↦ (env n).graph)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
      (In₁ := In₁) (In₂ := In₂) env :=
  OperationalCloseCutPackage.toBankOperationalCutSchedule env cuts
    (OperationalCloseCutPackage.bankOperationalRowAt cuts)

/-- Canonical schedule in the recurrent-BOTH regime. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutScheduleOfGraphBothRecurrent
    (env : EnvironmentSequence In₁ In₂)
    (hboth : GraphBothRecurrent (fun n ↦ (env n).graph)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
      (In₁ := In₁) (In₂ := In₂) env :=
  let cuts :=
    operationalCloseCutPackageOfGraphBothRecurrent
      (fun n ↦ (env n).graph) hboth
  OperationalCloseCutPackage.toCanonicalBankOperationalCutSchedule env cuts

/-- Canonical schedule in the persistent strict-reversal regime. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutScheduleOfPersistentStrictReversalTail
    (env : EnvironmentSequence In₁ In₂)
    (hreversal : PersistentStrictReversalTail (fun n ↦ (env n).graph)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
      (In₁ := In₁) (In₂ := In₂) env :=
  let cuts :=
    operationalCloseCutPackageOfPersistentStrictReversalTail
      (fun n ↦ (env n).graph) hreversal
  OperationalCloseCutPackage.toCanonicalBankOperationalCutSchedule env cuts

/-- Restrict an infinite cut schedule to any finite number of cuts. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule.toPrefix
    {env : EnvironmentSequence In₁ In₂}
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env)
    (count : Nat) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutPrefix
      (In₁ := In₁) (In₂ := In₂) env count where
  cut := schedule.cut
  direction := schedule.direction
  initial := schedule.initial
  step := fun k _hk ↦ schedule.step k

/-! ## Conditional cut-to-path theorems -/

/-- The sole controller-specific obligation left by the cut construction:
the authority state at the end of each operational block is the exact bank
child named by that block's physical-input direction. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutExact
    {env : EnvironmentSequence In₁ In₂}
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env)
    (trace : Nat → BankControl A strategy hwin) : Prop :=
  ∀ k : Nat,
    trace (schedule.cut (k + 1)) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin (trace (schedule.cut k)) (schedule.direction k)

/-- The exact-cut obligation specialized to the canonical linked-deferred
authority trace.  Same-side retention, phase restart at strict switches, and
BOTH close are exactly the three operational facts needed to prove it. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOperationalCutExact
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env) : Prop :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutExact A
    strategy hwin schedule
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
        A strategy hwin initialTag env)

/-- A finite sequence of exact cut equations is the corresponding finite
prefix of the root-started marked-bank child run. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtOperationalCuts_eq_childRun_upto
    (env : EnvironmentSequence In₁ In₂) (count : Nat)
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutPrefix
        (In₁ := In₁) (In₂ := In₂) env count)
    (control : CommonControl A strategy hwin)
    (trace : Nat → BankControl A strategy hwin)
    (hroot : trace (schedule.cut 0) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hexact : ∀ k : Nat, k < count →
      trace (schedule.cut (k + 1)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace (schedule.cut k)) (schedule.direction k)) :
    ∀ k : Nat, k ≤ count →
      trace (schedule.cut k) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control schedule.direction k := by
  intro k hk
  induction k with
  | zero => simpa using hroot
  | succ k ih =>
      have hklt : k < count := Nat.lt_of_succ_le hk
      rw [hexact k hklt, ih (Nat.le_of_lt hklt)]
      exact
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_succ
          A strategy hwin control schedule.direction k).symm

/-- With infinitely many completed operational cuts, the entire cut-indexed
authority trace is one allowed marked-bank path. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtOperationalCuts_eq_childRun
    (env : EnvironmentSequence In₁ In₂)
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env)
    (control : CommonControl A strategy hwin)
    (trace : Nat → BankControl A strategy hwin)
    (hroot : trace (schedule.cut 0) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hexact : ∀ k : Nat,
      trace (schedule.cut (k + 1)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace (schedule.cut k)) (schedule.direction k)) :
    ∀ k : Nat,
      trace (schedule.cut k) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control schedule.direction k := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun A
      strategy hwin control schedule.direction (fun k ↦ trace (schedule.cut k))
        hroot
  exact hexact

/-- Canonical linked-authority specialization: once the single exact-cut
predicate is proved, no further controller reasoning remains in the path
construction. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAtOperationalCuts_eq_childRun
    (initialTag :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A
        strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env)
    (control : CommonControl A strategy hwin)
    (hroot :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env (schedule.cut 0) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy
          hwin control)
    (hexact :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredOperationalCutExact
        A strategy hwin initialTag env schedule) :
    ∀ k : Nat,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env (schedule.cut k) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control schedule.direction k := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtOperationalCuts_eq_childRun
      A strategy hwin env schedule control
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env)
        hroot
  intro k
  exact hexact k

/-- The infinite result names the already constructed allowed bank path whose
states are reached at the operational cuts. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutPath
    (env : EnvironmentSequence In₁ In₂)
    (schedule :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankOperationalCutSchedule
        (In₁ := In₁) (In₂ := In₂) env)
    (control : CommonControl A strategy hwin)
    (trace : Nat → BankControl A strategy hwin)
    (hroot : trace (schedule.cut 0) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hexact : ∀ k : Nat,
      trace (schedule.cut (k + 1)) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace (schedule.cut k)) (schedule.direction k)) :
    ∃ direction : Nat →
        HybridDirection (In₁ := In₁) (In₂ := In₂),
      ∀ k : Nat,
        trace (schedule.cut k) =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
            A strategy hwin control direction k := by
  exact ⟨schedule.direction,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTraceAtOperationalCuts_eq_childRun
      A strategy hwin env schedule control trace hroot hexact⟩

end

end DetParityAutomaton

end DistributedSynthesis
