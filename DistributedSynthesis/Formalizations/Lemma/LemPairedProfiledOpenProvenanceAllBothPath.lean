/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenConsecutiveBothRecut
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenProvenanceDelayedBoundaryFork

/-!
# One coherent provenance path on an all-simultaneous environment

An infinite run of `.both` rounds never provides a later strict side with
which to resolve the delayed two-way fork.  It also does not need one: choose
either proof-side initial orientation and consume every real simultaneous
round by one ordinary zero-open direction.  The orientation then alternates
definitionally.

This file constructs the corresponding cursor recurrence.  Every query is
summarized at the *current cursor code*, every step is one exact edge of the
same provenance policy, and the resulting paired direction branch flattens
pointwise to the supplied physical environment.  The cursor is proof data;
no process receives its side, row, code, or selected candidate.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I] [Inhabited I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
variable (initialCode : ProfiledOpenIndexedBiBeliefCode A (I := I))
variable (codePolicy : ProfiledOpenIndexedProvenanceCodeRationalPolicy A
  strategy hwin basis initialCode)

variable {initialState : PairedProfiledTreeState A}
variable (fixedPolicy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)
variable (point : ProfiledOpenIndexedOptionalControlledSemanticState A
  strategy hwin basis initialCode)
variable (initialRoot : ProfiledFixedPolicyRoot A fixedPolicy)
variable (package : ProfiledOpenProvenancePolicyFixedTablePackage A strategy
  hwin basis initialCode codePolicy fixedPolicy point initialRoot)

private abbrev AllBothQuery :=
  ProfiledOpenWitnessedTableQuery A initialCode

/-- Row of the `n`-th direction.  Only the initial row is arbitrary; every
positive-time direction follows a real simultaneous close. -/
def profiledOpenAllBothRow : Nat → PairedEntryRow
  | 0 => .first
  | _ + 1 => .both

@[simp] theorem profiledOpenAllBothRow_zero :
    profiledOpenAllBothRow 0 = .first :=
  rfl

@[simp] theorem profiledOpenAllBothRow_succ (n : Nat) :
    profiledOpenAllBothRow (n + 1) = .both :=
  rfl

/-- Proof-side paired direction for physical round `n`. -/
def profiledOpenAllBothDirection
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    PairedEntryDirection (In₁ := In₁) (In₂ := In₂) :=
  pairedZeroOpenRoundDirection
    (pairedRoundSideAfter initialSide n) (profiledOpenAllBothRow n) (env n)

/-- The cursor reached before the `n`-th simultaneous query.  The recursive
query is built from that very cursor, hence at its current code and move. -/
noncomputable def profiledOpenProvenancePolicyAllBothCursorAt
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) : Nat → package.branch.Cursor
  | 0 => source
  | n + 1 =>
      let cursor := profiledOpenProvenancePolicyAllBothCursorAt source env
        initialSide n
      let query :=
        profiledOpenProvenancePolicyZeroOpenQueryOfCursor A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package cursor
          (pairedRoundSideAfter initialSide n) (profiledOpenAllBothRow n)
          (env n).inputOne (env n).inputTwo
      cursor.step package.branch query

/-- Literal query consumed at step `n`. -/
noncomputable def profiledOpenProvenancePolicyAllBothQueryAt
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    AllBothQuery A initialCode :=
  let cursor := profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin
    basis initialCode codePolicy fixedPolicy point initialRoot package source
      env initialSide n
  profiledOpenProvenancePolicyZeroOpenQueryOfCursor A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package cursor
    (pairedRoundSideAfter initialSide n) (profiledOpenAllBothRow n)
    (env n).inputOne (env n).inputTwo

@[simp] theorem profiledOpenProvenancePolicyAllBothCursorAt_zero
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) :
    profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source env
        initialSide 0 = source :=
  rfl

theorem profiledOpenProvenancePolicyAllBothCursorAt_succ
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source env
          initialSide (n + 1) =
      (profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source env
          initialSide n).step package.branch
        (profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin basis
          initialCode codePolicy fixedPolicy point initialRoot package source
          env initialSide n) :=
  rfl

/-- Every all-`.both` query has the advertised alternating proof-side side. -/
@[simp] theorem profiledOpenProvenancePolicyAllBothQueryAt_side
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    (profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source env
        initialSide n).1.1.1 = pairedRoundSideAfter initialSide n := by
  rfl

/-- The next query side is the opposite side, without a runtime side test. -/
theorem profiledOpenProvenancePolicyAllBothQueryAt_side_succ
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    (profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source env
        initialSide (n + 1)).1.1.1 =
      (profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source env
          initialSide n).1.1.1.other := by
  change pairedRoundSideAfter initialSide (n + 1) =
    (pairedRoundSideAfter initialSide n).other
  exact pairedRoundSideAfter_succ_eq_other initialSide n

/-- Every query tag is a literal empty-past realization at the current code
and move. -/
theorem profiledOpenProvenancePolicyAllBothQueryAt_realizableAt
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    let cursor := profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        env initialSide n
    let descriptor := profiledOpenProvenancePolicyCursorDescriptor A strategy
      hwin basis initialCode codePolicy fixedPolicy point initialRoot package
        cursor
    (profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin basis
      initialCode codePolicy fixedPolicy point initialRoot package source env
        initialSide n).1.2.RealizableAt A descriptor.code
          descriptor.moveIdentity := by
  exact profiledOpenProvenancePolicyZeroOpenQueryOfCursor_realizableAt A
    strategy hwin basis initialCode codePolicy fixedPolicy point initialRoot
    package _ _ _ _ _

/-- Every step is one exact edge of the same provenance-retagged table. -/
theorem profiledOpenProvenancePolicyAllBothCursorAt_exact
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    let cursor := profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        env initialSide n
    let next := profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        env initialSide (n + 1)
    let query := profiledOpenProvenancePolicyAllBothQueryAt A strategy hwin
      basis initialCode codePolicy fixedPolicy point initialRoot package source
        env initialSide n
    ProfiledOpenProvenancePolicyRetaggedExactEdge A strategy hwin basis
      initialCode codePolicy cursor.actual.2.1 cursor.actual.2.2
      (cursor.move package.branch) query next.actual.1 next.actual.2.2 := by
  dsimp only
  rw [profiledOpenProvenancePolicyAllBothCursorAt_succ]
  exact profiledOpenProvenancePolicyCursorStep_exact A strategy hwin basis
    initialCode codePolicy fixedPolicy point initialRoot package _ _

/-- Every finite all-`.both` cursor remains a genuine continuation of the
single source cursor. -/
theorem profiledOpenProvenancePolicyAllBothCursorAt_reachable
    (source : package.branch.Cursor)
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) : ∀ n : Nat,
    package.branch.CursorReachableFrom source
      (profiledOpenProvenancePolicyAllBothCursorAt A strategy hwin basis
        initialCode codePolicy fixedPolicy point initialRoot package source env
          initialSide n) := by
  intro n
  induction n with
  | zero => exact package.branch.cursorReachableFrom_refl source
  | succ n ih =>
      rw [profiledOpenProvenancePolicyAllBothCursorAt_succ]
      exact package.branch.cursorReachableFrom_step ih _

/-! ## Exact physical flattening -/

section
omit [Inhabited In₁] [Inhabited In₂] [Fintype In₁] [Fintype In₂] [DecidableEq In₁]
    [DecidableEq In₂]

/-- On an actual all-simultaneous environment, direction `n` contributes
exactly physical round `n`. -/
theorem profiledOpenAllBothDirection_chunk
    (env : EnvironmentSequence In₁ In₂)
    (hboth : ∀ n, (env n).graph = .both)
    (initialSide : IndexedLineageSide) (n : Nat) :
    pairedDirectionChunk
        (profiledOpenAllBothDirection env initialSide n)
        (profiledOpenAllBothDirection env initialSide (n + 1)) =
      [env n] := by
  rw [show profiledOpenAllBothDirection env initialSide (n + 1) =
      pairedZeroOpenRoundDirection
        (pairedRoundSideAfter initialSide n).other .both (env (n + 1)) by
    simp [profiledOpenAllBothDirection, pairedRoundSideAfter_other]]
  rw [profiledOpenAllBothDirection,
    pairedDirectionChunk_zeroOpen_other_both]
  simp [forceBothRound_eq_self (env n) (hboth n)]

@[simp] theorem profiledOpenAllBothDirection_blockLength
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) (n : Nat) :
    pairedDirectionBlockLength
        (profiledOpenAllBothDirection env initialSide n) = 1 := by
  unfold profiledOpenAllBothDirection
  cases hside : pairedRoundSideAfter initialSide n <;>
    simp [hside, pairedZeroOpenRoundDirection, pairedDirectionBlockLength]

/-- The direction cuts on an all-simultaneous path are the identity cuts. -/
@[simp] theorem profiledOpenAllBothDirection_cuts
    (env : EnvironmentSequence In₁ In₂)
    (initialSide : IndexedLineageSide) : ∀ n : Nat,
    pairedBranchCuts (profiledOpenAllBothDirection env initialSide) n = n
  | 0 => rfl
  | n + 1 => by
      rw [pairedBranchCuts_succ,
        profiledOpenAllBothDirection_cuts env initialSide n,
        profiledOpenAllBothDirection_blockLength]

/-- **Pointwise physical exactness.**  The infinite paired branch generated
by the all-`.both` recurrence is the supplied environment itself. -/
theorem pairedBranchEnvironment_profiledOpenAllBothDirection
    (env : EnvironmentSequence In₁ In₂)
    (hboth : ∀ n, (env n).graph = .both)
    (initialSide : IndexedLineageSide) :
    pairedBranchEnvironment (profiledOpenAllBothDirection env initialSide) =
      env := by
  funext n
  have hchunk : pairedBranchChunk
      (profiledOpenAllBothDirection env initialSide) n = [env n] := by
    exact profiledOpenAllBothDirection_chunk env hboth initialSide n
  have hat := pairedBranchEnvironment_at
    (profiledOpenAllBothDirection env initialSide) n 0
    (by simpa [hchunk])
  rw [profiledOpenAllBothDirection_cuts] at hat
  simpa [hchunk] using hat

end

end

end DetParityAutomaton

end DistributedSynthesis
