/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFreshPolicyFixedRerootControlEquations

/-!
# Canonical physical schedule for one fresh fixed policy

An arbitrary close schedule hides a harmless-looking circularity: its roots
determine the root-oriented cuts, while the physical input list of its next
query is determined by those cuts.  This file removes that circularity by
recursing on the proof-side pair `(current cut, current policy root)`.

At each step we first compute the next root-oriented cut, then read the
literal finite physical input prefix and closing input, and finally take the
query's checked target.  Projecting this recursion gives both the schedule and
the cuts used by the existing acceptance layer.  Consequently query length is
automatic rather than a carrier invariant.

Everything in this construction is proof-side.  Neither process receives the
current root, row, graph, cut, or orientation.
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
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

/-- Physical input pairs in the order expected by a right-block controller,
read from an absolute physical offset. -/
def profiledRawJointUnitPhysicalRightInputs
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₂ × In₁ :=
  fun j ↦ ((physicalEnv (start + j)).inputTwo,
    (physicalEnv (start + j)).inputOne)

/-- Physical input pairs in the order expected by a left-block controller. -/
def profiledRawJointUnitPhysicalLeftInputs
    (physicalEnv : EnvironmentSequence In₁ In₂) (start : Nat) :
    Nat → In₁ × In₂ :=
  fun j ↦ ((physicalEnv (start + j)).inputOne,
    (physicalEnv (start + j)).inputTwo)

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A literal right input prefix reproduces the physical environment on every
round whose graph is right. -/
theorem profiledRawJointUnitPhysicalRightInputs_environment_eq
    (physicalEnv : EnvironmentSequence In₁ In₂) (start length : Nat)
    (hgraph : ∀ j : Nat, j < length →
      (physicalEnv (start + j)).graph = .right) :
    ∀ j : Nat, j <
        (omegaPrefix
          (profiledRawJointUnitPhysicalRightInputs physicalEnv start)
          length).length →
      OmegaWord.drop physicalEnv start j =
        profiledRawJointUnitStrictRightEnvironment
          (omegaOfList
            (omegaPrefix
                (profiledRawJointUnitPhysicalRightInputs physicalEnv start)
                length ++
              [profiledRawJointUnitPhysicalRightInputs physicalEnv start
                length])) j := by
  intro j hj
  let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv start
  have hjLength : j < length := by
    simpa [omegaPrefix] using hj
  have hjPrefix : j < (omegaPrefix inputs length).length := by
    simpa [omegaPrefix] using hjLength
  have hjWord : j < (omegaPrefix inputs length ++ [inputs length]).length := by
    simp [omegaPrefix]
    omega
  have hword :
      omegaOfList (omegaPrefix inputs length ++ [inputs length]) j =
        inputs j := by
    rw [omegaOfList_eq_getElem _ j hjWord,
      List.getElem_append_left hjPrefix]
    simp [omegaPrefix]
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment,
      inputs, profiledRawJointUnitPhysicalRightInputs] using
        (congrArg Prod.snd hword).symm
  · apply Prod.ext
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment,
      inputs, profiledRawJointUnitPhysicalRightInputs] using
        (congrArg Prod.fst hword).symm
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictRightEnvironment] using
        hgraph j hjLength

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Left-oriented mirror of the literal environment-prefix equation. -/
theorem profiledRawJointUnitPhysicalLeftInputs_environment_eq
    (physicalEnv : EnvironmentSequence In₁ In₂) (start length : Nat)
    (hgraph : ∀ j : Nat, j < length →
      (physicalEnv (start + j)).graph = .left) :
    ∀ j : Nat, j <
        (omegaPrefix
          (profiledRawJointUnitPhysicalLeftInputs physicalEnv start)
          length).length →
      OmegaWord.drop physicalEnv start j =
        profiledRawJointUnitStrictLeftEnvironment
          (omegaOfList
            (omegaPrefix
                (profiledRawJointUnitPhysicalLeftInputs physicalEnv start)
                length ++
              [profiledRawJointUnitPhysicalLeftInputs physicalEnv start
                length])) j := by
  intro j hj
  let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv start
  have hjLength : j < length := by
    simpa [omegaPrefix] using hj
  have hjPrefix : j < (omegaPrefix inputs length).length := by
    simpa [omegaPrefix] using hjLength
  have hjWord : j < (omegaPrefix inputs length ++ [inputs length]).length := by
    simp [omegaPrefix]
    omega
  have hword :
      omegaOfList (omegaPrefix inputs length ++ [inputs length]) j =
        inputs j := by
    rw [omegaOfList_eq_getElem _ j hjWord,
      List.getElem_append_left hjPrefix]
    simp [omegaPrefix]
  apply EnvironmentRound.equivProd.injective
  apply Prod.ext
  · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment,
      inputs, profiledRawJointUnitPhysicalLeftInputs] using
        (congrArg Prod.fst hword).symm
  · apply Prod.ext
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment,
      inputs, profiledRawJointUnitPhysicalLeftInputs] using
        (congrArg Prod.snd hword).symm
    · simpa [OmegaWord.drop, profiledRawJointUnitStrictLeftEnvironment] using
        hgraph j hjLength

/-- The literal close query cut from one physical half-open interval.

The last round before `next` is the closing move.  All preceding rounds are
stored in `past`.  The definition is total; productive clocks later ensure
that `current < next`. -/
noncomputable def profiledRawJointUnitPolicyPhysicalCloseQuery
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (current next : Nat) (row : PairedEntryRow)
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) :
    ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy root :=
  let openLength := next - current - 1
  match root with
  | .inl source =>
      let inputs := profiledRawJointUnitPhysicalRightInputs physicalEnv current
      .right source row (omegaPrefix inputs openLength) (inputs openLength)
  | .inr source =>
      let inputs := profiledRawJointUnitPhysicalLeftInputs physicalEnv current
      .left source row (omegaPrefix inputs openLength) (inputs openLength)

omit [Inhabited Out₁] [Inhabited Out₂] [DecidableEq In₁] [DecidableEq In₂] in
@[simp] theorem profiledRawJointUnitPolicyPhysicalCloseQuery_inputListLength
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (current next : Nat) (row : PairedEntryRow)
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) :
    (profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial policy
      physicalEnv current next row root).inputListLength A strategy initial
        policy = next - current - 1 := by
  cases root <;>
    simp [profiledRawJointUnitPolicyPhysicalCloseQuery,
      ProfiledRawJointUnitPolicyCloseQuery.inputListLength, omegaPrefix]

/-- Simultaneously computed current physical cut and current fixed-policy
root.  This is the non-circular core of the construction. -/
noncomputable def profiledRawJointUnitPolicyPhysicalThreadState
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Nat →
      Nat × ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
        policy
  | 0 => (0, seed)
  | k + 1 =>
      let current := profiledRawJointUnitPolicyPhysicalThreadState physicalEnv
        base hterm seed rowAt k
      let next := rootOrientedCloseNext
        (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
          (current.2.graph A strategy initial policy) current.1
      let query := profiledRawJointUnitPolicyPhysicalCloseQuery A strategy
        initial policy physicalEnv (base + current.1) (base + next) (rowAt k)
          current.2
      (next, query.target A strategy initial policy bank)

/-- Projected canonical physical cuts. -/
noncomputable def profiledRawJointUnitPolicyPhysicalThreadCuts
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : Nat → Nat :=
  fun k ↦ (profiledRawJointUnitPolicyPhysicalThreadState A strategy initial
    policy bank physicalEnv base hterm seed rowAt k).1

/-- Projected canonical fixed-policy roots. -/
noncomputable def profiledRawJointUnitPolicyPhysicalThreadRoot
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) (k : Nat) :
    ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A) policy :=
  (profiledRawJointUnitPolicyPhysicalThreadState A strategy initial policy bank
    physicalEnv base hterm seed rowAt k).2

/-- The schedule induced by the simultaneous cut/root recursion.  Its value
away from the actual scheduled root is only a total dependent function and is
never observed by the proof. -/
noncomputable def profiledRawJointUnitPolicyPhysicalCloseSchedule
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) :
    ProfiledRawJointUnitPolicyCloseSchedule A strategy initial policy :=
  fun k root ↦
    let current := profiledRawJointUnitPolicyPhysicalThreadCuts A strategy
      initial policy bank physicalEnv base hterm seed rowAt k
    let next := rootOrientedCloseNext
      (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
        (root.graph A strategy initial policy) current
    profiledRawJointUnitPolicyPhysicalCloseQuery A strategy initial policy
      physicalEnv (base + current) (base + next) (rowAt k) root

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Scheduled roots of the projected schedule are exactly the roots of the
simultaneous physical recursion. -/
theorem profiledRawJointUnitPolicyScheduledRoot_physicalCloseSchedule
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : ∀ k : Nat,
    profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank seed
        (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial
          policy bank physicalEnv base hterm seed rowAt) k =
      profiledRawJointUnitPolicyPhysicalThreadRoot A strategy initial policy
        bank physicalEnv base hterm seed rowAt k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [profiledRawJointUnitPolicyScheduledRoot_succ, ih]
      rfl

/-- The root-oriented cuts generated by the projected schedule are exactly
the cut coordinates of the simultaneous physical recursion. -/
theorem profiledRawJointUnitPolicyRootOrientedCuts_physicalCloseSchedule
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) : ∀ k : Nat,
    profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
        physicalEnv base hterm seed
          (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial
            policy bank physicalEnv base hterm seed rowAt) k =
      profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial policy
        bank physicalEnv base hterm seed rowAt k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      change rootOrientedCloseNext
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
            (profiledRawJointUnitPolicyScheduledGraph A strategy initial policy
              bank seed
                (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
                  initial policy bank physicalEnv base hterm seed rowAt) k)
            (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
              policy bank physicalEnv base hterm seed
                (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
                  initial policy bank physicalEnv base hterm seed rowAt) k) =
        (profiledRawJointUnitPolicyPhysicalThreadState A strategy initial policy
          bank physicalEnv base hterm seed rowAt (k + 1)).1
      rw [ih]
      unfold profiledRawJointUnitPolicyScheduledGraph
      rw [profiledRawJointUnitPolicyScheduledRoot_physicalCloseSchedule]
      rfl

/-- The canonical schedule's finite input-list length is the canonical
root-oriented open length.  Thus the second field of the old fixed-reroot
invariant is constructional. -/
theorem profiledRawJointUnitPolicyPhysicalCloseSchedule_inputListLengthAt
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (rowAt : Nat → PairedEntryRow) (k : Nat) :
    let schedule := profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy
      initial policy bank physicalEnv base hterm seed rowAt
    let query := schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)
    query.inputListLength A strategy initial policy =
      profiledRawJointUnitPolicyRootOrientedOpenLength A strategy initial
        policy bank physicalEnv base hterm seed schedule k := by
  dsimp only
  rw [profiledRawJointUnitPolicyScheduledRoot_physicalCloseSchedule]
  simp only [profiledRawJointUnitPolicyPhysicalCloseSchedule]
  rw [profiledRawJointUnitPolicyPhysicalCloseQuery_inputListLength]
  change base + rootOrientedCloseNext
          (profiledRawJointPhysicalGraphTail physicalEnv base) hterm
            ((profiledRawJointUnitPolicyPhysicalThreadRoot A strategy initial
              policy bank physicalEnv base hterm seed rowAt k).graph A strategy
                initial policy)
            (profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial
              policy bank physicalEnv base hterm seed rowAt k) -
        (base + profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial
          policy bank physicalEnv base hterm seed rowAt k) - 1 =
      profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy bank
          physicalEnv base hterm seed
            (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial
              policy bank physicalEnv base hterm seed rowAt) (k + 1) -
        profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
          bank physicalEnv base hterm seed
            (profiledRawJointUnitPolicyPhysicalCloseSchedule A strategy initial
              policy bank physicalEnv base hterm seed rowAt) k - 1
  rw [profiledRawJointUnitPolicyRootOrientedCuts_physicalCloseSchedule,
    profiledRawJointUnitPolicyRootOrientedCuts_physicalCloseSchedule]
  change base +
          profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial
            policy bank physicalEnv base hterm seed rowAt (k + 1) -
        (base + profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial
          policy bank physicalEnv base hterm seed rowAt k) - 1 =
      profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial policy
          bank physicalEnv base hterm seed rowAt (k + 1) -
        profiledRawJointUnitPolicyPhysicalThreadCuts A strategy initial policy
          bank physicalEnv base hterm seed rowAt k - 1
  omega

end

end

end DetParityAutomaton

end DistributedSynthesis
