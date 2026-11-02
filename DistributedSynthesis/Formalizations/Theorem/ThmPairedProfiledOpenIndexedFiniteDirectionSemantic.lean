/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenIndexedDirectionSummary
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedCorrelatedSemanticParity

/-!
# Finite-direction presentation of the correlated semantic tree

The raw correlated direction contains arbitrarily long tagged pasts.  At a
fixed public move, their effect on the next public code is captured by the
finite `ProfiledOpenIndexedDirectionSummary`.  To obtain one fixed branch
alphabet, we tag each summary by the move at which it is typed.

A tag is *realizable* at a public code and move when its move tag matches and
the summary is in the image of the raw summarization map.  We choose a raw
representative in that case.  Every other tag is sent to an explicit
empty-past fallback direction.  Thus every finite-tag branch maps to a raw
branch, while no operational realizability is claimed for mismatched or
unrealizable tags.
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

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
variable (hwin : ∀ env : EnvironmentSequence In₁ In₂,
  A.Accepts (execution strategy env))
variable (basis : ∀ state : PairedProfiledTreeState A,
  (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)

/-! ## Fixed finite tags and raw representatives -/

/-- One fixed finite direction alphabet: a finite move tag together with a
finite summary typed at that move. -/
abbrev ProfiledOpenIndexedFiniteDirectionTag :=
  Σ move : ProfiledOpenIndexedBiBeliefMove A,
    ProfiledOpenIndexedDirectionSummary A (I := I) move

noncomputable instance profiledOpenIndexedFiniteDirectionTag_fintype :
    Fintype (ProfiledOpenIndexedFiniteDirectionTag A (I := I)) := by
  classical
  infer_instance

/-- Evidence that a finite tag is the summary of an actual raw direction at
the requested public code and move. -/
structure ProfiledOpenIndexedFiniteDirectionRealization
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) where
  move_eq : tag.1 = move
  raw : ProfiledOpenIndexedBiBeliefDirection
    (I := I) (In₁ := In₁) (In₂ := In₂)
  summary_eq :
    profiledOpenIndexedDirectionSummarize A code move raw =
      move_eq ▸ tag.2

/-- Realizability is deliberately explicit.  In particular it is false for
a mismatched move tag, and it need not hold for every element of the ambient
finite control type. -/
def ProfiledOpenIndexedFiniteDirectionTag.RealizableAt
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A) : Prop :=
  Nonempty
    (ProfiledOpenIndexedFiniteDirectionRealization A code move tag)

/-- Explicit raw fallback for a mismatched or unrealizable tag.  Its pivots
and current inputs are retained, while both unbounded pasts are empty. -/
def profiledOpenIndexedFiniteDirectionFallback
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  { rightPivot := tag.2.rightPivot
    rightTaggedPast := []
    rightInput := tag.2.rightInput
    leftPivot := tag.2.leftPivot
    leftTaggedPast := []
    leftInput := tag.2.leftInput }

/-- Chosen realization of a realizable tag. -/
noncomputable def profiledOpenIndexedFiniteDirectionRealization
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A code move) :
    ProfiledOpenIndexedFiniteDirectionRealization A code move tag :=
  Classical.choice hreal

/-- Total raw representative of every finite tag. -/
noncomputable def profiledOpenIndexedRawDirectionOfFiniteTag
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) := by
  classical
  exact if hreal : tag.RealizableAt A code move then
    (profiledOpenIndexedFiniteDirectionRealization A code move tag hreal).raw
  else profiledOpenIndexedFiniteDirectionFallback A tag

section
omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

theorem profiledOpenIndexedRawDirectionOfFiniteTag_eq_realization
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A code move) :
    profiledOpenIndexedRawDirectionOfFiniteTag A code move tag =
      (profiledOpenIndexedFiniteDirectionRealization A code move tag
        hreal).raw := by
  simp [profiledOpenIndexedRawDirectionOfFiniteTag, hreal]

theorem profiledOpenIndexedRawDirectionOfFiniteTag_eq_fallback
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : ¬ tag.RealizableAt A code move) :
    profiledOpenIndexedRawDirectionOfFiniteTag A code move tag =
      profiledOpenIndexedFiniteDirectionFallback A tag := by
  simp [profiledOpenIndexedRawDirectionOfFiniteTag, hreal]

/-- A mismatched move tag is never advertised as realizable. -/
theorem not_profiledOpenIndexedFiniteDirectionTag_realizableAt_of_move_ne
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hne : tag.1 ≠ move) :
    ¬ tag.RealizableAt A code move := by
  rintro ⟨realization⟩
  exact hne realization.move_eq

end

/-! ## Finite-tag successor -/

/-- Total public successor on the fixed finite tag alphabet. -/
noncomputable def profiledOpenIndexedBiBeliefNextFiniteTag
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedBiBeliefCode A (I := I) :=
  profiledOpenIndexedBiBeliefNext A code move
    (profiledOpenIndexedRawDirectionOfFiniteTag A code move tag)

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- On a realizable tag, the total successor is exactly the already proved
finite-summary successor. -/
theorem profiledOpenIndexedBiBeliefNextFiniteTag_eq_summary
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (move : ProfiledOpenIndexedBiBeliefMove A)
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A code move) :
    profiledOpenIndexedBiBeliefNextFiniteTag A code move tag =
      profiledOpenIndexedBiBeliefNextSummary A code move
        ((profiledOpenIndexedFiniteDirectionRealization A code move tag
          hreal).move_eq ▸ tag.2) := by
  rw [profiledOpenIndexedBiBeliefNextFiniteTag,
    profiledOpenIndexedRawDirectionOfFiniteTag_eq_realization A code move tag
      hreal]
  let realization := profiledOpenIndexedFiniteDirectionRealization A code
    move tag hreal
  rw [← realization.summary_eq]
  exact (profiledOpenIndexedBiBeliefNextSummary_summarize A code move
    realization.raw).symm

/-! ## Finite-tag correlated semantic tree -/

/-- Semantic step driven by a finite tag through its total raw
representative. -/
noncomputable def profiledOpenIndexedCorrelatedFiniteTagNext
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I) :=
  profiledOpenIndexedCorrelatedSemanticNext A strategy hwin basis state
    (profiledOpenIndexedRawDirectionOfFiniteTag A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) tag)

/-- The complete correlated unfolding over the fixed finite tag alphabet. -/
noncomputable def profiledOpenIndexedCorrelatedFiniteTagSemanticTree
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    SourceFreeBeliefSemanticTree
      (ProfiledOpenIndexedFiniteDirectionTag A (I := I))
      (ProfiledOpenIndexedBiBeliefMove A)
      (ProfiledOpenIndexedBiBeliefCode A (I := I)) where
  Semantic := ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
    (I := I)
  initial := initial
  step := profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis
  code := fun state => state.code A strategy hwin basis
  move := fun state => state.move A strategy hwin basis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Exact code equation for the total finite-tag semantic successor. -/
theorem profiledOpenIndexedCorrelatedFiniteTagNext_code
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis state tag
      |>.code A strategy hwin basis) =
      profiledOpenIndexedBiBeliefNextFiniteTag A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis) tag := by
  exact profiledOpenIndexedCorrelatedSemanticNext_code A strategy hwin basis
    state (profiledOpenIndexedRawDirectionOfFiniteTag A
      (state.code A strategy hwin basis)
      (state.move A strategy hwin basis) tag)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- On coherent tags, the semantic child's code is the direct finite-summary
computation. -/
theorem profiledOpenIndexedCorrelatedFiniteTagNext_code_eq_summary
    (state : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin basis
      (I := I))
    (tag : ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (hreal : tag.RealizableAt A (state.code A strategy hwin basis)
      (state.move A strategy hwin basis)) :
    (profiledOpenIndexedCorrelatedFiniteTagNext A strategy hwin basis state tag
      |>.code A strategy hwin basis) =
      profiledOpenIndexedBiBeliefNextSummary A
        (state.code A strategy hwin basis)
        (state.move A strategy hwin basis)
        ((profiledOpenIndexedFiniteDirectionRealization A
          (state.code A strategy hwin basis)
          (state.move A strategy hwin basis) tag hreal).move_eq ▸ tag.2) := by
  rw [profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis]
  exact profiledOpenIndexedBiBeliefNextFiniteTag_eq_summary A
    (state.code A strategy hwin basis)
    (state.move A strategy hwin basis) tag hreal

/-! ## Every finite-tag branch lifts to a raw branch -/

/-- Raw branch obtained by reading the chosen representative at the finite
semantic state reached before each tag. -/
noncomputable def profiledOpenIndexedRawBranchOfFiniteTagBranch
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    ProfiledOpenIndexedBiBeliefDirection
      (I := I) (In₁ := In₁) (In₂ := In₂) :=
  let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
    hwin basis initial
  let state := finite.stateAt (branchNode branch n)
  profiledOpenIndexedRawDirectionOfFiniteTag A
    (state.code A strategy hwin basis)
    (state.move A strategy hwin basis) (branch n)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The original raw semantic tree on the lifted branch and the finite-tag
tree reach literally the same proof-side semantic state at every depth. -/
theorem profiledOpenIndexedRawBranchOfFiniteTagBranch_stateAt
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I))
    (n : Nat) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
      hwin basis initial
    raw.stateAt
        (branchNode
          (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin basis
            initial branch) n) =
      finite.stateAt (branchNode branch n) := by
  let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
    initial
  let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
    hwin basis initial
  change raw.stateAt
      (branchNode
        (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin basis
          initial branch) n) =
    finite.stateAt (branchNode branch n)
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode
            (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin
              basis initial branch) (n + 1) =
            branchNode
                (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin
                  basis initial branch) n ++
              [profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin
                basis initial branch n] from rfl,
        show branchNode branch (n + 1) =
            branchNode branch n ++ [branch n] from rfl,
        raw.stateAt_append, finite.stateAt_append, ih]
      rfl

/-- Hence the finite-tag child-code word is exactly the raw child-code word
of its lifted branch, including all mismatched/unrealizable fallback tags. -/
theorem profiledOpenIndexedCorrelatedFiniteTag_childCodeWord_eq_raw
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
      initial
    let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
      hwin basis initial
    finite.childCodeWord branch =
      raw.childCodeWord
        (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin basis
          initial branch) := by
  let raw := profiledOpenIndexedCorrelatedSemanticTree A strategy hwin basis
    initial
  let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
    hwin basis initial
  funext n
  change
    (finite.stateAt (branchNode branch (n + 1))).code A strategy hwin basis =
      (raw.stateAt
        (branchNode
          (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin basis
            initial branch) (n + 1))).code A strategy hwin basis
  exact congrArg (fun state => state.code A strategy hwin basis)
    (profiledOpenIndexedRawBranchOfFiniteTagBranch_stateAt A strategy hwin
      basis initial branch (n + 1)).symm

/-- Every finite-tag branch inherits parity from its literal raw lift. -/
theorem profiledOpenIndexedCorrelatedFiniteTagSemanticTree_codeDPA_accepts
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I))
    (branch : Nat → ProfiledOpenIndexedFiniteDirectionTag A (I := I)) :
    (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A)).Accepts
      ((profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy hwin
        basis initial).childCodeWord branch) := by
  rw [profiledOpenIndexedCorrelatedFiniteTag_childCodeWord_eq_raw A strategy
    hwin basis initial branch]
  exact profiledOpenIndexedCorrelatedSemanticTree_codeDPA_accepts A strategy
    hwin basis initial
      (profiledOpenIndexedRawBranchOfFiniteTagBranch A strategy hwin basis
        initial branch)

end

/-! ## Unconditional finite-branch rationalization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Complete code-observable parity certificate on the finite tag alphabet. -/
theorem profiledOpenIndexedCorrelatedFiniteTag_codeParityCertificate
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
      hwin basis initial
    SourceFreeBeliefCodeParityCertificate
      (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A))
      (initial.code A strategy hwin basis)
      (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNextFiniteTag A) finite := by
  let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
    hwin basis initial
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact ProfiledOpenIndexedCorrelatedSemanticState.valid A strategy hwin basis
      (finite.stateAt node)
  · intro node tag
    exact profiledOpenIndexedCorrelatedFiniteTagNext_code A strategy hwin basis
      (finite.stateAt node) tag
  · intro branch
    exact profiledOpenIndexedCorrelatedFiniteTagSemanticTree_codeDPA_accepts A
      strategy hwin basis initial branch

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Because the tag alphabet is finite, the checked finite-direction Rabin
basis now yields a finite rational policy with no arbitrary-direction basis
hypothesis. -/
theorem nonempty_profiledOpenIndexedCorrelatedFiniteTagRationalPolicy
    (initial : ProfiledOpenIndexedCorrelatedSemanticState A strategy hwin
      basis (I := I)) :
    Nonempty (SourceFreeBeliefCodeParityRationalPolicy
      (codedAlternatingIndexedLineageCodeDPA
        (initial.code A strategy hwin basis)
        (profiledOpenIndexedBiBeliefCurrentSlots A)
        (profiledOpenIndexedRootPriority A))
      (initial.code A strategy hwin basis)
      (ProfiledOpenIndexedBiBeliefValid A)
      (profiledOpenIndexedBiBeliefNextFiniteTag A)) := by
  let finite := profiledOpenIndexedCorrelatedFiniteTagSemanticTree A strategy
    hwin basis initial
  apply SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (raw := finite)
  · exact profiledOpenIndexedCorrelatedFiniteTag_codeParityCertificate A
      strategy hwin basis initial
  · exact InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _

end

end DetParityAutomaton

end DistributedSynthesis
