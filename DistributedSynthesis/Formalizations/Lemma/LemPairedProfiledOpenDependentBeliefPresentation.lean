/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenExactDependentReceiverPairTest
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenReceiptSetBeliefHomogeneity
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledOpenStickyRowBankAdapterTest

/-!
# Dependent physical candidates present reachable beliefs

This file consumes the two fail-fast tests at their intended endpoint.

For one fixed public physical frame (descriptor, fixed value, reachable
query, sticky entry row, and current inputs), *every* retained dependent
member/root evaluation emits the same literal physical output pair.  The
receiver equality is the exact dependent pair theorem; the blind sender
equality is definitional.  No shape-free provenance premise remains.

We then retain the finite set of all such evaluations.  A proof-side frame
may be right- or left-oriented, but every candidate in its set has that same
frame.  Pairwise output homogeneity is therefore a theorem.  Instantiating
`ReceiptSetOutputPresentation` leaves only actual coverage: each state in a
reachable local belief must be represented by one retained candidate.  No
candidate, row, orientation, leader, member, or root is selected by a
process.
-/

namespace DistributedSynthesis

universe i u v w x y s

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

/-! ## The exact full-output pair, without a provenance hypothesis -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every two retained dependent evaluations of one right public frame emit
the same complete physical output pair. -/
theorem profiledOpenWitnessedRightPhysicalOutput_exactDependent_pair
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply Prod.ext
  · exact profiledOpenWitnessedRightSenderOutput_dependentEvaluation_pair A
      strategy hwin basis initialCode reachable left right row inputOne
  · exact
      profiledOpenWitnessedRightReceiverOutput_exactDependent_pair A strategy
        hwin basis initialCode reachable left right row inputOne inputTwo

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left-frame mirror. -/
theorem profiledOpenWitnessedLeftPhysicalOutput_exactDependent_pair
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (row : PairedEntryRow) (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left row) inputOne inputTwo =
      profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right row) inputOne inputTwo := by
  apply Prod.ext
  · exact
      profiledOpenWitnessedLeftReceiverOutput_exactDependent_pair A strategy
        hwin basis initialCode reachable left right row inputOne inputTwo
  · exact profiledOpenWitnessedLeftSenderOutput_dependentEvaluation_pair A
      strategy hwin basis initialCode reachable left right row inputTwo

/-! ## Literal consumption of the sticky receiver-bank row -/

open PairedStrategyMemory
open PairedStrategyMemory.PairedInitialProfiledRationalPackage

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- The exact right pair remains homogeneous when its sticky row is read
literally from either retained member of the process-two receiver bank. -/
theorem
    profiledOpenWitnessedRightPhysicalOutput_exactDependent_pair_of_receiverBankRow
    (package : PairedInitialProfiledRationalPackage A)
    {move : EndToEndRightFamilyPairMove A package}
    (bank : EndToEndRightFamilyReceiverBank A package move) (member : Bool)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedRightPinnedValue A initialCode}
    {query : ProfiledOpenFixedRightPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedRightQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedRightReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left (bank member).1)
          inputOne inputTwo =
      profiledOpenWitnessedRightPhysicalOutput A initialCode
          (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right (bank member).1)
          inputOne inputTwo :=
  profiledOpenWitnessedRightPhysicalOutput_exactDependent_pair A strategy hwin
    basis initialCode reachable left right (bank member).1 inputOne inputTwo

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Process-one/left-bank mirror. -/
theorem
    profiledOpenWitnessedLeftPhysicalOutput_exactDependent_pair_of_receiverBankRow
    (package : PairedInitialProfiledRationalPackage A)
    {move : EndToEndLeftFamilyPairMove A package}
    (bank : EndToEndLeftFamilyReceiverBank A package move) (member : Bool)
    {current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I)
      initialCode}
    {value : ProfiledOpenFixedLeftPinnedValue A initialCode}
    {query : ProfiledOpenFixedLeftPinnedBlockQuery A initialCode value}
    (reachable : ProfiledOpenFixedLeftQueryReachable A initialCode value
      query)
    (left right : ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy
      hwin basis initialCode current value query)
    (inputOne : In₁) (inputTwo : In₂) :
    profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable left (bank member).1)
          inputOne inputTwo =
      profiledOpenWitnessedLeftPhysicalOutput A initialCode
          (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
            basis initialCode reachable right (bank member).1)
          inputOne inputTwo :=
  profiledOpenWitnessedLeftPhysicalOutput_exactDependent_pair A strategy hwin
    basis initialCode reachable left right (bank member).1 inputOne inputTwo

/-! ## Finite public frames and all their erased evaluations -/

/-- The public data shared by all retained right member/root alternatives in
one physical round.  `entryRow` is sticky data; the bank adapter installs it
from the receiver's local row bank before this frame is formed. -/
structure ProfiledOpenWitnessedRightBeliefFrame where
  current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode
  value : ProfiledOpenFixedRightPinnedValue A initialCode
  query : ProfiledOpenFixedRightPinnedBlockQuery.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value
  reachable : ProfiledOpenFixedRightQueryReachable.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value query
  entryRow : PairedEntryRow
  inputOne : In₁
  inputTwo : In₂

/-- Left public frame. -/
structure ProfiledOpenWitnessedLeftBeliefFrame where
  current : ProfiledOpenIndexedOldMoveHiddenDescriptor A (I := I) initialCode
  value : ProfiledOpenFixedLeftPinnedValue A initialCode
  query : ProfiledOpenFixedLeftPinnedBlockQuery.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value
  reachable : ProfiledOpenFixedLeftQueryReachable.{i, u, v, x, y, s,
    max i u v x y s} A initialCode value query
  entryRow : PairedEntryRow
  inputOne : In₁
  inputTwo : In₂

/-- A right frame paired with one of all its proof-erased dependent
evaluations. -/
abbrev ProfiledOpenWitnessedRightBeliefCandidate :=
  Σ frame : ProfiledOpenWitnessedRightBeliefFrame A initialCode,
    ProfiledOpenFixedRightReanchoredRowEvaluation A strategy hwin basis
      initialCode frame.current frame.value frame.query

/-- Left candidate. -/
abbrev ProfiledOpenWitnessedLeftBeliefCandidate :=
  Σ frame : ProfiledOpenWitnessedLeftBeliefFrame A initialCode,
    ProfiledOpenFixedLeftReanchoredRowEvaluation A strategy hwin basis
      initialCode frame.current frame.value frame.query

/-- A proof-side round has either a right or a left physical frame.  This sum
is never exposed as a runtime orientation field. -/
abbrev ProfiledOpenWitnessedBeliefFrame :=
  ProfiledOpenWitnessedRightBeliefFrame A initialCode ⊕
    ProfiledOpenWitnessedLeftBeliefFrame A initialCode

/-- Retained candidate alternatives for either frame. -/
abbrev ProfiledOpenWitnessedBeliefCandidate :=
  ProfiledOpenWitnessedRightBeliefCandidate A strategy hwin basis initialCode
    ⊕
  ProfiledOpenWitnessedLeftBeliefCandidate A strategy hwin basis initialCode

/-- Literal physical output of one retained candidate. -/
noncomputable def profiledOpenWitnessedBeliefCandidateOutput
    (candidate : ProfiledOpenWitnessedBeliefCandidate A strategy hwin basis
      initialCode) : Out₁ × Out₂ :=
  match candidate with
  | .inl ⟨frame, evaluation⟩ =>
      profiledOpenWitnessedRightPhysicalOutput A initialCode
        (profiledOpenWitnessedRightRoundOverlayOfEvaluation A strategy hwin
          basis initialCode frame.reachable evaluation frame.entryRow)
        frame.inputOne frame.inputTwo
  | .inr ⟨frame, evaluation⟩ =>
      profiledOpenWitnessedLeftPhysicalOutput A initialCode
        (profiledOpenWitnessedLeftRoundOverlayOfEvaluation A strategy hwin
          basis initialCode frame.reachable evaluation frame.entryRow)
        frame.inputOne frame.inputTwo

/-- The finite set contains every dependent evaluation of the fixed frame.
There is no distinguished candidate. -/
noncomputable def profiledOpenWitnessedBeliefCandidates
    (frame : ProfiledOpenWitnessedBeliefFrame A initialCode) :
    Finset (ProfiledOpenWitnessedBeliefCandidate A strategy hwin basis
      initialCode) := by
  classical
  cases frame with
  | inl right =>
      exact Finset.univ.image (fun evaluation => Sum.inl ⟨right, evaluation⟩)
  | inr left =>
      exact Finset.univ.image (fun evaluation => Sum.inr ⟨left, evaluation⟩)

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every two candidates retained for one public frame have the same complete
physical output pair. -/
theorem profiledOpenWitnessedBeliefCandidates_output_eq
    (frame : ProfiledOpenWitnessedBeliefFrame A initialCode)
    {left right : ProfiledOpenWitnessedBeliefCandidate A strategy hwin basis
      initialCode}
    (hleft : left ∈ profiledOpenWitnessedBeliefCandidates A strategy hwin
      basis initialCode frame)
    (hright : right ∈ profiledOpenWitnessedBeliefCandidates A strategy hwin
      basis initialCode frame) :
    profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
        initialCode left =
      profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
        initialCode right := by
  classical
  cases frame with
  | inl frame =>
      simp only [profiledOpenWitnessedBeliefCandidates, Finset.mem_image,
        Finset.mem_univ, true_and] at hleft hright
      rcases hleft with ⟨leftEvaluation, rfl⟩
      rcases hright with ⟨rightEvaluation, rfl⟩
      exact profiledOpenWitnessedRightPhysicalOutput_exactDependent_pair A
        strategy hwin basis initialCode frame.reachable leftEvaluation
          rightEvaluation frame.entryRow frame.inputOne frame.inputTwo
  | inr frame =>
      simp only [profiledOpenWitnessedBeliefCandidates, Finset.mem_image,
        Finset.mem_univ, true_and] at hleft hright
      rcases hleft with ⟨leftEvaluation, rfl⟩
      rcases hright with ⟨rightEvaluation, rfl⟩
      exact profiledOpenWitnessedLeftPhysicalOutput_exactDependent_pair A
        strategy hwin basis initialCode frame.reachable leftEvaluation
          rightEvaluation frame.entryRow frame.inputOne frame.inputTwo

/-! ## One-arrow reachable-belief endpoint -/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- A common retained frame for each local belief, together with coverage of
the actual Moore output by one of its dependent candidates, is sufficient for
reachable-belief uniformity.  Candidate homogeneity is discharged above; the
only hypotheses here are the two actual coverage statements. -/
theorem profiledOpen_reachableBeliefsUniform_of_dependentCandidateCoverage
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (frameOne frameTwo :
      List (EnvironmentRound In₁ In₂) →
        ProfiledOpenWitnessedBeliefFrame A initialCode)
    (hcoverOne : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).1 →
        ∃ candidate ∈
            profiledOpenWitnessedBeliefCandidates A strategy hwin basis
              initialCode (frameOne rounds),
          outputOne state =
            (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
              initialCode candidate).1)
    (hcoverTwo : ∀ rounds state,
      state ∈ (G.beliefsAfter rounds).2 →
        ∃ candidate ∈
            profiledOpenWitnessedBeliefCandidates A strategy hwin basis
              initialCode (frameTwo rounds),
          outputTwo state =
            (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
              initialCode candidate).2) :
    G.ReachableBeliefsUniform outputOne outputTwo := by
  let summaryOne := fun rounds =>
    ((fun candidate =>
        (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
          initialCode candidate).1),
      profiledOpenWitnessedBeliefCandidates A strategy hwin basis initialCode
        (frameOne rounds))
  let summaryTwo := fun rounds =>
    ((fun candidate =>
        (profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
          initialCode candidate).2),
      profiledOpenWitnessedBeliefCandidates A strategy hwin basis initialCode
        (frameTwo rounds))
  apply FiniteGlobalRoundMachine.ReceiptSetOutputPresentation.reachableBeliefsUniform
    G outputOne outputTwo
  refine {
    summaryOne := summaryOne
    summaryTwo := summaryTwo
    EquivalentOne := Eq
    EquivalentTwo := Eq
    RepresentedOne := fun rounds state candidate =>
      outputOne state = (summaryOne rounds).1 candidate
    RepresentedTwo := fun rounds state candidate =>
      outputTwo state = (summaryTwo rounds).1 candidate
    coverOne := ?_
    coverTwo := ?_
    uniformOne := ?_
    uniformTwo := ?_
    outputOne_eq := ?_
    outputTwo_eq := ?_ }
  · exact hcoverOne
  · exact hcoverTwo
  · intro rounds left hleft right hright
    exact congrArg Prod.fst
      (profiledOpenWitnessedBeliefCandidates_output_eq A strategy hwin basis
        initialCode (frameOne rounds) hleft hright)
  · intro rounds left hleft right hright
    exact congrArg Prod.snd
      (profiledOpenWitnessedBeliefCandidates_output_eq A strategy hwin basis
        initialCode (frameTwo rounds) hleft hright)
  · intro rounds left right leftCandidate rightCandidate hleft hright heq
    exact hleft.trans (heq.trans hright.symm)
  · intro rounds left right leftCandidate rightCandidate hleft hright heq
    exact hleft.trans (heq.trans hright.symm)

/-! ## Optional actual-origin interface

The preceding belief theorem does not imply agreement with the source
strategy: a re-anchored semantic evaluation witnesses some coherent semantic
past, not necessarily the actual execution prefix.  The following theorem
states the exact additional anti-mosaic input.  It is intentionally separate
from ordinary candidate coverage.
-/

omit [Inhabited I] [Inhabited Out₁] [Inhabited Out₂] in
/-- If the actual global trace and the source strategy's actual local views
are both represented inside the *same* frame-candidate set, pair homogeneity
identifies them.  `hactualOrigin` is the genuine extra origin-continuity
obligation; it is not derived from re-anchored evaluation membership. -/
theorem profiledOpen_strategyOutputAgreement_of_actualOriginCoverage
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (frame : EnvironmentSequence In₁ In₂ → Nat →
      ProfiledOpenWitnessedBeliefFrame A initialCode)
    (htrace : ∀ env n,
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (frame env n),
        (outputOne (G.globalStateTrace env (n + 1)),
            outputTwo (G.globalStateTrace env (n + 1))) =
          profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
            initialCode candidate)
    (hactualOrigin : ∀ env n,
      ∃ candidate ∈
          profiledOpenWitnessedBeliefCandidates A strategy hwin basis
            initialCode (frame env n),
        profiledOpenWitnessedBeliefCandidateOutput A strategy hwin basis
            initialCode candidate =
          (strategy.one
              (nextView Proc.one (executionPrefix strategy env n) (env n)),
            strategy.two
              (nextView Proc.two (executionPrefix strategy env n) (env n)))) :
    G.StrategyOutputAgreement outputOne outputTwo strategy := by
  intro env n
  rcases htrace env n with
    ⟨traceCandidate, htraceMem, htraceOutput⟩
  rcases hactualOrigin env n with
    ⟨actualCandidate, hactualMem, hactualOutput⟩
  have hcandidates :=
    profiledOpenWitnessedBeliefCandidates_output_eq A strategy hwin basis
      initialCode (frame env n) htraceMem hactualMem
  have hpair := htraceOutput.trans (hcandidates.trans hactualOutput)
  exact ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

end

end DetParityAutomaton

end DistributedSynthesis
