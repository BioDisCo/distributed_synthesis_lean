/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaLinkedCommonRootSplice

/-!
# Common-root trajectory splice

At a strict orientation reversal, the common-root execution becomes
observationally equivalent to a canonical full restart at the authoritative
parent.  This file propagates that equivalence through the complete suffix and
identifies the resulting words literally.
-/

namespace DistributedSynthesis.DetParityAutomaton

universe u v x y s

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

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

theorem profiledRawJointHybridMegaLinkedCommonRootrightSwitch_zero
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .left)
    (hcurrent : (env (n + 1)).graph = .right) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    let commonNext :=
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env (cut + 1)
    let standardNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin restartTag (OmegaWord.drop env cut) 1
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        commonNext.1 standardNext.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        commonNext.2 standardNext.2 ∧
      (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy
          hwin tag env cut,
        profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
          hwin tag env cut) =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
            A strategy hwin restartTag (OmegaWord.drop env cut) 0,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
            A strategy hwin restartTag (OmegaWord.drop env cut) 0) := by
  let cut := n + 1
  have hcurrentCut : (env cut).graph = .right := by
    simpa [cut] using hcurrent
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin tag
      env cut
  have hopen :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth A
      strategy hwin tag env hnoBoth cut
  rcases hopen.1 with ⟨one, payloadOne, _payloadOne', honePair, _⟩
  rcases hopen.2 with ⟨two, payloadTwo, _payloadTwo', htwoPair, _⟩
  have hbits :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_succ_selected_lastRecv
      A strategy hwin tag env n
  rw [hprev] at hbits
  have hone : one.2.1 = true := by
    simpa [cut, pair,
      profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt, honePair] using
        hbits.1
  have htwo : two.2.1 = false := by
    simpa [cut, pair,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt, htwoPair] using
        hbits.2
  have hswitch :=
    profiledRawJointHybridMegaLinkedCommonRootOpenRel_rightSwitch A strategy
      hwin tag one two payloadOne payloadTwo
        ((env cut).inputOne, (env cut).inputTwo) hone htwo
  have hparent :
      profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
          cut =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin one two := by
    simp only [profiledRawJointHybridMegaLinkedCommonRootParentAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt,
      honePair, htwoPair,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open]
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  let standardZero :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin restartTag (OmegaWord.drop env cut) 0
  have hcommonNext :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env (cut + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin pair.1 (env cut).inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag)
              pair.2 (env cut).inputTwo pair.1 (env cut).inputOne).1) := by
    rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hcurrentCut]
    rfl
  have hstandardNext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1 =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
            A strategy hwin standardZero.1 (env cut).inputOne).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin restartTag)
              standardZero.2 (env cut).inputTwo standardZero.1
                (env cut).inputOne).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    simp only [OmegaWord.drop_apply, Nat.add_zero, hcurrentCut]
    rfl
  rcases hswitch with ⟨hsOne, hsTwo, hsOutput⟩
  have hrelOne :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (cut + 1)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1).1 := by
    rw [hcommonNext, hstandardNext]
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent]
      using hsOne
  have hrelTwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (cut + 1)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1).2 := by
    rw [hcommonNext, hstandardNext]
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent]
      using hsTwo
  have houtput :
      (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy
          hwin tag env cut,
        profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
          hwin tag env cut) =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
            A strategy hwin restartTag (OmegaWord.drop env cut) 0,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
            A strategy hwin restartTag (OmegaWord.drop env cut) 0) := by
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent,
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne,
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo,
      OmegaWord.drop_apply, Nat.add_zero, hcurrentCut] using hsOutput
  simpa only [cut, restartTag] using And.intro hrelOne (And.intro hrelTwo houtput)

theorem profiledRawJointHybridMegaLinkedCommonRootleftSwitch_zero
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .right)
    (hcurrent : (env (n + 1)).graph = .left) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    let commonNext :=
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
        tag env (cut + 1)
    let standardNext :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
        A strategy hwin restartTag (OmegaWord.drop env cut) 1
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        commonNext.1 standardNext.1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        commonNext.2 standardNext.2 ∧
      (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy
          hwin tag env cut,
        profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
          hwin tag env cut) =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
            A strategy hwin restartTag (OmegaWord.drop env cut) 0,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
            A strategy hwin restartTag (OmegaWord.drop env cut) 0) := by
  let cut := n + 1
  have hcurrentCut : (env cut).graph = .left := by
    simpa [cut] using hcurrent
  let pair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin tag
      env cut
  have hopen :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_open_of_noBoth A
      strategy hwin tag env hnoBoth cut
  rcases hopen.1 with ⟨one, payloadOne, _payloadOne', honePair, _⟩
  rcases hopen.2 with ⟨two, payloadTwo, _payloadTwo', htwoPair, _⟩
  have hbits :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt_succ_selected_lastRecv
      A strategy hwin tag env n
  rw [hprev] at hbits
  have hone : one.2.1 = false := by
    simpa [cut, pair,
      profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt, honePair] using
        hbits.1
  have htwo : two.2.1 = true := by
    simpa [cut, pair,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt, htwoPair] using
        hbits.2
  have hswitch :=
    profiledRawJointHybridMegaLinkedCommonRootOpenRel_leftSwitch A strategy
      hwin tag one two payloadOne payloadTwo
        ((env cut).inputOne, (env cut).inputTwo) hone htwo
  have hparent :
      profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
          cut =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOne
          A strategy hwin one two := by
    simp only [profiledRawJointHybridMegaLinkedCommonRootParentAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedOneAt,
      profiledRawJointHybridMegaLinkedCommonRootSelectedTwoAt,
      honePair, htwoPair,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedOne_open,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredSelectedTwo_open]
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  let standardZero :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin restartTag (OmegaWord.drop env cut) 0
  have hcommonNext :
      profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin
          tag env (cut + 1) =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin tag)
              pair.1 (env cut).inputOne pair.2 (env cut).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin pair.2 (env cut).inputTwo).1) := by
    rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
      hcurrentCut]
    rfl
  have hstandardNext :
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1 =
        ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
            A strategy hwin
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                A strategy hwin restartTag)
              standardZero.1 (env cut).inputOne standardZero.2
                (env cut).inputTwo).1,
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
            A strategy hwin standardZero.2 (env cut).inputTwo).1) := by
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
      FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace]
    simp only [OmegaWord.drop_apply, Nat.add_zero, hcurrentCut]
    rfl
  rcases hswitch with ⟨hsOne, hsTwo, hsOutput⟩
  have hrelOne :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (cut + 1)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1).1 := by
    rw [hcommonNext, hstandardNext]
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent]
      using hsOne
  have hrelTwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (cut + 1)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env cut) 1).2 := by
    rw [hcommonNext, hstandardNext]
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent]
      using hsTwo
  have houtput :
      (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy
          hwin tag env cut,
        profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
          hwin tag env cut) =
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
            A strategy hwin restartTag (OmegaWord.drop env cut) 0,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
            A strategy hwin restartTag (OmegaWord.drop env cut) 0) := by
    simpa only [pair, honePair, htwoPair, restartTag, standardZero, hparent,
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne,
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo,
      OmegaWord.drop_apply, Nat.add_zero, hcurrentCut] using hsOutput
  simpa only [cut, restartTag] using And.intro hrelOne (And.intro hrelTwo houtput)

theorem profiledRawJointHybridMegaLinkedCommonRootopenRel_semantic_step
    (tag restartTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start n : Nat)
    (hnoBoth : (env (start + n)).graph ≠ .both)
    (hone :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) n).1)
    (htwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) n).2) :
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env (start + n),
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env (start + n)) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin restartTag (OmegaWord.drop env start) n,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin restartTag (OmegaWord.drop env start) n) ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n + 1)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) (n + 1)).1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n + 1)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) (n + 1)).2 := by
  let commonPair :=
    profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy hwin tag
      env (start + n)
  let standardPair :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
      A strategy hwin restartTag (OmegaWord.drop env start) n
  cases hgraph : (env (start + n)).graph with
  | both => exact False.elim (hnoBoth hgraph)
  | right =>
      have hstep :=
        profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictRight A strategy
          hwin tag restartTag commonPair.1 standardPair.1 commonPair.2
            standardPair.2
            ((env (start + n)).inputOne, (env (start + n)).inputTwo) hone htwo
      have hstandardGraph :
          (OmegaWord.drop env start n).graph = .right := by
        simpa only [OmegaWord.drop_apply] using hgraph
      have hcommonNext :
          profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
              hwin tag env (start + n + 1) =
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin commonPair.1 (env (start + n)).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                    A strategy hwin tag)
                  commonPair.2 (env (start + n)).inputTwo commonPair.1
                    (env (start + n)).inputOne).1) := by
        rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hgraph]
        rfl
      have hstandardNext :
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
              A strategy hwin restartTag (OmegaWord.drop env start) (n + 1) =
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvOne
                A strategy hwin standardPair.1 (env (start + n)).inputOne).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvTwo
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                    A strategy hwin restartTag)
                  standardPair.2 (env (start + n)).inputTwo standardPair.1
                    (env (start + n)).inputOne).1) := by
        rw [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hstandardGraph]
        rfl
      rcases hstep with ⟨hnextOne, hnextTwo, houtput⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [commonPair, standardPair,
          profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne,
          profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo,
          OmegaWord.drop_apply, hgraph, hstandardGraph] using houtput
      · rw [hcommonNext, hstandardNext]
        exact hnextOne
      · rw [hcommonNext, hstandardNext]
        exact hnextTwo

  | left =>
      have hstep :=
        profiledRawJointHybridMegaLinkedCommonRootOpenRel_strictLeft A strategy
          hwin tag restartTag commonPair.1 standardPair.1 commonPair.2
            standardPair.2
            ((env (start + n)).inputOne, (env (start + n)).inputTwo) hone htwo
      have hstandardGraph :
          (OmegaWord.drop env start n).graph = .left := by
        simpa only [OmegaWord.drop_apply] using hgraph
      have hcommonNext :
          profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
              hwin tag env (start + n + 1) =
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                    A strategy hwin tag)
                  commonPair.1 (env (start + n)).inputOne commonPair.2
                    (env (start + n)).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin commonPair.2 (env (start + n)).inputTwo).1) := by
        rw [profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hgraph]
        rfl
      have hstandardNext :
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
              A strategy hwin restartTag (OmegaWord.drop env start) (n + 1) =
            ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredPhaseRestartOpenRecvOne
                A strategy hwin
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredInitialPair
                    A strategy hwin restartTag)
                  standardPair.1 (env (start + n)).inputOne standardPair.2
                    (env (start + n)).inputTwo).1,
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartNoRecvTwo
                A strategy hwin standardPair.2 (env (start + n)).inputTwo).1) := by
        rw [
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt,
          FiniteAcknowledgedDelayedCarrier.exactClosingSemanticPairTrace,
          hstandardGraph]
        rfl
      rcases hstep with ⟨hnextOne, hnextTwo, houtput⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa only [commonPair, standardPair,
          profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne,
          profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo,
          OmegaWord.drop_apply, hgraph, hstandardGraph] using houtput
      · rw [hcommonNext, hstandardNext]
        exact hnextOne
      · rw [hcommonNext, hstandardNext]
        exact hnextTwo


theorem profiledRawJointHybridMegaLinkedCommonRootopenRel_iterate
    (tag restartTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (hone :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env start).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) 0).1)
    (htwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env start).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) 0).2)
    (n : Nat) :
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) n).1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + n)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) n).2 := by
  induction n with
  | zero => simpa only [Nat.add_zero] using And.intro hone htwo
  | succ n ih =>
      have hstep :=
        profiledRawJointHybridMegaLinkedCommonRootopenRel_semantic_step A strategy hwin tag restartTag
          env start n (hnoBoth n) ih.1 ih.2
      simpa only [Nat.add_assoc, Nat.add_one, Nat.add_comm 1 n] using
        And.intro hstep.2.1 hstep.2.2

theorem profiledRawJointHybridMegaLinkedCommonRootopenRel_outputs
    (tag restartTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start : Nat)
    (hnoBoth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (hone :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env start).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) 0).1)
    (htwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env start).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) 0).2)
    (n : Nat) :
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env (start + n),
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env (start + n)) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin restartTag (OmegaWord.drop env start) n,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin restartTag (OmegaWord.drop env start) n) := by
  have hrel :=
    profiledRawJointHybridMegaLinkedCommonRootopenRel_iterate A strategy hwin tag restartTag env start
      hnoBoth hone htwo n
  exact (profiledRawJointHybridMegaLinkedCommonRootopenRel_semantic_step A strategy hwin tag restartTag
    env start n (hnoBoth n) hrel.1 hrel.2).1

theorem profiledRawJointHybridMegaLinkedCommonRootopenRel_iterate_from
    (tag restartTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start offset : Nat)
    (hnoBoth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (hone :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + offset)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) offset).1)
    (htwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + offset)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) offset).2)
    (n : Nat) :
    ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + (offset + n))).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) (offset + n)).1 ∧
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + (offset + n))).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) (offset + n)).2 := by
  induction n with
  | zero => simpa only [Nat.add_zero] using And.intro hone htwo
  | succ n ih =>
      have hstep :=
        profiledRawJointHybridMegaLinkedCommonRootopenRel_semantic_step A strategy hwin tag restartTag
          env start (offset + n) (hnoBoth (offset + n)) ih.1 ih.2
      simpa only [Nat.add_assoc, Nat.add_one, Nat.add_comm 1 n] using
        And.intro hstep.2.1 hstep.2.2

theorem profiledRawJointHybridMegaLinkedCommonRootopenRel_outputs_from
    (tag restartTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂) (start offset : Nat)
    (hnoBoth : ∀ n : Nat, (env (start + n)).graph ≠ .both)
    (hone :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelOne A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + offset)).1
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) offset).1)
    (htwo :
      ProfiledRawJointHybridMegaLinkedCommonRootOpenRelTwo A strategy hwin
        (profiledRawJointHybridMegaLinkedCommonRootSemanticPairAt A strategy
          hwin tag env (start + offset)).2
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartSemanticPairAt
          A strategy hwin restartTag (OmegaWord.drop env start) offset).2)
    (n : Nat) :
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env (start + (offset + n)),
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env (start + (offset + n))) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin restartTag (OmegaWord.drop env start) (offset + n),
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin restartTag (OmegaWord.drop env start) (offset + n)) := by
  have hrel :=
    profiledRawJointHybridMegaLinkedCommonRootopenRel_iterate_from A strategy hwin tag restartTag env
      start offset hnoBoth hone htwo n
  exact (profiledRawJointHybridMegaLinkedCommonRootopenRel_semantic_step A strategy hwin tag restartTag
    env start (offset + n) (hnoBoth (offset + n)) hrel.1 hrel.2).1

theorem profiledRawJointHybridMegaLinkedCommonRootrightSwitch_outputs
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .left)
    (hcurrent : (env (n + 1)).graph = .right) (k : Nat) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env (cut + k),
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env (cut + k)) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin restartTag (OmegaWord.drop env cut) k,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin restartTag (OmegaWord.drop env cut) k) := by
  let cut := n + 1
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  have hzero :=
    profiledRawJointHybridMegaLinkedCommonRootrightSwitch_zero A strategy hwin tag env hnoBoth n hprev
      hcurrent
  cases k with
  | zero => exact hzero.2.2
  | succ k =>
      have htail :=
        profiledRawJointHybridMegaLinkedCommonRootopenRel_outputs_from A strategy hwin tag restartTag
          env cut 1 (fun j ↦ hnoBoth (cut + j)) hzero.1 hzero.2.1 k
      simpa only [cut, restartTag, Nat.add_assoc, Nat.add_one,
        Nat.add_comm 1 k] using htail

theorem profiledRawJointHybridMegaLinkedCommonRootrightSwitch_drop_eq_fullRestartWord
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .left)
    (hcurrent : (env (n + 1)).graph = .right) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    OmegaWord.drop
        (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
          tag env) cut =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin restartTag (OmegaWord.drop env cut) := by
  let cut := n + 1
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  funext k
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · rfl
  · simp only [OmegaWord.drop_apply,
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord_outputPair,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_outputPair]
    exact profiledRawJointHybridMegaLinkedCommonRootrightSwitch_outputs A strategy hwin tag env hnoBoth
      n hprev hcurrent k

theorem profiledRawJointHybridMegaLinkedCommonRootleftSwitch_outputs
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .right)
    (hcurrent : (env (n + 1)).graph = .left) (k : Nat) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    (profiledRawJointHybridMegaLinkedCommonRootExpectedOutputOne A strategy hwin
        tag env (cut + k),
      profiledRawJointHybridMegaLinkedCommonRootExpectedOutputTwo A strategy
        hwin tag env (cut + k)) =
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputOne
          A strategy hwin restartTag (OmegaWord.drop env cut) k,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartExpectedOutputTwo
          A strategy hwin restartTag (OmegaWord.drop env cut) k) := by
  let cut := n + 1
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  have hzero :=
    profiledRawJointHybridMegaLinkedCommonRootleftSwitch_zero A strategy hwin tag env hnoBoth n hprev
      hcurrent
  cases k with
  | zero => exact hzero.2.2
  | succ k =>
      have htail :=
        profiledRawJointHybridMegaLinkedCommonRootopenRel_outputs_from A strategy hwin tag restartTag
          env cut 1 (fun j ↦ hnoBoth (cut + j)) hzero.1 hzero.2.1 k
      simpa only [cut, restartTag, Nat.add_assoc, Nat.add_one,
        Nat.add_comm 1 k] using htail

theorem profiledRawJointHybridMegaLinkedCommonRootleftSwitch_drop_eq_fullRestartWord
    (tag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (hnoBoth : ∀ k : Nat, (env k).graph ≠ .both)
    (n : Nat) (hprev : (env n).graph = .right)
    (hcurrent : (env (n + 1)).graph = .left) :
    let cut := n + 1
    let restartTag : RetainedTag A strategy hwin :=
      (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag
        env cut, (false, false))
    OmegaWord.drop
        (profiledRawJointHybridMegaLinkedCommonRootReferenceWord A strategy hwin
          tag env) cut =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord
        A strategy hwin restartTag (OmegaWord.drop env cut) := by
  let cut := n + 1
  let restartTag : RetainedTag A strategy hwin :=
    (profiledRawJointHybridMegaLinkedCommonRootParentAt A strategy hwin tag env
      cut, (false, false))
  funext k
  apply RoundRecord.eq_of_environment_eq_of_outputPair_eq
  · rfl
  · simp only [OmegaWord.drop_apply,
      profiledRawJointHybridMegaLinkedCommonRootReferenceWord_outputPair,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartWord_outputPair]
    exact profiledRawJointHybridMegaLinkedCommonRootleftSwitch_outputs A strategy hwin tag env hnoBoth
      n hprev hcurrent k
end

end DistributedSynthesis.DetParityAutomaton
