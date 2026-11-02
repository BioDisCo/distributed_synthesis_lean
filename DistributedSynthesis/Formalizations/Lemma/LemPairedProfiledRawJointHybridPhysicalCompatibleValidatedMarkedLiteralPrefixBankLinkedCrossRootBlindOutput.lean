/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedLiveLane

/-!
# Blind-output compatibility at a linked-bank root replacement

The old literal table and the payload-linked table have different finite
controller types, so their root controls cannot be equated.  On a reachable
live lane they are nevertheless rebuilt from the same exact semantic
occurrence.  Both literal-prefix readback theorems therefore identify their
first blind output with the same semantic sender output.

This is deliberately an output theorem, not a state-equality theorem.  It is
the local fact needed when a strict side switch replaces the former table by
the exact linked child.  All witnesses are proof-side; the executable sender
uses only its stored finite child and local input.
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

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev OldRightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev OldLeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev LinkedRightMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove A
    strategy hwin

private abbrev LinkedLeftMove :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove A
    strategy hwin

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

/-! ## Same incoming occurrence gives the same blind root output -/

/-- The right old and linked table roots emit the same process-one output.
Their controller states and alphabets remain unrelated. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedIncomingOrigin.initial_blind_output_eq
    {state : BankControl A strategy hwin}
    {source : HybridState A strategy}
    {oldMove : OldRightMove A}
    {linkedMove : LinkedRightMove A strategy hwin}
    (horigin :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightLinkedIncomingOrigin
        A strategy hwin state source oldMove linkedMove)
    (input : In₁) :
    (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
        (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A oldMove)
        input).1 =
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          linkedMove) input).1 := by
  rcases horigin with
    ⟨parent, old, rawDirection, family, familyDirection, semanticMember,
      member_eq, hsource, hannotation, _haligned, hold, hlinked⟩
  rw [hold, hlinked]
  have holdOutput := congrArg Prod.snd
    (profiledRawJointRightLiteralPrefixMoveOf_initial_first_pair A strategy
      hwin family familyDirection semanticMember member_eq false
        (default, input))
  have hlinkedOutput := congrArg Prod.snd
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_initial_first_pair
      A strategy hwin state family familyDirection semanticMember member_eq
        false (default, input))
  exact holdOutput.trans hlinkedOutput.symm

/-- Process-two/left mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedIncomingOrigin.initial_blind_output_eq
    {state : BankControl A strategy hwin}
    {source : HybridState A strategy}
    {oldMove : OldLeftMove A}
    {linkedMove : LinkedLeftMove A strategy hwin}
    (horigin :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftLinkedIncomingOrigin
        A strategy hwin state source oldMove linkedMove)
    (input : In₂) :
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
        (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A oldMove)
        input).1 =
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          linkedMove) input).1 := by
  rcases horigin with
    ⟨parent, old, rawDirection, family, familyDirection, semanticMember,
      member_eq, hsource, hannotation, _haligned, hold, hlinked⟩
  rw [hold, hlinked]
  have holdOutput := congrArg Prod.snd
    (profiledRawJointLeftLiteralPrefixMoveOf_initial_first_pair A strategy hwin
      family familyDirection semanticMember member_eq false (default, input))
  have hlinkedOutput := congrArg Prod.snd
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_initial_first_pair
      A strategy hwin state family familyDirection semanticMember member_eq
        false (default, input))
  exact holdOutput.trans hlinkedOutput.symm

/-! ## Executable finite lookup form -/

/-- Any certified right rebuild has cross-root blind-output compatibility. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds.initial_blind_output_eq
    {state : BankControl A strategy hwin}
    {oldMove : OldRightMove A}
    {linkedMove : LinkedRightMove A strategy hwin}
    (hrebuild :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRightRebuilds A
        strategy hwin state oldMove linkedMove)
    (input : In₁) :
    (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
        (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A oldMove)
        input).1 =
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
          linkedMove) input).1 := by
  rcases hrebuild with ⟨_hmarker, _hreachable, horigin⟩
  exact horigin.initial_blind_output_eq A strategy hwin input

/-- Left rebuild mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds.initial_blind_output_eq
    {state : BankControl A strategy hwin}
    {oldMove : OldLeftMove A}
    {linkedMove : LinkedLeftMove A strategy hwin}
    (hrebuild :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftRebuilds A
        strategy hwin state oldMove linkedMove)
    (input : In₂) :
    (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
        (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A oldMove)
        input).1 =
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
          linkedMove) input).1 := by
  rcases hrebuild with ⟨_hmarker, _hreachable, horigin⟩
  exact horigin.initial_blind_output_eq A strategy hwin input

/-! ## Reachable live-lane wrappers -/

/-- On a reachable live right lane, the concrete finite lookup exposes an old
literal move whose blind root output agrees with the installed linked root. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightCrossRootBlindOutput_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawRightSlot A)
    (hlive : code.family.right () = some slot)
    (input : In₁) :
    ∃ oldMove : OldRightMove A,
      (state.literal A strategy hwin).1 = some oldMove ∧
        (profiledRawJointGuardedCommonRightLiteralCrossSenderNoRecv A
            (profiledRawJointGuardedCommonRightLiteralCrossSenderInitial A
              oldMove) input).1 =
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
            (profiledRawJointRightFinitePayloadLiteralPrefixSenderInitial A
              (state.linkedRightMove A strategy hwin)) input).1 := by
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  exact ⟨oldMove, hmove,
    hrebuild.initial_blind_output_eq A strategy hwin input⟩

/-- Reachable live-left mirror. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftCrossRootBlindOutput_of_liveLane
    {state : BankControl A strategy hwin}
    (hreachable :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A
        strategy hwin state)
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1 = .oneSided code)
    (slot : ProfiledRawLeftSlot A)
    (hlive : code.family.left () = some slot)
    (input : In₂) :
    ∃ oldMove : OldLeftMove A,
      (state.literal A strategy hwin).2 = some oldMove ∧
        (profiledRawJointGuardedCommonLeftLiteralCrossSenderNoRecv A
            (profiledRawJointGuardedCommonLeftLiteralCrossSenderInitial A
              oldMove) input).1 =
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
            (profiledRawJointLeftFinitePayloadLiteralPrefixSenderInitial A
              (state.linkedLeftMove A strategy hwin)) input).1 := by
  obtain ⟨oldMove, hmove, hrebuild⟩ :=
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMove_of_liveLane
      A strategy hwin hreachable code hcode slot hlive
  exact ⟨oldMove, hmove,
    hrebuild.initial_blind_output_eq A strategy hwin input⟩

end

end DetParityAutomaton

end DistributedSynthesis
