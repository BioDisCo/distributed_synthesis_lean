/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteReceiverSelection

/-!
# Incoming origins at one-sided marked-bank states

At a reachable marked-bank state, validated inversion supplies one exact
semantic source and the current literal-table provenance.  If the public code
is one-sided, that source cannot be the marked common root.  Hence every
present right/left literal table has the fully linked incoming origin exposed
by `rightOrigin` / `leftOrigin`: a semantic family, direction, member, and the
literal `...LiteralPrefixMoveOf` equality.

This is the model-specific extraction needed to rebuild the same two-anchor
literal-prefix table with a finite next-bank payload before narrowing.  No
endpoint observes any of the semantic witnesses.
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

private abbrev BankReachable
    (state : BankControl A strategy hwin) :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
    hwin state

private abbrev RightMove :=
  ProfiledRawJointGuardedCommonRightLiteralCrossMove A

private abbrev LeftMove :=
  ProfiledRawJointGuardedCommonLeftLiteralCrossMove A

private abbrev PublicTarget :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev HybridState :=
  ProfiledRawJointHybridSemanticState A strategy

/-! ## Excluding the marked common root -/

/-- A reachable packet whose current public code is one-sided has an exact
one-sided semantic source. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_oneSided_of_code
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : PublicTarget A)
    (hcode : state.2.1.1 = .oneSided code) :
    ∃ source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit),
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
          strategy hwin state.1 state.2 hreachable).source =
          .oneSided source ∧
        source.code A = code := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  cases hsource : packet.source with
  | common world =>
      have himpossible := packet.source_code
      rw [hsource, hcode] at himpossible
      cases himpossible
  | oneSided source =>
      refine ⟨source, rfl, ?_⟩
      have hsourceCode := packet.source_code
      rw [hsource, hcode] at hsourceCode
      exact ProfiledRawJointHybridCode.oneSided.inj hsourceCode
  | dead =>
      have himpossible := packet.source_code
      rw [hsource, hcode] at himpossible
      cases himpossible

/-- A one-sided packet source is not the unique marked common root. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_ne_common_of_code
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : PublicTarget A)
    (hcode : state.2.1.1 = .oneSided code)
    (initial : ProfiledRawJointCommonBaseWorld A strategy) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable).source ≠ .common initial := by
  rintro hsource
  have himpossible :=
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
      strategy hwin state.1 state.2 hreachable).source_code
  rw [hsource, hcode] at himpossible
  cases himpossible

/-! ## Fully linked incoming origins -/

/-- At a one-sided reachable state, every present right literal table comes
from one fully exposed incoming semantic edge; the seed alternative is
impossible. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.rightIncomingOrigin
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : PublicTarget A)
    (hcode : state.2.1.1 = .oneSided code)
    (move : RightMove A)
    (hmove : (state.literal A strategy hwin).1 = some move) :
    ProfiledRawJointHybridRightLiteralPrefixIncomingOrigin A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable).source move := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
      packet.source state.2.1.2.2 packet.marked_current
  rcases hcurrent.rightOrigin A strategy hwin hmove with hroot | hincoming
  · exact
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_ne_common_of_code
        A strategy hwin hreachable code hcode
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin state.1).world hroot.1).elim
  · exact hincoming

/-- Left mirror. -/
theorem
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.leftIncomingOrigin
    {state : BankControl A strategy hwin}
    (hreachable : BankReachable A strategy hwin state)
    (code : PublicTarget A)
    (hcode : state.2.1.1 = .oneSided code)
    (move : LeftMove A)
    (hmove : (state.literal A strategy hwin).2 = some move) :
    ProfiledRawJointHybridLeftLiteralPrefixIncomingOrigin A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A
        strategy hwin state.1 state.2 hreachable).source move := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  have hcurrent :=
    profiledRawJointHybridLiteralPrefixCurrentCompatible_of_marked A strategy
      hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin state.1).world
      packet.source state.2.1.2.2 packet.marked_current
  rcases hcurrent.leftOrigin A strategy hwin hmove with hroot | hincoming
  · exact
      (ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankFiniteStep.source_ne_common_of_code
        A strategy hwin hreachable code hcode
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
          strategy hwin state.1).world hroot.1).elim
  · exact hincoming

end

end DetParityAutomaton

end DistributedSynthesis
