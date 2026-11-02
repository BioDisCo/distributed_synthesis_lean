/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartFirstThenBothScanAudit
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridFullRestartHomogeneousTail

/-!
# Audit of a separately represented FullRestart occurrence

After the same-occurrence shifted-`.both` splice failed, the only possible
repair using the present bank would be a second representation of the current
finite sender state whose advertised `.both` source is the actual post-first
DPA state.  This file audits exactly that possibility.

The selected occurrence's complete finite move is already the first component
of the graph-blind sender state.  In particular, its two hidden receiver
members have one common source, and any two semantic representations of the
same sender state have the same source.  Thus neither changing the hidden
member/anchor nor choosing another proof-side representation can reanchor the
DPA state.

The smallest uniform repair is consequently one additional finite scan lane:
it is seeded at the `.first` source, consumes the first physical record with
row `.first`, and consumes every later record with row `.both`.  Its state is
just the current DPA state together with the accumulated minimum priority;
no unbounded history or strict-leader knowledge is required.
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

private abbrev RightSender :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

/-! ## The source is executable sender data -/

/-- Read the right source advertised by the finite move stored in a sender.
The member argument only selects one of the two finite receiver descriptors. -/
noncomputable def profiledRawJointRightFinitePayloadLiteralPrefixSenderSource
    (sender : RightSender A strategy hwin) (member : Bool) :
    ProfiledRawRightSlot A :=
  (sender.1.1.descriptor member).base.source

/-- Left source accessor. -/
noncomputable def profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource
    (sender : LeftSender A strategy hwin) (member : Bool) :
    ProfiledRawLeftSlot A :=
  (sender.1.1.descriptor member).base.source

/-- Both hidden right receiver members of one semantic occurrence advertise
the same source slot. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf_source
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (member : Bool) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf
        A strategy hwin state family direction semanticMember hmember
    (move.1.descriptor member).base.source =
      profiledRawRightSlotOfSemanticPair A semanticMember := by
  classical
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMoveOf,
    profiledRawJointRightFinitePayloadLiteralPrefixMoveOf,
    finiteCrossAnchorLiteralPrefixMove,
    finiteCrossAnchorDescriptorFirstTwoMove,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations,
    profiledRawJointRightPhysicalSiblingActivation,
    profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf]

/-- Left hidden-member mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf_source
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (member : Bool) :
    let move :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf
        A strategy hwin state family direction semanticMember hmember
    (move.1.descriptor member).base.source =
      profiledRawLeftSlotOfSemanticPair A semanticMember := by
  classical
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMoveOf,
    profiledRawJointLeftFinitePayloadLiteralPrefixMoveOf,
    finiteCrossAnchorLiteralPrefixMove,
    finiteCrossAnchorDescriptorFirstTwoMove,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations,
    profiledRawJointLeftPhysicalSiblingActivation,
    profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf]

/-- The source of a canonical right sender at any prefix is exactly the
semantic occurrence's source and is independent of the chosen descriptor
member. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix_source
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcOnePairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).right () =
      some semanticMember)
    (past : List (In₂ × In₁)) (member : Bool) :
    profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        member =
      profiledRawRightSlotOfSemanticPair A semanticMember := by
  simp [profiledRawJointRightFinitePayloadLiteralPrefixSenderSource,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix]

/-- Left canonical-prefix mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix_source
    (state : BankControl A strategy hwin)
    (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
    (direction : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember : ProcTwoPairedEntryRep strategy × A.State)
    (hmember : (family.semanticChild A direction).left () =
      some semanticMember)
    (past : List (In₁ × In₂)) (member : Bool) :
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
          A strategy hwin state family direction semanticMember hmember past)
        member =
      profiledRawLeftSlotOfSemanticPair A semanticMember := by
  simp [profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix]

/-! ## No proof-side occurrence can change that source -/

/-- Two right semantic representations of the same executable sender state
necessarily advertise the same source.  The roots, semantic families,
directions, members, and represented prefixes may all differ. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix_source_unique
    (sender : RightSender A strategy hwin)
    (state₁ state₂ : BankControl A strategy hwin)
    (family₁ family₂ : ProfiledRawJointSemanticFamily A strategy
      (I := Unit))
    (direction₁ direction₂ : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember₁ semanticMember₂ :
      ProcOnePairedEntryRep strategy × A.State)
    (hmember₁ : (family₁.semanticChild A direction₁).right () =
      some semanticMember₁)
    (hmember₂ : (family₂.semanticChild A direction₂).right () =
      some semanticMember₂)
    (past₁ past₂ : List (In₂ × In₁))
    (hsender₁ : sender =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
        A strategy hwin state₁ family₁ direction₁ semanticMember₁
          hmember₁ past₁)
    (hsender₂ : sender =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
        A strategy hwin state₂ family₂ direction₂ semanticMember₂
          hmember₂ past₂) :
    profiledRawRightSlotOfSemanticPair A semanticMember₁ =
      profiledRawRightSlotOfSemanticPair A semanticMember₂ := by
  have hsource := congrArg
    (fun current ↦
      profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy
        hwin current false)
    (hsender₁.symm.trans hsender₂)
  simpa using hsource

/-- Left source-uniqueness mirror. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix_source_unique
    (sender : LeftSender A strategy hwin)
    (state₁ state₂ : BankControl A strategy hwin)
    (family₁ family₂ : ProfiledRawJointSemanticFamily A strategy
      (I := Unit))
    (direction₁ direction₂ : ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂))
    (semanticMember₁ semanticMember₂ :
      ProcTwoPairedEntryRep strategy × A.State)
    (hmember₁ : (family₁.semanticChild A direction₁).left () =
      some semanticMember₁)
    (hmember₂ : (family₂.semanticChild A direction₂).left () =
      some semanticMember₂)
    (past₁ past₂ : List (In₁ × In₂))
    (hsender₁ : sender =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
        A strategy hwin state₁ family₁ direction₁ semanticMember₁
          hmember₁ past₁)
    (hsender₂ : sender =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
        A strategy hwin state₂ family₂ direction₂ semanticMember₂
          hmember₂ past₂) :
    profiledRawLeftSlotOfSemanticPair A semanticMember₁ =
      profiledRawLeftSlotOfSemanticPair A semanticMember₂ := by
  have hsource := congrArg
    (fun current ↦
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy
        hwin current false)
    (hsender₁.symm.trans hsender₂)
  simpa using hsource

/-- On every represented right pair, changing the hidden receiver member
cannot change the source stored by the graph-blind sender. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.senderSource_member_independent
    {state : BankControl A strategy hwin}
    {sender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state sender receiver)
    (left right : Bool) :
    profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy hwin
        sender left =
      profiledRawJointRightFinitePayloadLiteralPrefixSenderSource A strategy
        hwin sender right := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      _hreceiver⟩
  rw [hsender]
  simp

/-- Left represented-pair mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.senderSource_member_independent
    {state : BankControl A strategy hwin}
    {sender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state sender receiver)
    (left right : Bool) :
    profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy hwin
        sender left =
      profiledRawJointLeftFinitePayloadLiteralPrefixSenderSource A strategy
        hwin sender right := by
  rcases hpair with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      _hreceiver⟩
  rw [hsender]
  simp

end

end DetParityAutomaton

end DistributedSynthesis
