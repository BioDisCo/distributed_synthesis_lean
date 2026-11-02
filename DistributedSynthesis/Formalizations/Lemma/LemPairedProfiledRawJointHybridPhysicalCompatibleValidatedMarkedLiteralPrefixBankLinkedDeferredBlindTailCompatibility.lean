/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredFullRestartController

/-!
# Blind-tail compatibility for a linked fixed-tail handoff

At a strict-side switch the full-restart controller puts the blind sender and
receiver on literally the same linked table.  After an unresolved
simultaneous close, however, the blind endpoint must retain the common table
while the receiver may resolve the closed child.  Equality of the first blind
output does not imply equality of the independently rationalized finite
trees at arbitrary depth.

This file states the exact all-depth property needed at that one seam and
proves that it is sufficient for the existing accepted linked-table tail.
The property quantifies only over local input words; it contains no graph,
leader, hierarchy-side, or history oracle.
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

private abbrev RightReceiver :=
  ProfiledRawJointRightFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

private abbrev LeftSender :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixSenderState A
    (BankControl A strategy hwin)

private abbrev LeftReceiver :=
  ProfiledRawJointLeftFinitePayloadLiteralPrefixReceiverState A
    (BankControl A strategy hwin)

/-! ## Sender-only runs -/

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
    (sender : RightSender A strategy hwin) (inputs : Nat → In₁) : Nat →
      RightSender A strategy hwin
  | 0 => sender
  | n + 1 =>
      (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
          sender inputs n) (inputs n)).2

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
    (sender : RightSender A strategy hwin) (inputs : Nat → In₁)
    (n : Nat) : Out₁ :=
  (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
      A strategy hwin sender inputs n) (inputs n)).1

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
    (sender : LeftSender A strategy hwin) (inputs : Nat → In₂) : Nat →
      LeftSender A strategy hwin
  | 0 => sender
  | n + 1 =>
      (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
          sender inputs n) (inputs n)).2

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
    (sender : LeftSender A strategy hwin) (inputs : Nat → In₂)
    (n : Nat) : Out₂ :=
  (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
      A strategy hwin sender inputs n) (inputs n)).1

/-- Two finite right-sender controls induce the same complete blind local
strategy. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
    (left right : RightSender A strategy hwin) : Prop :=
  ∀ inputs n,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
        A strategy hwin left inputs n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
        A strategy hwin right inputs n

/-- Left mirror. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
    (left right : LeftSender A strategy hwin) : Prop :=
  ∀ inputs n,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
        A strategy hwin left inputs n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
        A strategy hwin right inputs n

@[refl] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible.refl
    (sender : RightSender A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
      A strategy hwin sender sender := by
  intro inputs n
  rfl

@[refl] theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible.refl
    (sender : LeftSender A strategy hwin) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
      A strategy hwin sender sender := by
  intro inputs n
  rfl

/-! ## Finite one-step coinduction interface -/

/-- Prefix one local input to an infinite continuation. -/
def profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream
    {Input : Type*} (head : Input) (tail : Nat → Input) : Nat → Input
  | 0 => head
  | n + 1 => tail n

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun_prefixStream
    (sender : RightSender A strategy hwin) (head : In₁)
    (tail : Nat → In₁) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
        A strategy hwin sender
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream
            head tail) (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
        A strategy hwin
          (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A sender
            head).2 tail n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun]
      rw [ih]
      rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun_prefixStream
    (sender : LeftSender A strategy hwin) (head : In₂)
    (tail : Nat → In₂) (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
        A strategy hwin sender
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream
            head tail) (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
        A strategy hwin
          (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A sender
            head).2 tail n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun]
      rw [ih]
      rfl

/-- A relation is a right-sender output bisimulation if one private input
gives the same output and related successor controls. -/
def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindBisimulation
    (R : RightSender A strategy hwin → RightSender A strategy hwin → Prop) :
    Prop :=
  ∀ left right, R left right → ∀ input,
    (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A left input).1 =
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A right input).1 ∧
      R
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A left input).2
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A right input).2

def
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindBisimulation
    (R : LeftSender A strategy hwin → LeftSender A strategy hwin → Prop) :
    Prop :=
  ∀ left right, R left right → ∀ input,
    (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A left input).1 =
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A right input).1 ∧
      R
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A left input).2
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A right input).2

/-- Any finite one-step bisimulation proves equality on all blind input
tails.  This is the convenient interface for a locally consistent tree
automaton strategy or a finite partition-refinement certificate. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible_of_bisimulation
    {R : RightSender A strategy hwin → RightSender A strategy hwin → Prop}
    (hbisim :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindBisimulation
        A strategy hwin R)
    {left right : RightSender A strategy hwin} (hrel : R left right) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
      A strategy hwin left right := by
  intro inputs n
  induction n generalizing left right inputs with
  | zero =>
      exact (hbisim left right hrel (inputs 0)).1
  | succ n ih =>
      let nextLeft :=
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A left
          (inputs 0)).2
      let nextRight :=
        (profiledRawJointRightFinitePayloadLiteralPrefixSenderNoRecv A right
          (inputs 0)).2
      let tail := fun k ↦ inputs (k + 1)
      have hnext : R nextLeft nextRight :=
        (hbisim left right hrel (inputs 0)).2
      have hleftRun :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun_prefixStream
          A strategy hwin left (inputs 0) tail n
      have hrightRun :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun_prefixStream
          A strategy hwin right (inputs 0) tail n
      have hstream :
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream
              (inputs 0) tail = inputs := by
        funext k
        cases k <;> rfl
      rw [hstream] at hleftRun hrightRun
      unfold
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
      rw [hleftRun, hrightRun]
      exact ih hnext tail

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible_of_bisimulation
    {R : LeftSender A strategy hwin → LeftSender A strategy hwin → Prop}
    (hbisim :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindBisimulation
        A strategy hwin R)
    {left right : LeftSender A strategy hwin} (hrel : R left right) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
      A strategy hwin left right := by
  intro inputs n
  induction n generalizing left right inputs with
  | zero =>
      exact (hbisim left right hrel (inputs 0)).1
  | succ n ih =>
      let nextLeft :=
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A left
          (inputs 0)).2
      let nextRight :=
        (profiledRawJointLeftFinitePayloadLiteralPrefixSenderNoRecv A right
          (inputs 0)).2
      let tail := fun k ↦ inputs (k + 1)
      have hnext : R nextLeft nextRight :=
        (hbisim left right hrel (inputs 0)).2
      have hleftRun :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun_prefixStream
          A strategy hwin left (inputs 0) tail n
      have hrightRun :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun_prefixStream
          A strategy hwin right (inputs 0) tail n
      have hstream :
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream
              (inputs 0) tail = inputs := by
        funext k
        cases k <;> rfl
      rw [hstream] at hleftRun hrightRun
      unfold
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
      rw [hleftRun, hrightRun]
      exact ih hnext tail

/-- Tail compatibility is itself the greatest such one-step relation. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible_bisimulation :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindBisimulation
      A strategy hwin
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
          A strategy hwin) := by
  intro left right hcompatible input
  refine ⟨?_, ?_⟩
  · simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun]
      using hcompatible (fun _ ↦ input) 0
  · intro inputs n
    let prefixed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream input
        inputs
    have h := hcompatible prefixed (n + 1)
    unfold
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
      at h ⊢
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun_prefixStream,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun_prefixStream]
      at h
    exact h

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible_bisimulation :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindBisimulation
      A strategy hwin
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
          A strategy hwin) := by
  intro left right hcompatible input
  refine ⟨?_, ?_⟩
  · simpa [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun]
      using hcompatible (fun _ ↦ input) 0
  · intro inputs n
    let prefixed :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrefixStream input
        inputs
    have h := hcompatible prefixed (n + 1)
    unfold
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
      at h ⊢
    rw [
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun_prefixStream,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun_prefixStream]
      at h
    exact h

/-! ## Pair-run projection -/

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun_fst
    (sender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun
      A strategy hwin sender receiver inputs n).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun
          A strategy hwin sender (fun k ↦ (inputs k).1) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderRun]
      rw [ih]

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_fst
    (sender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun
      A strategy hwin sender receiver inputs n).1 =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun
          A strategy hwin sender (fun k ↦ (inputs k).2) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun,
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderRun]
      rw [ih]

/-! ## Mixed physical pairs -/

/-- Use the actual blind sender with the exact receiver coordinate of a
proof-side linked occurrence. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput
    (actualSender exactSender : RightSender A strategy hwin)
    (receiver : RightReceiver A strategy hwin) (row : PairedEntryRow)
    (inputs : Nat → In₁ × In₂) (n : Nat) : Out₁ × Out₂ :=
  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderOutput
      A strategy hwin actualSender (fun k ↦ (inputs k).1) n,
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
      A strategy hwin exactSender receiver row inputs n).2)

noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput
    (actualSender exactSender : LeftSender A strategy hwin)
    (receiver : LeftReceiver A strategy hwin) (row : PairedEntryRow)
    (inputs : Nat → In₁ × In₂) (n : Nat) : Out₁ × Out₂ :=
  ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
      A strategy hwin exactSender receiver row inputs n).1,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderOutput
      A strategy hwin actualSender (fun k ↦ (inputs k).2) n)

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput_eq
    {actualSender exactSender : RightSender A strategy hwin}
    (receiver : RightReceiver A strategy hwin) (row : PairedEntryRow)
    (inputs : Nat → In₁ × In₂) (n : Nat)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
        A strategy hwin actualSender exactSender) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput
        A strategy hwin actualSender exactSender receiver row inputs n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput
        A strategy hwin exactSender receiver row inputs n := by
  apply Prod.ext
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput]
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairOutput]
    simp only
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairRun_fst]
    exact hcompatible (fun k ↦ (inputs k).1) n
  · rfl

theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput_eq
    {actualSender exactSender : LeftSender A strategy hwin}
    (receiver : LeftReceiver A strategy hwin) (row : PairedEntryRow)
    (inputs : Nat → In₁ × In₂) (n : Nat)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
        A strategy hwin actualSender exactSender) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput
        A strategy hwin actualSender exactSender receiver row inputs n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput
        A strategy hwin exactSender receiver row inputs n := by
  apply Prod.ext
  · rfl
  · rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput]
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairOutput]
    simp only
    rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairRun_fst]
    exact hcompatible (fun k ↦ (inputs k).2) n

/-! ## Exact accepted-tail consumption -/

/-- All-depth blind compatibility is precisely enough to replace the exact
sender in the accepted linked right word by the runtime sender. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix.mixedPhysicalTail_exists
    {state : BankControl A strategy hwin}
    {actualSender exactSender : RightSender A strategy hwin}
    {receiver : RightReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPairAtPrefix
        A strategy hwin state exactSender receiver)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightBlindTailCompatible
        A strategy hwin actualSender exactSender)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcOnePairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).right () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₂ × In₁)),
          exactSender =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightSenderAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  past ∧
            receiver =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightReceiverAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankRightActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointRightFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin state)
              let tableEnv := OmegaWord.prependList past
                (fun k ↦ ((inputs k).2, (inputs k).1))
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                    A strategy hwin state family direction semanticMember hmember
                      anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput
                      A strategy hwin actualSender exactSender receiver row inputs
                        n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightPhysicalWord
                      A strategy hwin state family direction semanticMember
                        hmember anchor row tableEnv
                        (past.length + n)).outputPair) := by
  rcases hpair.physicalTail_exists A strategy hwin row inputs with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      hreceiver, haccepts, houtputs⟩
  refine ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
    hreceiver, haccepts, ?_⟩
  intro n
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedRightMixedPairOutput_eq
    A strategy hwin receiver row inputs n hcompatible]
  exact houtputs n

/-- Left accepted-tail mirror. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix.mixedPhysicalTail_exists
    {state : BankControl A strategy hwin}
    {actualSender exactSender : LeftSender A strategy hwin}
    {receiver : LeftReceiver A strategy hwin}
    (hpair :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPairAtPrefix
        A strategy hwin state exactSender receiver)
    (hcompatible :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftBlindTailCompatible
        A strategy hwin actualSender exactSender)
    (row : PairedEntryRow) (inputs : Nat → In₁ × In₂) :
    ∃ (family : ProfiledRawJointSemanticFamily A strategy (I := Unit))
      (direction : ProfiledRawJointFamilyDirection
        (I := Unit) (In₁ := In₁) (In₂ := In₂))
      (semanticMember : ProcTwoPairedEntryRep strategy × A.State),
      ∃ hmember : (family.semanticChild A direction).left () =
          some semanticMember,
        ∃ (anchor : Bool) (past : List (In₁ × In₂)),
          exactSender =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftSenderAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  past ∧
            receiver =
              profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftReceiverAtPrefix
                A strategy hwin state family direction semanticMember hmember
                  anchor past ∧
            (let activation :=
                profiledRawJointHybridValidatedMarkedLiteralPrefixBankLeftActivations
                  A strategy hwin family direction semanticMember hmember anchor
              let descriptor :=
                profiledRawJointLeftFinitePayloadLinkedSiblingDescriptorOf A
                  activation
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren
                      A strategy hwin state)
              let tableEnv := OmegaWord.prependList past inputs
              A.AcceptsFrom
                  (pairedCodeStateForRow A row descriptor.source.1.1)
                  (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                    A strategy hwin state family direction semanticMember hmember
                      anchor row tableEnv) ∧
                ∀ n : Nat,
                  profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput
                      A strategy hwin actualSender exactSender receiver row inputs
                        n =
                    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftPhysicalWord
                      A strategy hwin state family direction semanticMember
                        hmember anchor row tableEnv
                        (past.length + n)).outputPair) := by
  rcases hpair.physicalTail_exists A strategy hwin row inputs with
    ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
      hreceiver, haccepts, houtputs⟩
  refine ⟨family, direction, semanticMember, hmember, anchor, past, hsender,
    hreceiver, haccepts, ?_⟩
  intro n
  rw [profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedLeftMixedPairOutput_eq
    A strategy hwin receiver row inputs n hcompatible]
  exact houtputs n

end

end DetParityAutomaton

end DistributedSynthesis
