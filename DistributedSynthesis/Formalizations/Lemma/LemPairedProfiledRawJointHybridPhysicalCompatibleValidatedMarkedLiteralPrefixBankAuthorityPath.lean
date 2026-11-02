/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankLinkedDeferredAuthorityTrace
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedBridge

/-!
# The exact bank-child run is an allowed marked-bank path

The linked deferred controller carries the exact finite table
`direction ↦ BankChildren state direction`.  This file turns repeated use of
that table into a root-started path of the already selected rational bank.
There is no second move choice and no second rationalization: at every step
the requested finite child code is literally `state.childCode direction`.

The final induction theorem is deliberately interface-level.  Once a selected
authority subsequence (normally the epoch-cut subsequence, not necessarily
every physical round) is shown to start at the selected bank root and to take
the corresponding exact child at every selected step, it is pointwise equal
to this allowed path.
Directions remain proof-side witnesses; no endpoint learns the graph or the
strict leader.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev BankControl :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl A strategy hwin

private abbrev BankPolicy
    (control : CommonControl A strategy hwin) :=
  profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy hwin
    control

private abbrev BankPolicyState
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixPolicyState
    A strategy hwin
      (profiledRawJointHybridValidatedMarkedLiteralPrefixBankInstalled A
        strategy hwin control).world

private abbrev BankPath
    (control : CommonControl A strategy hwin) :=
  ProfiledRawJointHybridPhysicalCompatibleValidatedExtraAllowedPath A strategy
    hwin (BankPolicy A strategy hwin control)

private abbrev RetainedTag :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankRetainedTag A strategy
    hwin

/-! ## The child-table run inside one fixed bank entry -/

/-- Run the policy state by requesting at step `n` the exact raw child code of
the proof-side direction `direction n`. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    Nat → BankPolicyState A strategy hwin control
  | 0 => (BankPolicy A strategy hwin control).run []
  | n + 1 =>
      let state :=
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState
          control direction n
      (BankPolicy A strategy hwin control).successor state
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode
          A strategy hwin
            (⟨control, state⟩ : BankControl A strategy hwin) (direction n))

/-- The same run with its fixed bank index restored. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) : BankControl A strategy hwin :=
  ⟨control,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState A
      strategy hwin control direction n⟩

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_zero
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt A
        strategy hwin control direction 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control :=
  rfl

/-- One step of the run is definitionally the exact bank-child table lookup. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_succ
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt A
        strategy hwin control direction (n + 1) =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction n)
        (direction n) :=
  rfl

/-! ## Materialization as an accepted-bank candidate path -/

/-- Repeated exact child-table lookup is a root-started allowed path of the
same fixed marked policy. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    BankPath A strategy hwin control where
  state :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState A
      strategy hwin control direction
  initial_state := rfl
  allowed := fun n ↦ by
    let state :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState A
        strategy hwin control direction n
    exact
      ⟨ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode
          A strategy hwin
            (⟨control, state⟩ : BankControl A strategy hwin) (direction n), rfl⟩

@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath_state
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath A
        strategy hwin control direction).state n =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunState A
        strategy hwin control direction n :=
  rfl

/-- Every control reached by the exact child-table run satisfies the bank
reachability invariant. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_reachable
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankReachable A strategy
      hwin
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction n) := by
  exact
    ProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankPath_reachable
      A strategy hwin control
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunPath A
          strategy hwin control direction) n

/-! ## Authority-trace induction -/

/-- Any bank-control trace with the selected root and the exact
`BankChildren` successor equations is pointwise the allowed child-table run.
This is the final state-level induction consumed after the linked trace has
been sampled at the semantic commit points and its cases have been converted
to one direction stream. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (trace : Nat → BankControl A strategy hwin)
    (hzero : trace 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hsucc : ∀ n : Nat,
      trace (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace n) (direction n)) :
    ∀ n : Nat,
      trace n =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction n := by
  intro n
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      rw [hsucc n, ih]
      exact
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_succ
          A strategy hwin control direction n).symm

/-- Offset form of `BankTrace_eq_childRun`.  A trace installed at an already
reached descendant and then driven by the corresponding suffix directions is
the matching suffix of the same root-started accepted bank path.  This is the
form needed after a finite mixed front closes at a dynamically reached child.
-/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun_from
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (rootOffset : Nat)
    (trace : Nat → BankControl A strategy hwin)
    (hzero : trace 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt A
        strategy hwin control direction rootOffset)
    (hsucc : ∀ n : Nat,
      trace (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace n) (direction (rootOffset + n))) :
    ∀ n : Nat,
      trace n =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction (rootOffset + n) := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
      rw [hsucc n, ih]
      have hstep :=
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_succ
          A strategy hwin control direction (rootOffset + n)).symm
      simpa only [Nat.add_assoc] using hstep

/-- Conditional specialization to the physical-round authority trace.  It is
useful when an application really has a child transition at each round; the
main linked construction is expected to apply the preceding generic theorem
to its epoch-cut subsequence instead. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt_eq_childRun
    (initialTag : RetainedTag A strategy hwin)
    (env : EnvironmentSequence In₁ In₂)
    (control : CommonControl A strategy hwin)
    (direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (hroot : initialTag.1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A strategy hwin
        control)
    (hsucc : ∀ n : Nat,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
            A strategy hwin initialTag env n)
          (direction n)) :
    ∀ n : Nat,
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env n =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control direction n := by
  apply
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun A
      strategy hwin control direction
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankLinkedDeferredParentOneAt
          A strategy hwin initialTag env)
  · simpa using hroot
  · exact hsucc

/-! ## The one-child bootstrap used by the mega handoff -/

/-- Prepend the front-phase handoff direction to the directions reconstructed
by the linked tail. -/
def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
    (first : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (tail : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)
  | 0 => first
  | n + 1 => tail n

/-- The first state after a prepended direction is the exact child of the
selected bank root. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_prepend_one
    (control : CommonControl A strategy hwin)
    (first : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (tail : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt A
        strategy hwin control
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
            first tail) 1 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) first :=
  rfl

/-- A tail trace installed at one exact child of a bank root is the suffix,
at offset one, of a root-started allowed bank path.  This is the shape of the
mega front-to-linked-tail handoff: the front supplies `first`, and the linked
controller supplies the later exact-child equations. -/
theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun_prepend
    (control : CommonControl A strategy hwin)
    (first : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (tailDirection : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂))
    (trace : Nat → BankControl A strategy hwin)
    (hzero : trace 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) first)
    (hsucc : ∀ n : Nat,
      trace (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace n) (tailDirection n)) :
    ∀ n : Nat,
      trace n =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
          A strategy hwin control
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
              first tailDirection) (n + 1) := by
  intro n
  induction n with
  | zero =>
      simpa using hzero
  | succ n ih =>
      rw [hsucc n, ih]
      exact
        (profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt_succ
          A strategy hwin control
            (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
              first tailDirection) (n + 1)).symm

/-- Choice packaging of the last local obligation.  If every tail round has
some exact bank direction, those witnesses assemble into one root-started
allowed path whose offset-one controls are the authority trace.  The choice
is entirely proof-side. -/
theorem
    exists_profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRun_of_step_exists
    (control : CommonControl A strategy hwin)
    (first : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (trace : Nat → BankControl A strategy hwin)
    (hzero : trace 0 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A strategy
        hwin
          (profiledRawJointHybridValidatedMarkedLiteralPrefixBankRoot A
            strategy hwin control) first)
    (hstep : ∀ n : Nat, ∃ direction :
        HybridDirection (In₁ := In₁) (In₂ := In₂),
      trace (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace n) direction) :
    ∃ direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂),
      ∀ n : Nat,
        trace n =
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildRunControlAt
            A strategy hwin control
              (profiledRawJointHybridValidatedMarkedLiteralPrefixBankPrependDirection
                first direction) (n + 1) := by
  let direction : Nat → HybridDirection (In₁ := In₁) (In₂ := In₂) :=
    fun n ↦ Classical.choose (hstep n)
  have hsucc : ∀ n : Nat,
      trace (n + 1) =
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankChildren A
          strategy hwin (trace n) (direction n) :=
    fun n ↦ Classical.choose_spec (hstep n)
  exact ⟨direction,
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTrace_eq_childRun_prepend
      A strategy hwin control first direction trace hzero hsucc⟩

end

end DetParityAutomaton

end DistributedSynthesis
