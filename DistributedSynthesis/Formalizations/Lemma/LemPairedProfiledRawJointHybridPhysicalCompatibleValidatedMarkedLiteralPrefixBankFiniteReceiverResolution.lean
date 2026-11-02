/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridPhysicalCompatibleValidatedMarkedLiteralPrefixBankRetainedReinstallation
import DistributedSynthesis.Formalizations.Lemma.LemRowExactIndexedTargetReceiverOutput

/-!
# Finite receiver-target resolution for the marked retained bank

`ProfiledRawJointHybridPhysicalCompatibleSuccessorDecoration` already gives
the right local interface in the unmarked construction: a receiver emits its
ordinary finite incidence target together with a same-policy successor key.
For the marked literal bank a target need not determine one annotated key, so
choosing a single representative would be unsound.  The exact replacement is
the finite set of all same-bank successors having that public target.

This file builds that resolver and decorates the existing right/left receiver
tables with it.  The physical output and bare target project definitionally.
An actual reachable semantic child is proved to belong to the finite set from
only its public-target equation.  Thus the executable handoff no longer needs
the proof-side `HybridDirection` (which contains an unbounded tagged past), a
graph, hierarchy side, leader bit, or strict-leader bit.

What remains outside this adapter is scheduling: a local receive cannot tell
strict from simultaneous, so a controller must carry the finite candidate
set until a later delivered partner state resolves the event.  No semantic
or infinitary data remain in that resolver contract.
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

private abbrev HybridDirection :=
  ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂)

private abbrev PublicTarget :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointHybridCode A)
    (Annotation :=
      ProfiledRawJointHybridPhysicalCompatibleExtraAnnotation A
        (ProfiledRawJointHybridMarkedLiteralPrefixExtra A))

/-! ## Exact finite relation and its materialization -/

/-- One finite same-bank successor whose public child is the receiver's bare
one-sided incidence target. -/
structure
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
    (state : BankControl A strategy hwin) (target : PublicTarget A)
    (next : BankControl A strategy hwin) where
  childCode : LinkedCode A
  successor : next =
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
      hwin state childCode
  publicTarget : next.2.1.1 = .oneSided target

/-- The exact finite set of all resolutions of one bare receiver target. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates
    (state : BankControl A strategy hwin) (target : PublicTarget A) :
    Finset (BankControl A strategy hwin) := by
  classical
  exact Finset.univ.filter fun next ↦
    Nonempty
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
        A strategy hwin state target next)

/-- Set membership is exactly the resolution relation, with no completeness
or representative assumption hidden in the definition. -/
theorem
    mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates_iff
    (state next : BankControl A strategy hwin) (target : PublicTarget A) :
    next ∈
        profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates
          A strategy hwin state target ↔
      Nonempty
        (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
          A strategy hwin state target next) := by
  classical
  simp [profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates]

/-- Every candidate remains in the same fixed bank entry. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.same_index
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
        A strategy hwin state target next) :
    next.1 = state.1 := by
  rw [resolution.successor]
  rfl

/-- Every candidate successor of a reachable key is reachable in that same
bank. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt.reachable
    {state next : BankControl A strategy hwin} {target : PublicTarget A}
    (resolution :
      ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetResolutionAt
        A strategy hwin state target next)
    (hreachable : BankReachable A strategy hwin state) :
    BankReachable A strategy hwin next := by
  rw [resolution.successor]
  exact
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor_reachable A
      strategy hwin state hreachable resolution.childCode

/-! ## The real raw child belongs to the finite resolver -/

/-- Full code, not only the literal component, is preserved when the total
bank lookup follows a real direction at a reachable state. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂)) :
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
        hwin state (state.childCode A strategy hwin direction)).2.1 =
      state.childCode A strategy hwin direction := by
  let packet :=
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankFiniteStep A strategy
      hwin state.1 state.2 hreachable
  have hmove :=
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.move_eq_of_reachable
      A strategy hwin state hreachable
  have hsuccessor :=
    packet.successor
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
        state.2.1 packet.move direction)
  have hfinite :
      sourceFreeBeliefFiniteCodeNext
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
          state.2.1 packet.move
          (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
            state.2.1 packet.move direction) =
        sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A)
          state.2.1 packet.move direction :=
    sourceFreeBeliefFiniteCodeNext_of_direction
      (sourceFreeBeliefParentLinkedNext (profiledRawJointHybridNext A))
      state.2.1 packet.move direction
  rw [hfinite] at hsuccessor
  have hcode := congrArg Prod.fst hsuccessor
  change
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixPolicyBank A strategy
        hwin state.1).successor state.2
          (state.childCode A strategy hwin direction)).1 =
      state.childCode A strategy hwin direction
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.childCode,
    hmove]
  exact hcode

/-- If the finite receiver reports the real child's public target, then the
real successor is in the resolver set.  This is the precise replacement for
passing the infinitary direction to the runtime callback. -/
theorem
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_mem_targetCandidates
    (state : BankControl A strategy hwin)
    (hreachable : BankReachable A strategy hwin state)
    (direction : HybridDirection (In₁ := In₁) (In₂ := In₂))
    (target : PublicTarget A)
    (hpublic : (state.childCode A strategy hwin direction).1 =
      .oneSided target) :
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankSuccessor A strategy
          hwin state (state.childCode A strategy hwin direction) ∈
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state target := by
  rw [mem_profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates_iff]
  refine ⟨
    { childCode := state.childCode A strategy hwin direction
      successor := rfl
      publicTarget := ?_ }⟩
  rw [ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankControl.advance_code
    A strategy hwin state hreachable direction]
  exact hpublic

/-! ## Row-exact decoration of the existing finite receiver output -/

/-- A bare target, its literal row, and all compatible marked-bank successor
keys. -/
abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTarget :=
  PublicTarget A ×
    (PairedEntryRow × Finset (BankControl A strategy hwin))

noncomputable instance
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTargetFintype :
    Fintype
      (ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTarget A
        strategy hwin) := by
  classical
  infer_instance

private abbrev ResolvedTarget :=
  ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTarget A
    strategy hwin

def profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTargetRow
    (target : ResolvedTarget A strategy hwin) : PairedEntryRow :=
  target.2.1

abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedRightReceiverOutput :=
  RowExactIndexedTargetReceiverOutput
    (PairedRightReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow (ResolvedTarget A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTargetRow A
      strategy hwin)

abbrev
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedLeftReceiverOutput :=
  RowExactIndexedTargetReceiverOutput
    (PairedLeftReceiverOutput (Out₁ := Out₁) (Out₂ := Out₂))
    PairedEntryRow (ResolvedTarget A strategy hwin)
    (profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedTargetRow A
      strategy hwin)

/-- Decorate every row of an existing right receiver output with its complete
finite marked-bank successor set. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveRightReceiverOutput
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedRightReceiverOutput
      A strategy hwin :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates
            A strategy hwin state (output.target row))))
    (fun _ ↦ rfl)

/-- Left mirror. -/
noncomputable def
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveLeftReceiverOutput
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) :
    ProfiledRawJointHybridValidatedMarkedLiteralPrefixBankResolvedLeftReceiverOutput
      A strategy hwin :=
  RowExactIndexedTargetReceiverOutput.ofTarget output.physical
    (fun row ↦
      (output.target row,
        (row,
          profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates
            A strategy hwin state (output.target row))))
    (fun _ ↦ rfl)

/-- Erasing the candidate sets and row proofs recovers the original right
receiver output definitionally. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveRightReceiverOutput_project
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) :
    let resolved :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveRightReceiverOutput
        A strategy hwin state output
    ({ physical := resolved.physical
       target := fun row ↦ (resolved.target row).1.1 } :
      ProfiledRawJointTargetRightReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) = output :=
  rfl

/-- Left projection. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveLeftReceiverOutput_project
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) :
    let resolved :=
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveLeftReceiverOutput
        A strategy hwin state output
    ({ physical := resolved.physical
       target := fun row ↦ (resolved.target row).1.1 } :
      ProfiledRawJointTargetLeftReceiverOutput
        (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A)) = output :=
  rfl

/-- The candidate field at a right receiver row is exactly the finite resolver
for that row's original bare target. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveRightReceiverOutput_candidates
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetRightReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A))
    (row : PairedEntryRow) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveRightReceiverOutput
        A strategy hwin state output).target row).1.2.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state (output.target row) :=
  rfl

/-- Left mirror. -/
@[simp] theorem
    profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveLeftReceiverOutput_candidates
    (state : BankControl A strategy hwin)
    (output : ProfiledRawJointTargetLeftReceiverOutput
      (Out₁ := Out₁) (Out₂ := Out₂) (PublicTarget A))
    (row : PairedEntryRow) :
    ((profiledRawJointHybridValidatedMarkedLiteralPrefixBankResolveLeftReceiverOutput
        A strategy hwin state output).target row).1.2.2 =
      profiledRawJointHybridValidatedMarkedLiteralPrefixBankTargetCandidates A
        strategy hwin state (output.target row) :=
  rfl

end

end DetParityAutomaton

end DistributedSynthesis
