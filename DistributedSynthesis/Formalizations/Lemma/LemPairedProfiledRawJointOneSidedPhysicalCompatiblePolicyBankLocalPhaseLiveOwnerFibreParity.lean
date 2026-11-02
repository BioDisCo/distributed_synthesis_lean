/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatiblePolicyBankLocalPhaseLiveOwnerFibreEntry
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodePolicyImage
import DistributedSynthesis.Formalizations.Lemma.LemFiniteGlobalMachinePhysicalAcceptanceOfAccepts

/-!
# Policy parity behind the owner-fibre recurrent carrier

The owner-fibre carrier keeps several endpoint-local views of the current
bank state.  Its acceptance proof must nevertheless follow one rational
policy, rather than paste accepting fragments selected at successive roots.

This file isolates the policy-level part of that argument.  A path starts at
one fixed admissible bank key and every edge is a successor of the policy
selected once at that key.  The complete parent-linked code word is therefore
accepted.  Erasing the installed physical annotation yields acceptance of the
underlying one-sided incidence-code word.
-/

namespace DistributedSynthesis

universe u v x y s w

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

private abbrev RootKey :=
  ProfiledRawJointOneSidedPhysicalCompatibleRootKey A strategy

private abbrev PhysicalAnnotation :=
  ProfiledRawJointHybridPhysicalEdgeAnnotation A

private abbrev LinkedCode :=
  SourceFreeBeliefParentLinkedCode
    (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private noncomputable abbrev BareDPA (key : RootKey A strategy) :=
  profiledRawJointOneSidedCodeParityDPA A key.1.1

private noncomputable abbrev LinkedDPA (key : RootKey A strategy) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A) (BareDPA A strategy key)

private abbrev PolicyState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatiblePolicyState A strategy hwin
    key.1.1 key.1.2

private noncomputable abbrev Policy (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleRationalPolicy A strategy hwin
    key.1.1 key.1.2

/-- A root-started path through the successor image of the single policy
selected for `key`.  The path may choose a different finite child code at
each step, but it cannot change its bank key or rational policy. -/
structure ProfiledRawJointOneSidedPhysicalCompatibleBankPath
    (key : RootKey A strategy) where
  state : Nat → PolicyState A strategy hwin key
  initial_state :
    state 0 =
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key).run []
  allowed : ∀ n : Nat,
    ∃ childCode : LinkedCode A,
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
          key).successor (state n) childCode = state (n + 1)

namespace ProfiledRawJointOneSidedPhysicalCompatibleBankPath

variable {key : RootKey A strategy}

/-- The unique state sequence obtained by feeding a linked-code word to the
policy selected once at `key`.  This definition is proof-side: it introduces
no policy choice after time zero. -/
noncomputable def stateOfLinkedCodeWord
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A)) :
    Nat → PolicyState A strategy hwin key
  | 0 =>
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key).run []
  | n + 1 =>
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key).successor (stateOfLinkedCodeWord key word n) (word n)

@[simp] theorem stateOfLinkedCodeWord_zero
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A)) :
    stateOfLinkedCodeWord A strategy hwin key word 0 =
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key).run [] :=
  rfl

@[simp] theorem stateOfLinkedCodeWord_succ
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A)) (n : Nat) :
    stateOfLinkedCodeWord A strategy hwin key word (n + 1) =
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key).successor (stateOfLinkedCodeWord A strategy hwin key word n)
          (word n) :=
  rfl

/-- Every linked-code word canonically induces a root-started path through
the single policy stored at `key`.  Later controller proofs therefore need
only identify the linked code completed by each physical block; they do not
need to select a new policy state or policy at that block. -/
noncomputable def ofLinkedCodeWord
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A)) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin key :=
  { state := stateOfLinkedCodeWord A strategy hwin key word
    initial_state := rfl
    allowed := fun n ↦ ⟨word n, rfl⟩ }

@[simp] theorem ofLinkedCodeWord_state
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A)) (n : Nat) :
    (ofLinkedCodeWord A strategy hwin key word).state n =
      stateOfLinkedCodeWord A strategy hwin key word n :=
  rfl

/-- Positive-time word of complete parent-linked codes. -/
def linkedCodeWord
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key) : OmegaWord (LinkedCode A) :=
  fun n ↦ (path.state (n + 1)).1

theorem ofLinkedCodeWord_linkedCodeWord_eq
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A))
    (hexact : ∀ n : Nat,
      ((profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
          key).successor
        (stateOfLinkedCodeWord A strategy hwin key word n) (word n)).1 =
          word n) :
    (ofLinkedCodeWord A strategy hwin key word).linkedCodeWord A strategy
        hwin = word := by
  funext n
  exact hexact n

/-- Positive-time word after erasing the installed physical annotation. -/
def bareCodeWord
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key) : OmegaWord (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  fun n ↦ (path.state (n + 1)).1.1

@[simp] theorem linkedCodeWord_fst
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key) :
    OmegaWord.map Prod.fst (path.linkedCodeWord A strategy hwin) =
      path.bareCodeWord A strategy hwin := by
  rfl

theorem ofLinkedCodeWord_bareCodeWord_eq
    (key : RootKey A strategy) (word : OmegaWord (LinkedCode A))
    (hexact : ∀ n : Nat,
      ((profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
          key).successor
        (stateOfLinkedCodeWord A strategy hwin key word n) (word n)).1 =
          word n) :
    (ofLinkedCodeWord A strategy hwin key word).bareCodeWord A strategy hwin =
      OmegaWord.map Prod.fst word := by
  calc
    _ = OmegaWord.map Prod.fst
          ((ofLinkedCodeWord A strategy hwin key word).linkedCodeWord A
            strategy hwin) :=
      (linkedCodeWord_fst A strategy hwin
        (ofLinkedCodeWord A strategy hwin key word)).symm
    _ = OmegaWord.map Prod.fst word := congrArg (OmegaWord.map Prod.fst)
      (ofLinkedCodeWord_linkedCodeWord_eq A strategy hwin key word hexact)

/-- The complete linked-code word is accepted by the parent-linked DPA of the
single bank policy. -/
theorem linkedCodeWord_accepts
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key) :
    (LinkedDPA A strategy key).Accepts
      (path.linkedCodeWord A strategy hwin) := by
  simpa only [linkedCodeWord] using
    SourceFreeBeliefFiniteCodePolicyImage.accepts_of_allowedTarget_path
      (LinkedDPA A strategy key) key.1
      (sourceFreeBeliefParentLinkedValid
        (ProfiledRawJointOneSidedProvenanceValid A strategy)
        (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy
          hwin))
      (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))
      (profiledRawJointOneSidedPhysicalCompatiblePolicyBank A strategy hwin
        key)
      path.state path.initial_state path.allowed

/-- The anti-mosaic parity conclusion needed by the physical acceptance
argument: after annotation erasure, the path is accepted by the original
one-sided incidence-code DPA. -/
theorem bareCodeWord_accepts
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key) :
    (BareDPA A strategy key).Accepts
      (path.bareCodeWord A strategy hwin) := by
  have hlinked := path.linkedCodeWord_accepts A strategy hwin
  change ((BareDPA A strategy key).comap Prod.fst).Accepts _ at hlinked
  rw [DetParityAutomaton.comap_accepts_iff] at hlinked
  simpa only [linkedCodeWord_fst] using hlinked

/-- Every initially selected hidden lineage along the coherent bank path has
min-even parity.  The next physical-acceptance seam must identify the live
root selected by this run at time `n + 1` with the root at the corresponding
physical block cut. -/
theorem threadPriority_parity
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key)
    (initialSide : IndexedLineageSide) :
    NatSeqMinEvenParity (fun n ↦
      (codedAlternatingIndexedLineageCodeThreadSystem key.1.1
        (profiledRawJointOneSidedCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun key.1.1
          (profiledRawJointOneSidedCurrentSlots A)
          (path.bareCodeWord A strategy hwin) initialSide () n)) := by
  have haccepts := path.bareCodeWord_accepts A strategy hwin
  have hcoded :
      (codedAlternatingIndexedLineageCodeDPA key.1.1
        (profiledRawJointOneSidedCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).Accepts
          (path.bareCodeWord A strategy hwin) := by
    simpa only [BareDPA, profiledRawJointOneSidedCodeParityDPA] using haccepts
  exact
    (codedAlternatingIndexedLineageCodeDPA_accepts_iff key.1.1
      (profiledRawJointOneSidedCurrentSlots A)
      (profiledRawJointThreadRootPriority A)
      (path.bareCodeWord A strategy hwin)).mp hcoded initialSide ()

end ProfiledRawJointOneSidedPhysicalCompatibleBankPath

/-! ## Acceptance-facing physical cut alignment -/

/-- The remaining acceptance contract for an actual finite controller trace.

The path fixes one admissible bank key and hence one rational policy.  The
controller-specific obligation is the displayed block-minimum equation: the
minimum automaton priority in physical block `k` must equal the priority of a
single hidden lineage along that fixed policy path.  The proof-side `offset`
may skip a finite bootstrap before the recurrent carrier is active. -/
structure
    ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment
    {key : RootKey A strategy}
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  initialSide : IndexedLineageSide
  offset : Nat
  blockMin_eq_threadPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k =
      (codedAlternatingIndexedLineageCodeThreadSystem key.1.1
        (profiledRawJointOneSidedCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
        (codedAlternatingIndexedLineageCodeRun key.1.1
          (profiledRawJointOneSidedCurrentSlots A)
          (path.bareCodeWord A strategy hwin) initialSide () (offset + k))

/-- A more checkable decomposition of the preceding acceptance contract.

The physical proof identifies the minimum of each block with a concrete live
target root.  Independently, the policy proof identifies that same root with
the live root of its coded-lineage run.  Thus no theorem needs to equate
semantic representatives or independently selected policies. -/
structure
    ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment
    {key : RootKey A strategy}
    (path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (start : Nat) (cuts : Nat → Nat) where
  cuts_strictMono : StrictMono cuts
  cuts_zero : cuts 0 = 0
  rootAt : Nat → ProfiledRawJointThreadRoot A
  blockMin_eq_rootPriority : ∀ k : Nat,
    cutBlockMin
        (fun n ↦ A.priority
          (A.run (G.globalMachineTraceWord outputOne outputTwo env)
            (start + n)))
        cuts k = profiledRawJointThreadRootPriority A (rootAt k)
  initialSide : IndexedLineageSide
  offset : Nat
  lineage_live_at_root : ∀ k : Nat,
    ∃ side : IndexedLineageSide,
      ∃ code : ProfiledRawJointIncidenceCode A (I := Unit),
        codedAlternatingIndexedLineageCodeRun key.1.1
            (profiledRawJointOneSidedCurrentSlots A)
            (path.bareCodeWord A strategy hwin) initialSide () (offset + k) =
          (code, .live side () (rootAt k))

namespace
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment

/-- Composing the physical target-priority equation with literal live-root
alignment yields the direct block-minimum contract. -/
noncomputable def toPhysicalCutAlignment
    {key : RootKey A strategy}
    {path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment
        A strategy hwin path G outputOne outputTwo env start cuts) :
    ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment A
      strategy hwin path G outputOne outputTwo env start cuts :=
  { cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    initialSide := alignment.initialSide
    offset := alignment.offset
    blockMin_eq_threadPriority := fun k ↦ by
      obtain ⟨side, code, hlive⟩ := alignment.lineage_live_at_root k
      calc
        _ = profiledRawJointThreadRootPriority A (alignment.rootAt k) :=
          alignment.blockMin_eq_rootPriority k
        _ = _ := by rw [hlive]; rfl }

end
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment

namespace
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment

/-- The physical cut equation and fixed-policy path supply an ordinary epoch
coupling for the complete controller trace. -/
noncomputable def epochCoupling
    {key : RootKey A strategy}
    {path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment A
        strategy hwin path G outputOne outputTwo env start cuts) :
    A.FiniteGlobalMachineEpochCoupling G outputOne outputTwo env := by
  let priorities := fun n ↦
    (codedAlternatingIndexedLineageCodeThreadSystem key.1.1
      (profiledRawJointOneSidedCurrentSlots A)
      (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun key.1.1
        (profiledRawJointOneSidedCurrentSlots A)
        (path.bareCodeWord A strategy hwin) alignment.initialSide () n)
  have hfull : NatSeqMinEvenParity priorities := by
    simpa only [priorities] using
      path.threadPriority_parity A strategy hwin alignment.initialSide
  have hshift :
      NatSeqMinEvenParity (fun k ↦ priorities (alignment.offset + k)) :=
    (natSeqMinEvenParity_shift priorities alignment.offset).mpr hfull
  exact {
    start := start
    cuts := cuts
    cuts_strictMono := alignment.cuts_strictMono
    cuts_zero := alignment.cuts_zero
    epochPriority := fun k ↦ priorities (alignment.offset + k)
    epochParity := hshift
    blockMin_eq_epochPriority := fun k ↦ by
      simpa only [priorities] using
        alignment.blockMin_eq_threadPriority k }

/-- A controller trace satisfying the cut alignment is accepted.  Any finite
prefix before `start` is ignored by the parity condition. -/
theorem accepts
    {key : RootKey A strategy}
    {path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment A
        strategy hwin path G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  A.finiteGlobalMachineTraceWord_accepts_of_epochCoupling G outputOne outputTwo
    env (alignment.epochCoupling A strategy hwin)

end
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalCutAlignment

namespace
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment

/-- The decomposed root alignment is sufficient for acceptance. -/
theorem accepts
    {key : RootKey A strategy}
    {path : ProfiledRawJointOneSidedPhysicalCompatibleBankPath A strategy hwin
      key}
    {G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂}
    {outputOne : G.State → Out₁} {outputTwo : G.State → Out₂}
    {env : EnvironmentSequence In₁ In₂}
    {start : Nat} {cuts : Nat → Nat}
    (alignment :
      ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment
        A strategy hwin path G outputOne outputTwo env start cuts) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (alignment.toPhysicalCutAlignment A strategy hwin).accepts A strategy hwin

end
  ProfiledRawJointOneSidedPhysicalCompatibleBankPhysicalRootCutAlignment

end

end DetParityAutomaton

end DistributedSynthesis
