/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleExactEffectTable

/-!
# Semantic characterization of the exact owner-table obligation

The raw-table owner verifier is meaningful before its memory is finite.  This
file identifies its acceptance condition exactly.  From a live entry, the
guarded verifier accepts if and only if every finite prefix satisfies the
structural decoder and the objective automaton accepts the literal round word
emitted by the unguarded kernel.  From the rejecting sink it never accepts.

This removes the old active-parent proxy from the remaining proof: the two
facts still required are decoder preservation and acceptance of the literal
emitted word.  Equality with an execution suffix of the named `strategy` is
not a valid general route to the second fact: physical sibling owners have
already been rationalized, even when bank memory is exact.  The separate
`LemFiniteBlindLiteralTraceObstruction` gives a winning strategy whose output
no finite blind owner can reproduce on any suffix.  An acceptance proof must
justify the changed outputs, rather than assume their literal preservation.
-/

namespace DistributedSynthesis

universe u v x y s m

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable {Memory : Type m}
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

private abbrev ExactMemory :=
  ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy

private abbrev Direction :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

private abbrev TableFamily :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy

private abbrev ExactBankControl :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankControl
    (Memory := ExactMemory A strategy) A strategy

private abbrev ExactPacket :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryBankResolvedTarget
    (Memory := ExactMemory A strategy) A strategy

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

variable (tables : TableFamily (Memory := Memory) A strategy)

/-- Exact literal word emitted by the unguarded raw-table kernel. -/
def ownerFibreSafetyWord
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂) :=
  fun n ↦
    let state := tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
      (branchNode branch n)
    tables.ownerFibreRoundRecord A strategy hwin state.1 (branch n).1
      (branch n).2

theorem ownerFibreSafetyLiveStateAt_append
    (initial : LiveState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
        (node ++ [direction]) =
      tables.ownerFibreSafetyLiveStep A strategy hwin
        (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial node)
        direction := by
  simp [ownerFibreSafetyLiveStateAt, List.foldl_append]

theorem ownerFibreSafetyStateAt_append
    (initial : SafetyState (Memory := Memory) A strategy)
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂)))
    (direction : Direction (In₁ := In₁) (In₂ := In₂)) :
    tables.ownerFibreSafetyStateAt A strategy hwin initial
        (node ++ [direction]) =
      tables.ownerFibreSafetyStep A strategy hwin
        (tables.ownerFibreSafetyStateAt A strategy hwin initial node)
        direction := by
  simp [ownerFibreSafetyStateAt, List.foldl_append]

/-- The objective coordinate of the live product is the DPA run on the
literal word emitted by the owner kernel. -/
theorem ownerFibreSafetyLiveStateAt_dpa
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    ∀ n,
      (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
        (branchNode branch n)).2 =
      A.runFrom initial.2
        (tables.ownerFibreSafetyWord A strategy hwin initial branch) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        tables.ownerFibreSafetyLiveStateAt_append A strategy hwin initial
          (branchNode branch n) (branch n)]
      simp only [ownerFibreSafetyLiveStep, runFrom, ownerFibreSafetyWord]
      rw [ih]

@[simp] theorem ownerFibreSafetyStateAt_none
    (node : TreeNode (Direction (In₁ := In₁) (In₂ := In₂))) :
    tables.ownerFibreSafetyStateAt A strategy hwin none node = none := by
  induction node using List.reverseRecOn with
  | nil => rfl
  | append_singleton node direction ih =>
      rw [tables.ownerFibreSafetyStateAt_append A strategy hwin none node
        direction, ih]
      rfl

/-- Once the rejecting sink is reached, it persists on the rest of a branch. -/
theorem ownerFibreSafetyStateAt_none_persists
    (initial : SafetyState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (N : Nat)
    (hN : tables.ownerFibreSafetyStateAt A strategy hwin initial
      (branchNode branch N) = none) :
    ∀ k,
      tables.ownerFibreSafetyStateAt A strategy hwin initial
        (branchNode branch (N + k)) = none := by
  intro k
  induction k with
  | zero => simpa using hN
  | succ k ih =>
      rw [show branchNode branch (N + (k + 1)) =
          branchNode branch (N + k) ++ [branch (N + k)] by congr 1,
        tables.ownerFibreSafetyStateAt_append A strategy hwin initial
          (branchNode branch (N + k)) (branch (N + k)), ih]
      rfl

/-- An accepting guarded raw-table run never reaches decoder failure. -/
theorem OwnerFibreSafe.stateAt_ne_none
    (initial : SafetyState (Memory := Memory) A strategy)
    (hsafe : tables.OwnerFibreSafe A strategy hwin initial)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (N : Nat) :
    tables.ownerFibreSafetyStateAt A strategy hwin initial
      (branchNode branch N) ≠ none := by
  intro hN
  have hpersist := tables.ownerFibreSafetyStateAt_none_persists A strategy hwin
    initial branch N hN
  have heventual : ∃ cutoff, ∀ n, cutoff ≤ n →
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
          (Memory := Memory) A strategy
          (tables.ownerFibreSafetyStateAt A strategy hwin initial
            (branchNode branch n)) = 1 := by
    refine ⟨N, ?_⟩
    intro n hn
    have heq : N + (n - N) = n := by omega
    rw [← heq, hpersist]
    rfl
  rcases hsafe branch with ⟨p, hpEven, hpSeen, _hpMin⟩
  rcases heventual with ⟨cutoff, heventual⟩
  rcases hpSeen cutoff with ⟨k, hk, hpriority⟩
  have hp : p = 1 := hpriority.symm.trans (heventual k hk)
  subst p
  rcases hpEven with ⟨q, hq⟩
  omega

/-- Under acceptance, the guarded prefix is exactly the live prefix. -/
theorem OwnerFibreSafe.stateAt_eq_some_liveStateAt
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : tables.OwnerFibreSafe A strategy hwin (some initial))
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    ∀ n,
      tables.ownerFibreSafetyStateAt A strategy hwin (some initial)
          (branchNode branch n) =
        some (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
          (branchNode branch n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        tables.ownerFibreSafetyStateAt_append A strategy hwin (some initial)
          (branchNode branch n) (branch n),
        tables.ownerFibreSafetyLiveStateAt_append A strategy hwin initial
          (branchNode branch n) (branch n), ih]
      by_cases hdecodes :
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := Memory) A strategy
            (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
              (branchNode branch n)).1.1
            (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
              (branchNode branch n)).1.2
      · simp [ownerFibreSafetyStep, hdecodes]
      · exfalso
        apply OwnerFibreSafe.stateAt_ne_none (Memory := Memory) A strategy hwin
          tables (some initial) hsafe branch (n + 1)
        rw [show branchNode branch (n + 1) =
            branchNode branch n ++ [branch n] from rfl,
          tables.ownerFibreSafetyStateAt_append A strategy hwin (some initial)
            (branchNode branch n) (branch n), ih]
        simp [ownerFibreSafetyStep, hdecodes]

/-- Acceptance forces the structural decoder invariant at every live prefix. -/
theorem OwnerFibreSafe.decodes
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : tables.OwnerFibreSafe A strategy hwin (some initial))
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (n : Nat) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy
      (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
        (branchNode branch n)).1.1
      (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
        (branchNode branch n)).1.2 := by
  by_contra hdecodes
  apply OwnerFibreSafe.stateAt_ne_none (Memory := Memory) A strategy hwin
    tables (some initial) hsafe branch (n + 1)
  rw [show branchNode branch (n + 1) =
      branchNode branch n ++ [branch n] from rfl,
    tables.ownerFibreSafetyStateAt_append A strategy hwin (some initial)
      (branchNode branch n) (branch n),
    OwnerFibreSafe.stateAt_eq_some_liveStateAt (Memory := Memory) A strategy
      hwin tables initial hsafe branch n]
  simp [ownerFibreSafetyStep, hdecodes]

/-- Acceptance of the guarded run implies acceptance of its literal word from
the entry DPA state. -/
theorem OwnerFibreSafe.acceptsFrom
    (initial : LiveState (Memory := Memory) A strategy)
    (hsafe : tables.OwnerFibreSafe A strategy hwin (some initial))
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂)) :
    A.AcceptsFrom initial.2
      (tables.ownerFibreSafetyWord A strategy hwin initial branch) := by
  change NatSeqMinEvenParity (fun n ↦
    A.priority (A.runFrom initial.2
      (tables.ownerFibreSafetyWord A strategy hwin initial branch) n))
  simpa only [OwnerFibreSafe.stateAt_eq_some_liveStateAt
      (Memory := Memory) A strategy hwin tables initial hsafe branch,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority,
    tables.ownerFibreSafetyLiveStateAt_dpa A strategy hwin initial branch]
    using hsafe branch

/-- Branchwise decoding keeps the raw-table monitor out of the sink. -/
theorem ownerFibreSafetyStateAt_eq_some_of_decodes
    (initial : LiveState (Memory := Memory) A strategy)
    (branch : Nat → Direction (In₁ := In₁) (In₂ := In₂))
    (hdecodes : ∀ n,
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
        (Memory := Memory) A strategy
        (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
          (branchNode branch n)).1.1
        (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
          (branchNode branch n)).1.2) :
    ∀ n,
      tables.ownerFibreSafetyStateAt A strategy hwin (some initial)
          (branchNode branch n) =
        some (tables.ownerFibreSafetyLiveStateAt A strategy hwin initial
          (branchNode branch n)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        tables.ownerFibreSafetyStateAt_append A strategy hwin (some initial)
          (branchNode branch n) (branch n),
        tables.ownerFibreSafetyLiveStateAt_append A strategy hwin initial
          (branchNode branch n) (branch n), ih]
      simp [ownerFibreSafetyStep, hdecodes n]

/-- Exact semantic characterization of raw-table owner safety, valid before
any finiteness assumption on the memory. -/
theorem ownerFibreSafe_iff_exists_live_decodes_and_acceptsFrom
    (initial : SafetyState (Memory := Memory) A strategy) :
    tables.OwnerFibreSafe A strategy hwin initial ↔
      ∃ live : LiveState (Memory := Memory) A strategy,
        initial = some live ∧
        (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
          ∀ n,
            ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
              (Memory := Memory) A strategy
              (tables.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch n)).1.1
              (tables.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch n)).1.2) ∧
        (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
          A.AcceptsFrom live.2
            (tables.ownerFibreSafetyWord A strategy hwin live branch)) := by
  constructor
  · intro hsafe
    cases initial with
    | none =>
        exfalso
        exact OwnerFibreSafe.stateAt_ne_none (Memory := Memory) A strategy hwin
          tables none hsafe (fun _ ↦ ((default, default), .both)) 0 rfl
    | some live =>
        exact ⟨live, rfl,
          OwnerFibreSafe.decodes (Memory := Memory) A strategy hwin tables live
            hsafe,
          OwnerFibreSafe.acceptsFrom (Memory := Memory) A strategy hwin tables
            live hsafe⟩
  · rintro ⟨live, rfl, hdecodes, haccepts⟩ branch
    have hacceptsBranch := haccepts branch
    change NatSeqMinEvenParity (fun n ↦
      A.priority (A.runFrom live.2
        (tables.ownerFibreSafetyWord A strategy hwin live branch) n)) at hacceptsBranch
    simpa only [tables.ownerFibreSafetyStateAt_eq_some_of_decodes A strategy
        hwin live branch (hdecodes branch),
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority,
      tables.ownerFibreSafetyLiveStateAt_dpa A strategy hwin live branch]
      using hacceptsBranch

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-! ## Exact-memory alignment of every stored entry coordinate -/

/-- One bank coordinate belongs to `key` and its public linked code is
exactly the public image of its perfect-recall semantic memory. -/
def ExactBankAt
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy) : Prop :=
  state.1 = key ∧
    state.2.1.1 = exactMemoryPublicCode A strategy state.2.2

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The fixed-key exact table family starts at an exact bank coordinate. -/
theorem exactEffectTable_family_root_exactBankAt
    (key : RootKey A strategy) :
    ExactBankAt A strategy key
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
        A strategy (exactInitialMemory A strategy) key) := by
  exact ⟨rfl, exactEffectTable_root_aligned A strategy key⟩

/-- Any family successor of an exact bank coordinate remains exact at the
same key. -/
theorem ExactBankAt.family_successor
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (childCode :
      SourceFreeBeliefParentLinkedCode
        (BeliefCode := ProfiledRawJointIncidenceCode A (I := Unit))
        (Annotation := ProfiledRawJointHybridPhysicalEdgeAnnotation A)) :
    ExactBankAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).successor A strategy state childCode) := by
  rcases state with ⟨stateKey, state⟩
  rcases hexact with ⟨hkey, haligned⟩
  change stateKey = key at hkey
  subst stateKey
  refine ⟨rfl, ?_⟩
  exact
    (show ExactPolicyAligned A strategy key state from haligned
      ).family_successor A strategy hwin key state childCode

/-- In particular, the complete packet returned by the resolver carries an
exact successor coordinate, independently of which target was requested. -/
theorem ExactBankAt.resolvePacket
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (target : ProfiledRawJointIncidenceCode A (I := Unit)) :
    ExactBankAt A strategy key
      ((((exactEffectTable A strategy hwin key).family A strategy key
        ).resolvePacket A strategy hwin state target).successor) := by
  exact hexact.family_successor A strategy hwin key state
    (((exactEffectTable A strategy hwin key).family A strategy key
      ).resolveTarget A strategy hwin state target)

/-- Exactness of every bank coordinate retained by a staged right-to-left
bridge. -/
def ExactRightToLeftBridgeAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match control with
  | .inl staged =>
      ExactBankAt A strategy key staged.1 ∧
        ∀ packet, staged.2.2 = some packet →
          ExactBankAt A strategy key packet.successor
  | .inr installed => ExactBankAt A strategy key installed.1

/-- Left-to-right mirror of `ExactRightToLeftBridgeAt`. -/
def ExactLeftToRightBridgeAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match control with
  | .inl staged =>
      ExactBankAt A strategy key staged.1 ∧
        ∀ packet, staged.2.2 = some packet →
          ExactBankAt A strategy key packet.successor
  | .inr installed => ExactBankAt A strategy key installed.1

/-- Both dormant-left receiver meanings in a pending owner fibre carry exact
bank coordinates. -/
def ExactRightToLeftOwnerFibreAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy
        ⟨false, control.2.1, control.2.2⟩).1 ∧
    ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy
        ⟨true, control.2.1, control.2.2⟩).1

/-- Both dormant-right receiver meanings in the mirrored pending fibre carry
exact bank coordinates. -/
def ExactLeftToRightOwnerFibreAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy
        ⟨false, control.2.1, control.2.2⟩).1 ∧
    ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy
        ⟨true, control.2.1, control.2.2⟩).1

def ExactBoundaryOneBaseAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneBase
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match control with
  | .inl bridge => ExactLeftToRightBridgeAt A strategy key bridge
  | .inr pending => ExactRightToLeftOwnerFibreAt A strategy key pending

def ExactBoundaryTwoBaseAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoBase
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match control with
  | .inl bridge => ExactRightToLeftBridgeAt A strategy key bridge
  | .inr pending => ExactLeftToRightOwnerFibreAt A strategy key pending

/-- Every bank coordinate stored by process one is synchronized with its own
exact semantic memory. -/
def ExactBoundaryOneAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBoundaryOneBaseAt A strategy key control.1 ∧
    ExactBankAt A strategy key control.2.1 ∧
    ExactBankAt A strategy key control.2.2

/-- Every bank coordinate stored by process two is synchronized with its own
exact semantic memory. -/
def ExactBoundaryTwoAt
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBoundaryTwoBaseAt A strategy key control.1 ∧
    ExactBankAt A strategy key control.2.1 ∧
    ExactBankAt A strategy key control.2.2

/-- Complete alignment invariant for the two endpoint controls of a live
owner state. -/
def ExactOwnerLiveAt
    (key : RootKey A strategy)
    (live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBoundaryOneAt A strategy key live.1.1 ∧
    ExactBoundaryTwoAt A strategy key live.1.2

def ExactRightPhaseDataAt
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBankAt A strategy key data.1.1 ∧
    ExactBankAt A strategy key data.2.1

def ExactLeftPhaseDataAt
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactBankAt A strategy key data.1.1 ∧
    ExactBankAt A strategy key data.2.1

/-! ### Exact phase data as two operational orientations -/

/-- Read the dormant left owner/receiver pair of a right-live phase as a
left boundary.  This is the finite-memory counterpart of the semantic phase
projection used by the recurrent carrier proof. -/
noncomputable def ExactRightPhaseDormantLeftData
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy :=
  (phaseData.2.1, ⟨phaseData.1.2.2, phaseData.2.2⟩,
    phaseData.1.receiver (Memory := ExactMemory A strategy) A strategy)

/-- Mirrored dormant-right projection. -/
noncomputable def ExactLeftPhaseDormantRightData
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy :=
  (phaseData.2.1, ⟨phaseData.1.2.2, phaseData.2.2⟩,
    phaseData.1.receiver (Memory := ExactMemory A strategy) A strategy)

/-! ### Reachable operational alignment

Exact bank memory prevents semantic mosaics, but the endpoint decoder also
depends on a physical receiver and its owner controller having advanced along
one common input prefix.  These two predicates record precisely that missing
operational fact for the active orientation. -/

def ExactRightBoundaryOperationalAt
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy) : Prop :=
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let move := receiver.1
  let monitor := profiledRawJointRightPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  ∃ currentCode : ProfiledRawJointIncidenceCode A (I := Unit),
    ∃ root : ProfiledRawJointThreadRoot A,
      ∃ past : List (In₂ × In₁),
        ExactBankAt A strategy key data.1 ∧
          data.1.2.1.1.1 = currentCode ∧
          profiledRawJointOneSidedCurrentSlots A .right currentCode () =
            some root ∧
          data.1.2.1.1.2.1 = some move ∧
          data.owner (Memory := ExactMemory A strategy) A strategy =
            controller.controlAt (senderWord past) ∧
          receiver.2.2.1 =
            narrowedControl monitor controller.labeledTree past

def ExactLeftBoundaryOperationalAt
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy) : Prop :=
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let move := receiver.1
  let monitor := profiledRawJointLeftPhysicalSiblingMonitor A move.1 false
  let controller := move.memberController A false
  ∃ currentCode : ProfiledRawJointIncidenceCode A (I := Unit),
    ∃ root : ProfiledRawJointThreadRoot A,
      ∃ past : List (In₁ × In₂),
        ExactBankAt A strategy key data.1 ∧
          data.1.2.1.1.1 = currentCode ∧
          profiledRawJointOneSidedCurrentSlots A .left currentCode () =
            some root ∧
          data.1.2.1.1.2.2 = some move ∧
          data.owner (Memory := ExactMemory A strategy) A strategy =
            controller.controlAt (senderWord past) ∧
          receiver.2.2.1 =
            narrowedControl monitor controller.labeledTree past

/-- A right-live phase is operational only when both the active right pair
and the dormant left pair are matched to their respective exact bank cells.
The dormant half is needed because a simultaneous close promotes it. -/
def ExactRightPhaseOperationalAt
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactRightBoundaryOperationalAt A strategy key phaseData.1 ∧
    ExactLeftBoundaryOperationalAt A strategy key
      (ExactRightPhaseDormantLeftData A strategy phaseData)

/-- Active-left/dormant-right mirror. -/
def ExactLeftPhaseOperationalAt
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactLeftBoundaryOperationalAt A strategy key phaseData.1 ∧
    ExactRightBoundaryOperationalAt A strategy key
      (ExactLeftPhaseDormantRightData A strategy phaseData)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- A valid right owner fibre, together with the exact bank cell carrying its
move, reconstructs a matched operational right boundary. -/
theorem exactRightBoundaryOperationalAt_of_fibre
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (template : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (fibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (hexact : ExactBankAt A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (hmove : state.2.1.1.2.1 = some fibre.1)
    (hfibre : ProfiledRawJointRightOwnerFibreValid A fibre) :
    ExactRightBoundaryOperationalAt A strategy key
      (state, ⟨fibre.finiteMemoryReceiverAt A template, fibre.2.1⟩,
        oldReceiver) := by
  rcases hfibre with ⟨past, howner, hreceiver⟩
  refine ⟨currentCode, root, past, hexact, hcode, hroot, hmove, ?_, ?_⟩
  · simpa [ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt]
      using howner
  · simpa [ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt]
      using hreceiver

/-- Left-fibre mirror of `exactRightBoundaryOperationalAt_of_fibre`. -/
theorem exactLeftBoundaryOperationalAt_of_fibre
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (template : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (fibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (hexact : ExactBankAt A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (hmove : state.2.1.1.2.2 = some fibre.1)
    (hfibre : ProfiledRawJointLeftOwnerFibreValid A fibre) :
    ExactLeftBoundaryOperationalAt A strategy key
      (state, ⟨fibre.finiteMemoryReceiverAt A template, fibre.2.1⟩,
        oldReceiver) := by
  rcases hfibre with ⟨past, howner, hreceiver⟩
  refine ⟨currentCode, root, past, hexact, hcode, hroot, hmove, ?_, ?_⟩
  · simpa [ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt]
      using howner
  · simpa [ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt]
      using hreceiver

/-- An exact cell with a live right slot and its installed move yields the
initial matched-prefix right boundary (the common prefix is empty). -/
theorem exactRightBoundaryOperationalAt_initial
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (hexact : ExactBankAt A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .right currentCode () =
      some root)
    (hmove : state.2.1.1.2.1 = some move) :
    ExactRightBoundaryOperationalAt A strategy key
      (state,
        ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move row,
          (move.memberController A false).initial⟩,
        oldReceiver) := by
  refine ⟨currentCode, root, [], hexact, hcode, hroot, hmove, ?_, ?_⟩
  · rfl
  · rfl

/-- Initial left-boundary mirror. -/
theorem exactLeftBoundaryOperationalAt_initial
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (row : PairedEntryRow)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (hexact : ExactBankAt A strategy key state)
    (currentCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hcode : state.2.1.1.1 = currentCode)
    (root : ProfiledRawJointThreadRoot A)
    (hroot : profiledRawJointOneSidedCurrentSlots A .left currentCode () =
      some root)
    (hmove : state.2.1.1.2.2 = some move) :
    ExactLeftBoundaryOperationalAt A strategy key
      (state,
        ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move row,
          (move.memberController A false).initial⟩,
        oldReceiver) := by
  refine ⟨currentCode, root, [], hexact, hcode, hroot, hmove, ?_, ?_⟩
  · rfl
  · rfl

/-- Matched-prefix operational alignment survives one strict-right physical
step.  The right monitor reads `(input.2, input.1)`, exactly the pair appended
to the owner history. -/
theorem ExactRightBoundaryOperationalAt.step
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let ownerNext := profiledRawJointRightPhysicalSiblingMemberNoRecvStep A
      receiver.1 false
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.1
    let receiverNext := stepProfiledRawJointRightPhysicalSiblingReceiverFor A
      receiver.1 (data.owner (Memory := ExactMemory A strategy) A strategy)
        receiver.2.1 receiver.2.2.1 (input.2, input.1)
    ExactRightBoundaryOperationalAt A strategy key
      (data.1, ⟨receiverNext.2, ownerNext.2⟩, data.2.2) := by
  rcases data with
    ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩, owner⟩,
      oldReceiver⟩
  dsimp only [ExactRightBoundaryOperationalAt,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner]
    at hoperational
  rcases hoperational with
    ⟨currentCode, root, past, hexact, hcode, hroot, hmove,
      howner, hreceiverState⟩
  subst owner
  subst receiverState
  refine ⟨currentCode, root, past ++ [(input.2, input.1)], hexact, hcode,
    hroot, hmove, ?_, ?_⟩
  · dsimp only [profiledRawJointRightPhysicalSiblingMemberNoRecvStep,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner]
    rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · dsimp only [stepProfiledRawJointRightPhysicalSiblingReceiverFor,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner]
    rw [narrowedControl_append]
    simp [narrowedRecord, TransitionRationalTree.labeledTree]

/-- Matched-prefix operational alignment survives one strict-left physical
step.  The owner reads the second input component, while the monitor reads
the whole ordered pair; both therefore move from the same witness `past` to
the common witness `past ++ [input]`. -/
theorem ExactLeftBoundaryOperationalAt.step
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let ownerNext := profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A
      receiver.1 false
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.2
    let receiverNext := stepProfiledRawJointLeftPhysicalSiblingReceiverFor A
      receiver.1 (data.owner (Memory := ExactMemory A strategy) A strategy)
        receiver.2.1 receiver.2.2.1 input
    ExactLeftBoundaryOperationalAt A strategy key
      (data.1, ⟨receiverNext.2, ownerNext.2⟩, data.2.2) := by
  rcases data with
    ⟨state, ⟨⟨move, row, receiverState, lastTarget⟩, owner⟩,
      oldReceiver⟩
  dsimp only [ExactLeftBoundaryOperationalAt,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner]
    at hoperational
  rcases hoperational with
    ⟨currentCode, root, past, hexact, hcode, hroot, hmove,
      howner, hreceiverState⟩
  subst owner
  subst receiverState
  refine ⟨currentCode, root, past ++ [input], hexact, hcode, hroot,
    hmove, ?_, ?_⟩
  · dsimp only [profiledRawJointLeftPhysicalSiblingMemberNoRecvStep,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner]
    rw [senderWord_append, TransitionRationalTree.controlAt_append]
    simp
  · dsimp only [stepProfiledRawJointLeftPhysicalSiblingReceiverFor,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner]
    rw [narrowedControl_append]
    simp [narrowedRecord, TransitionRationalTree.labeledTree]

end

/-- An operational right boundary creates two valid members of its outgoing
right-owner fibre.  Only reachability of the active owner is used; the packet
and its exact-memory coordinate are irrelevant to this physical certificate. -/
theorem ExactRightBoundaryOperationalAt.ownerFibreReceive_valid
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data)
    (oldState : ExactBankControl A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.rightBoundaryOwnerFibreReceive A strategy hwin data oldState
        oldOwner input
    ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy
        result.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy
        result.1.closedControl := by
  rcases hoperational with
    ⟨_currentCode, _root, past, _hexact, _hcode, _hroot, _hmove,
      howner, _hreceiver⟩
  have hreachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A
        (data.receiver (Memory := ExactMemory A strategy) A strategy).1
        (data.owner (Memory := ExactMemory A strategy) A strategy) :=
    ⟨senderWord past, howner⟩
  simpa only [
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightBoundaryOwnerFibreReceive]
    using
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork_valid
        (Memory := ExactMemory A strategy) A strategy
          ⟨(data.receiver (Memory := ExactMemory A strategy) A strategy).1,
            data.owner (Memory := ExactMemory A strategy) A strategy⟩
          hreachable oldState data.2.2 oldOwner
          (((exactEffectTable A strategy hwin key).family A strategy key
            ).resolvePacket A strategy hwin data.1
              (data.target (Memory := ExactMemory A strategy) A strategy
                input)) input

/-- Mirrored validity of the two outgoing left-owner fibre members. -/
theorem ExactLeftBoundaryOperationalAt.ownerFibreReceive_valid
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data)
    (oldState : ExactBankControl A strategy)
    (oldOwner : (data.2.2.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.leftBoundaryOwnerFibreReceive A strategy hwin data oldState oldOwner
        input
    ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy
        result.1.openControl ∧
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy
        result.1.closedControl := by
  rcases hoperational with
    ⟨_currentCode, _root, past, _hexact, _hcode, _hroot, _hmove,
      howner, _hreceiver⟩
  have hreachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A
        (data.receiver (Memory := ExactMemory A strategy) A strategy).1
        (data.owner (Memory := ExactMemory A strategy) A strategy) :=
    ⟨senderWord past, howner⟩
  simpa only [
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftBoundaryOwnerFibreReceive]
    using
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork_valid
        (Memory := ExactMemory A strategy) A strategy
          ⟨(data.receiver (Memory := ExactMemory A strategy) A strategy).1,
            data.owner (Memory := ExactMemory A strategy) A strategy⟩
          hreachable oldState data.2.2 oldOwner
          (((exactEffectTable A strategy hwin key).family A strategy key
            ).resolvePacket A strategy hwin data.1
              (data.target (Memory := ExactMemory A strategy) A strategy
                input)) (input.2, input.1)

def ExactRightBoundaryReadyAt
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ∀ input : In₁ × In₂,
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let target := (((receiver.1.memberController A false).labelOf
      (data.owner (Memory := ExactMemory A strategy) A strategy)).2
        receiver.2.2.1 (input.2, input.1) |>.target receiver.2.1)
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    tables.ChildRealizes A strategy hwin data.1 target
        (tables.resolveTarget A strategy hwin data.1 target) ∧
      ∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointOneSidedCurrentSlots A .left target () = some root

def ExactLeftBoundaryReadyAt
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ∀ input : In₁ × In₂,
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let target := (((receiver.1.memberController A false).labelOf
      (data.owner (Memory := ExactMemory A strategy) A strategy)).2
        receiver.2.2.1 input |>.target receiver.2.1)
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    tables.ChildRealizes A strategy hwin data.1 target
        (tables.resolveTarget A strategy hwin data.1 target) ∧
      ∃ root : ProfiledRawJointThreadRoot A,
        profiledRawJointOneSidedCurrentSlots A .right target () = some root

/-- Matched physical owner/receiver prefixes make every right-oriented
resolver query a genuine exact semantic edge with a live crossed slot. -/
theorem ExactRightBoundaryOperationalAt.ready
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data) :
    ExactRightBoundaryReadyAt A strategy hwin key data := by
  rcases data with ⟨⟨stateKey, state⟩,
    ⟨⟨move, row, receiverState, lastTarget⟩, owner⟩, oldReceiver⟩
  dsimp only [ExactRightBoundaryOperationalAt,
    ExactRightBoundaryReadyAt,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner]
    at hoperational ⊢
  rcases hoperational with
    ⟨currentCode, root, past, hexact, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  rcases hexact with ⟨hkey, haligned⟩
  change stateKey = key at hkey
  subst stateKey
  intro input
  let blockInput : In₂ × In₁ := (input.2, input.1)
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [blockInput])
  have hat := profiledRawJointRightPhysicalSibling_treePlay_at_prefix A move
    past blockInput
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hat hsafe
  rw [hat] at hsafe
  dsimp only [narrowedRecord] at hsafe
  rw [← howner, ← hreceiverState] at hsafe
  let target :=
    (((move.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1) |>.target row)
  have hrealizes :=
    (show ExactPolicyAligned A strategy key state from haligned
      ).resolveTarget_realizes_right A strategy hwin key state currentCode
        hcurrentCode root hroot move hmove target hsafe.2
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointLeftSlot_of_rightPhysicalTargetSafe A _ _ _ _
      hsafe.1
  refine ⟨hrealizes, Sum.inr slot, ?_⟩
  change Option.map Sum.inr
      (((((move.memberController A false).labelOf owner).2 receiverState
        (input.2, input.1) |>.target row).family.left ())) =
    some (Sum.inr slot)
  simpa [blockInput] using hslot

/-- Left-oriented mirror of exact operational readiness. -/
theorem ExactLeftBoundaryOperationalAt.ready
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data) :
    ExactLeftBoundaryReadyAt A strategy hwin key data := by
  rcases data with ⟨⟨stateKey, state⟩,
    ⟨⟨move, row, receiverState, lastTarget⟩, owner⟩, oldReceiver⟩
  dsimp only [ExactLeftBoundaryOperationalAt,
    ExactLeftBoundaryReadyAt,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner]
    at hoperational ⊢
  rcases hoperational with
    ⟨currentCode, root, past, hexact, hcurrentCode, hroot, hmove,
      howner, hreceiverState⟩
  rcases hexact with ⟨hkey, haligned⟩
  change stateKey = key at hkey
  subst stateKey
  intro input
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [input])
  have hat := profiledRawJointLeftPhysicalSibling_treePlay_at_prefix A move
    past input
  have hsafe := move.memberController_targetSafe A false env past.length row
  dsimp only at hat hsafe
  rw [hat] at hsafe
  dsimp only [narrowedRecord] at hsafe
  rw [← howner, ← hreceiverState] at hsafe
  let target :=
    (((move.memberController A false).labelOf owner).2 receiverState input
      |>.target row)
  have hrealizes :=
    (show ExactPolicyAligned A strategy key state from haligned
      ).resolveTarget_realizes_left A strategy hwin key state currentCode
        hcurrentCode root hroot move hmove target hsafe.2
  obtain ⟨slot, hslot⟩ :=
    exists_profiledRawJointRightSlot_of_leftPhysicalTargetSafe A _ _ _ _
      hsafe.1
  refine ⟨hrealizes, Sum.inl slot, ?_⟩
  change Option.map Sum.inl
      (((((move.memberController A false).labelOf owner).2 receiverState input
        |>.target row).family.right ())) = some (Sum.inl slot)
  simpa using hslot

/-- The exact packet selected from an operational right boundary contains the
left move required by the next decoder configuration. -/
theorem ExactRightBoundaryOperationalAt.resolvePacket_leftMove_exists
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.1.2.2 = some move := by
  dsimp only
  obtain ⟨hrealizes, root, hroot⟩ :=
    hoperational.ready A strategy hwin key data input
  exact childRealizes_resolvePacket_leftMove_exists
    (Memory := ExactMemory A strategy) A strategy hwin
      ((exactEffectTable A strategy hwin key).family A strategy key) data.1
        (data.target (Memory := ExactMemory A strategy) A strategy input)
          hrealizes root hroot

/-- Mirrored concrete packet equation for an operational left boundary. -/
theorem ExactLeftBoundaryOperationalAt.resolvePacket_rightMove_exists
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.1.2.1 = some move := by
  dsimp only
  obtain ⟨hrealizes, root, hroot⟩ :=
    hoperational.ready A strategy hwin key data input
  exact childRealizes_resolvePacket_rightMove_exists
    (Memory := ExactMemory A strategy) A strategy hwin
      ((exactEffectTable A strategy hwin key).family A strategy key) data.1
        (data.target (Memory := ExactMemory A strategy) A strategy input)
          hrealizes root hroot

/-- The public incidence code of a packet selected from an operational right
boundary is the requested target code. -/
theorem ExactRightBoundaryOperationalAt.resolvePacket_code_eq_target
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    packet.successor.2.1.1.1 = target := by
  dsimp only
  obtain ⟨hrealizes, _root, _hroot⟩ :=
    hoperational.ready A strategy hwin key data input
  rcases hrealizes with
    ⟨_move, _source, _actual, _hsourceCode, _hsourceMove,
      _hcompatible, _hchildren, _hchildCode, hbare, hsuccessor⟩
  exact (congrArg (fun publicState ↦ publicState.1.1) hsuccessor).trans
    hbare

/-- Mirrored packet-code identity. -/
theorem ExactLeftBoundaryOperationalAt.resolvePacket_code_eq_target
    (key : RootKey A strategy)
    (data : ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
      (Memory := ExactMemory A strategy) A strategy)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    packet.successor.2.1.1.1 = target := by
  dsimp only
  obtain ⟨hrealizes, _root, _hroot⟩ :=
    hoperational.ready A strategy hwin key data input
  rcases hrealizes with
    ⟨_move, _source, _actual, _hsourceCode, _hsourceMove,
      _hcompatible, _hchildren, _hchildCode, hbare, hsuccessor⟩
  exact (congrArg (fun publicState ↦ publicState.1.1) hsuccessor).trans
    hbare

/-! ### Simultaneous-close decoder seam -/

/-- Semantic phase reconstructed from the closed members of a right-live
receive.  The new left boundary is rooted at the exact packet successor; the
advanced right owner fibre supplies the coherent dormant right pair. -/
noncomputable def ExactRightPhaseAfterBoth
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
      (Memory := ExactMemory A strategy) A strategy :=
  let data := phaseData.1
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let advancedOwner : ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨receiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A receiver.1
        false (data.owner (Memory := ExactMemory A strategy) A strategy)
          input.1).2⟩
  let fibre := profiledRawJointRightOwnerFibreControlOfOwner A advancedOwner
  let target := data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin data.1 target
  let steppedReceiver :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
      (data.owner (Memory := ExactMemory A strategy) A strategy) receiver.2.1
        receiver.2.2.1 (input.2, input.1)).2
  let active :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both,
        (move.memberController A false).initial⟩,
      fibre.finiteMemoryReceiverAt A steppedReceiver)
  ⟨active, data.1, fibre.2.1⟩

/-- Mirrored phase reconstructed after closing a left-live receive. -/
noncomputable def ExactLeftPhaseAfterBoth
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A) :
    ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
      (Memory := ExactMemory A strategy) A strategy :=
  let data := phaseData.1
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let advancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨receiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A receiver.1 false
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.2).2⟩
  let fibre := profiledRawJointLeftOwnerFibreControlOfOwner A advancedOwner
  let target := data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin data.1 target
  let steppedReceiver :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
      (data.owner (Memory := ExactMemory A strategy) A strategy) receiver.2.1
        receiver.2.2.1 input).2
  let active :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move .both,
        (move.memberController A false).initial⟩,
      fibre.finiteMemoryReceiverAt A steppedReceiver)
  ⟨active, data.1, fibre.2.1⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The two closed controls produced from a right-live exact phase decode as
the advertised left-live phase.  This theorem closes the dependent decoder
seam: the proof uses the actual move stored in the exact packet successor,
not a default or an independently chosen move. -/
theorem exactRightPhaseOwnerFibreClose_decodes_left
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (move : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      let data := phaseData.1
      let target := data.target (Memory := ExactMemory A strategy) A strategy
        input
      let packet := (exactEffectTable A strategy hwin key).family A strategy
        key |>.resolvePacket A strategy hwin data.1 target
      packet.successor.2.1.1.2.2 = some move) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.rightPhaseOwnerFibreReceive A strategy hwin phaseData input
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := ExactMemory A strategy) A strategy
        result.1.1.closedControl result.2.1.closedControl =
      some (ExactRightPhaseAfterBoth A strategy hwin key phaseData input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨rightMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨leftMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((rightMove.memberController A false).labelOf owner).2 receiverState
      (input.2, input.1)).target row)
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin state target
  have hmove' : packet.successor.2.1.1.2.2 = some move := by
    simpa only [packet, target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner] using hmove
  have hnewMove :
      packet.successor.2.1.1.2.2.getD leftMove = move := by
    simp [hmove']
  let steppedRight :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove owner row
      receiverState (input.2, input.1)).2
  let advancedRight : ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightMove,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
        owner input.1).2⟩
  let rightFibre :=
    profiledRawJointRightOwnerFibreControlOfOwner A advancedRight
  let freshLeft :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both
  let advancedOldLeft :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove oldOwner
      oldRow oldReceiverState input).2
  have hrightReceive :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor
          A strategy hwin
            ((exactEffectTable A strategy hwin key).family A strategy key)
              state ⟨rightMove, row, receiverState, lastTarget⟩ owner
                (input.2, input.1) =
        ((state, steppedRight, some packet),
          (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
            owner row receiverState (input.2, input.1)).1) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor,
      steppedRight, packet, target]
  have hdecode :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_fibreInstalled
      (Memory := ExactMemory A strategy) A strategy packet.successor freshLeft
        (move.memberController A false).initial steppedRight rightFibre
        (oldState, advancedOldLeft) (state, packet.successor)
          (state, packet.successor)
  simp only [
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightBoundaryOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
    profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftAdvanceOldReceiver,
    profiledRawJointRecurrentFiniteMemoryRightToLeftMove,
    profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork,
    profiledRawJointRecurrentFiniteMemoryRightToLeftShared,
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
    profiledRawJointRightOwnerFibreControlOfOwner,
    initialProfiledRawJointLeftPhysicalSiblingReceiver,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
    ExactRightPhaseAfterBoth, target, packet, steppedRight, advancedRight,
    rightFibre, freshLeft, advancedOldLeft, hmove', hrightReceive]
  rw [hnewMove]
  exact hdecode

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Left-live mirror of `exactRightPhaseOwnerFibreClose_decodes_left`. -/
theorem exactLeftPhaseOwnerFibreClose_decodes_right
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (move : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      let data := phaseData.1
      let target := data.target (Memory := ExactMemory A strategy) A strategy
        input
      let packet := (exactEffectTable A strategy hwin key).family A strategy
        key |>.resolvePacket A strategy hwin data.1 target
      packet.successor.2.1.1.2.1 = some move) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.leftPhaseOwnerFibreReceive A strategy hwin phaseData input
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := ExactMemory A strategy) A strategy
        result.1.1.closedControl result.2.1.closedControl =
      some (ExactLeftPhaseAfterBoth A strategy hwin key phaseData input move) := by
  rcases phaseData with ⟨data, oldState, oldOwner⟩
  rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
  rcases receiver with ⟨leftMove, row, receiverState, lastTarget⟩
  rcases oldReceiver with
    ⟨rightMove, oldRow, oldReceiverState, oldLastTarget⟩
  let target : ProfiledRawJointIncidenceCode A (I := Unit) :=
    ((((leftMove.memberController A false).labelOf owner).2 receiverState
      input).target row)
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin state target
  have hmove' : packet.successor.2.1.1.2.1 = some move := by
    simpa only [packet, target,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] using hmove
  have hnewMove :
      packet.successor.2.1.1.2.1.getD rightMove = move := by
    simp [hmove']
  let steppedLeft :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove owner row
      receiverState input).2
  let advancedLeft : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftMove,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
        owner input.2).2⟩
  let leftFibre :=
    profiledRawJointLeftOwnerFibreControlOfOwner A advancedLeft
  let freshRight :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A move .both
  let advancedOldRight :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove oldOwner
      oldRow oldReceiverState (input.2, input.1)).2
  have hleftReceive :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftReceiveFor
          A strategy hwin
            ((exactEffectTable A strategy hwin key).family A strategy key)
              state ⟨leftMove, row, receiverState, lastTarget⟩ owner input =
        ((state, steppedLeft, some packet),
          (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
            owner row receiverState input).1) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftReceiveFor,
      steppedLeft, packet, target]
  have hdecode :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedFibreClosed
      (Memory := ExactMemory A strategy) A strategy packet.successor
        freshRight (move.memberController A false).initial steppedLeft
          leftFibre (oldState, advancedOldRight) (packet.successor, state)
            (packet.successor, state)
  simp only [
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftBoundaryOwnerFibreReceive,
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
    profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork,
    profiledRawJointRecurrentFiniteMemoryLeftToRightAdvanceOldReceiver,
    profiledRawJointRecurrentFiniteMemoryLeftToRightMove,
    profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork,
    profiledRawJointRecurrentFiniteMemoryLeftToRightShared,
    FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
    profiledRawJointLeftOwnerFibreControlOfOwner,
    initialProfiledRawJointRightPhysicalSiblingReceiver,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
    ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
    ExactLeftPhaseAfterBoth, target, packet, steppedLeft, advancedLeft,
    leftFibre, freshRight, advancedOldRight, hmove', hleftReceive]
  rw [hnewMove]
  exact hdecode

/-- A simultaneous close of an operational right-live phase is again fully
operational in the left orientation.  The active half is the initial prefix
of the literal packet successor.  The dormant half is rebuilt from the fibre
of the advanced right owner, whose witness supplies a (possibly different)
matched prefix at the unchanged exact right bank cell. -/
theorem ExactRightPhaseOperationalAt.afterBoth
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hphase : ExactRightPhaseOperationalAt A strategy key phaseData)
    (input : In₁ × In₂) :
    let data := phaseData.1
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := (exactEffectTable A strategy hwin key).family A strategy key
      |>.resolvePacket A strategy hwin data.1 target
    ∃ move : ProfiledRawJointLeftPhysicalSiblingMove A,
      packet.successor.2.1.1.2.2 = some move ∧
        ExactLeftPhaseOperationalAt A strategy key
          (ExactRightPhaseAfterBoth A strategy hwin key phaseData input move) := by
  dsimp only
  have hactive := hphase.1
  obtain ⟨move, hmove⟩ :=
    hactive.resolvePacket_leftMove_exists A strategy hwin key phaseData.1
      input
  refine ⟨move, hmove, ?_⟩
  let data := phaseData.1
  let receiver :=
    data.receiver (Memory := ExactMemory A strategy) A strategy
  let target :=
    data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin data.1 target
  let steppedReceiver :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1
      (data.owner (Memory := ExactMemory A strategy) A strategy) receiver.2.1
        receiver.2.2.1 (input.2, input.1)).2
  let advancedOwner : ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨receiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A receiver.1
        false (data.owner (Memory := ExactMemory A strategy) A strategy)
          input.1).2⟩
  let fibre := profiledRawJointRightOwnerFibreControlOfOwner A advancedOwner
  have hpacketMove : packet.successor.2.1.1.2.2 = some move := by
    simpa only [packet, target, data] using hmove
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [packet, target, data] using
      hactive.resolvePacket_code_eq_target A strategy hwin key phaseData.1
        input
  obtain ⟨_hrealizes, targetRoot, htargetRoot⟩ :=
    hactive.ready A strategy hwin key phaseData.1 input
  rcases hactive with
    ⟨currentCode, currentRoot, past, hstate, hcurrentCode,
      hcurrentRoot, hstateMove, howner, _hreceiver⟩
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hstate.resolvePacket A strategy hwin key data.1 target
  have hactiveNext :
      ExactLeftBoundaryOperationalAt A strategy key
        (packet.successor,
          ⟨initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both,
            (move.memberController A false).initial⟩,
          fibre.finiteMemoryReceiverAt A steppedReceiver) := by
    exact exactLeftBoundaryOperationalAt_initial A strategy key
      packet.successor move .both
        (fibre.finiteMemoryReceiverAt A steppedReceiver) hpacketExact target
          hpacketCode targetRoot htargetRoot hpacketMove
  have hownerReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A receiver.1
        (data.owner (Memory := ExactMemory A strategy) A strategy) := by
    exact ⟨senderWord past, howner⟩
  have hadvancedReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A receiver.1
        advancedOwner.2 := by
    simpa only [advancedOwner] using
      hownerReachable.step A receiver.1
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.1
  have hfibre : ProfiledRawJointRightOwnerFibreValid A fibre := by
    simpa only [fibre, advancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        profiledRawJointRightOwnerFibreChoiceControl_valid A receiver.1
          advancedOwner.2 hadvancedReachable
  have hdormantNext :
      ExactRightBoundaryOperationalAt A strategy key
        (data.1, ⟨fibre.finiteMemoryReceiverAt A steppedReceiver,
            fibre.2.1⟩,
          initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both) := by
    apply exactRightBoundaryOperationalAt_of_fibre A strategy key data.1
      steppedReceiver fibre
        (initialProfiledRawJointLeftPhysicalSiblingReceiver A move .both)
          hstate currentCode hcurrentCode currentRoot hcurrentRoot
    · simpa only [fibre, advancedOwner,
        profiledRawJointRightOwnerFibreControlOfOwner] using hstateMove
    · exact hfibre
  simpa only [ExactLeftPhaseOperationalAt, ExactRightPhaseAfterBoth,
    ExactLeftPhaseDormantRightData, data, receiver, target, packet,
    steppedReceiver, advancedOwner, fibre] using
      And.intro hactiveNext hdormantNext

/-- Mirrored simultaneous-close operational preservation. -/
theorem ExactLeftPhaseOperationalAt.afterBoth
    (key : RootKey A strategy)
    (phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hphase : ExactLeftPhaseOperationalAt A strategy key phaseData)
    (input : In₁ × In₂) :
    let data := phaseData.1
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := (exactEffectTable A strategy hwin key).family A strategy key
      |>.resolvePacket A strategy hwin data.1 target
    ∃ move : ProfiledRawJointRightPhysicalSiblingMove A,
      packet.successor.2.1.1.2.1 = some move ∧
        ExactRightPhaseOperationalAt A strategy key
          (ExactLeftPhaseAfterBoth A strategy hwin key phaseData input move) := by
  dsimp only
  have hactive := hphase.1
  obtain ⟨move, hmove⟩ :=
    hactive.resolvePacket_rightMove_exists A strategy hwin key phaseData.1
      input
  refine ⟨move, hmove, ?_⟩
  let data := phaseData.1
  let receiver :=
    data.receiver (Memory := ExactMemory A strategy) A strategy
  let target :=
    data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := (exactEffectTable A strategy hwin key).family A strategy key
    |>.resolvePacket A strategy hwin data.1 target
  let steppedReceiver :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1
      (data.owner (Memory := ExactMemory A strategy) A strategy) receiver.2.1
        receiver.2.2.1 input).2
  let advancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨receiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A receiver.1 false
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.2).2⟩
  let fibre := profiledRawJointLeftOwnerFibreControlOfOwner A advancedOwner
  have hpacketMove : packet.successor.2.1.1.2.1 = some move := by
    simpa only [packet, target, data] using hmove
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [packet, target, data] using
      hactive.resolvePacket_code_eq_target A strategy hwin key phaseData.1
        input
  obtain ⟨_hrealizes, targetRoot, htargetRoot⟩ :=
    hactive.ready A strategy hwin key phaseData.1 input
  rcases hactive with
    ⟨currentCode, currentRoot, past, hstate, hcurrentCode,
      hcurrentRoot, hstateMove, howner, _hreceiver⟩
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hstate.resolvePacket A strategy hwin key data.1 target
  have hactiveNext :
      ExactRightBoundaryOperationalAt A strategy key
        (packet.successor,
          ⟨initialProfiledRawJointRightPhysicalSiblingReceiver A move .both,
            (move.memberController A false).initial⟩,
          fibre.finiteMemoryReceiverAt A steppedReceiver) := by
    exact exactRightBoundaryOperationalAt_initial A strategy key
      packet.successor move .both
        (fibre.finiteMemoryReceiverAt A steppedReceiver) hpacketExact target
          hpacketCode targetRoot htargetRoot hpacketMove
  have hownerReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A receiver.1
        (data.owner (Memory := ExactMemory A strategy) A strategy) := by
    exact ⟨senderWord past, howner⟩
  have hadvancedReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A receiver.1
        advancedOwner.2 := by
    simpa only [advancedOwner] using
      hownerReachable.step A receiver.1
        (data.owner (Memory := ExactMemory A strategy) A strategy) input.2
  have hfibre : ProfiledRawJointLeftOwnerFibreValid A fibre := by
    simpa only [fibre, advancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        profiledRawJointLeftOwnerFibreChoiceControl_valid A receiver.1
          advancedOwner.2 hadvancedReachable
  have hdormantNext :
      ExactLeftBoundaryOperationalAt A strategy key
        (data.1, ⟨fibre.finiteMemoryReceiverAt A steppedReceiver,
            fibre.2.1⟩,
          initialProfiledRawJointRightPhysicalSiblingReceiver A move .both) := by
    apply exactLeftBoundaryOperationalAt_of_fibre A strategy key data.1
      steppedReceiver fibre
        (initialProfiledRawJointRightPhysicalSiblingReceiver A move .both)
          hstate currentCode hcurrentCode currentRoot hcurrentRoot
    · simpa only [fibre, advancedOwner,
        profiledRawJointLeftOwnerFibreControlOfOwner] using hstateMove
    · exact hfibre
  simpa only [ExactRightPhaseOperationalAt, ExactLeftPhaseAfterBoth,
    ExactRightPhaseDormantLeftData, data, receiver, target, packet,
    steppedReceiver, advancedOwner, fibre] using
      And.intro hactiveNext hdormantNext

/-! ### Operational selection and actual simultaneous closure -/

/-- A decoder-selected exact endpoint pair together with the operational
certificate for the selected phase.  The left constructor records rejection
by the right-priority decoder, so this proposition describes the phase that
the executable kernel will actually use. -/
inductive ExactOwnerBoundarySelectedAt
    (key : RootKey A strategy) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy →
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy → Prop
  | right {one two}
      (phaseData :
        ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
          (Memory := ExactMemory A strategy) A strategy)
      (hdata :
        profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
            (Memory := ExactMemory A strategy) A strategy one two =
          some phaseData)
      (operational : ExactRightPhaseOperationalAt A strategy key phaseData) :
      ExactOwnerBoundarySelectedAt key one two
  | left {one two}
      (phaseData :
        ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
          (Memory := ExactMemory A strategy) A strategy)
      (hright :
        profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
            (Memory := ExactMemory A strategy) A strategy one two = none)
      (hdata :
        profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := ExactMemory A strategy) A strategy one two =
          some phaseData)
      (operational : ExactLeftPhaseOperationalAt A strategy key phaseData) :
      ExactOwnerBoundarySelectedAt key one two

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Operational selection entails the public decoder obligation. -/
theorem ExactOwnerBoundarySelectedAt.decodes
    (key : RootKey A strategy)
    {one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy}
    {two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy}
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := ExactMemory A strategy) A strategy one two := by
  cases hselected with
  | right phaseData hdata operational => exact Or.inl ⟨phaseData, hdata⟩
  | left phaseData hright hdata operational =>
      exact Or.inr ⟨phaseData, hdata⟩

/-! The selected phase is not by itself inductive under a strict one-sided
round.  Such a round can expose a fibre or a staged receiver that was hidden
from the selected decoder.  The following three predicates retain exactly
the certificates needed when that happens. -/

/-- Every pending first-endpoint payload carries a valid right owner fibre. -/
def ExactOwnerBoundaryOneValid
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match one.1 with
  | .inl _ => True
  | .inr pending =>
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy pending

/-- Every pending second-endpoint payload carries a valid left owner fibre. -/
def ExactOwnerBoundaryTwoValid
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  match two.1 with
  | .inl _ => True
  | .inr pending =>
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
        (Memory := ExactMemory A strategy) A strategy pending

/-- A staged left receiver at process one is anchored at the left bank
coordinate retained by that endpoint. -/
def ExactOwnerBoundaryOneStagedAnchor
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ∀ staged, one.1 = .inl (.inl staged) → one.2.2 = staged.1

/-- Mirrored anchor for a staged right receiver at process two. -/
def ExactOwnerBoundaryTwoStagedAnchor
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ∀ staged, two.1 = .inl (.inl staged) → two.2.1 = staged.1

def ExactOwnerBoundaryStagedAnchor
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy) : Prop :=
  ExactOwnerBoundaryOneStagedAnchor A strategy one ∧
    ExactOwnerBoundaryTwoStagedAnchor A strategy two

/-- Full exact operational invariant.  `selected` controls the executable
decoder; `oneValid` and `twoValid` certify latent fibres; `stagedAnchor`
relates latent staged receivers to their bank register; and `exact` rules out
mixing bank coordinates belonging to different semantic histories. -/
structure ExactOwnerFibreBoundaryOperationalAt
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy) : Prop where
  selected : ExactOwnerBoundarySelectedAt A strategy key one two
  oneValid : ExactOwnerBoundaryOneValid A strategy one
  twoValid : ExactOwnerBoundaryTwoValid A strategy two
  stagedAnchor : ExactOwnerBoundaryStagedAnchor A strategy one two
  exact : ExactBoundaryOneAt A strategy key one ∧
    ExactBoundaryTwoAt A strategy key two

/-- An operational right boundary enters the recurrent carrier in the exact
right-oriented installed/staged shape.  Readiness of the active boundary
supplies the target root, while the literal packet move initializes the
dormant left phase at the packet successor. -/
theorem exactRightEntry_selected_of_operational
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (hoperational : ExactRightBoundaryOperationalAt A strategy key data)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hmove :
      let tables := (exactEffectTable A strategy hwin key).family A strategy key
      let target := data.target (Memory := ExactMemory A strategy) A strategy
        input
      let packet := tables.resolvePacket A strategy hwin data.1 target
      packet.successor.2.1.1.2.2 = some leftMove) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    ExactOwnerBoundarySelectedAt A strategy key
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryOne
        (Memory := ExactMemory A strategy) A strategy data.1 receiver
          (data.owner (Memory := ExactMemory A strategy) A strategy) data.2.2
            packet)
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryTwo
        (Memory := ExactMemory A strategy) A strategy data.1 receiver packet) := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let target := data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := tables.resolvePacket A strategy hwin data.1 target
  let freshLeft :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let phaseData :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(data.1,
        ⟨receiver,
          data.owner (Memory := ExactMemory A strategy) A strategy⟩,
        freshLeft),
      packet.successor, (leftMove.memberController A false).initial⟩
  have hmove' : packet.successor.2.1.1.2.2 = some leftMove := by
    simpa only [tables, target, packet] using hmove
  have hstate : ExactBankAt A strategy key data.1 := by
    rcases hoperational with
      ⟨currentCode, root, past, hstate, hcode, hroot, hstateMove,
        howner, hreceiver⟩
    exact hstate
  have hactive :
      ExactRightBoundaryOperationalAt A strategy key phaseData.1 := by
    simpa only [phaseData, freshLeft, receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner] using
        hoperational
  obtain ⟨_realizes, targetRoot, htargetRoot⟩ :=
    hoperational.ready A strategy hwin key data input
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hstate.resolvePacket A strategy hwin key data.1 target
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [tables, target, packet] using
      hoperational.resolvePacket_code_eq_target A strategy hwin key data input
  have hdormant :
      ExactLeftBoundaryOperationalAt A strategy key
        (ExactRightPhaseDormantLeftData A strategy phaseData) := by
    simpa only [ExactRightPhaseDormantLeftData, phaseData, freshLeft,
      receiver] using
        exactLeftBoundaryOperationalAt_initial A strategy key packet.successor
          leftMove .first receiver hpacketExact target hpacketCode targetRoot
            htargetRoot hmove'
  have hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryOne
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              (data.owner (Memory := ExactMemory A strategy) A strategy)
                data.2.2 packet)
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryTwo
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              packet) = some phaseData := by
    simpa only [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryOne,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryTwo,
      phaseData, freshLeft, receiver] using
        profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_entry_exact
          (Memory := ExactMemory A strategy) A strategy data.1 receiver
            (data.owner (Memory := ExactMemory A strategy) A strategy)
              data.2.2 packet leftMove hmove'
  exact .right phaseData hdecode ⟨hactive, hdormant⟩

/-- Mirrored exact entry theorem for an operational left boundary. -/
theorem exactLeftEntry_selected_of_operational
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (hoperational : ExactLeftBoundaryOperationalAt A strategy key data)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hmove :
      let tables := (exactEffectTable A strategy hwin key).family A strategy key
      let target := data.target (Memory := ExactMemory A strategy) A strategy
        input
      let packet := tables.resolvePacket A strategy hwin data.1 target
      packet.successor.2.1.1.2.1 = some rightMove) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let receiver :=
      data.receiver (Memory := ExactMemory A strategy) A strategy
    let target := data.target (Memory := ExactMemory A strategy) A strategy
      input
    let packet := tables.resolvePacket A strategy hwin data.1 target
    ExactOwnerBoundarySelectedAt A strategy key
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryOne
        (Memory := ExactMemory A strategy) A strategy data.1 receiver packet)
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryTwo
        (Memory := ExactMemory A strategy) A strategy data.1 receiver
          (data.owner (Memory := ExactMemory A strategy) A strategy) data.2.2
            packet) := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let receiver := data.receiver (Memory := ExactMemory A strategy) A strategy
  let target := data.target (Memory := ExactMemory A strategy) A strategy input
  let packet := tables.resolvePacket A strategy hwin data.1 target
  let freshRight :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let phaseData :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(data.1,
        ⟨receiver,
          data.owner (Memory := ExactMemory A strategy) A strategy⟩,
        freshRight),
      packet.successor, (rightMove.memberController A false).initial⟩
  have hmove' : packet.successor.2.1.1.2.1 = some rightMove := by
    simpa only [tables, target, packet] using hmove
  have hstate : ExactBankAt A strategy key data.1 := by
    rcases hoperational with
      ⟨currentCode, root, past, hstate, hcode, hroot, hstateMove,
        howner, hreceiver⟩
    exact hstate
  have hactive :
      ExactLeftBoundaryOperationalAt A strategy key phaseData.1 := by
    simpa only [phaseData, freshRight, receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] using
        hoperational
  obtain ⟨_realizes, targetRoot, htargetRoot⟩ :=
    hoperational.ready A strategy hwin key data input
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hstate.resolvePacket A strategy hwin key data.1 target
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [tables, target, packet] using
      hoperational.resolvePacket_code_eq_target A strategy hwin key data input
  have hdormant :
      ExactRightBoundaryOperationalAt A strategy key
        (ExactLeftPhaseDormantRightData A strategy phaseData) := by
    simpa only [ExactLeftPhaseDormantRightData, phaseData, freshRight,
      receiver] using
        exactRightBoundaryOperationalAt_initial A strategy key
          packet.successor rightMove .first receiver hpacketExact target
            hpacketCode targetRoot htargetRoot hmove'
  have hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryOne
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              packet)
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryTwo
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              (data.owner (Memory := ExactMemory A strategy) A strategy)
                data.2.2 packet) = some phaseData := by
    simpa only [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryOne,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryTwo,
      phaseData, freshRight, receiver] using
        profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_entry_exact
          (Memory := ExactMemory A strategy) A strategy data.1 receiver
            (data.owner (Memory := ExactMemory A strategy) A strategy)
              data.2.2 packet rightMove hmove'
  have hright :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryOne
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              packet)
          (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryTwo
            (Memory := ExactMemory A strategy) A strategy data.1 receiver
              (data.owner (Memory := ExactMemory A strategy) A strategy)
                data.2.2 packet) = none :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_none_of_left_some
      (Memory := ExactMemory A strategy) A strategy _ _ _ hdecode
  exact .left phaseData hright hdecode ⟨hactive, hdormant⟩

/-- The actual simultaneous-close map of the exact table preserves
operational selection and reverses the active orientation.  This combines
the exact packet readiness theorem, the two dependent decoder equations, and
decoder disjointness; it is therefore a complete executable-kernel theorem,
not merely a semantic successor construction. -/
theorem ExactOwnerBoundarySelectedAt.closeRound
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    let result :=
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo
    ExactOwnerBoundarySelectedAt A strategy key result.1.1 result.1.2 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let input : In₁ × In₂ := (inputOne, inputTwo)
  cases hselected with
  | right phaseData hdata hoperational =>
      obtain ⟨move, hmove, hnext⟩ :=
        hoperational.afterBoth A strategy hwin key phaseData input
      let receiveResult :=
        tables.rightPhaseOwnerFibreReceive A strategy hwin phaseData input
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two input =
            some receiveResult := by
        simp [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hdata, receiveResult]
      have hleft :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
              (Memory := ExactMemory A strategy) A strategy
              receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (ExactRightPhaseAfterBoth A strategy hwin key phaseData input
                move) := by
        simpa only [receiveResult, tables] using
          exactRightPhaseOwnerFibreClose_decodes_left A strategy hwin key
            phaseData input move hmove
      have hright :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
              (Memory := ExactMemory A strategy) A strategy
              receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl = none :=
        profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_none_of_left_some
          (Memory := ExactMemory A strategy) A strategy _ _ _ hleft
      have hreceive' :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) = some receiveResult := by
        simpa only [input] using hreceive
      change ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo).1.1
        (tables.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo).1.2
      rw [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive']
      exact .left
        (ExactRightPhaseAfterBoth A strategy hwin key phaseData input move)
          hright hleft hnext
  | left phaseData hright hdata hoperational =>
      obtain ⟨move, hmove, hnext⟩ :=
        hoperational.afterBoth A strategy hwin key phaseData input
      let receiveResult :=
        tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData input
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two input =
            some receiveResult := by
        simp [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hdata, receiveResult]
      have hnextDecode :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
              (Memory := ExactMemory A strategy) A strategy
              receiveResult.1.1.closedControl
              receiveResult.2.1.closedControl =
            some
              (ExactLeftPhaseAfterBoth A strategy hwin key phaseData input
                move) := by
        simpa only [receiveResult, tables] using
          exactLeftPhaseOwnerFibreClose_decodes_right A strategy hwin key
            phaseData input move hmove
      have hreceive' :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) = some receiveResult := by
        simpa only [input] using hreceive
      change ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo).1.1
        (tables.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo).1.2
      rw [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive']
      exact .right
        (ExactLeftPhaseAfterBoth A strategy hwin key phaseData input move)
          hnextDecode hnext

/-- In particular, an operationally selected pair still satisfies the
option-valued decoder after every simultaneous physical round. -/
theorem ExactOwnerBoundarySelectedAt.closeRound_decodes
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    let result :=
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := ExactMemory A strategy) A strategy result.1.1 result.1.2 := by
  exact
    (hselected.closeRound A strategy hwin key one inputOne two inputTwo
      ).decodes A strategy key

/-! ### The strict orientation-reversal test -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Same-orientation strict-right closure of an installed/staged exact entry.
The installed owner and staged receiver advance along the same physical
input, while the resolved exact child initializes the new dormant left
boundary. -/
theorem exactOwnerBoundarySelectedAt_strictRight_installedStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (oldLeftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (holdLeftMove : oldPacket.successor.2.1.1.2.2 = some oldLeftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove
              .first),
          oldPacket.successor,
          (oldLeftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := ExactMemory A strategy) A strategy one inputOne).1
        (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let oldLeftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A oldLeftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, oldLeftInitial),
      oldPacket.successor,
      (oldLeftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldLeftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate oldPacket oldLeftMove
            holdLeftMove oneCoordinates twoCoordinates
  have hcurrentOperational' :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase, oldLeftInitial] using hcurrentOperational
  refine ⟨.right currentPhase hcurrentRight hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight]
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightReceiver.1
      rightOwner rightReceiver.2.1 rightReceiver.2.2.1
        (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
      false rightOwner inputOne).2
  let target :=
    ((rightReceiver.1.memberController A false).labelOf rightOwner).2
      rightReceiver.2.2.1 (inputTwo, inputOne) |>.target rightReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin rightState target
  obtain ⟨leftMove, hleftMove⟩ :=
    hcurrentOperational'.1.resolvePacket_leftMove_exists A strategy hwin key
      currentPhase.1 (inputOne, inputTwo)
  have hleftMove' : packet.successor.2.1.1.2.2 = some leftMove := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner] using
        hleftMove
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightAdvanced, rightAdvancedOwner⟩, leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩
  have honeNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates) inputOne).1 =
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩,
                leftTemplate)),
          oneCoordinates) := by
    simp [
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne,
      profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
      rightAdvancedOwner]
  have hrightReceive :
      tables.rightReceiveFor A strategy hwin rightState rightReceiver
          rightOwner (inputTwo, inputOne) =
        ((rightState, rightAdvanced, some packet),
          (stepProfiledRawJointRightPhysicalSiblingReceiverFor A
            rightReceiver.1 rightOwner rightReceiver.2.1
              rightReceiver.2.2.1 (inputTwo, inputOne)).1) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor,
      rightAdvanced, packet, target]
  have htwoNext :
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
      hreceive]
    simp only [currentPhase,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      rightAdvanced, target, packet, hrightReceive, hleftMove']
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightAdvancedOwner⟩,
                leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) = some nextPhase := by
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightAdvanced rightAdvancedOwner leftTemplate packet leftMove
            hleftMove' oneCoordinates (rightState, packet.successor)

  have hactiveStepped :=
    hcurrentOperational'.1.step A strategy key currentPhase.1
      (inputOne, inputTwo)
  have hactiveNext :
      ExactRightBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [ExactRightBoundaryOperationalAt, nextPhase, currentPhase,
      oldLeftInitial, leftInitial,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      rightAdvanced, rightAdvancedOwner] using hactiveStepped
  have hactive := hcurrentOperational'.1
  rcases hactive with
    ⟨rightCode, rightRoot, _past, hrightState, _hrightCode, _hrightRoot,
      _hrightMove, _hrightOwner, _hrightReceiver⟩
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hrightState.resolvePacket A strategy hwin key rightState target
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner] using
        hcurrentOperational'.1.resolvePacket_code_eq_target A strategy hwin
          key currentPhase.1 (inputOne, inputTwo)
  obtain ⟨_hrealizes, targetRoot, htargetRoot⟩ :=
    hcurrentOperational'.1.ready A strategy hwin key currentPhase.1
      (inputOne, inputTwo)
  have hdormantNext :
      ExactLeftBoundaryOperationalAt A strategy key
        (ExactRightPhaseDormantLeftData A strategy nextPhase) := by
    simpa only [ExactRightPhaseDormantLeftData, nextPhase, leftInitial] using
      exactLeftBoundaryOperationalAt_initial A strategy key packet.successor
        leftMove .first rightAdvanced hpacketExact target hpacketCode
          targetRoot htargetRoot hleftMove'
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Same-orientation strict-left closure of a staged/installed exact entry.
The installed left owner and staged receiver advance on the same input, and
the resolved exact child initializes the new dormant right boundary. -/
theorem exactOwnerBoundarySelectedAt_strictLeft_stagedInstalled
    (key : RootKey A strategy)
    (leftState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (oldRightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (holdRightMove : oldPacket.successor.2.1.1.2.1 = some oldRightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hcurrentOperational :
      ExactLeftPhaseOperationalAt A strategy key
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove
              .first),
          oldPacket.successor,
          (oldRightMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let oldRightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A oldRightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, oldRightInitial),
      oldPacket.successor,
      (oldRightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, oldRightInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate oldPacket oldRightMove holdRightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
  have hcurrentOperational' :
      ExactLeftPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase, oldRightInitial] using hcurrentOperational
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft
    hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.leftPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight, hcurrentLeft]
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftReceiver.1
      leftOwner leftReceiver.2.1 leftReceiver.2.2.1
        (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
      false leftOwner inputTwo).2
  let target :=
    ((leftReceiver.1.memberController A false).labelOf leftOwner).2
      leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin leftState target
  obtain ⟨rightMove, hrightMove⟩ :=
    hcurrentOperational'.1.resolvePacket_rightMove_exists A strategy hwin key
      currentPhase.1 (inputOne, inputTwo)
  have hrightMove' : packet.successor.2.1.1.2.1 = some rightMove := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] using
        hrightMove
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftAdvanced, leftAdvancedOwner⟩, rightInitial),
      packet.successor, (rightMove.memberController A false).initial⟩
  have hleftReceive :
      tables.leftReceiveFor A strategy hwin leftState leftReceiver leftOwner
          (inputOne, inputTwo) =
        ((leftState, leftAdvanced, some packet),
          (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A
            leftReceiver.1 leftOwner leftReceiver.2.1
              leftReceiver.2.2.1 (inputOne, inputTwo)).1) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftReceiveFor,
      leftAdvanced, packet, target]
  have honeNext :
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1 =
        (.inl (.inl (leftState, leftAdvanced, some packet)),
          (packet.successor, leftState)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
      hreceive]
    simp only [currentPhase,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      leftAdvanced, target, packet, hleftReceive, hrightMove']
  have htwoNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) inputTwo).1 =
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩,
                rightTemplate)),
          twoCoordinates) := by
    simp [
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
      profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
      leftAdvancedOwner]
  rw [honeNext, htwoNext]
  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftAdvanced, some packet)),
            (packet.successor, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftAdvancedOwner⟩,
                rightTemplate)),
            twoCoordinates) = some nextPhase := by
    simpa only [nextPhase, rightInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftAdvanced
          leftAdvancedOwner rightTemplate packet rightMove hrightMove'
            (packet.successor, leftState) twoCoordinates

  have hactiveStepped :=
    hcurrentOperational'.1.step A strategy key currentPhase.1
      (inputOne, inputTwo)
  have hactiveNext :
      ExactLeftBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [ExactLeftBoundaryOperationalAt, nextPhase, currentPhase,
      oldRightInitial, rightInitial,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
      leftAdvanced, leftAdvancedOwner] using hactiveStepped
  have hactive := hcurrentOperational'.1
  rcases hactive with
    ⟨leftCode, leftRoot, _past, hleftState, _hleftCode, _hleftRoot,
      _hleftMove, _hleftOwner, _hleftReceiver⟩
  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hleftState.resolvePacket A strategy hwin key leftState target
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] using
        hcurrentOperational'.1.resolvePacket_code_eq_target A strategy hwin
          key currentPhase.1 (inputOne, inputTwo)
  obtain ⟨_hrealizes, targetRoot, htargetRoot⟩ :=
    hcurrentOperational'.1.ready A strategy hwin key currentPhase.1
      (inputOne, inputTwo)
  have hdormantNext :
      ExactRightBoundaryOperationalAt A strategy key
        (ExactLeftPhaseDormantRightData A strategy nextPhase) := by
    simpa only [ExactLeftPhaseDormantRightData, nextPhase, rightInitial] using
      exactRightBoundaryOperationalAt_initial A strategy key packet.successor
        rightMove .first leftAdvanced hpacketExact target hpacketCode
          targetRoot htargetRoot hrightMove'
  exact .left nextPhase (by
    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?])
      hnextDecode ⟨hactiveNext, hdormantNext⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- Opposite-orientation strict-right closure of a staged/installed exact
entry.  The staged dormant right pair becomes installed after one matched
step, and the active left owner is retained as a freshly certified fibre. -/
theorem exactOwnerBoundarySelectedAt_strictRight_stagedInstalled
    (key : RootKey A strategy)
    (leftState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hleftCoordinate : oneCoordinates.2 = leftState)
    (hcurrentOperational :
      ExactLeftPhaseOperationalAt A strategy key
        ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
            initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
              .first),
          oldPacket.successor,
          (rightMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl (.inl (leftState, leftReceiver, some oldPacket)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := ExactMemory A strategy) A strategy one inputOne).1
        (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightInitial),
      oldPacket.successor,
      (rightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, rightInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate oldPacket rightMove hrightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
  have hcurrentOperational' :
      ExactLeftPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase, rightInitial] using hcurrentOperational
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft
    hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.leftPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight, hcurrentLeft]
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightMove
      (rightMove.memberController A false).initial rightInitial.2.1
        rightInitial.2.2.1 (inputTwo, inputOne)).2
  let rightAdvancedOwner :=
    (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightMove false
      (rightMove.memberController A false).initial inputOne).2
  let leftAdvancedOwner :
      ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let target :=
    ((leftReceiver.1.memberController A false).labelOf leftOwner).2
      leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin leftState target
  let nextRightMove := packet.successor.2.1.1.2.1.getD rightMove
  let nextNewRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A nextRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(oldPacket.successor, ⟨rightAdvanced, rightAdvancedOwner⟩,
        leftNext.finiteMemoryReceiverAt A leftReceiver),
      leftState, leftNext.2.1⟩
  have honeNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates) inputOne).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                leftReceiver)),
          oneCoordinates) := by
    simp [
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne,
      profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
      hrightMove, rightAdvancedOwner]
  have htwoNext :
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
          (oldPacket.successor, leftState)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
      hreceive]
    simp only [currentPhase, rightInitial,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftBoundaryOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentFiniteMemoryLeftToRightMove,
      profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightShared,
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      initialProfiledRawJointRightPhysicalSiblingReceiver,
      rightAdvanced, leftNext, leftAdvancedOwner, target, packet,
      nextNewRight, nextRightMove]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (oldPacket.successor, ⟨rightMove, rightAdvancedOwner⟩,
                leftReceiver)),
            oneCoordinates)
          (.inr
            (false,
              (leftNext,
                ⟨(oldPacket.successor, rightAdvanced), nextNewRight⟩), ()),
            (oldPacket.successor, leftState)) = some nextPhase := by
    simpa only [nextPhase, hleftCoordinate] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openInstalledFibre
        (Memory := ExactMemory A strategy) A strategy oldPacket.successor
          rightAdvanced rightAdvancedOwner leftReceiver leftNext nextNewRight
            oneCoordinates (oldPacket.successor, leftState)

  have hrightStepped :=
    hcurrentOperational'.2.step A strategy key
      (ExactLeftPhaseDormantRightData A strategy currentPhase)
      (inputOne, inputTwo)
  have hnextActive :
      ExactRightBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [ExactRightBoundaryOperationalAt, nextPhase, currentPhase,
      rightInitial, ExactLeftPhaseDormantRightData,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      initialProfiledRawJointRightPhysicalSiblingReceiver, rightAdvanced,
      rightAdvancedOwner] using hrightStepped

  have hactive := hcurrentOperational'.1
  rcases hactive with
    ⟨leftCode, leftRoot, past, hleftState, hleftCode, hleftRoot,
      hleftMove, hleftOwner, _hleftReceiver⟩
  have hleftOwnerReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A leftReceiver.1
        leftOwner := by
    exact ⟨senderWord past, hleftOwner⟩
  have hleftAdvancedReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A leftReceiver.1
        leftAdvancedOwner.2 := by
    simpa only [leftAdvancedOwner] using
      hleftOwnerReachable.step A leftReceiver.1 leftOwner inputTwo
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        profiledRawJointLeftOwnerFibreChoiceControl_valid A leftReceiver.1
          leftAdvancedOwner.2 hleftAdvancedReachable
  have hleftNextMove : leftState.2.1.1.2.2 = some leftNext.1 := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using hleftMove
  have hnextDormant :
      ExactLeftBoundaryOperationalAt A strategy key
        (ExactRightPhaseDormantLeftData A strategy nextPhase) := by
    simpa only [ExactRightPhaseDormantLeftData, nextPhase] using
      exactLeftBoundaryOperationalAt_of_fibre A strategy key leftState
        leftReceiver leftNext rightAdvanced hleftState leftCode hleftCode
          leftRoot hleftRoot hleftNextMove hleftNext
  exact .right nextPhase hnextDecode ⟨hnextActive, hnextDormant⟩

/-- The strict-right reversal closes for exact memory.
A left-oriented fibre/installed state advances the right fibre without a
receive and lets process two receive through the installed left owner.  The
actual table transition yields two pending controls with opposite member
bits; their selected right phase is operational on both orientations.

Each successor is certified by its own fibre; the proof does not identify
an owner with its successor. -/
theorem exactOwnerBoundarySelectedAt_strictRight_fibreInstalled_switch
    (key : RootKey A strategy)
    (leftState rightState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (hactive :
      ExactLeftBoundaryOperationalAt A strategy key
        (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate))
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hrightState : ExactBankAt A strategy key rightState)
    (rightCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hrightCode : rightState.2.1.1.1 = rightCode)
    (rightRoot : ProfiledRawJointThreadRoot A)
    (hrightRoot :
      profiledRawJointOneSidedCurrentSlots A .right rightCode () =
        some rightRoot)
    (hrightMove : rightState.2.1.1.2.1 = some rightFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let coordinates :
        ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
          (Memory := ExactMemory A strategy) A strategy :=
      (rightState, leftState)
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := ExactMemory A strategy) A strategy :=
      (true,
        (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ())
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inr pendingOne, coordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
        coordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := ExactMemory A strategy) A strategy one inputOne).1
        (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩,
        rightFibre.finiteMemoryReceiverAt A rightTemplate),
      rightState, rightFibre.2.1⟩
  have hcurrentLeft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState)) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_fibreInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate rightFibre oldLeft (rightState, leftState)
            (rightState, leftState)
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState)) = none := by
    exact
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_reject_fibreInstalled
        (Memory := ExactMemory A strategy) A strategy
          (true,
            (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ())
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)
          (rightState, leftState) (rightState, leftState)
  have hdormant :
      ExactRightBoundaryOperationalAt A strategy key
        (rightState,
          ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
            rightFibre.2.1⟩,
          leftReceiver) := by
    exact exactRightBoundaryOperationalAt_of_fibre A strategy key rightState
      rightTemplate rightFibre leftReceiver hrightState rightCode hrightCode
        rightRoot hrightRoot hrightMove hrightFibre
  have hcurrentOperational :
      ExactLeftPhaseOperationalAt A strategy key currentPhase := by
    simpa only [ExactLeftPhaseOperationalAt,
      ExactLeftPhaseDormantRightData, currentPhase] using
        And.intro hactive hdormant
  refine ⟨.left currentPhase hcurrentRight hcurrentLeft hcurrentOperational, ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            (rightState, leftState))
          (inputOne, inputTwo) =
        some (tables.leftPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight, hcurrentLeft]

  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let leftAdvancedOwner : ProfiledRawJointLeftPhysicalSiblingExceptional A :=
    ⟨leftReceiver.1,
      (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftReceiver.1
        false leftOwner inputTwo).2⟩
  let leftNext :=
    profiledRawJointLeftOwnerFibreControlOfOwner A leftAdvancedOwner
  let target :=
    ((leftReceiver.1.memberController A false).labelOf leftOwner).2
      leftReceiver.2.2.1 (inputOne, inputTwo) |>.target leftReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin leftState target
  let newRightMove :=
    packet.successor.2.1.1.2.1.getD rightFibre.1
  let newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      initialProfiledRawJointRightPhysicalSiblingReceiver A newRightMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightNext.finiteMemoryReceiverAt A rightAdvanced, rightNext.2.1⟩,
        leftNext.finiteMemoryReceiverAt A leftReceiver),
      leftState, leftNext.2.1⟩

  have honeNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState)) inputOne).1 =
        (.inr
            (true,
              (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          (rightState, leftState)) := by
    rfl
  have htwoNext :
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          (rightState, leftState)) inputTwo
        (.inr
            (true,
              (rightFibre, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
          (rightState, leftState)) inputOne).1 =
        (.inr
            (false,
              (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
          (rightState, leftState)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
      hreceive]
    simp only [currentPhase,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftBoundaryOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightPacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightAdvanceOldReceiver,
      profiledRawJointRecurrentFiniteMemoryLeftToRightMove,
      profiledRawJointRecurrentFiniteMemoryLeftToRightPendingFork,
      profiledRawJointRecurrentFiniteMemoryLeftToRightShared,
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      leftNext, leftAdvancedOwner, rightAdvanced, target, packet, newRight,
      newRightMove]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
              (true,
                (rightNext, ⟨oldLeft, (leftState, leftReceiver)⟩), ()),
            (rightState, leftState))
          (.inr
              (false,
                (leftNext, ⟨(rightState, rightAdvanced), newRight⟩), ()),
            (rightState, leftState)) =
        some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreFibre
        (Memory := ExactMemory A strategy) A strategy rightState leftState
          rightAdvanced leftReceiver rightNext leftNext oldLeft newRight
            (rightState, leftState) (rightState, leftState)

  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    exact ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre
      hrightFibre inputOne
  have hactiveCopy := hactive
  rcases hactiveCopy with
    ⟨leftCode, leftRoot, past, hleftState, hleftCode, hleftRoot,
      hleftMove, hleftOwner, _hleftReceiver⟩
  have hleftOwnerReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A leftReceiver.1
        leftOwner := by
    exact ⟨senderWord past, hleftOwner⟩
  have hleftAdvancedReachable :
      ProfiledRawJointLeftPhysicalSiblingOwnerReachable A leftReceiver.1
        leftAdvancedOwner.2 := by
    simpa only [leftAdvancedOwner] using
      hleftOwnerReachable.step A leftReceiver.1 leftOwner inputTwo
  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    simpa only [leftNext, leftAdvancedOwner,
      profiledRawJointLeftOwnerFibreControlOfOwner] using
        profiledRawJointLeftOwnerFibreChoiceControl_valid A leftReceiver.1
          leftAdvancedOwner.2 hleftAdvancedReachable
  have hnextActive :
      ExactRightBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [nextPhase] using
      exactRightBoundaryOperationalAt_of_fibre A strategy key rightState
        rightAdvanced rightNext
          (leftNext.finiteMemoryReceiverAt A leftReceiver) hrightState
            rightCode hrightCode rightRoot hrightRoot (by
              simpa only [rightNext] using hrightMove) hrightNext
  have hnextDormant :
      ExactLeftBoundaryOperationalAt A strategy key
        (ExactRightPhaseDormantLeftData A strategy nextPhase) := by
    simpa only [ExactRightPhaseDormantLeftData, nextPhase] using
      exactLeftBoundaryOperationalAt_of_fibre A strategy key leftState
        leftReceiver leftNext
          (rightNext.finiteMemoryReceiverAt A rightAdvanced) hleftState
            leftCode hleftCode leftRoot hleftRoot (by
              simpa only [leftNext, leftAdvancedOwner,
                profiledRawJointLeftOwnerFibreControlOfOwner] using hleftMove)
              hleftNext
  have hnextOperational :
      ExactRightPhaseOperationalAt A strategy key nextPhase :=
    ⟨hnextActive, hnextDormant⟩
  exact .right nextPhase hnextDecode hnextOperational

/-- Mirrored strict-left reversal.  An installed right boundary and a
delivered left fibre become an operational left deferred/deferred phase under
the literal exact-table transition. -/
theorem exactOwnerBoundarySelectedAt_strictLeft_installedFibre_switch
    (key : RootKey A strategy)
    (rightState leftState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (oldRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (hactive :
      ExactRightBoundaryOperationalAt A strategy key
        (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate))
    (hleftFibre : ProfiledRawJointLeftOwnerFibreValid A leftFibre)
    (hleftState : ExactBankAt A strategy key leftState)
    (leftCode : ProfiledRawJointIncidenceCode A (I := Unit))
    (hleftCode : leftState.2.1.1.1 = leftCode)
    (leftRoot : ProfiledRawJointThreadRoot A)
    (hleftRoot :
      profiledRawJointOneSidedCurrentSlots A .left leftCode () =
        some leftRoot)
    (hleftMove : leftState.2.1.1.2.2 = some leftFibre.1)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let coordinates :
        ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
          (Memory := ExactMemory A strategy) A strategy :=
      (rightState, leftState)
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := ExactMemory A strategy) A strategy :=
      (true,
        (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ())
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        coordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inr pendingTwo, coordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
        leftFibre.finiteMemoryReceiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            (rightState, leftState))
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedFibreClosed
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate leftFibre oldRight
            (rightState, leftState) (rightState, leftState)
  have hdormant :
      ExactLeftBoundaryOperationalAt A strategy key
        (leftState,
          ⟨leftFibre.finiteMemoryReceiverAt A leftTemplate,
            leftFibre.2.1⟩,
          rightReceiver) := by
    exact exactLeftBoundaryOperationalAt_of_fibre A strategy key leftState
      leftTemplate leftFibre rightReceiver hleftState leftCode hleftCode
        leftRoot hleftRoot hleftMove hleftFibre
  have hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    simpa only [ExactRightPhaseOperationalAt,
      ExactRightPhaseDormantLeftData, currentPhase] using
        And.intro hactive hdormant
  refine ⟨.right currentPhase hcurrentRight hcurrentOperational, ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            (rightState, leftState))
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState))
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight]

  let leftNext :=
    (profiledRawJointLeftOwnerFibreNoRecv A leftFibre inputTwo).1
  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftFibre.1
      leftFibre.2.1 leftTemplate.2.1 leftFibre.2.2
        (inputOne, inputTwo)).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightReceiver.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightReceiver.1
        false rightOwner inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let target :=
    ((rightReceiver.1.memberController A false).labelOf rightOwner).2
      rightReceiver.2.2.1 (inputTwo, inputOne) |>.target rightReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin rightState target
  let newLeftMove := packet.successor.2.1.1.2.2.getD leftFibre.1
  let newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A newLeftMove .both)
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState,
        ⟨leftNext.finiteMemoryReceiverAt A leftAdvanced, leftNext.2.1⟩,
        rightNext.finiteMemoryReceiverAt A rightReceiver),
      rightState, rightNext.2.1⟩

  have honeNext :
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          (rightState, leftState)) inputOne
        (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          (rightState, leftState)) inputTwo).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
          (rightState, leftState)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
      hreceive]
    simp only [currentPhase,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightBoundaryOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentFiniteMemoryRightToLeftMove,
      profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftShared,
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointLeftOwnerFibreControl.finiteMemoryReceiverAt,
      rightNext, rightAdvancedOwner, leftAdvanced, target, packet, newLeft,
      newLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inr
            (true,
              (leftFibre, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) inputTwo).1 =
        (.inr
            (true,
              (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
          (rightState, leftState)) := by
    rfl
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
              (false,
                (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
              (true,
                (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) =
        some nextPhase := by
    simpa only [nextPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_fibreFibre
        (Memory := ExactMemory A strategy) A strategy rightState leftState
          rightReceiver leftAdvanced rightNext leftNext newLeft oldRight
            (rightState, leftState) (rightState, leftState)
  have hnextRightReject :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
              (false,
                (rightNext, ⟨(leftState, leftAdvanced), newLeft⟩), ()),
            (rightState, leftState))
          (.inr
              (true,
                (leftNext, ⟨oldRight, (rightState, rightReceiver)⟩), ()),
            (rightState, leftState)) = none :=
    profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_none_of_left_some
      (Memory := ExactMemory A strategy) A strategy _ _ _ hnextDecode

  have hleftNext : ProfiledRawJointLeftOwnerFibreValid A leftNext := by
    exact ProfiledRawJointLeftOwnerFibreValid.noRecv A leftFibre hleftFibre
      inputTwo
  have hactiveCopy := hactive
  rcases hactiveCopy with
    ⟨rightCode, rightRoot, past, hrightState, hrightCode, hrightRoot,
      hrightMove, hrightOwner, _hrightReceiver⟩
  have hrightOwnerReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A rightReceiver.1
        rightOwner := by
    exact ⟨senderWord past, hrightOwner⟩
  have hrightAdvancedReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A rightReceiver.1
        rightAdvancedOwner.2 := by
    simpa only [rightAdvancedOwner] using
      hrightOwnerReachable.step A rightReceiver.1 rightOwner inputOne
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        profiledRawJointRightOwnerFibreChoiceControl_valid A rightReceiver.1
          rightAdvancedOwner.2 hrightAdvancedReachable
  have hnextActive :
      ExactLeftBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [nextPhase] using
      exactLeftBoundaryOperationalAt_of_fibre A strategy key leftState
        leftAdvanced leftNext
          (rightNext.finiteMemoryReceiverAt A rightReceiver) hleftState
            leftCode hleftCode leftRoot hleftRoot (by
              simpa only [leftNext] using hleftMove) hleftNext
  have hnextDormant :
      ExactRightBoundaryOperationalAt A strategy key
        (ExactLeftPhaseDormantRightData A strategy nextPhase) := by
    simpa only [ExactLeftPhaseDormantRightData, nextPhase] using
      exactRightBoundaryOperationalAt_of_fibre A strategy key rightState
        rightReceiver rightNext
          (leftNext.finiteMemoryReceiverAt A leftAdvanced) hrightState
            rightCode hrightCode rightRoot hrightRoot (by
              simpa only [rightNext, rightAdvancedOwner,
                profiledRawJointRightOwnerFibreControlOfOwner] using
                  hrightMove) hrightNext
  have hnextOperational :
      ExactLeftPhaseOperationalAt A strategy key nextPhase :=
    ⟨hnextActive, hnextDormant⟩
  exact .left nextPhase hnextRightReject hnextDecode hnextOperational

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The hard continuation of the reachable equal-bit state is closed by the
exact table.  From `(false,false)`, a strict-right round advances the right
fibre blindly and stages the packet emitted by the informed right receiver.
Exact readiness supplies the literal left move in that packet, so the
fibre/staged decoder reconstructs an operational right phase. -/
theorem exactOwnerBoundarySelectedAt_strictRight_openOpen_fibreStaged
    (key : RootKey A strategy)
    (rightState leftState : ExactBankControl A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre)
    (hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
              rightFibre.2.1⟩,
            leftFibre.finiteMemoryReceiverAt A leftTemplate),
          leftState, leftFibre.2.1⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let pendingOne :
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
          (Memory := ExactMemory A strategy) A strategy :=
      (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ())
    let pendingTwo :
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
          (Memory := ExactMemory A strategy) A strategy :=
      (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ())
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inr pendingOne, oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inr pendingTwo, twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := ExactMemory A strategy) A strategy one inputOne).1
        (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
          rightFibre.2.1⟩,
        leftFibre.finiteMemoryReceiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openOpen
        (Memory := ExactMemory A strategy) A strategy rightState leftState
          rightTemplate leftTemplate rightFibre leftFibre newLeft newRight
            oneCoordinates twoCoordinates
  have hcurrentOperational' :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase] using hcurrentOperational
  refine ⟨.right currentPhase hcurrentRight hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight]

  let rightNext :=
    (profiledRawJointRightOwnerFibreNoRecv A rightFibre inputOne).1
  let rightAdvanced :=
    (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
      rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
        (inputTwo, inputOne)).2
  let target :=
    ((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
      rightFibre.2.2 (inputTwo, inputOne) |>.target rightTemplate.2.1
  let packet := tables.resolvePacket A strategy hwin rightState target
  obtain ⟨leftMove, hpacketMove, _⟩ :=
    hcurrentOperational'.afterBoth A strategy hwin key currentPhase
      (inputOne, inputTwo)
  have hpacketMove' : packet.successor.2.1.1.2.2 = some leftMove := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt] using
        hpacketMove
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightNext.finiteMemoryReceiverAt A rightAdvanced, rightNext.2.1⟩,
        leftInitial),
      packet.successor, (leftMove.memberController A false).initial⟩

  have honeNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates) inputOne).1 =
        (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) := by
    rfl
  have hrightReceive :
      tables.rightReceiveFor A strategy hwin rightState
          (rightFibre.finiteMemoryReceiverAt A rightTemplate) rightFibre.2.1
            (inputTwo, inputOne) =
        ((rightState, rightAdvanced, some packet),
          (stepProfiledRawJointRightPhysicalSiblingReceiverFor A rightFibre.1
            rightFibre.2.1 rightTemplate.2.1 rightFibre.2.2
              (inputTwo, inputOne)).1) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      rightAdvanced, packet, target]
  simp only [ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt]
    at hrightReceive
  have htwoNext :
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) inputOne).1 =
        (.inl (.inl (rightState, rightAdvanced, some packet)),
          (rightState, packet.successor)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
      hreceive]
    simp only [currentPhase,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      rightAdvanced, target, packet, hrightReceive, hpacketMove']
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightNext, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightAdvanced, some packet)),
            (rightState, packet.successor)) =
        some nextPhase := by
    simpa only [nextPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightAdvanced rightNext (leftState, leftTemplate) newLeft packet
            leftMove hpacketMove' oneCoordinates
              (rightState, packet.successor)

  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    exact ProfiledRawJointRightOwnerFibreValid.noRecv A rightFibre hrightFibre
      inputOne
  have hactive := hcurrentOperational'.1
  rcases hactive with
    ⟨rightCode, rightRoot, past, hrightState, hrightCode, hrightRoot,
      hrightMove, _hrightOwner, _hrightReceiver⟩
  have hrightNextMove :
      rightState.2.1.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, profiledRawJointRightOwnerFibreNoRecv] using
      hrightMove
  have hactiveNext :
      ExactRightBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [nextPhase] using
      exactRightBoundaryOperationalAt_of_fibre A strategy key rightState
        rightAdvanced rightNext leftInitial hrightState rightCode hrightCode
          rightRoot hrightRoot hrightNextMove hrightNext

  have hpacketExact : ExactBankAt A strategy key packet.successor := by
    exact hrightState.resolvePacket A strategy hwin key rightState target
  have hpacketCode : packet.successor.2.1.1.1 = target := by
    simpa only [packet, target, currentPhase,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt] using
        hcurrentOperational'.1.resolvePacket_code_eq_target A strategy hwin
          key currentPhase.1 (inputOne, inputTwo)
  obtain ⟨_hrealizes, targetRoot, htargetRoot⟩ :=
    hcurrentOperational'.1.ready A strategy hwin key currentPhase.1
      (inputOne, inputTwo)
  have hdormantNext :
      ExactLeftBoundaryOperationalAt A strategy key
        (ExactRightPhaseDormantLeftData A strategy nextPhase) := by
    simpa only [ExactRightPhaseDormantLeftData, nextPhase, leftInitial] using
      exactLeftBoundaryOperationalAt_initial A strategy key packet.successor
        leftMove .first
          (rightNext.finiteMemoryReceiverAt A rightAdvanced) hpacketExact
            target hpacketCode targetRoot htargetRoot hpacketMove'
  exact .right nextPhase hnextDecode ⟨hactiveNext, hdormantNext⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The reverse hard handoff from the reachable fibre/staged state.  A
strict-left round advances the dormant left owner and receiver along one
common input prefix, installs that owner at process two, and replaces the
active right owner by its freshly certified fibre.  The resulting
fibre/installed state decodes as an operational left phase. -/
theorem exactOwnerBoundarySelectedAt_strictLeft_fibreStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (oldPacket : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key
        ⟨(rightState,
            ⟨rightFibre.finiteMemoryReceiverAt A rightReceiver,
              rightFibre.2.1⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          oldPacket.successor,
          (leftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightFibre.finiteMemoryReceiverAt A rightReceiver,
          rightFibre.2.1⟩,
        leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightFibre oldLeft newLeft oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hcurrentOperational' :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase, leftInitial] using hcurrentOperational
  refine ⟨.right currentPhase hcurrentRight hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight]

  let leftAdvanced :=
    (stepProfiledRawJointLeftPhysicalSiblingReceiverFor A leftMove
      (leftMove.memberController A false).initial leftInitial.2.1
        leftInitial.2.2.1 (inputOne, inputTwo)).2
  let leftAdvancedOwner :=
    (profiledRawJointLeftPhysicalSiblingMemberNoRecvStep A leftMove false
      (leftMove.memberController A false).initial inputTwo).2
  let rightAdvancedOwner :
      ProfiledRawJointRightPhysicalSiblingExceptional A :=
    ⟨rightFibre.1,
      (profiledRawJointRightPhysicalSiblingMemberNoRecvStep A rightFibre.1
        false rightFibre.2.1 inputOne).2⟩
  let rightNext :=
    profiledRawJointRightOwnerFibreControlOfOwner A rightAdvancedOwner
  let target :=
    ((rightFibre.1.memberController A false).labelOf rightFibre.2.1).2
      rightFibre.2.2 (inputTwo, inputOne) |>.target rightReceiver.2.1
  let packet := tables.resolvePacket A strategy hwin rightState target
  let nextLeftMove := packet.successor.2.1.1.2.2.getD leftMove
  let nextNewLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy :=
    (packet.successor,
      initialProfiledRawJointLeftPhysicalSiblingReceiver A nextLeftMove
        .both)
  let nextPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(oldPacket.successor, ⟨leftAdvanced, leftAdvancedOwner⟩,
        rightNext.finiteMemoryReceiverAt A rightReceiver),
      rightState, rightNext.2.1⟩

  have honeNext :
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
        (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
          (rightState, oldPacket.successor)) := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
      hreceive]
    simp only [currentPhase, leftInitial,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightBoundaryOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftPacketBoundaryFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftAdvanceOldReceiver,
      profiledRawJointRecurrentFiniteMemoryRightToLeftMove,
      profiledRawJointRecurrentFiniteMemoryRightToLeftPendingFork,
      profiledRawJointRecurrentFiniteMemoryRightToLeftShared,
      FiniteAcknowledgedDelayedCarrier.deferredMemberFork,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      initialProfiledRawJointLeftPhysicalSiblingReceiver,
      rightNext, rightAdvancedOwner, leftAdvanced, target, packet,
      nextNewLeft, nextLeftMove]
  have htwoNext :
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) inputTwo).1 =
        (.inl
            (.inr
              (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                rightReceiver)),
          twoCoordinates) := by
    simp [
      profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
      profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
      hleftMove, leftAdvancedOwner]
  rw [honeNext, htwoNext]

  have hnextDecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, oldPacket.successor))
          (.inl
              (.inr
                (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                  rightReceiver)),
            twoCoordinates) =
        some nextPhase := by
    simpa only [nextPhase, hrightCoordinate] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_openFibreInstalled
        (Memory := ExactMemory A strategy) A strategy oldPacket.successor
          leftAdvanced leftAdvancedOwner rightReceiver rightNext nextNewLeft
            (rightState, oldPacket.successor) twoCoordinates
  have hnextRightReject :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightNext,
                ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ()),
            (rightState, oldPacket.successor))
          (.inl
              (.inr
                (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
                  rightReceiver)),
            twoCoordinates) = none := by
    exact
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_reject_fibreInstalled
        (Memory := ExactMemory A strategy) A strategy
          (false,
            (rightNext,
              ⟨(oldPacket.successor, leftAdvanced), nextNewLeft⟩), ())
          (oldPacket.successor, ⟨leftMove, leftAdvancedOwner⟩,
            rightReceiver)
          (rightState, oldPacket.successor) twoCoordinates

  have hleftStepped :=
    hcurrentOperational'.2.step A strategy key
      (ExactRightPhaseDormantLeftData A strategy currentPhase)
      (inputOne, inputTwo)
  have hnextActive :
      ExactLeftBoundaryOperationalAt A strategy key nextPhase.1 := by
    simpa only [ExactLeftBoundaryOperationalAt, nextPhase, currentPhase,
      leftInitial, ExactRightPhaseDormantLeftData,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
      initialProfiledRawJointLeftPhysicalSiblingReceiver, leftAdvanced,
      leftAdvancedOwner] using hleftStepped

  have hactive := hcurrentOperational'.1
  rcases hactive with
    ⟨rightCode, rightRoot, past, hrightState, hrightCode, hrightRoot,
      hrightMove, hrightOwner, _hrightReceiver⟩
  have hrightOwnerReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A rightFibre.1
        rightFibre.2.1 := by
    exact ⟨senderWord past, hrightOwner⟩
  have hrightAdvancedReachable :
      ProfiledRawJointRightPhysicalSiblingOwnerReachable A rightFibre.1
        rightAdvancedOwner.2 := by
    simpa only [rightAdvancedOwner] using
      hrightOwnerReachable.step A rightFibre.1 rightFibre.2.1 inputOne
  have hrightNext : ProfiledRawJointRightOwnerFibreValid A rightNext := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using
        profiledRawJointRightOwnerFibreChoiceControl_valid A rightFibre.1
          rightAdvancedOwner.2 hrightAdvancedReachable
  have hrightNextMove : rightState.2.1.1.2.1 = some rightNext.1 := by
    simpa only [rightNext, rightAdvancedOwner,
      profiledRawJointRightOwnerFibreControlOfOwner] using hrightMove
  have hnextDormant :
      ExactRightBoundaryOperationalAt A strategy key
        (ExactLeftPhaseDormantRightData A strategy nextPhase) := by
    simpa only [ExactLeftPhaseDormantRightData, nextPhase] using
      exactRightBoundaryOperationalAt_of_fibre A strategy key rightState
        rightReceiver rightNext leftAdvanced hrightState rightCode hrightCode
          rightRoot hrightRoot hrightNextMove hrightNext
  exact .left nextPhase hnextRightReject hnextDecode
    ⟨hnextActive, hnextDormant⟩

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The opposite strict exit from an installed/staged exact entry.  Its
active owner and monitor define the same right fibre used by the hard
fibre/staged theorem.  The receiver's cached last target is immaterial to
the next receive, so that theorem applies without weakening the exact
matched-history invariant. -/
theorem exactOwnerBoundarySelectedAt_strictLeft_installedStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hrightCoordinate : twoCoordinates.1 = rightState)
    (hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key
        ⟨(rightState, ⟨rightReceiver, rightOwner⟩,
            initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
              .first),
          oldPacket.successor,
          (leftMove.memberController A false).initial⟩)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let one :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
        oneCoordinates)
    let two :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy :=
      (.inl (.inl (rightState, rightReceiver, some oldPacket)),
        twoCoordinates)
    ExactOwnerBoundarySelectedAt A strategy key one two ∧
      ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hcurrentOperational' :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    simpa only [currentPhase, leftInitial] using hcurrentOperational

  let rightFibre : ProfiledRawJointRightOwnerFibreControl A :=
    ⟨rightReceiver.1, rightOwner, rightReceiver.2.2.1⟩
  let storedLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy :=
    (oldPacket.successor, leftInitial)
  let syntheticPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightFibre.finiteMemoryReceiverAt A rightReceiver,
          rightFibre.2.1⟩,
        leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hsyntheticOperational :
      ExactRightPhaseOperationalAt A strategy key syntheticPhase := by
    simpa only [syntheticPhase, rightFibre,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      ExactRightPhaseOperationalAt, ExactRightBoundaryOperationalAt,
      ExactRightPhaseDormantLeftData, ExactLeftBoundaryOperationalAt,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] using
        hcurrentOperational'
  have hbase :=
    exactOwnerBoundarySelectedAt_strictLeft_fibreStaged A strategy hwin key
      rightState rightReceiver rightFibre storedLeft storedLeft oldPacket
        leftMove hleftMove oneCoordinates twoCoordinates hrightCoordinate
          hsyntheticOperational inputOne inputTwo

  refine ⟨.right currentPhase hcurrentRight hcurrentOperational', ?_⟩

  have hreceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin currentPhase
          (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hcurrentRight]
  have hsyntheticRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr (false, (rightFibre, ⟨storedLeft, storedLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some syntheticPhase := by
    simpa only [syntheticPhase, storedLeft, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightFibre storedLeft storedLeft oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hsyntheticReceive :
      tables.ownerFibreBoundaryReceive? A strategy hwin
          (.inr (false, (rightFibre, ⟨storedLeft, storedLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates)
          (inputOne, inputTwo) =
        some (tables.rightPhaseOwnerFibreReceive A strategy hwin
          syntheticPhase (inputOne, inputTwo)) := by
    simp [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
      hsyntheticRight]
  have hopen :
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 =
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (false, (rightFibre, ⟨storedLeft, storedLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1 := by
    rw [
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
      hreceive, hsyntheticReceive]
    simp only [currentPhase, syntheticPhase, rightFibre,
      ProfiledRawJointRightOwnerFibreControl.finiteMemoryReceiverAt,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightBoundaryOwnerFibreReceive,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
      ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner]
  rw [hopen]
  exact hbase.2

/-! ### Strict-round preservation of the non-decoder fields -/

omit [Inhabited Out₂] in
theorem ExactOwnerBoundaryOneValid.noRecv
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (hvalid : ExactOwnerBoundaryOneValid A strategy one)
    (inputOne : In₁) :
    ExactOwnerBoundaryOneValid A strategy
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy one inputOne).1 := by
  rcases one with ⟨base, coordinates⟩
  cases base with
  | inl bridge => exact True.intro
  | inr pending =>
      change
        ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid
          (Memory := ExactMemory A strategy) A strategy pending at hvalid
      simpa only [ExactOwnerBoundaryOneValid,
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne]
        using hvalid.noRecv A strategy pending inputOne

omit [Inhabited Out₁] in
theorem ExactOwnerBoundaryTwoValid.noRecv
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hvalid : ExactOwnerBoundaryTwoValid A strategy two)
    (inputTwo : In₂) :
    ExactOwnerBoundaryTwoValid A strategy
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  rcases two with ⟨base, coordinates⟩
  cases base with
  | inl bridge => exact True.intro
  | inr pending =>
      change
        ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreValid
          (Memory := ExactMemory A strategy) A strategy pending at hvalid
      simpa only [ExactOwnerBoundaryTwoValid,
        profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo]
        using hvalid.noRecv A strategy pending inputTwo

/-- The receiving endpoint of a strict-right round carries a valid latent
fibre whenever its next base is pending. -/
theorem ExactOwnerBoundarySelectedAt.openRecvTwo_valid
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryTwoValid A strategy
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        hreceive]
      exact True.intro
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        hreceive]
      have hvalid := hphase.1.ownerFibreReceive_valid A strategy hwin key
        phaseData.1 phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa only [ExactOwnerBoundaryTwoValid,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive]
        using hvalid.1

/-- Strict-left mirror of `openRecvTwo_valid`. -/
theorem ExactOwnerBoundarySelectedAt.openRecvOne_valid
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryOneValid A strategy
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        hreceive]
      have hvalid := hphase.1.ownerFibreReceive_valid A strategy hwin key
        phaseData.1 phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa only [ExactOwnerBoundaryOneValid,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive]
        using hvalid.1
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        hreceive]
      exact True.intro

omit [Inhabited Out₂] in
theorem ExactOwnerBoundaryOneStagedAnchor.noRecv
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (hanchor : ExactOwnerBoundaryOneStagedAnchor A strategy one)
    (inputOne : In₁) :
    ExactOwnerBoundaryOneStagedAnchor A strategy
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy one inputOne).1 := by
  rcases one with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          have hsource : coordinates.2 = state := hanchor _ rfl
          cases packet with
          | none =>
              intro next hnext
              simp only [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne,
                profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv]
                at hnext
              cases hnext
              exact hsource
          | some packet =>
              cases hmove : packet.successor.2.1.1.2.1 with
              | none =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
                  exact hsource
              | some move =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne,
                    profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
      | inr installed =>
          intro staged hstaged
          change Sum.inl (Sum.inr _) = Sum.inl (Sum.inl staged) at hstaged
          cases hstaged
  | inr pending =>
      intro staged hstaged
      change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged

omit [Inhabited Out₁] in
theorem ExactOwnerBoundaryTwoStagedAnchor.noRecv
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hanchor : ExactOwnerBoundaryTwoStagedAnchor A strategy two)
    (inputTwo : In₂) :
    ExactOwnerBoundaryTwoStagedAnchor A strategy
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  rcases two with ⟨base, coordinates⟩
  cases base with
  | inl bridge =>
      cases bridge with
      | inl staged =>
          rcases staged with ⟨state, receiver, packet⟩
          have hsource : coordinates.1 = state := hanchor _ rfl
          cases packet with
          | none =>
              intro next hnext
              simp only [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
                profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv]
                at hnext
              cases hnext
              exact hsource
          | some packet =>
              cases hmove : packet.successor.2.1.1.2.2 with
              | none =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
                  exact hsource
              | some move =>
                  intro next hnext
                  simp only [
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo,
                    profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv,
                    hmove] at hnext
                  cases hnext
      | inr installed =>
          intro staged hstaged
          change Sum.inl (Sum.inr _) = Sum.inl (Sum.inl staged) at hstaged
          cases hstaged
  | inr pending =>
      intro staged hstaged
      change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged

/-- The informed endpoint of a strict-right round satisfies its staged
coordinate anchor independently of which orientation is selected. -/
theorem ExactOwnerBoundarySelectedAt.openRecvTwo_stagedAnchor
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryTwoStagedAnchor A strategy
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        hreceive]
      rcases phaseData with ⟨data, oldState, oldOwner⟩
      rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
      intro staged hstaged
      simp only [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor,
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target]
        at hstaged ⊢
      split at * <;> cases hstaged <;> rfl
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        hreceive]
      intro staged hstaged
      change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged

/-- Strict-left mirror of `openRecvTwo_stagedAnchor`. -/
theorem ExactOwnerBoundarySelectedAt.openRecvOne_stagedAnchor
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryOneStagedAnchor A strategy
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo).1 := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        hreceive]
      intro staged hstaged
      change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        hreceive]
      rcases phaseData with ⟨data, oldState, oldOwner⟩
      rcases data with ⟨state, ⟨receiver, owner⟩, oldReceiver⟩
      intro staged hstaged
      simp only [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftReceiveFor,
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target]
        at hstaged ⊢
      split at * <;> cases hstaged <;> rfl

theorem ExactOwnerBoundaryStagedAnchor.strictRight
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (hanchor : ExactOwnerBoundaryStagedAnchor A strategy one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryStagedAnchor A strategy
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy one inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne).1 := by
  dsimp only
  exact ⟨hanchor.1.noRecv A strategy one inputOne,
    hselected.openRecvTwo_stagedAnchor A strategy hwin key one two inputOne
      inputTwo⟩

theorem ExactOwnerBoundaryStagedAnchor.strictLeft
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two)
    (hanchor : ExactOwnerBoundaryStagedAnchor A strategy one two)
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerBoundaryStagedAnchor A strategy
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only
  exact ⟨hselected.openRecvOne_stagedAnchor A strategy hwin key one two
      inputOne inputTwo,
    hanchor.2.noRecv A strategy two inputTwo⟩

/-- The first endpoint produced by a simultaneous exact-table close has a
valid latent fibre whenever it is pending. -/
theorem ExactOwnerBoundarySelectedAt.closeRound_oneValid
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo
    ExactOwnerBoundaryOneValid A strategy result.1.1 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      have hvalid := hphase.1.ownerFibreReceive_valid A strategy hwin key
        phaseData.1 phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa only [ExactOwnerBoundaryOneValid,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive]
        using hvalid.2
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      exact True.intro

/-- Mirrored simultaneous-close fibre validity at the second endpoint. -/
theorem ExactOwnerBoundarySelectedAt.closeRound_twoValid
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo
    ExactOwnerBoundaryTwoValid A strategy result.1.2 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      exact True.intro
  | left phaseData hright hleft hphase =>
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      have hvalid := hphase.1.ownerFibreReceive_valid A strategy hwin key
        phaseData.1 phaseData.2.1 phaseData.2.2 (inputOne, inputTwo)
      simpa only [ExactOwnerBoundaryTwoValid,
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive]
        using hvalid.2

/-- A simultaneous close leaves no staged base on either endpoint, so the
two staged-coordinate obligations hold vacuously. -/
theorem ExactOwnerBoundarySelectedAt.closeRound_stagedAnchor
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hselected : ExactOwnerBoundarySelectedAt A strategy key one two) :
    let result := (exactEffectTable A strategy hwin key).family A strategy key
      |>.ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
        inputTwo
    ExactOwnerBoundaryStagedAnchor A strategy result.1.1 result.1.2 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hselected with
  | right phaseData hright hphase =>
      obtain ⟨move, hmove, _⟩ :=
        hphase.afterBoth A strategy hwin key phaseData (inputOne, inputTwo)
      change
        (tables.resolvePacket A strategy hwin phaseData.1.1
          (phaseData.1.target (Memory := ExactMemory A strategy) A strategy
            (inputOne, inputTwo))).successor.2.1.1.2.2 = some move at hmove
      simp only [
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner] at hmove
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.rightPhaseOwnerFibreReceive A strategy hwin
              phaseData (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      change ExactOwnerBoundaryStagedAnchor A strategy
        (tables.rightPhaseOwnerFibreReceive A strategy hwin phaseData
          (inputOne, inputTwo)).1.1.closedControl
        (tables.rightPhaseOwnerFibreReceive A strategy hwin phaseData
          (inputOne, inputTwo)).2.1.closedControl
      constructor
      · intro staged hstaged
        change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
        cases hstaged
      · intro staged hstaged
        simp only [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightPhaseOwnerFibreReceive,
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo,
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.receiver,
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.owner,
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData.target,
          hmove] at hstaged
        cases hstaged
  | left phaseData hright hleft hphase =>
      obtain ⟨move, hmove, _⟩ :=
        hphase.afterBoth A strategy hwin key phaseData (inputOne, inputTwo)
      change
        (tables.resolvePacket A strategy hwin phaseData.1.1
          (phaseData.1.target (Memory := ExactMemory A strategy) A strategy
            (inputOne, inputTwo))).successor.2.1.1.2.1 = some move at hmove
      simp only [
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner] at hmove
      have hreceive :
          tables.ownerFibreBoundaryReceive? A strategy hwin one two
              (inputOne, inputTwo) =
            some (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
              (inputOne, inputTwo)) := by
        simp [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
          hright, hleft]
      rw [
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
        hreceive]
      change ExactOwnerBoundaryStagedAnchor A strategy
        (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
          (inputOne, inputTwo)).1.1.closedControl
        (tables.leftPhaseOwnerFibreReceive A strategy hwin phaseData
          (inputOne, inputTwo)).2.1.closedControl
      constructor
      · intro staged hstaged
        simp only [
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftPhaseOwnerFibreReceive,
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne,
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.receiver,
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.owner,
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData.target,
          hmove] at hstaged
        cases hstaged
      · intro staged hstaged
        change Sum.inr _ = Sum.inl (Sum.inl staged) at hstaged
        cases hstaged

/-! ### Blind preservation -/

omit [Inhabited Out₁] in
theorem ExactRightToLeftBridgeAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactRightToLeftBridgeAt A strategy key control)
    (input : In₂) :
    ExactRightToLeftBridgeAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change ExactBankAt A strategy key state ∧ _ at hexact
      cases packet with
      | none => exact hexact
      | some packet =>
          have hsuccessor := hexact.2 packet rfl
          dsimp [profiledRawJointRecurrentFiniteMemoryRightToLeftBridgeNoRecv]
          split
          · exact hexact
          · exact hsuccessor
  | inr installed => exact hexact

omit [Inhabited Out₂] in
theorem ExactLeftToRightBridgeAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactLeftToRightBridgeAt A strategy key control)
    (input : In₁) :
    ExactLeftToRightBridgeAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  cases control with
  | inl staged =>
      rcases staged with ⟨state, receiver, packet⟩
      change ExactBankAt A strategy key state ∧ _ at hexact
      cases packet with
      | none => exact hexact
      | some packet =>
          have hsuccessor := hexact.2 packet rfl
          dsimp [profiledRawJointRecurrentFiniteMemoryLeftToRightBridgeNoRecv]
          split
          · exact hexact
          · exact hsuccessor
  | inr installed => exact hexact

section
omit [Inhabited Out₁] [Inhabited Out₂]

theorem ExactRightToLeftOwnerFibreAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactRightToLeftOwnerFibreAt A strategy key control)
    (input : In₁) :
    ExactRightToLeftOwnerFibreAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simpa [ExactRightToLeftOwnerFibreAt,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hexact

theorem ExactLeftToRightOwnerFibreAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactLeftToRightOwnerFibreAt A strategy key control)
    (input : In₂) :
    ExactLeftToRightOwnerFibreAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  rcases control with ⟨member, shared, payload⟩
  cases member <;>
    simpa [ExactLeftToRightOwnerFibreAt,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreNoRecv,
      profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreStep,
      FiniteAcknowledgedDelayedCarrier.deferredMemberNoRecv] using hexact

theorem ExactRightToLeftOwnerFibreAt.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactRightToLeftOwnerFibreAt A strategy key control) :
    ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy control).1 := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      hmember] using hexact.2
  · simpa [profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver,
      hmember] using hexact.1

theorem ExactLeftToRightOwnerFibreAt.receiver
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePending
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactLeftToRightOwnerFibreAt A strategy key control) :
    ExactBankAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
        (Memory := ExactMemory A strategy) A strategy control).1 := by
  by_cases hmember : control.1
  · simpa [profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      hmember] using hexact.2
  · simpa [profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver,
      hmember] using hexact.1

end

/-! ### Successful-decoder exactness

The decoder is allowed to inspect several dormant coordinates and staged
packets.  The following two lemmas rule out a hidden mosaic: whenever a
decoder succeeds, both bank states that it exposes are exact coordinates at
the same root key. -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem rightBoundaryData?_exact
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hone : ExactBoundaryOneAt A strategy key one)
    (htwo : ExactBoundaryTwoAt A strategy key two)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := ExactMemory A strategy) A strategy one two = some data) :
    ExactRightPhaseDataAt A strategy key data := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  rcases oneBase with oneBridge | onePending
  · rcases oneBridge with oneStaged | oneInstalled
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled <;>
          simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
            at hdecode
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled
        · rcases twoStaged with ⟨stagedState, receiver, packet⟩
          change ExactBankAt A strategy key stagedState ∧ _ at htwoBase
          cases packet with
          | none =>
              simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | some packet =>
              have hpacket := htwoBase.2 packet rfl
              cases hmove : packet.successor.2.1.1.2.2 with
              | none =>
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                    hmove] at hdecode
              | some move =>
                  have hdecode' := hdecode
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                    hmove] at hdecode'
                  have hstates :=
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
                      (Memory := ExactMemory A strategy) A strategy
                        oneInstalled.1 oneInstalled.2.1 receiver
                        packet.successor
                        ⟨move, (move.memberController A false).initial⟩
                        (initialProfiledRawJointLeftPhysicalSiblingReceiver A
                          move .first) data hdecode'.2
                  exact ⟨by rw [hstates.1]; exact honeBase,
                    by rw [hstates.2]; exact hpacket⟩
        · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
            at hdecode
      · have hreceiver :=
          htwoBase.receiver A strategy key twoPending
        simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
        split at hdecode
        · have hstates :=
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
              (Memory := ExactMemory A strategy) A strategy oneInstalled.1
                oneInstalled.2.1
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy twoPending).2
                oneCoordinates.2
                (profiledRawJointLeftOwnerFibreExceptional A
                  twoPending.2.1.1)
                (twoPending.2.1.1.finiteMemoryReceiverAt A
                  oneInstalled.2.2) data hdecode
          exact ⟨by rw [hstates.1]; exact honeBase,
            by rw [hstates.2]; exact honeLeft⟩
        · simp at hdecode
  · rcases twoBase with twoBridge | twoPending
    · rcases twoBridge with twoStaged | twoInstalled
      · rcases twoStaged with ⟨stagedState, receiver, packet⟩
        change ExactBankAt A strategy key stagedState ∧ _ at htwoBase
        cases packet with
        | none =>
            simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
              at hdecode
        | some packet =>
            have hpacket := htwoBase.2 packet rfl
            cases hmove : packet.successor.2.1.1.2.2 with
            | none =>
                simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                  hmove] at hdecode
            | some move =>
                have hstates :=
                  profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
                    (Memory := ExactMemory A strategy) A strategy stagedState
                      (profiledRawJointRightOwnerFibreExceptional A
                        onePending.2.1.1)
                      (onePending.2.1.1.finiteMemoryReceiverAt A receiver)
                      packet.successor
                      ⟨move, (move.memberController A false).initial⟩
                      (initialProfiledRawJointLeftPhysicalSiblingReceiver A
                        move .first) data
                      (by simpa [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?,
                        hmove] using hdecode)
                exact ⟨by rw [hstates.1]; exact htwoBase.1,
                  by rw [hstates.2]; exact hpacket⟩
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
          at hdecode
    · have hright := htwoBase.receiver A strategy key twoPending
      have hleft := honeBase.receiver A strategy key onePending
      simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
        at hdecode
      split at hdecode
      · have hstates :=
          profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeRight?_states
            (Memory := ExactMemory A strategy) A strategy
              (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                (Memory := ExactMemory A strategy) A strategy twoPending).1
              (profiledRawJointRightOwnerFibreExceptional A
                onePending.2.1.1)
              (onePending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy twoPending).2)
              (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                (Memory := ExactMemory A strategy) A strategy onePending).1
              (profiledRawJointLeftOwnerFibreExceptional A
                twoPending.2.1.1)
              (twoPending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy onePending).2)
              data hdecode
        exact ⟨by rw [hstates.1]; exact hright,
          by rw [hstates.2]; exact hleft⟩
      · simp at hdecode

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem leftBoundaryData?_exact
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hone : ExactBoundaryOneAt A strategy key one)
    (htwo : ExactBoundaryTwoAt A strategy key two)
    (hdecode :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
        (Memory := ExactMemory A strategy) A strategy one two = some data) :
    ExactLeftPhaseDataAt A strategy key data := by
  rcases one with ⟨oneBase, oneCoordinates⟩
  rcases two with ⟨twoBase, twoCoordinates⟩
  rcases hone with ⟨honeBase, honeRight, honeLeft⟩
  rcases htwo with ⟨htwoBase, htwoRight, htwoLeft⟩
  rcases oneBase with oneBridge | onePending
  · rcases oneBridge with oneStaged | oneInstalled
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled
        · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
            at hdecode
        · rcases oneStaged with ⟨stagedState, receiver, packet⟩
          change ExactBankAt A strategy key stagedState ∧ _ at honeBase
          cases packet with
          | none =>
              simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
          | some packet =>
              have hpacket := honeBase.2 packet rfl
              cases hmove : packet.successor.2.1.1.2.1 with
              | none =>
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                    hmove] at hdecode
              | some move =>
                  have hdecode' := hdecode
                  simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                    hmove] at hdecode'
                  have hstates :=
                    profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
                      (Memory := ExactMemory A strategy) A strategy
                        twoInstalled.1 twoInstalled.2.1 receiver
                        packet.successor
                        ⟨move, (move.memberController A false).initial⟩
                        (initialProfiledRawJointRightPhysicalSiblingReceiver A
                          move .first) data hdecode'.2
                  exact ⟨by rw [hstates.1]; exact htwoBase,
                    by rw [hstates.2]; exact hpacket⟩
      · rcases oneStaged with ⟨stagedState, receiver, packet⟩
        change ExactBankAt A strategy key stagedState ∧ _ at honeBase
        cases hmember : twoPending.1 with
        | false =>
            simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
              hmember] at hdecode
        | true =>
            cases packet with
            | none =>
                simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                  hmember] at hdecode
            | some packet =>
                have hpacket := honeBase.2 packet rfl
                cases hmove : packet.successor.2.1.1.2.1 with
                | none =>
                    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                      hmember, hmove] at hdecode
                | some move =>
                    have hstates :=
                      profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
                        (Memory := ExactMemory A strategy) A strategy
                          stagedState
                          (profiledRawJointLeftOwnerFibreExceptional A
                            twoPending.2.1.1)
                          (twoPending.2.1.1.finiteMemoryReceiverAt A receiver)
                          packet.successor
                          ⟨move, (move.memberController A false).initial⟩
                          (initialProfiledRawJointRightPhysicalSiblingReceiver A
                            move .first) data
                          (by simpa [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?,
                            hmember, hmove] using hdecode)
                    exact ⟨by rw [hstates.1]; exact honeBase.1,
                      by rw [hstates.2]; exact hpacket⟩
    · rcases twoBase with twoBridge | twoPending
      · rcases twoBridge with twoStaged | twoInstalled <;>
          simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
            at hdecode
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
  · rcases twoBase with twoBridge | twoPending
    · rcases twoBridge with twoStaged | twoInstalled
      · simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
      · have hreceiver := honeBase.receiver A strategy key onePending
        simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
          at hdecode
        split at hdecode
        · have hstates :=
            profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
              (Memory := ExactMemory A strategy) A strategy twoInstalled.1
                twoInstalled.2.1
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy onePending).2
                twoCoordinates.1
                (profiledRawJointRightOwnerFibreExceptional A
                  onePending.2.1.1)
                (onePending.2.1.1.finiteMemoryReceiverAt A
                  twoInstalled.2.2) data hdecode
          exact ⟨by rw [hstates.1]; exact htwoBase,
            by rw [hstates.2]; exact htwoRight⟩
        · simp at hdecode
    · have hleft := honeBase.receiver A strategy key onePending
      have hright := htwoBase.receiver A strategy key twoPending
      simp only [profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
        at hdecode
      split at hdecode
      · have hstates :=
          profiledRawJointRecurrentFiniteMemoryOwnerFibreMakeLeft?_states
            (Memory := ExactMemory A strategy) A strategy
              (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                (Memory := ExactMemory A strategy) A strategy onePending).1
              (profiledRawJointLeftOwnerFibreExceptional A
                twoPending.2.1.1)
              (twoPending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy onePending).2)
              (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                (Memory := ExactMemory A strategy) A strategy twoPending).1
              (profiledRawJointRightOwnerFibreExceptional A
                onePending.2.1.1)
              (onePending.2.1.1.finiteMemoryReceiverAt A
                (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibreReceiver
                  (Memory := ExactMemory A strategy) A strategy twoPending).2)
              data hdecode
        exact ⟨by rw [hstates.1]; exact hleft,
          by rw [hstates.2]; exact hright⟩
      · simp at hdecode

omit [Inhabited Out₂] in
theorem ExactBoundaryOneAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactBoundaryOneAt A strategy key control)
    (input : In₁) :
    ExactBoundaryOneAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hexact with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv A strategy key bridge input, hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv A strategy key pending input, hcoordinates⟩

omit [Inhabited Out₁] in
theorem ExactBoundaryTwoAt.noRecv
    (key : RootKey A strategy)
    (control :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactBoundaryTwoAt A strategy key control)
    (input : In₂) :
    ExactBoundaryTwoAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy control input).1 := by
  rcases control with ⟨base, coordinates⟩
  rcases hexact with ⟨hbase, hcoordinates⟩
  cases base with
  | inl bridge =>
      exact ⟨hbase.noRecv A strategy key bridge input, hcoordinates⟩
  | inr pending =>
      exact ⟨hbase.noRecv A strategy key pending input, hcoordinates⟩

/-! ### Informed-fork preservation -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Both meanings of a fresh right-to-left owner fibre retain exactly the
old coordinate and the resolved exact successor. -/
theorem exactRightToLeftOwnerFibrePacketBoundaryFork
    (key : RootKey A strategy)
    (sender : ProfiledRawJointRightPhysicalSiblingExceptional A)
    (oldState : ExactBankControl A strategy)
    (oldReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : ExactPacket A strategy)
    (input : In₁ × In₂)
    (hold : ExactBankAt A strategy key oldState)
    (hpacket : ExactBankAt A strategy key packet.successor) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibrePacketBoundaryFork
        (Memory := ExactMemory A strategy) A strategy sender oldState
          oldReceiver oldOwner packet input).1
    ExactRightToLeftOwnerFibreAt A strategy key fork.openControl ∧
      ExactRightToLeftOwnerFibreAt A strategy key fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored exact-coordinate law for a fresh left-to-right owner fibre. -/
theorem exactLeftToRightOwnerFibrePacketBoundaryFork
    (key : RootKey A strategy)
    (sender : ProfiledRawJointLeftPhysicalSiblingExceptional A)
    (oldState : ExactBankControl A strategy)
    (oldReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldOwner : (oldReceiver.1.memberController A false).Control)
    (packet : ExactPacket A strategy)
    (input : In₂ × In₁)
    (hold : ExactBankAt A strategy key oldState)
    (hpacket : ExactBankAt A strategy key packet.successor) :
    let fork :=
      (profiledRawJointRecurrentFiniteMemoryLeftToRightOwnerFibrePacketBoundaryFork
        (Memory := ExactMemory A strategy) A strategy sender oldState
          oldReceiver oldOwner packet input).1
    ExactLeftToRightOwnerFibreAt A strategy key fork.openControl ∧
      ExactLeftToRightOwnerFibreAt A strategy key fork.closedControl := by
  exact ⟨⟨hold, hpacket⟩, ⟨hold, hpacket⟩⟩

/-- The staged result of an informed right receive contains only exact bank
coordinates. -/
theorem ExactBankAt.rightReceiveFor
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let next := tables.rightReceiveFor A strategy hwin state receiver owner
      input
    ExactRightToLeftBridgeAt A strategy key (.inl next.1) := by
  dsimp only
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightReceiveFor
  dsimp only
  generalize hnext :
      stepProfiledRawJointRightPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none =>
      simp only [hnext, htarget]
      exact ⟨hexact, by intro packet hpacket; simp at hpacket⟩
  | some target =>
      simp only [hnext, htarget]
      refine ⟨hexact, ?_⟩
      intro packet hpacket
      cases Option.some.inj hpacket
      exact hexact.resolvePacket A strategy hwin key state target

/-- A raw exact-table right receive stages only an exact successor packet;
if the opposite move is already available, its installed closed candidate is
exact as well. -/
theorem ExactBankAt.rightToLeftBridgeForkTwo
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (receiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₂ × In₁) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let fork :=
      (tables.rightToLeftBridgeForkTwo A strategy hwin state receiver owner
        input).1
    ExactRightToLeftBridgeAt A strategy key fork.openControl ∧
      ExactRightToLeftBridgeAt A strategy key fork.closedControl := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let next := tables.rightReceiveFor A strategy hwin state receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet := tables.resolvePacket A strategy hwin state target
  have hopen : ExactRightToLeftBridgeAt A strategy key (.inl next.1) :=
    hexact.rightReceiveFor A strategy hwin key state receiver owner input
  have hpacket : ExactBankAt A strategy key packet.successor :=
    hexact.resolvePacket A strategy hwin key state target
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.rightToLeftBridgeForkTwo
  dsimp only
  split
  · exact ⟨hopen, hopen⟩
  · exact ⟨hopen, hpacket⟩

/-- The staged result of an informed left receive contains only exact bank
coordinates. -/
theorem ExactBankAt.leftReceiveFor
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let next := tables.leftReceiveFor A strategy hwin state receiver owner
      input
    ExactLeftToRightBridgeAt A strategy key (.inl next.1) := by
  dsimp only
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftReceiveFor
  dsimp only
  generalize hnext :
      stepProfiledRawJointLeftPhysicalSiblingReceiverFor A receiver.1 owner
        receiver.2.1 receiver.2.2.1 input = next
  cases htarget : next.2.2.2.2 with
  | none =>
      simp only [hnext, htarget]
      exact ⟨hexact, by intro packet hpacket; simp at hpacket⟩
  | some target =>
      simp only [hnext, htarget]
      refine ⟨hexact, ?_⟩
      intro packet hpacket
      cases Option.some.inj hpacket
      exact hexact.resolvePacket A strategy hwin key state target

/-- Left-to-right mirror of exact informed-bridge preservation. -/
theorem ExactBankAt.leftToRightBridgeForkOne
    (key : RootKey A strategy)
    (state : ExactBankControl A strategy)
    (hexact : ExactBankAt A strategy key state)
    (receiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (owner : (receiver.1.memberController A false).Control)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let fork :=
      (tables.leftToRightBridgeForkOne A strategy hwin state receiver owner
        input).1
    ExactLeftToRightBridgeAt A strategy key fork.openControl ∧
      ExactLeftToRightBridgeAt A strategy key fork.closedControl := by
  dsimp only
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let next := tables.leftReceiveFor A strategy hwin state receiver owner input
  let target := (((receiver.1.memberController A false).labelOf owner).2
    receiver.2.2.1 input |>.target receiver.2.1)
  let packet := tables.resolvePacket A strategy hwin state target
  have hopen : ExactLeftToRightBridgeAt A strategy key (.inl next.1) :=
    hexact.leftReceiveFor A strategy hwin key state receiver owner input
  have hpacket : ExactBankAt A strategy key packet.successor :=
    hexact.resolvePacket A strategy hwin key state target
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.leftToRightBridgeForkOne
  dsimp only
  split
  · exact ⟨hopen, hopen⟩
  · exact ⟨hopen, hpacket⟩

/-! ### Exactness through a complete decoded phase -/

theorem rightPhaseOwnerFibreReceive_exact
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactRightPhaseDataAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let result :=
      tables.rightPhaseOwnerFibreReceive A strategy hwin data input
    ExactBoundaryOneAt A strategy key result.1.1.openControl ∧
      ExactBoundaryOneAt A strategy key result.1.1.closedControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.openControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.closedControl := by
  rcases data with ⟨⟨state, ⟨receiver, owner⟩, oldReceiver⟩,
    oldState, oldOwner⟩
  rcases hexact with ⟨hstate, hold⟩
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let packet := tables.resolvePacket A strategy hwin state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 (input.2, input.1)).target receiver.2.1))
  have hpacket : ExactBankAt A strategy key packet.successor :=
    hstate.resolvePacket A strategy hwin key state _
  have hphase :=
    exactRightToLeftOwnerFibrePacketBoundaryFork A strategy key
      ⟨receiver.1, owner⟩ oldState oldReceiver oldOwner packet input hold
        hpacket
  have hbridge := hstate.rightToLeftBridgeForkTwo A strategy hwin key state
    receiver owner (input.2, input.1)
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hphaseOpen, hstate, hold⟩,
    ⟨hphaseClosed, hstate, hpacket⟩,
    ⟨hbridgeOpen, hstate, hpacket⟩,
    ⟨hbridgeClosed, hstate, hpacket⟩⟩

theorem leftPhaseOwnerFibreReceive_exact
    (key : RootKey A strategy)
    (data :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactLeftPhaseDataAt A strategy key data)
    (input : In₁ × In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    let result :=
      tables.leftPhaseOwnerFibreReceive A strategy hwin data input
    ExactBoundaryOneAt A strategy key result.1.1.openControl ∧
      ExactBoundaryOneAt A strategy key result.1.1.closedControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.openControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.closedControl := by
  rcases data with ⟨⟨state, ⟨receiver, owner⟩, oldReceiver⟩,
    oldState, oldOwner⟩
  rcases hexact with ⟨hstate, hold⟩
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  let packet := tables.resolvePacket A strategy hwin state
    (((((receiver.1.memberController A false).labelOf owner).2
      receiver.2.2.1 input).target receiver.2.1))
  have hpacket : ExactBankAt A strategy key packet.successor :=
    hstate.resolvePacket A strategy hwin key state _
  have hphase :=
    exactLeftToRightOwnerFibrePacketBoundaryFork A strategy key
      ⟨receiver.1, owner⟩ oldState oldReceiver oldOwner packet
        (input.2, input.1) hold hpacket
  have hbridge := hstate.leftToRightBridgeForkOne A strategy hwin key state
    receiver owner input
  rcases hphase with ⟨hphaseOpen, hphaseClosed⟩
  rcases hbridge with ⟨hbridgeOpen, hbridgeClosed⟩
  exact ⟨⟨hbridgeOpen, hpacket, hstate⟩,
    ⟨hbridgeClosed, hpacket, hstate⟩,
    ⟨hphaseOpen, hold, hstate⟩,
    ⟨hphaseClosed, hpacket, hstate⟩⟩

/-- A successful raw boundary receive returns four exact endpoint candidates.
This includes both orientations selected by the decoder. -/
theorem ownerFibreBoundaryReceive?_exact
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (result :
      (FiniteDelayedFork
          (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
            (Memory := ExactMemory A strategy) A strategy) × Out₁) ×
        (FiniteDelayedFork
          (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
            (Memory := ExactMemory A strategy) A strategy) × Out₂))
    (hone : ExactBoundaryOneAt A strategy key one)
    (htwo : ExactBoundaryTwoAt A strategy key two)
    (hreceive :
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryReceive? A strategy hwin one two input =
          some result) :
    ExactBoundaryOneAt A strategy key result.1.1.openControl ∧
      ExactBoundaryOneAt A strategy key result.1.1.closedControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.openControl ∧
      ExactBoundaryTwoAt A strategy key result.2.1.closedControl := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hright :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
        (Memory := ExactMemory A strategy) A strategy one two with
  | some data =>
      have hdata := rightBoundaryData?_exact A strategy key one two data hone
        htwo hright
      have hall := rightPhaseOwnerFibreReceive_exact A strategy hwin key data
        hdata input
      rw [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
        hright] at hreceive
      cases Option.some.inj hreceive
      exact hall
  | none =>
      cases hleft :
          profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
            (Memory := ExactMemory A strategy) A strategy one two with
      | some data =>
          have hdata := leftBoundaryData?_exact A strategy key one two data
            hone htwo hleft
          have hall := leftPhaseOwnerFibreReceive_exact A strategy hwin key
            data hdata input
          rw [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
            hright, hleft] at hreceive
          cases Option.some.inj hreceive
          exact hall
      | none =>
          simp [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryReceive?,
            hright, hleft] at hreceive

theorem ownerFibreBoundaryOpenRecvOne_exact
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hone : ExactBoundaryOneAt A strategy key one)
    (htwo : ExactBoundaryTwoAt A strategy key two) :
    ExactBoundaryOneAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hreceive : tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | none =>
      simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        tables, hreceive] using hone.noRecv A strategy key one inputOne
  | some result =>
      have hall := ownerFibreBoundaryReceive?_exact A strategy hwin key one two
        (inputOne, inputTwo) result hone htwo hreceive
      simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvOne,
        tables, hreceive] using hall.1

theorem ownerFibreBoundaryOpenRecvTwo_exact
    (key : RootKey A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (htwo : ExactBoundaryTwoAt A strategy key two)
    (hone : ExactBoundaryOneAt A strategy key one) :
    ExactBoundaryTwoAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hreceive : tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | none =>
      simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        tables, hreceive] using htwo.noRecv A strategy key two inputTwo
  | some result =>
      have hall := ownerFibreBoundaryReceive?_exact A strategy hwin key one two
        (inputOne, inputTwo) result hone htwo hreceive
      simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryOpenRecvTwo,
        tables, hreceive] using hall.2.2.1

/-- Once decoder selection for the next strict-right state is known, all
other fields of the exact operational invariant are automatic. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictRight_of_selected
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂)
    (hselected :
      let tables := (exactEffectTable A strategy hwin key).family A strategy
        key
      ExactOwnerBoundarySelectedAt A strategy key
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
          (Memory := ExactMemory A strategy) A strategy one inputOne).1
        (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
          inputOne).1) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy one inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin two inputTwo one
        inputOne).1 := by
  dsimp only at hselected ⊢
  exact
    { selected := hselected
      oneValid := hoperational.oneValid.noRecv A strategy one inputOne
      twoValid :=
        hoperational.selected.openRecvTwo_valid A strategy hwin key one two
          inputOne inputTwo
      stagedAnchor :=
        hoperational.stagedAnchor.strictRight A strategy hwin key one two
          hoperational.selected inputOne inputTwo
      exact :=
        ⟨hoperational.exact.1.noRecv A strategy key one inputOne,
          ownerFibreBoundaryOpenRecvTwo_exact A strategy hwin key two inputTwo
            one inputOne hoperational.exact.2 hoperational.exact.1⟩ }

/-- Strict-left mirror of `strictRight_of_selected`. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictLeft_of_selected
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key one two)
    (inputOne : In₁) (inputTwo : In₂)
    (hselected :
      let tables := (exactEffectTable A strategy hwin key).family A strategy
        key
      ExactOwnerBoundarySelectedAt A strategy key
        (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
          inputTwo).1
        (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
          (Memory := ExactMemory A strategy) A strategy two inputTwo).1) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin one inputOne two
        inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy two inputTwo).1 := by
  dsimp only at hselected ⊢
  exact
    { selected := hselected
      oneValid :=
        hoperational.selected.openRecvOne_valid A strategy hwin key one two
          inputOne inputTwo
      twoValid := hoperational.twoValid.noRecv A strategy two inputTwo
      stagedAnchor :=
        hoperational.stagedAnchor.strictLeft A strategy hwin key one two
          hoperational.selected inputOne inputTwo
      exact :=
        ⟨ownerFibreBoundaryOpenRecvOne_exact A strategy hwin key one
            inputOne two inputTwo hoperational.exact.1 hoperational.exact.2,
          hoperational.exact.2.noRecv A strategy key two inputTwo⟩ }

/-- Both semantic and bookkeeping fields survive a strict-right round from
an installed/staged exact entry. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictRight_installedStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inl
              (.inr
                (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates) inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentRight.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
    | left phaseData hright hdecode hphase =>
        rw [hcurrentRight] at hright
        cases hright
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictRight_installedStaged A strategy hwin
      key rightState rightReceiver rightOwner leftTemplate oldPacket leftMove
        hleftMove oneCoordinates twoCoordinates hcurrentOperational inputOne
          inputTwo).2
  exact hoperational.strictRight_of_selected A strategy hwin key
    (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
      oneCoordinates)
    (.inl (.inl (rightState, rightReceiver, some oldPacket)),
      twoCoordinates)
    inputOne inputTwo hselectedNext

/-- Opposite-orientation strict-left closure of the full invariant from the
same installed/staged exact entry. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictLeft_installedStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) inputTwo).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState, ⟨rightReceiver, rightOwner⟩, leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl
            (.inr
              (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentRight.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
    | left phaseData hright hdecode hphase =>
        rw [hcurrentRight] at hright
        cases hright
  have hrightCoordinate : twoCoordinates.1 = rightState := by
    exact hoperational.stagedAnchor.2
      (rightState, rightReceiver, some oldPacket) rfl
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictLeft_installedStaged A strategy hwin
      key rightState rightReceiver rightOwner leftTemplate oldPacket leftMove
        hleftMove oneCoordinates twoCoordinates hrightCoordinate
          hcurrentOperational inputOne inputTwo).2
  exact hoperational.strictLeft_of_selected A strategy hwin key
    (.inl
        (.inr
          (rightState, ⟨rightReceiver.1, rightOwner⟩, leftTemplate)),
      oneCoordinates)
    (.inl (.inl (rightState, rightReceiver, some oldPacket)),
      twoCoordinates)
    inputOne inputTwo hselectedNext

/-- Full-invariant same-orientation closure of the mirrored honest entry. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictLeft_stagedInstalled
    (key : RootKey A strategy)
    (leftState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl
              (.inr
                (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) inputTwo).1 := by
  dsimp only
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightInitial),
      oldPacket.successor,
      (rightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, rightInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate oldPacket rightMove hrightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
  have hcurrentOperational :
      ExactLeftPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        rw [hcurrentRight] at hdecode
        cases hdecode
    | left phaseData hright hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentLeft.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictLeft_stagedInstalled A strategy hwin
      key leftState leftReceiver leftOwner rightTemplate oldPacket rightMove
        hrightMove oneCoordinates twoCoordinates hcurrentOperational inputOne
          inputTwo).2
  exact hoperational.strictLeft_of_selected A strategy hwin key
    (.inl (.inl (leftState, leftReceiver, some oldPacket)), oneCoordinates)
    (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
      twoCoordinates)
    inputOne inputTwo hselectedNext

/-- Full-invariant opposite-orientation closure of the mirrored honest
entry. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictRight_stagedInstalled
    (key : RootKey A strategy)
    (leftState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (oldPacket : ExactPacket A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hrightMove : oldPacket.successor.2.1.1.2.1 = some rightMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates)
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates) inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
          twoCoordinates) inputTwo
        (.inl (.inl (leftState, leftReceiver, some oldPacket)),
          oneCoordinates) inputOne).1 := by
  dsimp only
  let rightInitial :=
    initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryLeftPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(leftState, ⟨leftReceiver, leftOwner⟩, rightInitial),
      oldPacket.successor,
      (rightMove.memberController A false).initial⟩
  have hcurrentLeft :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = some currentPhase := by
    simpa only [currentPhase, rightInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate oldPacket rightMove hrightMove
            oneCoordinates twoCoordinates
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (leftState, leftReceiver, some oldPacket)),
            oneCoordinates)
          (.inl
            (.inr
              (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
            twoCoordinates) = none := by
    simp [profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
  have hcurrentOperational :
      ExactLeftPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        rw [hcurrentRight] at hdecode
        cases hdecode
    | left phaseData hright hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentLeft.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
  have hleftCoordinate : oneCoordinates.2 = leftState := by
    exact hoperational.stagedAnchor.1
      (leftState, leftReceiver, some oldPacket) rfl
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictRight_stagedInstalled A strategy hwin
      key leftState leftReceiver leftOwner rightTemplate oldPacket rightMove
        hrightMove oneCoordinates twoCoordinates hleftCoordinate
          hcurrentOperational inputOne inputTwo).2
  exact hoperational.strictRight_of_selected A strategy hwin key
    (.inl (.inl (leftState, leftReceiver, some oldPacket)), oneCoordinates)
    (.inl
        (.inr
          (leftState, ⟨leftReceiver.1, leftOwner⟩, rightTemplate)),
      twoCoordinates)
    inputOne inputTwo hselectedNext

/-- The complete bridge/bridge quadrant of the exact operational invariant is
closed under strict-right rounds.  Two tag combinations are decoder-empty;
the other two are the two honest-entry theorems above. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictRight_bridgeBridge
    (key : RootKey A strategy)
    (oneBridge :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (twoBridge :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inl oneBridge, oneCoordinates) inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inl twoBridge, twoCoordinates) inputTwo
          (.inl oneBridge, oneCoordinates) inputOne).1 := by
  cases oneBridge with
  | inl oneStaged =>
      cases twoBridge with
      | inl twoStaged =>
          cases hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          cases hselected : hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              obtain ⟨leftState, leftReceiver, leftOwner, rightTemplate,
                  packet, rightMove, rfl, rfl, hrightMove, rfl⟩ :=
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled_inv
                  (Memory := ExactMemory A strategy) A strategy oneStaged
                    twoInstalled oneCoordinates twoCoordinates phaseData
                      hdecode
              exact hoperational.strictRight_stagedInstalled A strategy hwin
                key leftState leftReceiver leftOwner rightTemplate packet
                  rightMove hrightMove oneCoordinates twoCoordinates inputOne
                    inputTwo
  | inr oneInstalled =>
      cases twoBridge with
      | inl twoStaged =>
          cases hselected : hoperational.selected with
          | right phaseData hdecode hphase =>
              obtain ⟨rightState, rightReceiver, rightOwner, leftTemplate,
                  packet, leftMove, rfl, rfl, hleftMove, rfl⟩ :=
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged_inv
                  (Memory := ExactMemory A strategy) A strategy oneInstalled
                    twoStaged oneCoordinates twoCoordinates phaseData hdecode
              exact hoperational.strictRight_installedStaged A strategy hwin
                key rightState rightReceiver rightOwner leftTemplate packet
                  leftMove hleftMove oneCoordinates twoCoordinates inputOne
                    inputTwo
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          cases hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode

/-- Strict-left closure of the complete bridge/bridge quadrant. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictLeft_bridgeBridge
    (key : RootKey A strategy)
    (oneBridge :
      ProfiledRawJointRecurrentFiniteMemoryLeftToRightBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (twoBridge :
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftBridgeControl
        (Memory := ExactMemory A strategy) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inl oneBridge, oneCoordinates) (.inl twoBridge, twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inl oneBridge, oneCoordinates) inputOne
          (.inl twoBridge, twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl twoBridge, twoCoordinates) inputTwo).1 := by
  cases oneBridge with
  | inl oneStaged =>
      cases twoBridge with
      | inl twoStaged =>
          cases hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          cases hselected : hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              obtain ⟨leftState, leftReceiver, leftOwner, rightTemplate,
                  packet, rightMove, rfl, rfl, hrightMove, rfl⟩ :=
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?_stagedInstalled_inv
                  (Memory := ExactMemory A strategy) A strategy oneStaged
                    twoInstalled oneCoordinates twoCoordinates phaseData
                      hdecode
              exact hoperational.strictLeft_stagedInstalled A strategy hwin
                key leftState leftReceiver leftOwner rightTemplate packet
                  rightMove hrightMove oneCoordinates twoCoordinates inputOne
                    inputTwo
  | inr oneInstalled =>
      cases twoBridge with
      | inl twoStaged =>
          cases hselected : hoperational.selected with
          | right phaseData hdecode hphase =>
              obtain ⟨rightState, rightReceiver, rightOwner, leftTemplate,
                  packet, leftMove, rfl, rfl, hleftMove, rfl⟩ :=
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_installedStaged_inv
                  (Memory := ExactMemory A strategy) A strategy oneInstalled
                    twoStaged oneCoordinates twoCoordinates phaseData hdecode
              exact hoperational.strictLeft_installedStaged A strategy hwin
                key rightState rightReceiver rightOwner leftTemplate packet
                  leftMove hleftMove oneCoordinates twoCoordinates inputOne
                    inputTwo
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode
      | inr twoInstalled =>
          cases hoperational.selected with
          | right phaseData hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?]
                at hdecode
          | left phaseData hright hdecode hphase =>
              simp [
                profiledRawJointRecurrentFiniteMemoryOwnerFibreLeftBoundaryData?]
                at hdecode

/-- Induction-ready form of the hard equal-bit strict-right case.  Unlike the
shape theorem above, this statement assumes only the full source invariant
and returns that same invariant for the executable successor. -/
theorem
    ExactOwnerFibreBoundaryOperationalAt.strictRight_openOpen_fibreStaged
    (key : RootKey A strategy)
    (rightState leftState : ExactBankControl A strategy)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (leftFibre : ProfiledRawJointLeftOwnerFibreControl A)
    (newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (newRight :
      ProfiledRawJointRecurrentFiniteMemoryBankedRightReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates)
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvOne
        (Memory := ExactMemory A strategy) A strategy
          (.inr
              (false,
                (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates) inputOne).1
      (tables.ownerFibreBoundaryOpenRecvTwo A strategy hwin
        (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
          twoCoordinates) inputTwo
        (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
          oneCoordinates) inputOne).1 := by
  dsimp only
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightFibre.finiteMemoryReceiverAt A rightTemplate,
          rightFibre.2.1⟩,
        leftFibre.finiteMemoryReceiverAt A leftTemplate),
      leftState, leftFibre.2.1⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr
            (false,
              (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
            oneCoordinates)
          (.inr
            (false,
              (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_openOpen
        (Memory := ExactMemory A strategy) A strategy rightState leftState
          rightTemplate leftTemplate rightFibre leftFibre newLeft newRight
            oneCoordinates twoCoordinates
  have hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentRight.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
    | left phaseData hright hdecode hphase =>
        rw [hcurrentRight] at hright
        cases hright
  have hrightFibre : ProfiledRawJointRightOwnerFibreValid A rightFibre := by
    simpa only [ExactOwnerBoundaryOneValid,
      ProfiledRawJointRecurrentFiniteMemoryRightToLeftOwnerFibreValid] using
        hoperational.oneValid
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictRight_openOpen_fibreStaged A strategy
      hwin key rightState leftState rightTemplate leftTemplate rightFibre
        leftFibre newLeft newRight oneCoordinates twoCoordinates hrightFibre
          hcurrentOperational inputOne inputTwo).2
  exact hoperational.strictRight_of_selected A strategy hwin key
    (.inr
        (false, (rightFibre, ⟨(leftState, leftTemplate), newLeft⟩), ()),
      oneCoordinates)
    (.inr
        (false, (leftFibre, ⟨(rightState, rightTemplate), newRight⟩), ()),
      twoCoordinates)
    inputOne inputTwo hselectedNext

/-- Induction-ready reverse of the hard equal-bit continuation.  Starting
from the fibre/staged state produced by
`strictRight_openOpen_fibreStaged`, a strict-left round preserves the full
five-field exact operational invariant. -/
theorem ExactOwnerFibreBoundaryOperationalAt.strictLeft_fibreStaged
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightFibre : ProfiledRawJointRightOwnerFibreControl A)
    (oldLeft newLeft :
      ProfiledRawJointRecurrentFiniteMemoryBankedLeftReceiver
        (Memory := ExactMemory A strategy) A strategy)
    (oldPacket : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hleftMove : oldPacket.successor.2.1.1.2.2 = some leftMove)
    (oneCoordinates twoCoordinates :
      ProfiledRawJointRecurrentFiniteMemoryBoundaryBankCoordinates
        (Memory := ExactMemory A strategy) A strategy)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key
        (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates)
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates))
    (inputOne : In₁) (inputTwo : In₂) :
    let tables := (exactEffectTable A strategy hwin key).family A strategy key
    ExactOwnerFibreBoundaryOperationalAt A strategy key
      (tables.ownerFibreBoundaryOpenRecvOne A strategy hwin
        (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
          oneCoordinates) inputOne
        (.inl (.inl (rightState, rightReceiver, some oldPacket)),
          twoCoordinates) inputTwo).1
      (profiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryNoRecvTwo
        (Memory := ExactMemory A strategy) A strategy
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) inputTwo).1 := by
  dsimp only
  let leftInitial :=
    initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove .first
  let currentPhase :
      ProfiledRawJointRecurrentFiniteMemoryRightPhaseLiveBoundaryData
        (Memory := ExactMemory A strategy) A strategy :=
    ⟨(rightState,
        ⟨rightFibre.finiteMemoryReceiverAt A rightReceiver,
          rightFibre.2.1⟩,
        leftInitial),
      oldPacket.successor,
      (leftMove.memberController A false).initial⟩
  have hcurrentRight :
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?
          (Memory := ExactMemory A strategy) A strategy
          (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
            oneCoordinates)
          (.inl (.inl (rightState, rightReceiver, some oldPacket)),
            twoCoordinates) =
        some currentPhase := by
    simpa only [currentPhase, leftInitial] using
      profiledRawJointRecurrentFiniteMemoryOwnerFibreRightBoundaryData?_fibreStaged
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightFibre oldLeft newLeft oldPacket leftMove
            hleftMove oneCoordinates twoCoordinates
  have hcurrentOperational :
      ExactRightPhaseOperationalAt A strategy key currentPhase := by
    cases hoperational.selected with
    | right phaseData hdecode hphase =>
        have heq : some currentPhase = some phaseData :=
          hcurrentRight.symm.trans hdecode
        cases Option.some.inj heq
        exact hphase
    | left phaseData hright hdecode hphase =>
        rw [hcurrentRight] at hright
        cases hright
  have hrightCoordinate : twoCoordinates.1 = rightState := by
    exact hoperational.stagedAnchor.2
      (rightState, rightReceiver, some oldPacket) rfl
  have hselectedNext :=
    (exactOwnerBoundarySelectedAt_strictLeft_fibreStaged A strategy hwin key
      rightState rightReceiver rightFibre oldLeft newLeft oldPacket leftMove
        hleftMove oneCoordinates twoCoordinates hrightCoordinate
          hcurrentOperational inputOne inputTwo).2
  exact hoperational.strictLeft_of_selected A strategy hwin key
    (.inr (false, (rightFibre, ⟨oldLeft, newLeft⟩), ()),
      oneCoordinates)
    (.inl (.inl (rightState, rightReceiver, some oldPacket)),
      twoCoordinates)
    inputOne inputTwo hselectedNext

theorem ownerFibreBoundaryCloseRound_exact
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hone : ExactBoundaryOneAt A strategy key one)
    (htwo : ExactBoundaryTwoAt A strategy key two) :
    let result :=
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo
    ExactBoundaryOneAt A strategy key result.1.1 ∧
      ExactBoundaryTwoAt A strategy key result.1.2 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  cases hreceive : tables.ownerFibreBoundaryReceive? A strategy hwin one two
      (inputOne, inputTwo) with
  | none =>
      exact ⟨by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
            tables, hreceive] using hone.noRecv A strategy key one inputOne,
        by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
            tables, hreceive] using htwo.noRecv A strategy key two inputTwo⟩
  | some result =>
      have hall := ownerFibreBoundaryReceive?_exact A strategy hwin key one two
        (inputOne, inputTwo) result hone htwo hreceive
      exact ⟨by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
            tables, hreceive] using hall.2.1,
        by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreBoundaryCloseRound,
            tables, hreceive] using hall.2.2.2⟩

/-- The full exact operational invariant is closed under a simultaneous
physical round.  Readiness rules out the decoder's defaulted packet branch;
the remaining four fields are preserved by the literal table transition. -/
theorem ExactOwnerFibreBoundaryOperationalAt.closeRound
    (key : RootKey A strategy)
    (one :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputOne : In₁)
    (two :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
        (Memory := ExactMemory A strategy) A strategy)
    (inputTwo : In₂)
    (hoperational :
      ExactOwnerFibreBoundaryOperationalAt A strategy key one two) :
    let result :=
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreBoundaryCloseRound A strategy hwin one inputOne two
          inputTwo
    ExactOwnerFibreBoundaryOperationalAt A strategy key result.1.1
      result.1.2 := by
  dsimp only
  exact
    { selected :=
        hoperational.selected.closeRound A strategy hwin key one inputOne two
          inputTwo
      oneValid :=
        hoperational.selected.closeRound_oneValid A strategy hwin key one
          inputOne two inputTwo
      twoValid :=
        hoperational.selected.closeRound_twoValid A strategy hwin key one
          inputOne two inputTwo
      stagedAnchor :=
        hoperational.selected.closeRound_stagedAnchor A strategy hwin key one
          inputOne two inputTwo
      exact :=
        ownerFibreBoundaryCloseRound_exact A strategy hwin key one inputOne
          two inputTwo hoperational.exact.1 hoperational.exact.2 }

/-- Every raw physical round of the exact table preserves synchronization of
all bank coordinates, for every input pair and every graph symbol. -/
theorem ownerFibreRound_exactOwnerLiveAt
    (key : RootKey A strategy)
    (controls :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryOneControl
          (Memory := ExactMemory A strategy) A strategy ×
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreBoundaryTwoControl
          (Memory := ExactMemory A strategy) A strategy)
    (input : In₁ × In₂)
    (graph : Graph)
    (hexact : ExactBoundaryOneAt A strategy key controls.1 ∧
      ExactBoundaryTwoAt A strategy key controls.2) :
    let result :=
      ((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreRound A strategy hwin controls input graph
    ExactBoundaryOneAt A strategy key result.1.1 ∧
      ExactBoundaryTwoAt A strategy key result.1.2 := by
  rcases hexact with ⟨hone, htwo⟩
  cases graph with
  | right =>
      exact ⟨by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound]
            using hone.noRecv A strategy key controls.1 input.1,
        by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound]
            using ownerFibreBoundaryOpenRecvTwo_exact A strategy hwin key
              controls.2 input.2 controls.1 input.1 htwo hone⟩
  | left =>
      exact ⟨by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound]
            using ownerFibreBoundaryOpenRecvOne_exact A strategy hwin key
              controls.1 input.1 controls.2 input.2 hone htwo,
        by
          simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound]
            using htwo.noRecv A strategy key controls.2 input.2⟩
  | both =>
      simpa [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreRound]
        using ownerFibreBoundaryCloseRound_exact A strategy hwin key
          controls.1 input.1 controls.2 input.2 hone htwo

/-- The DPA product coordinate is irrelevant to bank exactness, so the full
live safety step preserves the exact owner invariant. -/
theorem ExactOwnerLiveAt.liveStep
    (key : RootKey A strategy)
    (live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactOwnerLiveAt A strategy key live)
    (direction :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂)) :
    ExactOwnerLiveAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreSafetyLiveStep A strategy hwin live direction) := by
  unfold
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreSafetyLiveStep
  dsimp only
  exact ownerFibreRound_exactOwnerLiveAt A strategy hwin key live.1
    direction.1 direction.2 hexact

/-- Consequently every finite raw-owner prefix remains exactly synchronized,
uniformly over the environment branch. -/
theorem ExactOwnerLiveAt.liveStateAt
    (key : RootKey A strategy)
    (live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy)
    (hexact : ExactOwnerLiveAt A strategy key live)
    (node : TreeNode
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))) :
    ExactOwnerLiveAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreSafetyLiveStateAt A strategy hwin live node) := by
  induction node generalizing live with
  | nil => exact hexact
  | cons direction node ih =>
      exact ih
        (((exactEffectTable A strategy hwin key).family A strategy key
          ).ownerFibreSafetyLiveStep A strategy hwin live direction)
        (hexact.liveStep A strategy hwin key live direction)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The right-oriented entry constructor preserves all exact bank
coordinates, including the packet successor hidden in the staged bridge. -/
theorem ownerFibreRightEntryLiveState_exactOwnerLiveAt
    (key : RootKey A strategy)
    (rightState : ExactBankControl A strategy)
    (rightReceiver : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (rightOwner : (rightReceiver.1.memberController A false).Control)
    (leftTemplate : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (packet : ExactPacket A strategy)
    (leftMove : ProfiledRawJointLeftPhysicalSiblingMove A)
    (hstate : ExactBankAt A strategy key rightState)
    (hpacket : ExactBankAt A strategy key packet.successor) :
    ExactOwnerLiveAt A strategy key
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryLiveState
        (Memory := ExactMemory A strategy) A strategy rightState
          rightReceiver rightOwner leftTemplate packet leftMove) := by
  exact
    ⟨⟨hstate, hstate, hpacket⟩,
      ⟨⟨hstate, by
          intro candidate hc
          cases Option.some.inj hc
          exact hpacket⟩,
        hstate, hpacket⟩⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Mirrored exactness of every bank coordinate in a left-oriented entry. -/
theorem ownerFibreLeftEntryLiveState_exactOwnerLiveAt
    (key : RootKey A strategy)
    (leftState : ExactBankControl A strategy)
    (leftReceiver : ProfiledRawJointLeftPhysicalSiblingReceiver A)
    (leftOwner : (leftReceiver.1.memberController A false).Control)
    (rightTemplate : ProfiledRawJointRightPhysicalSiblingReceiver A)
    (packet : ExactPacket A strategy)
    (rightMove : ProfiledRawJointRightPhysicalSiblingMove A)
    (hstate : ExactBankAt A strategy key leftState)
    (hpacket : ExactBankAt A strategy key packet.successor) :
    ExactOwnerLiveAt A strategy key
      (ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryLiveState
        (Memory := ExactMemory A strategy) A strategy leftState leftReceiver
          leftOwner rightTemplate packet rightMove) := by
  exact
    ⟨⟨⟨hstate, by
          intro candidate hc
          cases Option.some.inj hc
          exact hpacket⟩,
        hpacket, hstate⟩,
      ⟨hstate, hpacket, hstate⟩⟩

/-- Every exact-table realization of an honest front is synchronized in all
of its stored bank coordinates, not only in its active outer register. -/
theorem RealizesOwnerFibreFrontContext.exactOwnerLiveAt
    {key : RootKey A strategy}
    {context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key}
    {live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy}
    (hrealizes :
      (exactEffectTable A strategy hwin key).RealizesOwnerFibreFrontContext
        A strategy hwin (exactInitialMemory A strategy) key context live) :
    ExactOwnerLiveAt A strategy key live := by
  rcases context with context | context
  · rcases hrealizes with ⟨leftMove, _hleftMove, rfl⟩
    apply ownerFibreRightEntryLiveState_exactOwnerLiveAt A strategy key
    · exact exactEffectTable_family_root_exactBankAt A strategy key
    · exact
        (exactEffectTable_family_root_exactBankAt A strategy key
          ).resolvePacket A strategy hwin key _ _
  · rcases hrealizes with ⟨rightMove, _hrightMove, rfl⟩
    apply ownerFibreLeftEntryLiveState_exactOwnerLiveAt A strategy key
    · exact exactEffectTable_family_root_exactBankAt A strategy key
    · exact
        (exactEffectTable_family_root_exactBankAt A strategy key
          ).resolvePacket A strategy hwin key _ _

/-- Every honest exact front enters the strengthened operationally selected
relation.  Thus the invariant used by simultaneous closure is not an
assumption about an arbitrary decoded pair: it holds at every actual
recurrent entry generated by the finite front. -/
theorem RealizesOwnerFibreFrontContext.exactSelectedAt
    {key : RootKey A strategy}
    {context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key}
    {live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy}
    (hrealizes :
      (exactEffectTable A strategy hwin key).RealizesOwnerFibreFrontContext
        A strategy hwin (exactInitialMemory A strategy) key context live) :
    ExactOwnerBoundarySelectedAt A strategy key live.1.1 live.1.2 := by
  let tables := (exactEffectTable A strategy hwin key).family A strategy key
  rcases context with context | context
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨rightMove, row, leftTemplate, input⟩
    rcases hrealizes with ⟨leftMove, hleftMove, rfl⟩
    let rightState :=
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
        A strategy (exactInitialMemory A strategy) key
    let rightReceiver :=
      initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove row
    let rightOwner := (rightMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
          (Memory := ExactMemory A strategy) A strategy :=
      (rightState, ⟨rightReceiver, rightOwner⟩, leftTemplate)
    have hactive :
        ExactRightBoundaryOperationalAt A strategy key data := by
      refine exactRightBoundaryOperationalAt_initial A strategy key rightState
        rightMove row leftTemplate
          (exactEffectTable_family_root_exactBankAt A strategy key)
            key.1.1 ?_ (.inl rightMove.1.source) ?_ ?_
      · rfl
      · exact hroot
      · simpa [rightState,
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root]
          using hinstalled
    simpa only [tables, rightState, rightReceiver, rightOwner, data] using
      exactRightEntry_selected_of_operational A strategy hwin key data input
        hactive leftMove hleftMove
  · rcases context with ⟨parameter, hinstalled, hroot⟩
    rcases parameter with ⟨leftMove, row, rightTemplate, input⟩
    rcases hrealizes with ⟨rightMove, hrightMove, rfl⟩
    let leftState :=
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
        A strategy (exactInitialMemory A strategy) key
    let leftReceiver :=
      initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove row
    let leftOwner := (leftMove.memberController A false).initial
    let data :
        ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
          (Memory := ExactMemory A strategy) A strategy :=
      (leftState, ⟨leftReceiver, leftOwner⟩, rightTemplate)
    have hactive :
        ExactLeftBoundaryOperationalAt A strategy key data := by
      refine exactLeftBoundaryOperationalAt_initial A strategy key leftState
        leftMove row rightTemplate
          (exactEffectTable_family_root_exactBankAt A strategy key)
            key.1.1 ?_ (.inr leftMove.1.source) ?_ ?_
      · rfl
      · exact hroot
      · simpa [leftState,
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root]
          using hinstalled
    simpa only [tables, leftState, leftReceiver, leftOwner, data] using
      exactLeftEntry_selected_of_operational A strategy hwin key data input
        hactive rightMove hrightMove

/-- Honest front realization establishes the complete invariant needed for
strict as well as simultaneous recurrent rounds.  The fibre-validity fields
are vacuous at entry; the unique staged endpoint is anchored by construction. -/
theorem RealizesOwnerFibreFrontContext.exactOperationalAt
    {key : RootKey A strategy}
    {context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key}
    {live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy}
    (hrealizes :
      (exactEffectTable A strategy hwin key).RealizesOwnerFibreFrontContext
        A strategy hwin (exactInitialMemory A strategy) key context live) :
    ExactOwnerFibreBoundaryOperationalAt A strategy key live.1.1 live.1.2 := by
  have hselected := hrealizes.exactSelectedAt A strategy hwin
  have hexact := hrealizes.exactOwnerLiveAt A strategy hwin
  rcases context with context | context
  · rcases hrealizes with ⟨leftMove, _hleftMove, rfl⟩
    refine
      { selected := hselected
        oneValid := True.intro
        twoValid := True.intro
        stagedAnchor := ?_
        exact := hexact }
    constructor
    · intro staged hstaged
      change Sum.inl (Sum.inr _) = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged
    · intro staged hstaged
      change Sum.inl (Sum.inl _) = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged
      rfl
  · rcases hrealizes with ⟨rightMove, _hrightMove, rfl⟩
    refine
      { selected := hselected
        oneValid := True.intro
        twoValid := True.intro
        stagedAnchor := ?_
        exact := hexact }
    constructor
    · intro staged hstaged
      change Sum.inl (Sum.inl _) = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged
      rfl
    · intro staged hstaged
      change Sum.inl (Sum.inr _) = Sum.inl (Sum.inl staged) at hstaged
      cases hstaged

/-- Every table realization of an honest front starts in one of the two
decoded entry shapes.  This is a purely structural statement and therefore
does not require the table memory to be finite. -/
theorem RealizesOwnerFibreFrontContext.decodes
    {Memory : Type m}
    {initialMemory : RootKey A strategy → Memory}
    {key : RootKey A strategy}
    {table :
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
        (Memory := Memory) A strategy key}
    {context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key}
    {live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := Memory) A strategy}
    (hrealizes : table.RealizesOwnerFibreFrontContext A strategy hwin
      initialMemory key context live) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
      (Memory := Memory) A strategy live.1.1 live.1.2 := by
  rcases context with context | context
  · rcases hrealizes with ⟨leftMove, hleftMove, rfl⟩
    exact
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryLiveState_decodes
        (Memory := Memory) A strategy _ _ _ _ _ leftMove hleftMove
  · rcases hrealizes with ⟨rightMove, hrightMove, rfl⟩
    exact
      ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryLiveState_decodes
        (Memory := Memory) A strategy _ _ _ _ _ rightMove hrightMove

/-- The exact honest-front initializer simultaneously supplies a live state,
the structural decoder, and exact semantic-memory alignment for every bank
coordinate stored at either endpoint. -/
theorem exactEffectTable_ownerFibreInitialState_live_decodes_exactOwnerLiveAt
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ live :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := ExactMemory A strategy) A strategy,
      ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context = some live ∧
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
          (Memory := ExactMemory A strategy) A strategy live.1.1 live.1.2 ∧
        ExactOwnerLiveAt A strategy key live := by
  classical
  have hexists : ∃ live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy,
      (exactEffectTable A strategy hwin key).RealizesOwnerFibreFrontContext
        A strategy hwin (exactInitialMemory A strategy) key context live :=
    (exactEffectTable_effectEnrichedValidAt A strategy hwin key
      ).ownerFibreFrontContext_realizes A strategy hwin
        (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context
  let live := Classical.choose hexists
  have hrealizes :
      (exactEffectTable A strategy hwin key).RealizesOwnerFibreFrontContext
        A strategy hwin (exactInitialMemory A strategy) key context live :=
    Classical.choose_spec hexists
  refine ⟨live, ?_, hrealizes.decodes A strategy hwin,
    hrealizes.exactOwnerLiveAt A strategy hwin⟩
  unfold ownerFibreInitialStateUnrestricted
  rw [dif_pos hexists]

/-- Every finite prefix from an honest exact-table entry preserves exact
semantic alignment simultaneously in every dormant and active bank
coordinate. -/
theorem exactEffectTable_ownerFibreInitialState_liveStateAt_exactOwnerLiveAt
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key)
    (live :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
        (Memory := ExactMemory A strategy) A strategy)
    (hinitial :
      ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context = some live)
    (node : TreeNode
      (ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
        (In₁ := In₁) (In₂ := In₂))) :
    ExactOwnerLiveAt A strategy key
      (((exactEffectTable A strategy hwin key).family A strategy key
        ).ownerFibreSafetyLiveStateAt A strategy hwin live node) := by
  obtain ⟨chosen, hchosen, _hdecodes, hexact⟩ :=
    exactEffectTable_ownerFibreInitialState_live_decodes_exactOwnerLiveAt A
      strategy hwin key context
  have heq : chosen = live := Option.some.inj (hchosen.symm.trans hinitial)
  subst chosen
  exact hexact.liveStateAt A strategy hwin key live node

/-- The exact perfect-recall table never enters the rejecting sink at an
honest front.  Moreover, the selected live entry already satisfies the
structural decoder, so the time-zero part of `ExactOwnerTraceObligations` is
fully discharged. -/
theorem exactEffectTable_ownerFibreInitialState_live_decodes
    (key : RootKey A strategy)
    (context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key) :
    ∃ live :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := ExactMemory A strategy) A strategy,
      ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context = some live ∧
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
          (Memory := ExactMemory A strategy) A strategy live.1.1 live.1.2 := by
  obtain ⟨live, hinitial, hdecodes, _hexact⟩ :=
    exactEffectTable_ownerFibreInitialState_live_decodes_exactOwnerLiveAt
      A strategy hwin key context
  exact ⟨live, hinitial, hdecodes⟩

/-- The two literal semantic obligations left for the exact perfect-recall
table: every honest-front initializer is live, every resulting prefix decodes,
and every emitted word is accepted from its exact entry DPA state. -/
def ExactOwnerTraceObligations (key : RootKey A strategy) : Prop :=
  ∀ context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key,
    ∃ live :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := ExactMemory A strategy) A strategy,
      ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context = some live ∧
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        ∀ n,
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := ExactMemory A strategy) A strategy
            ((exactEffectTable A strategy hwin key).family A strategy key
              |>.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch n)).1.1
            ((exactEffectTable A strategy hwin key).family A strategy key
              |>.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch n)).1.2) ∧
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        A.AcceptsFrom live.2
          ((exactEffectTable A strategy hwin key).family A strategy key
            |>.ownerFibreSafetyWord A strategy hwin live branch))

/-- After live initialization and time-zero decoding have been proved, the
remaining exact obligation starts strictly after the first kernel step. -/
def ExactOwnerContinuationObligations (key : RootKey A strategy) : Prop :=
  ∀ context :
      ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy
        key,
    ∀ live :
        ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
          (Memory := ExactMemory A strategy) A strategy,
      ownerFibreInitialStateUnrestricted A strategy hwin
          (exactInitialMemory A strategy) key
          (exactEffectTable A strategy hwin key) context = some live →
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        ∀ n,
          ProfiledRawJointRecurrentFiniteMemoryOwnerFibreDecodes
            (Memory := ExactMemory A strategy) A strategy
            ((exactEffectTable A strategy hwin key).family A strategy key
              |>.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch (n + 1))).1.1
            ((exactEffectTable A strategy hwin key).family A strategy key
              |>.ownerFibreSafetyLiveStateAt A strategy hwin live
                (branchNode branch (n + 1))).1.2) ∧
      (∀ branch : Nat → Direction (In₁ := In₁) (In₂ := In₂),
        A.AcceptsFrom live.2
          ((exactEffectTable A strategy hwin key).family A strategy key
            |>.ownerFibreSafetyWord A strategy hwin live branch))

/-- Exact front realization removes precisely the zero-prefix decoder case.
Consequently the complete owner target is equivalent to positive-time
decoder preservation together with literal-word acceptance. -/
theorem exactOwnerTraceObligations_iff_continuation
    (key : RootKey A strategy) :
    ExactOwnerTraceObligations A strategy hwin key ↔
      ExactOwnerContinuationObligations A strategy hwin key := by
  constructor
  · intro hobligations context live hinitial
    obtain ⟨chosen, hchosen, hdecodes, haccepts⟩ := hobligations context
    have hlive : chosen = live := Option.some.inj (hchosen.symm.trans hinitial)
    subst chosen
    exact ⟨fun branch n ↦ hdecodes branch (n + 1), haccepts⟩
  · intro hcontinuation context
    obtain ⟨live, hinitial, hzero⟩ :=
      exactEffectTable_ownerFibreInitialState_live_decodes A strategy hwin key
        context
    obtain ⟨hpositive, haccepts⟩ := hcontinuation context live hinitial
    refine ⟨live, hinitial, ?_, haccepts⟩
    intro branch n
    cases n with
    | zero =>
        simpa only [branchNode, List.take_zero,
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreSafetyLiveStateAt]
          using hzero
    | succ n => exact hpositive branch n

/-- Exact owner safety contains no further hidden condition: it is equivalent
to `ExactOwnerTraceObligations`. -/
theorem exactEffectTable_enrichedOwnerSafeUnrestricted_iff_traceObligations
    (key : RootKey A strategy) :
    EnrichedOwnerSafeUnrestricted A strategy hwin
        (exactInitialMemory A strategy) key
        (exactEffectTable A strategy hwin key) ↔
      ExactOwnerTraceObligations A strategy hwin key := by
  unfold EnrichedOwnerSafeUnrestricted ExactOwnerTraceObligations
  constructor
  · intro hsafe context
    exact
      (((exactEffectTable A strategy hwin key).family A strategy key
        |>.ownerFibreSafe_iff_exists_live_decodes_and_acceptsFrom A strategy
          hwin
          (ownerFibreInitialStateUnrestricted A strategy hwin
            (exactInitialMemory A strategy) key
            (exactEffectTable A strategy hwin key) context))).mp
        (hsafe context)
  · intro hobligations context
    exact
      (((exactEffectTable A strategy hwin key).family A strategy key
        |>.ownerFibreSafe_iff_exists_live_decodes_and_acceptsFrom A strategy
          hwin
          (ownerFibreInitialStateUnrestricted A strategy hwin
            (exactInitialMemory A strategy) key
            (exactEffectTable A strategy hwin key) context))).mpr
        (hobligations context)

/-- Combining the exact table construction with the owner characterization
reduces the complete pre-regularization checker to the literal trace
obligations alone. -/
theorem exactEffectTable_effectEnrichedChecksUnrestricted_iff_traceObligations
    (key : RootKey A strategy) :
    EffectEnrichedChecksUnrestricted A strategy hwin
        (exactInitialMemory A strategy) key
        (exactEffectTable A strategy hwin key) ↔
      ExactOwnerTraceObligations A strategy hwin key := by
  rw [exactEffectTable_effectEnrichedChecksUnrestricted_iff_ownerSafe A
    strategy hwin key,
    exactEffectTable_enrichedOwnerSafeUnrestricted_iff_traceObligations A
      strategy hwin key]

end
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

end

end DetParityAutomaton

end DistributedSynthesis
