/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableOwnerFibreSafetyAutomaton
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelectionOwnerFibreHonestEntry
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedPhysicalCompatibleCommonActionMemory

/-!
# A selection-free enriched verifier at one root key

For one fixed root key this automaton existentially chooses one finite
augmented successor table.  Its universal branches then perform two checks on
that same table:

* a policy branch checks node-local physical-compatible realization and the
  forward code-parity objective for every public child-code request;
* one owner branch for every selection-independent honest-front context runs
  every input/graph direction through the literal augmented owner-fibre
  kernel, with decoder failure represented by the absorbing rejecting state.

The direction type always contains a policy branch, represented by `none`,
even when the honest-front context type is empty.  Thus emptiness of that
context type cannot make forward legality or parity vacuous.  The chosen
table is stored in every below-root state and is never replaced.
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
variable [Fintype Memory]

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

private abbrev ActualDirection :=
  ProfiledRawJointActualDirection (I := Unit) (In₁ := In₁) (In₂ := In₂)

private abbrev OneSidedState :=
  ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)

private abbrev LinkedMove :=
  SourceFreeBeliefParentLinkedMove
    (Direction := ActualDirection (In₁ := In₁) (In₂ := In₂))
    (Move := ProfiledRawJointLambdaFamilyMove A (I := Unit))
    (Annotation := PhysicalAnnotation A)

private abbrev PolicyDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :=
  sourceFreeBeliefParentLinkedCodeParityDPA
    (Annotation := PhysicalAnnotation A)
    (profiledRawJointOneSidedCodeParityDPA A initialCode)

private abbrev PolicyValid :=
  sourceFreeBeliefParentLinkedValid
    (ProfiledRawJointOneSidedProvenanceValid A strategy)
    (ProfiledRawJointOneSidedPhysicalCompatibleParentLinkValid A strategy hwin)

private noncomputable abbrev PolicyNext :
    LinkedCode A →
      LinkedMove A (In₁ := In₁) (In₂ := In₂) →
        LinkedCode A → LinkedCode A :=
  sourceFreeBeliefFiniteCodeNext
    (sourceFreeBeliefParentLinkedNext (profiledRawJointOneSidedNext A))

private abbrev FixedTable (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable
    (Memory := Memory) A strategy key

private abbrev PolicyState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyState
    (Memory := Memory) A key.1.1

private abbrev SafetyDirection :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyDirection
    (In₁ := In₁) (In₂ := In₂)

private abbrev SafetyState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
    (Memory := Memory) A strategy

private abbrev LiveState :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyLiveState
    (Memory := Memory) A strategy

private abbrev ExactState :=
  ProfiledRawJointOneSidedPhysicalExactCommonActionMemory A strategy

private abbrev Context (key : RootKey A strategy) :=
  ProfiledRawJointRecurrentFiniteMemoryOwnerFibreFrontContextAt A strategy key

/-- One universal direction contains all coordinates required below either
kind of root branch.  `context = none` selects the forward-policy check;
`some context` selects that honest owner-fibre entry.  Below the root the
irrelevant coordinates are ignored. -/
structure
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedDirection
    (key : RootKey A strategy) where
  context : Option (Context A strategy key)
  policyChild : LinkedCode A
  safety : SafetyDirection (In₁ := In₁) (In₂ := In₂)
  deriving Fintype

/-- The table chosen at the fresh root is carried unchanged in either check
mode. -/
inductive
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedState
    (key : RootKey A strategy) where
  | root
  | policy (table : FixedTable (Memory := Memory) A strategy key)
      (state : PolicyState (Memory := Memory) A strategy key)
  | owner (table : FixedTable (Memory := Memory) A strategy key)
      (state : SafetyState (Memory := Memory) A strategy)
  deriving Fintype

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

variable
  (initialMemory : RootKey A strategy → Memory)
  (key : RootKey A strategy)
  (table : FixedTable (Memory := Memory) A strategy key)

private abbrev TableFamily :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection
    (Memory := Memory) A strategy

/-- The single fixed-key table, extended only by identity tables at irrelevant
keys so that it can drive the already typed bank kernel. -/
def family : TableFamily (Memory := Memory) A strategy :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.singletonAt
    (Memory := Memory) A strategy key table

/-- The exact node-local transition obligation of the forward policy
automaton.  The raw move is a proposition-level witness and is not stored in
the finite enriched state. -/
def exactStep
    (state : ExactState A strategy)
    (childCode : LinkedCode A) : ExactState A strategy :=
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    state.1.1 state.1.2
  let actual := profiledRawJointOneSidedPhysicalActualOfChildCode A
    (state.1.1.code A, state.1.2) move childCode
  let child := state.1.1.step A actual
  let annotation :=
    profiledRawJointOneSidedPhysicalAnnotationAdvance A strategy hwin
      state.1.1 state.1.2 actual
  ⟨(child, annotation),
    profiledRawJointOneSidedPhysicalAnnotationAdvance_compatible A strategy
      hwin state.1.1 state.1.2 actual⟩

/-- The public data of the exact finite-tag child are precisely the
finite-code successor selected from the current exact source. -/
theorem exactStep_publicCode
    (state : ExactState A strategy)
    (childCode : LinkedCode A) :
    let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
      state.1.1 state.1.2
    ((exactStep A strategy hwin state childCode).1.1.code A,
        (exactStep A strategy hwin state childCode).1.2) =
      PolicyNext A (In₁ := In₁) (In₂ := In₂)
        (state.1.1.code A, state.1.2) move childCode := by
  dsimp only
  unfold exactStep PolicyNext
  dsimp only
  apply Prod.ext
  · rw [ProfiledRawJointOneSidedSemanticState.step_code]
    rfl
  · rfl

/-- Exact semantic/annotation state obtained from one root realization along
a finite public child-code history. -/
def exactStateAt
    (initial : ExactState A strategy)
    (node : TreeNode (LinkedCode A)) : ExactState A strategy :=
  node.foldl (exactStep A strategy hwin) initial

theorem exactStateAt_append
    (initial : ExactState A strategy)
    (node : TreeNode (LinkedCode A))
    (childCode : LinkedCode A) :
    exactStateAt A strategy hwin initial (node ++ [childCode]) =
      exactStep A strategy hwin
        (exactStateAt A strategy hwin initial node) childCode := by
  simp [exactStateAt, List.foldl_append]

/-- Exact states whose public data are the fixed admissible root key. -/
def ExactAtKey (state : ExactState A strategy) : Prop :=
  state.1.1.code A = key.1.1 ∧ state.1.2 = key.1.2

/-- Fix one proof-side exact realization of the admissible public root key.
The choice is made once per key; it is not observable by the policy table. -/
def canonicalExactInitial : ExactState A strategy :=
  ⟨(profiledRawJointOneSidedPhysicalCompatibleBankSource A strategy key,
      key.1.2),
    profiledRawJointOneSidedPhysicalCompatibleBankSource_compatible A strategy
      key⟩

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem canonicalExactInitial_code :
    (canonicalExactInitial A strategy key).1.1.code A = key.1.1 :=
  profiledRawJointOneSidedPhysicalCompatibleBankSource_code A strategy key

@[simp] theorem canonicalExactInitial_annotation :
    (canonicalExactInitial A strategy key).1.2 = key.1.2 :=
  rfl

theorem canonicalExactInitial_atKey :
    ExactAtKey A strategy key (canonicalExactInitial A strategy key) :=
  ⟨canonicalExactInitial_code A strategy key,
    canonicalExactInitial_annotation A strategy key⟩

end

/-- Canonical belief cell of a table state: all finite child-code histories
of one fixed exact root realization which the table merges into that
augmented state.  Quantifying over every unrelated exact realization of the
same public root would impose an unnecessary root-uniformity hypothesis. -/
def CanonicalBelief
    (state : PolicyState (Memory := Memory) A strategy key)
    (exact : ExactState A strategy) : Prop :=
  ∃ node : TreeNode (LinkedCode A),
    sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
          (PolicyDPA A key.1.1) key.1 (initialMemory key) table node =
        state ∧
      exactStateAt A strategy hwin (canonicalExactInitial A strategy key)
        node = exact

/-- A canonical table cell is nonempty and all of its exact sources carry
the public code and installed annotation advertised by that table state. -/
def CanonicalBeliefAt
    (state : PolicyState (Memory := Memory) A strategy key) : Prop :=
  (∃ exact, table.CanonicalBelief A strategy hwin initialMemory key state
      exact) ∧
    ∀ exact,
      table.CanonicalBelief A strategy hwin initialMemory key state exact →
        exact.1.1.code A = state.1.1.1 ∧
          exact.1.2 = state.1.1.2

/-- One complete linked move is common to every exact history merged into
the current finite table state. -/
def CanonicalCommonMove
    (state : PolicyState (Memory := Memory) A strategy key)
    (move : LinkedMove A (In₁ := In₁) (In₂ := In₂)) : Prop :=
  ∀ exact,
    table.CanonicalBelief A strategy hwin initialMemory key state exact →
      profiledRawJointOneSidedSemanticLinkedMove A strategy hwin exact.1.1
          exact.1.2 =
        move

/-- Finite public effect of the (possibly infinite) raw linked move induced
by one exact source.  Its domain and codomain are finite; it forgets all raw
move distinctions which have the same child-code/DPA behavior. -/
def ExactPublicSuccessorSignature
    (state : PolicyState (Memory := Memory) A strategy key)
    (exact : ExactState A strategy) :
    LinkedCode A → LinkedCode A × (PolicyDPA A key.1.1).State :=
  let move := profiledRawJointOneSidedSemanticLinkedMove A strategy hwin
    exact.1.1 exact.1.2
  fun childCode ↦
    sourceFreeBeliefCodeParityControllerNext
      (PolicyDPA A key.1.1) state.1 move
      (PolicyNext A (In₁ := In₁) (In₂ := In₂)
        state.1.1 move childCode)

/-- Finite public effect literally stored by the successor table at one
augmented state. -/
def StoredPublicSuccessorSignature
    (state : PolicyState (Memory := Memory) A strategy key) :
    LinkedCode A → LinkedCode A × (PolicyDPA A key.1.1).State :=
  fun childCode ↦ (table.successor state childCode).1

/-- Every exact history merged into a canonical table cell has the same
finite public successor signature, namely the row stored by the table.  This
is strictly the effect-level condition to test before retaining equality of
the generally infinite raw moves. -/
def CanonicalPublicSuccessorCoherent
    (state : PolicyState (Memory := Memory) A strategy key) : Prop :=
  ∀ exact,
    table.CanonicalBelief A strategy hwin initialMemory key state exact →
      ExactPublicSuccessorSignature A strategy hwin key state exact =
        table.StoredPublicSuccessorSignature A strategy key state

def LocallyValid
    (state : PolicyState (Memory := Memory) A strategy key) : Prop :=
  table.CanonicalBeliefAt A strategy hwin initialMemory key state ∧
    ∃ move : LinkedMove A (In₁ := In₁) (In₂ := In₂),
      table.CanonicalCommonMove A strategy hwin initialMemory key state move ∧
        PolicyValid A strategy hwin state.1.1 move ∧
        ∀ childCode : LinkedCode A,
          (table.successor state childCode).1 =
            sourceFreeBeliefCodeParityControllerNext
              (PolicyDPA A key.1.1) state.1 move
              (PolicyNext A (In₁ := In₁) (In₂ := In₂)
              state.1.1 move childCode)

omit [Fintype Memory] in
/-- Strong common raw-move coherence implies finite public-effect coherence.
The converse is intentionally not asserted. -/
theorem LocallyValid.canonicalPublicSuccessorCoherent
    (state : PolicyState (Memory := Memory) A strategy key)
    (hvalid : table.LocallyValid A strategy hwin initialMemory key state) :
    table.CanonicalPublicSuccessorCoherent A strategy hwin initialMemory key
      state := by
  rcases hvalid with
    ⟨_beliefAt, move, hcommon, _hmove, hsuccessor⟩
  intro exact hexact
  funext childCode
  unfold ExactPublicSuccessorSignature StoredPublicSuccessorSignature
  rw [hcommon exact hexact]
  exact (hsuccessor childCode).symm

/-! ## Raw table realization of selection-independent front contexts -/

/-- A raw fixed-key table realizes a front context when its resolved packet
installs the opposite move needed to construct the exact live seam state. -/
def RealizesOwnerFibreFrontContext
    (context : Context A strategy key)
    (state : LiveState (Memory := Memory) A strategy) : Prop :=
  match context with
  | .inl context =>
      let rightMove := context.1.installedMove
      let rightState :=
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
          A strategy initialMemory key
      let rightReceiver :=
        initialProfiledRawJointRightPhysicalSiblingReceiver A rightMove
          context.1.row
      let rightOwner := (rightMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryRightBoundaryData
            (Memory := Memory) A strategy :=
        (rightState, ⟨rightReceiver, rightOwner⟩,
          context.1.dormantTemplate)
      let packet := table.family A strategy key |>.resolvePacket A strategy
        hwin rightState
          (data.target (Memory := Memory) A strategy context.1.closingInput)
      ∃ leftMove : ProfiledRawJointLeftPhysicalSiblingMove A,
        packet.successor.2.1.1.2.2 = some leftMove ∧
          state =
            ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreRightEntryLiveState
              (Memory := Memory) A strategy rightState rightReceiver rightOwner
              context.1.dormantTemplate packet leftMove
  | .inr context =>
      let leftMove := context.1.installedMove
      let leftState :=
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.root
          A strategy initialMemory key
      let leftReceiver :=
        initialProfiledRawJointLeftPhysicalSiblingReceiver A leftMove
          context.1.row
      let leftOwner := (leftMove.memberController A false).initial
      let data :
          ProfiledRawJointRecurrentFiniteMemoryLeftBoundaryData
            (Memory := Memory) A strategy :=
        (leftState, ⟨leftReceiver, leftOwner⟩,
          context.1.dormantTemplate)
      let packet := table.family A strategy key |>.resolvePacket A strategy
        hwin leftState
          (data.target (Memory := Memory) A strategy context.1.closingInput)
      ∃ rightMove : ProfiledRawJointRightPhysicalSiblingMove A,
        packet.successor.2.1.1.2.1 = some rightMove ∧
          state =
            ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreLeftEntryLiveState
              (Memory := Memory) A strategy leftState leftReceiver leftOwner
              context.1.dormantTemplate packet rightMove

omit [Fintype Memory] in
/-- Total initial monitor state for one context.  Missing packet realization
is sent directly to the rejecting sink. -/
def ownerFibreInitialState
    (context : Context A strategy key) :
    ProfiledRawJointRecurrentFiniteMemoryOwnerFibreSafetyState
      (Memory := Memory) A strategy := by
  classical
  exact if h : ∃ state,
      table.RealizesOwnerFibreFrontContext A strategy hwin initialMemory key
        context state then
    some (Classical.choose h)
  else
    none

/-! ## The three obligations checked by the enriched branches -/

/-- Strong forward legality: every table-reachable state carries its
canonical nonempty belief cell, one move common to the whole cell, and the
exact finite public successor map induced by that move. -/
def EnrichedValidAt : Prop :=
  ∀ node : TreeNode (LinkedCode A),
    let state :=
      sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
        (PolicyDPA A key.1.1) key.1 (initialMemory key) table node
    table.LocallyValid A strategy hwin initialMemory key state

/-- Forward parity of the same finite table. -/
def EnrichedForwardAccepts : Prop :=
  table.Accepts (PolicyDPA A key.1.1) key.1 (initialMemory key)

section
omit [Fintype Memory]

/-- Every selection-independent honest-front context is realized and its
complete guarded owner-fibre unfolding is accepting.  Failure to realize a
context yields `none`, hence fails this parity obligation. -/
def EnrichedOwnerSafe : Prop :=
  ∀ context : Context A strategy key,
    (table.family A strategy key).OwnerFibreSafe A strategy hwin
      (table.ownerFibreInitialState A strategy hwin initialMemory key context)

/-- Exact conjunction represented by the two classes of universal branches. -/
def EnrichedChecks : Prop :=
  table.EnrichedValidAt A strategy hwin initialMemory key ∧
    table.EnrichedForwardAccepts A strategy initialMemory key ∧
    table.EnrichedOwnerSafe A strategy hwin initialMemory key

/-- The strong common-action condition in `EnrichedValidAt` implies the
ordinary local validity needed to certify the finite successor table. -/
theorem EnrichedValidAt.toTransitionTableValidAt
    (hvalid : table.EnrichedValidAt A strategy hwin initialMemory key) :
    table.ValidAt (PolicyDPA A key.1.1) key.1 (initialMemory key)
      (PolicyValid A strategy hwin)
      (PolicyNext A (In₁ := In₁) (In₂ := In₂)) := by
  intro node
  rcases hvalid node with ⟨_beliefAt, move, _common, hmove, hsuccessor⟩
  exact ⟨move, hmove, hsuccessor⟩

end

/-- Once its forward branches accept, the chosen fixed-key table becomes the
existing certified augmented physical-compatible policy. -/
def toFiniteMemoryPolicy
    (hvalid : table.EnrichedValidAt A strategy hwin initialMemory key)
    (haccepts : table.EnrichedForwardAccepts A strategy initialMemory key) :
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicy
      (Memory := Memory) A strategy hwin (initialMemory key) key.1.1 key.1.2 :=
  SourceFreeBeliefCodeParityFiniteMemoryTransitionTable.toFiniteMemoryPolicy
    (PolicyDPA A key.1.1) key.1 (initialMemory key)
    (PolicyValid A strategy hwin)
    (PolicyNext A (In₁ := In₁) (In₂ := In₂))
    table
    (hvalid.toTransitionTableValidAt A strategy hwin initialMemory key)
    haccepts

end ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

private abbrev EnrichedDirection (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedDirection
    A strategy key

private abbrev EnrichedState (key : RootKey A strategy) :=
  ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedState
    (Memory := Memory) A strategy key

/-- Canonical enriched direction used to traverse the forward-policy
subtree. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
    (key : RootKey A strategy) (childCode : LinkedCode A) :
    EnrichedDirection A strategy key :=
  ⟨none, childCode, ((default, default), .both)⟩

/-- Canonical enriched direction used to traverse one owner-fibre subtree. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
    (key : RootKey A strategy) (context : Context A strategy key)
    (direction : SafetyDirection (In₁ := In₁) (In₂ := In₂)) :
    EnrichedDirection A strategy key :=
  ⟨some context, key.1, direction⟩

/-- Enter the policy mode once and then follow a finite child-code node. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
    (key : RootKey A strategy) (node : TreeNode (LinkedCode A)) :
    TreeNode (EnrichedDirection A strategy key) :=
  profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
      A strategy key key.1 ::
    node.map
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
        A strategy key)

/-- Enter one owner context once and then follow a finite environment node. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
    (key : RootKey A strategy) (context : Context A strategy key)
    (node : TreeNode
      (SafetyDirection (In₁ := In₁) (In₂ := In₂))) :
    TreeNode (EnrichedDirection A strategy key) :=
  profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
      A strategy key context ((default, default), .both) ::
    node.map
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
        A strategy key context)

private theorem branchNode_map
    {X Y : Type*} (f : X → Y) (branch : Nat → X) : ∀ n,
    branchNode (fun k ↦ f (branch k)) n =
      (branchNode branch n).map f := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode (fun k ↦ f (branch k)) (n + 1) =
          branchNode (fun k ↦ f (branch k)) n ++ [f (branch n)] from rfl,
        show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        ih]
      simp

/-- One selection-free enriched automaton for a fixed root key.  The fresh
root chooses a finite table once.  Universal directions then launch the
forward checker and every honest owner-fibre context; below the root they
range over all public child codes and all physical environment moves. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy) :
    InputFreeRunParityTreeAutomaton
      (EnrichedDirection A strategy key) where
  State := EnrichedState (Memory := Memory) A strategy key
  stateFinite := inferInstance
  initial := .root
  delta state _ children :=
    match state with
    | .root =>
        ∃ table : FixedTable (Memory := Memory) A strategy key,
          ∀ direction,
            children direction =
              match direction.context with
              | none =>
                  .policy table
                    ((key.1, (PolicyDPA A key.1.1).initial),
                      initialMemory key)
              | some context =>
                  .owner table
                    (table.ownerFibreInitialState A strategy hwin
                      initialMemory key context)
    | .policy table policyState =>
        table.LocallyValid A strategy hwin initialMemory key policyState ∧
          ∀ direction,
            children direction =
              .policy table
                (table.successor policyState direction.policyChild)
    | .owner table safetyState =>
        ∀ direction,
          children direction =
            .owner table
              ((table.family A strategy key).ownerFibreSafetyStep A strategy
                hwin safetyState direction.safety)
  priority state :=
    match state with
    | .root => 0
    | .policy _ policyState =>
        (PolicyDPA A key.1.1).priority policyState.1.2
    | .owner _ safetyState =>
        ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
          (Memory := Memory) A strategy safetyState

/-- The literal finite successor function generated by one fixed table.  The
table chosen at the root is retained in every descendant state. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key) :
    EnrichedState (Memory := Memory) A strategy key →
      EnrichedDirection A strategy key →
        EnrichedState (Memory := Memory) A strategy key
  | .root, direction =>
      match direction.context with
      | none =>
          .policy table
            ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
      | some context =>
          .owner table
            (table.ownerFibreInitialState A strategy hwin initialMemory key
              context)
  | .policy current currentState, direction =>
      .policy current
        (current.successor currentState direction.policyChild)
  | .owner current currentState, direction =>
      .owner current
        ((current.family A strategy key).ownerFibreSafetyStep A strategy hwin
          currentState direction.safety)

/-- Finite run obtained by folding the literal successor function of one
fixed table from the fresh root. -/
def profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (node : TreeNode (EnrichedDirection A strategy key)) :
    EnrichedState (Memory := Memory) A strategy key :=
  node.foldl
    (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
      (Memory := Memory) A strategy hwin initialMemory key table)
    .root

private theorem enrichedTableSuccessor_fold_policy
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (state : PolicyState (Memory := Memory) A strategy key) :
    ∀ node : TreeNode (EnrichedDirection A strategy key),
      node.foldl
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
            (Memory := Memory) A strategy hwin initialMemory key table)
          (.policy table state) =
        .policy table
          ((node.map fun direction ↦ direction.policyChild).foldl
            table.successor state) := by
  intro node
  induction node generalizing state with
  | nil => rfl
  | cons direction node ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih _

private theorem enrichedTableSuccessor_fold_owner
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (state : SafetyState (Memory := Memory) A strategy) :
    ∀ node : TreeNode (EnrichedDirection A strategy key),
      node.foldl
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
            (Memory := Memory) A strategy hwin initialMemory key table)
          (.owner table state) =
        .owner table
          ((node.map fun direction ↦ direction.safety).foldl
            ((table.family A strategy key).ownerFibreSafetyStep A strategy hwin)
            state) := by
  intro node
  induction node generalizing state with
  | nil => rfl
  | cons direction node ih =>
      simp only [List.foldl_cons, List.map_cons]
      exact ih _

theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_policy
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (first : EnrichedDirection A strategy key)
    (hcontext : first.context = none)
    (node : TreeNode (EnrichedDirection A strategy key)) :
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
        (Memory := Memory) A strategy hwin initialMemory key table
          (first :: node) =
      .policy table
        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
          (PolicyDPA A key.1.1) key.1 (initialMemory key) table
          (node.map fun direction ↦ direction.policyChild)) := by
  rw [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun,
    List.foldl_cons,
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor,
    hcontext, enrichedTableSuccessor_fold_policy]
  rfl

theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_owner
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (first : EnrichedDirection A strategy key)
    (context : Context A strategy key)
    (hcontext : first.context = some context)
    (node : TreeNode (EnrichedDirection A strategy key)) :
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
        (Memory := Memory) A strategy hwin initialMemory key table
          (first :: node) =
      .owner table
        ((table.family A strategy key).ownerFibreSafetyStateAt A strategy hwin
          (table.ownerFibreInitialState A strategy hwin initialMemory key
            context)
          (node.map fun direction ↦ direction.safety)) := by
  rw [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun,
    List.foldl_cons,
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor,
    hcontext, enrichedTableSuccessor_fold_owner]
  rfl

/-- Every rational policy of the enriched automaton exposes one finite table
at its root, and every first-level branch carries exactly that same table. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_exists_rootTable
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy) :
    ∃ table : FixedTable (Memory := Memory) A strategy key,
      ∀ direction,
        policy.successor .root direction =
          match direction.context with
          | none =>
              .policy table
                ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
          | some context =>
              .owner table
                (table.ownerFibreInitialState A strategy hwin initialMemory
                  key context) := by
  have hlegal := policy.legal_at []
  rw [policy.accepts.1.1] at hlegal
  simpa only [
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton]
    using hlegal

/-- Below the policy root child, an enriched rational policy carrying
`table` follows the literal finite successor-table fold. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_policy_run
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)) :
    ∀ node : TreeNode (LinkedCode A),
      policy.run
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
            A strategy key node) =
        .policy table
          (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
            (PolicyDPA A key.1.1) key.1 (initialMemory key) table node) := by
  intro node
  induction node using List.reverseRecOn with
  | nil =>
      let first :=
        profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
          A strategy key key.1
      change policy.run ([] ++ [first]) = _
      rw [← policy.successor_at [] first, policy.accepts.1.1]
      change policy.successor .root first = _
      rw [hroot]
      rfl
  | append_singleton node childCode ih =>
      let direction :=
        profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
          A strategy key childCode
      have hnode :
          profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
              A strategy key (node ++ [childCode]) =
            profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
                A strategy key node ++
              [direction] := by
        simp [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode,
          direction, List.map_append]
      rw [hnode, ← policy.successor_at, ih]
      have hlegal := policy.legal_at
        (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
          A strategy key node)
      rw [ih] at hlegal
      change
        table.LocallyValid A strategy hwin initialMemory key
              (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                (PolicyDPA A key.1.1) key.1 (initialMemory key) table node) ∧
          ∀ nextDirection,
            policy.successor
                (.policy table
                  (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                    (PolicyDPA A key.1.1) key.1 (initialMemory key) table
                      node))
                nextDirection =
              .policy table
                (table.successor
                  (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                    (PolicyDPA A key.1.1) key.1 (initialMemory key) table node)
                  nextDirection.policyChild) at hlegal
      rw [hlegal.2 direction]
      congr 1
      rw [sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt_append]
      rfl

/-- Below an owner-context root child, the same enriched rational policy
follows the literal rejecting-sink owner-fibre monitor. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_owner_run
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context))
    (context : Context A strategy key) :
    ∀ node : TreeNode
        (SafetyDirection (In₁ := In₁) (In₂ := In₂)),
      policy.run
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
            A strategy key context node) =
        .owner table
          ((table.family A strategy key).ownerFibreSafetyStateAt A strategy
            hwin
            (table.ownerFibreInitialState A strategy hwin initialMemory key
              context)
            node) := by
  intro node
  induction node using List.reverseRecOn with
  | nil =>
      let first :=
        profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
          A strategy key context ((default, default), .both)
      change policy.run ([] ++ [first]) = _
      rw [← policy.successor_at [] first, policy.accepts.1.1]
      change policy.successor .root first = _
      rw [hroot]
      rfl
  | append_singleton node safetyDirection ih =>
      let direction :=
        profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
          A strategy key context safetyDirection
      have hnode :
          profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
              A strategy key context (node ++ [safetyDirection]) =
            profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
                A strategy key context node ++
              [direction] := by
        simp [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode,
          direction, List.map_append]
      rw [hnode, ← policy.successor_at, ih]
      have hlegal := policy.legal_at
        (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
          A strategy key context node)
      rw [ih] at hlegal
      change ∀ nextDirection,
        policy.successor
            (.owner table
              ((table.family A strategy key).ownerFibreSafetyStateAt A
                strategy hwin
                (table.ownerFibreInitialState A strategy hwin initialMemory key
                  context)
                node))
            nextDirection =
          .owner table
            ((table.family A strategy key).ownerFibreSafetyStep A strategy hwin
              ((table.family A strategy key).ownerFibreSafetyStateAt A strategy
                hwin
                (table.ownerFibreInitialState A strategy hwin initialMemory key
                  context)
                node)
              nextDirection.safety) at hlegal
      rw [hlegal direction]
      congr 1
      simp [ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTableSelection.ownerFibreSafetyStateAt,
        List.foldl_append, direction,
        profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection]

/-- Legality of every policy-mode node extracts the strong canonical
common-move obligation of the fixed root table. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_validAt
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)) :
    table.EnrichedValidAt A strategy hwin initialMemory key := by
  intro node
  have hlegal := policy.legal_at
    (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
      A strategy key node)
  rw [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_policy_run
    (Memory := Memory) A strategy hwin initialMemory key policy table hroot
    node] at hlegal
  change
    table.LocallyValid A strategy hwin initialMemory key
        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
          (PolicyDPA A key.1.1) key.1 (initialMemory key) table node) ∧
      _ at hlegal
  exact hlegal.1

/-- Acceptance of all enriched branches extracts forward parity of the same
fixed table selected at the root. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_forwardAccepts
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)) :
    table.EnrichedForwardAccepts A strategy initialMemory key := by
  intro branch
  let first :=
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
      A strategy key key.1
  let tail : Nat → EnrichedDirection A strategy key := fun n ↦
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
      A strategy key (branch n)
  let lifted := InputFreeRunParityTreeAutomaton.prefixedBranch first tail
  let priorities : Nat → Nat := fun n ↦
    (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
      (Memory := Memory) A strategy hwin initialMemory key).priority
      (policy.run (branchNode lifted n))
  have hparity : NatSeqMinEvenParity priorities := policy.accepts.2 lifted
  have hshift : NatSeqMinEvenParity (fun n ↦ priorities (1 + n)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hparity
  have heq :
      (fun n ↦ priorities (1 + n)) =
        fun n ↦
          (PolicyDPA A key.1.1).priority
            (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
              (PolicyDPA A key.1.1) key.1 (initialMemory key) table
                (branchNode branch n)).1.2 := by
    funext n
    change
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).priority
          (policy.run (branchNode lifted (1 + n))) = _
    rw [show 1 + n = n + 1 by omega,
      InputFreeRunParityTreeAutomaton.branchNode_prefixedBranch]
    have htailNode :
        branchNode tail n =
          (branchNode branch n).map
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
              A strategy key) :=
      branchNode_map
        (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyDirection
          A strategy key) branch n
    rw [htailNode]
    change
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).priority
          (policy.run
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedPolicyNode
              A strategy key (branchNode branch n))) = _
    rw [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_policy_run
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot]
    rfl
  rw [heq] at hshift
  exact hshift

/-- Acceptance of the owner-mode branches extracts rejection-sink safety for
every selection-independent honest-front context of the same fixed table. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_ownerSafe
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)) :
    table.EnrichedOwnerSafe A strategy hwin initialMemory key := by
  intro context branch
  let first :=
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
      A strategy key context ((default, default), .both)
  let tail : Nat → EnrichedDirection A strategy key := fun n ↦
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
      A strategy key context (branch n)
  let lifted := InputFreeRunParityTreeAutomaton.prefixedBranch first tail
  let priorities : Nat → Nat := fun n ↦
    (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
      (Memory := Memory) A strategy hwin initialMemory key).priority
      (policy.run (branchNode lifted n))
  have hparity : NatSeqMinEvenParity priorities := policy.accepts.2 lifted
  have hshift : NatSeqMinEvenParity (fun n ↦ priorities (1 + n)) :=
    (natSeqMinEvenParity_shift priorities 1).mpr hparity
  have heq :
      (fun n ↦ priorities (1 + n)) =
        fun n ↦
          ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
            (Memory := Memory) A strategy
            ((table.family A strategy key).ownerFibreSafetyStateAt A strategy
              hwin
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)
              (branchNode branch n)) := by
    funext n
    change
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).priority
          (policy.run (branchNode lifted (1 + n))) = _
    rw [show 1 + n = n + 1 by omega,
      InputFreeRunParityTreeAutomaton.branchNode_prefixedBranch]
    have htailNode :
        branchNode tail n =
          (branchNode branch n).map
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
              A strategy key context) :=
      branchNode_map
        (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerDirection
          A strategy key context) branch n
    rw [htailNode]
    change
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).priority
          (policy.run
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedOwnerNode
              A strategy key context (branchNode branch n))) = _
    rw [profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_owner_run
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot
      context]
    rfl
  rw [heq] at hshift
  exact hshift

/-- The root table of any accepting rational enriched policy satisfies all
three obligations represented by the universal branches. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_rootTable_checks
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hroot : ∀ direction,
      policy.successor .root direction =
        match direction.context with
        | none =>
            .policy table
              ((key.1, (PolicyDPA A key.1.1).initial), initialMemory key)
        | some context =>
            .owner table
              (table.ownerFibreInitialState A strategy hwin initialMemory key
                context)) :
    table.EnrichedChecks A strategy hwin initialMemory key := by
  exact ⟨
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_validAt
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot,
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_forwardAccepts
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot,
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_ownerSafe
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot⟩

/-- Any accepting rational enriched policy therefore yields one finite table
which simultaneously certifies canonical common-action coherence, forward
parity, and every honest owner-fibre safety obligation. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_exists_checkedTable
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (policy :
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key)
        |>.RationalTransitionPolicy) :
    ∃ table : FixedTable (Memory := Memory) A strategy key,
      table.EnrichedChecks A strategy hwin initialMemory key := by
  rcases
      profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_exists_rootTable
        (Memory := Memory) A strategy hwin initialMemory key policy with
    ⟨table, hroot⟩
  exact ⟨table,
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_rootTable_checks
      (Memory := Memory) A strategy hwin initialMemory key policy table hroot⟩

namespace
    ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-- Conversely, a table satisfying the three enriched obligations generates
the literal accepting rational policy of the enriched automaton. -/
noncomputable def toEnrichedRationalTransitionPolicy
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy)
    (table : FixedTable (Memory := Memory) A strategy key)
    (hchecks : table.EnrichedChecks A strategy hwin initialMemory key) :
    (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
      (Memory := Memory) A strategy hwin initialMemory key)
      |>.RationalTransitionPolicy := by
  let successor :=
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
      (Memory := Memory) A strategy hwin initialMemory key table
  let run :=
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
      (Memory := Memory) A strategy hwin initialMemory key table
  have hsuccessor : ∀ node direction,
      successor (run node) direction = run (node ++ [direction]) := by
    intro node direction
    dsimp only [successor, run]
    change
      profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
          (Memory := Memory) A strategy hwin initialMemory key table
          (node.foldl
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
              (Memory := Memory) A strategy hwin initialMemory key table)
            .root)
          direction =
        (node ++ [direction]).foldl
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableSuccessor
            (Memory := Memory) A strategy hwin initialMemory key table)
          .root
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hlegal : ∀ node,
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).delta
        (run node) PUnit.unit (successor (run node)) := by
    intro node
    cases node with
    | nil =>
        change ∃ chosen : FixedTable (Memory := Memory) A strategy key,
          ∀ direction,
            successor .root direction =
              match direction.context with
              | none =>
                  .policy chosen
                    ((key.1, (PolicyDPA A key.1.1).initial),
                      initialMemory key)
              | some context =>
                  .owner chosen
                    (chosen.ownerFibreInitialState A strategy hwin
                      initialMemory key context)
        exact ⟨table, fun direction ↦ rfl⟩
    | cons first node =>
        cases hcontext : first.context with
        | none =>
            have hrun :=
              profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_policy
                (Memory := Memory) A strategy hwin initialMemory key table
                first hcontext node
            change
              (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
                (Memory := Memory) A strategy hwin initialMemory key).delta
                (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
                  (Memory := Memory) A strategy hwin initialMemory key table
                    (first :: node))
                PUnit.unit
                (successor
                  (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
                    (Memory := Memory) A strategy hwin initialMemory key table
                      (first :: node)))
            rw [hrun]
            change
              table.LocallyValid A strategy hwin initialMemory key
                  (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                    (PolicyDPA A key.1.1) key.1 (initialMemory key) table
                      (node.map fun direction ↦ direction.policyChild)) ∧
                ∀ direction,
                  successor
                      (.policy table
                        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                          (PolicyDPA A key.1.1) key.1 (initialMemory key)
                          table
                          (node.map fun direction ↦
                            direction.policyChild)))
                      direction =
                    .policy table
                      (table.successor
                        (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                          (PolicyDPA A key.1.1) key.1 (initialMemory key)
                          table
                          (node.map fun direction ↦
                            direction.policyChild))
                        direction.policyChild)
            exact ⟨hchecks.1 (node.map fun direction ↦ direction.policyChild),
              fun direction ↦ rfl⟩
        | some context =>
            have hrun :=
              profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_owner
                (Memory := Memory) A strategy hwin initialMemory key table
                first context hcontext node
            change
              (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
                (Memory := Memory) A strategy hwin initialMemory key).delta
                (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
                  (Memory := Memory) A strategy hwin initialMemory key table
                    (first :: node))
                PUnit.unit
                (successor
                  (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun
                    (Memory := Memory) A strategy hwin initialMemory key table
                      (first :: node)))
            rw [hrun]
            intro direction
            rfl
  have hparity : ∀ branch : Nat → EnrichedDirection A strategy key,
      NatSeqMinEvenParity
        (fun n ↦
          (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
            (Memory := Memory) A strategy hwin initialMemory key).priority
            (run (branchNode branch n))) := by
    intro branch
    let priorities : Nat → Nat := fun n ↦
      (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
        (Memory := Memory) A strategy hwin initialMemory key).priority
        (run (branchNode branch n))
    apply (natSeqMinEvenParity_shift priorities 1).mp
    cases hcontext : (branch 0).context with
    | none =>
        let projected : Nat → LinkedCode A := fun n ↦
          (InputFreeRunParityTreeAutomaton.branchTail branch n).policyChild
        have htail := hchecks.2.1 projected
        have heq :
            (fun n ↦ priorities (1 + n)) =
              fun n ↦
                (PolicyDPA A key.1.1).priority
                  (sourceFreeBeliefCodeParityFiniteMemoryTransitionStateAt
                    (PolicyDPA A key.1.1) key.1 (initialMemory key) table
                      (branchNode projected n)).1.2 := by
          funext n
          change
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
              (Memory := Memory) A strategy hwin initialMemory key).priority
                (run (branchNode branch (1 + n))) = _
          dsimp only [run]
          rw [show 1 + n = n + 1 by omega,
            InputFreeRunParityTreeAutomaton.branchNode_succ_eq_cons_tail,
            profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_policy
              (Memory := Memory) A strategy hwin initialMemory key table
                (branch 0) hcontext]
          have hnode :
              (branchNode
                  (InputFreeRunParityTreeAutomaton.branchTail branch) n).map
                    (fun direction ↦ direction.policyChild) =
                branchNode projected n := by
            exact (branchNode_map (fun direction ↦ direction.policyChild)
              (InputFreeRunParityTreeAutomaton.branchTail branch) n).symm
          rw [hnode]
          rfl
        rw [heq]
        exact htail
    | some context =>
        let projected : Nat → SafetyDirection (In₁ := In₁) (In₂ := In₂) :=
          fun n ↦
            (InputFreeRunParityTreeAutomaton.branchTail branch n).safety
        have htail := hchecks.2.2 context projected
        have heq :
            (fun n ↦ priorities (1 + n)) =
              fun n ↦
                ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicySelection.ownerFibreSafetyPriority
                  (Memory := Memory) A strategy
                  ((table.family A strategy key).ownerFibreSafetyStateAt A
                    strategy hwin
                    (table.ownerFibreInitialState A strategy hwin
                      initialMemory key context)
                    (branchNode projected n)) := by
          funext n
          change
            (profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
              (Memory := Memory) A strategy hwin initialMemory key).priority
                (run (branchNode branch (1 + n))) = _
          dsimp only [run]
          rw [show 1 + n = n + 1 by omega,
            InputFreeRunParityTreeAutomaton.branchNode_succ_eq_cons_tail,
            profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedTableRun_cons_owner
              (Memory := Memory) A strategy hwin initialMemory key table
                (branch 0) context hcontext]
          have hnode :
              (branchNode
                  (InputFreeRunParityTreeAutomaton.branchTail branch) n).map
                    (fun direction ↦ direction.safety) =
                branchNode projected n := by
            exact (branchNode_map (fun direction ↦ direction.safety)
              (InputFreeRunParityTreeAutomaton.branchTail branch) n).symm
          rw [hnode]
          rfl
        rw [heq]
        exact htail
  exact {
    run := run
    accepts := ⟨⟨rfl, by
      intro node
      rw [show (fun direction ↦ run (node ++ [direction])) =
          successor (run node) by
        funext direction
        exact (hsuccessor node direction).symm]
      exact hlegal node⟩, hparity⟩
    successor := successor
    successor_at := hsuccessor
    legal_at := hlegal }

end ProfiledRawJointOneSidedPhysicalCompatibleFiniteMemoryPolicyTable

/-- Thus, for fixed finite memory, accepting enriched rational policies are
equivalent to finite tables satisfying exactly the three advertised checks. -/
theorem
    profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_policy_iff_checkedTable
    (initialMemory : RootKey A strategy → Memory)
    (key : RootKey A strategy) :
    Nonempty
        ((profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton
          (Memory := Memory) A strategy hwin initialMemory key)
          |>.RationalTransitionPolicy) ↔
      ∃ table : FixedTable (Memory := Memory) A strategy key,
        table.EnrichedChecks A strategy hwin initialMemory key := by
  constructor
  · rintro ⟨policy⟩
    exact
      profiledRawJointOneSidedPhysicalCompatibleFiniteMemoryEnrichedAutomaton_exists_checkedTable
        (Memory := Memory) A strategy hwin initialMemory key policy
  · rintro ⟨table, hchecks⟩
    exact ⟨table.toEnrichedRationalTransitionPolicy A strategy hwin
      initialMemory key hchecks⟩

end

end DetParityAutomaton

end DistributedSynthesis
