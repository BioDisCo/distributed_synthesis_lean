/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonPairCarrier
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTargetHandoff
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonHybridSemanticParity
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodeParityRationalization

/-!
# Occurrence-sensitive rationalization of guarded common pairs

A represented guarded pair is not, by itself, a sound autonomous state:
choosing a new semantic representative after every simultaneous round can
mosaic unrelated winning executions.  This file keeps the semantic world
only in the pre-rationalization tree.  Its finite node label is the pair of
guarded sibling moves extracted jointly at that occurrence.

The complete child assignment is source-free.  For every next input pair it
merges the two targets emitted by the guarded root records.  The first-record
guards prove that this is exactly the incidence code of the literal next
common world.  Hence the existing code-parity rationalization theorem applies
to the whole tree at once.  The returned finite policy may distinguish two
occurrences with the same incidence code by its parity-control coordinate;
it never chooses a semantic representative at runtime.
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

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

/-! ## The finite child assignment of one guarded pair -/

/-- The complete common incidence code emitted at a simultaneous root.

Both arguments of `profiledRawJointBothTargetMerge` are read from the actual
guarded controllers.  No semantic representative is consulted. -/
noncomputable def ProfiledRawJointGuardedCommonPair.bothNextCode
    (pair : CommonPair A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  profiledRawJointBothTargetMerge A input
    ((pair.rightRootRecord A strategy hwin input).2.1.target .both)
    ((pair.leftRootRecord A strategy hwin input).2.1.target .both)

/-! ## One actual occurrence of a common guarded pair -/

/-- A proof-side occurrence is an incoming simultaneous edge of the literal
semantic unfolding.  Its live world is the target of that edge, and its
finite move is extracted jointly before any rational policy is selected. -/
structure ProfiledRawJointGuardedCommonSemanticPoint where
  parent : ProfiledRawJointCommonBaseWorld A strategy
  incoming : In₁ × In₂

namespace ProfiledRawJointGuardedCommonSemanticPoint

/-- Literal common world at this occurrence. -/
def world
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointCommonWorldAfterBoth A point.parent point.incoming

/-- Complete finite incidence code at this occurrence. -/
def code
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  (profiledRawJointCommonWorldFamily A (point.world A strategy)).incidenceCode A

/-- Jointly extracted finite guarded label at this occurrence. -/
noncomputable def move
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    CommonPair A strategy hwin :=
  profiledRawJointGuardedCommonPairOfWorld A strategy hwin point.parent
    point.incoming

/-- The literal child occurrence for one further simultaneous input pair. -/
def step
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSemanticPoint A strategy :=
  ⟨point.world A strategy, input⟩

/-- **Whole-child-assignment equation.**  At one actual occurrence, the
finite guarded pair computes the exact code of every literal simultaneous
child.  This is the source-free T1 law used by tree rationalization. -/
theorem step_code
    (point : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (input : In₁ × In₂) :
    (point.step A strategy input).code A strategy =
      (point.move A strategy hwin).bothNextCode A strategy hwin input := by
  let family := profiledRawJointCommonWorldFamily A point.parent
  let direction := profiledRawJointBothRestartDirection point.incoming
  let child := point.world A strategy
  have hchild : family.semanticChild A direction =
      profiledRawJointCommonWorldFamily A child := by
    exact profiledRawJointCommonWorld_semanticChild_eq_bothRestart A
      point.parent point.incoming
  simpa [ProfiledRawJointGuardedCommonSemanticPoint.step,
    ProfiledRawJointGuardedCommonSemanticPoint.code,
    ProfiledRawJointGuardedCommonSemanticPoint.move,
    ProfiledRawJointGuardedCommonSemanticPoint.world,
    ProfiledRawJointGuardedCommonPair.bothNextCode,
    profiledRawJointGuardedCommonPairOfWorld,
    profiledRawJointGuardedCommonRightMoveOfWorld,
    profiledRawJointGuardedCommonLeftMoveOfWorld] using
      (profiledRawJointGuardedSiblingControllerRootRecords_merge_eq_commonWorldAfterBoth
        A hwin family direction child hchild false false input).symm

end ProfiledRawJointGuardedCommonSemanticPoint

/-! ## Source-free semantic tree -/

/-- Finite validity relation for a guarded pair at an incidence code.  The
semantic occurrence is proof-only; both runtime arguments are finite. -/
def ProfiledRawJointGuardedCommonMoveValid
    (code : ProfiledRawJointIncidenceCode A (I := Unit))
    (pair : CommonPair A strategy hwin) : Prop :=
  ∃ point : ProfiledRawJointGuardedCommonSemanticPoint A strategy,
    point.code A strategy = code ∧ point.move A strategy hwin = pair

/-- Source-free successor computed solely from the finite guarded label. -/
noncomputable def profiledRawJointGuardedCommonNext
    (_code : ProfiledRawJointIncidenceCode A (I := Unit))
    (pair : CommonPair A strategy hwin) (input : In₁ × In₂) :
    ProfiledRawJointIncidenceCode A (I := Unit) :=
  pair.bothNextCode A strategy hwin input

/-- The actual common-input unfolding labeled by finite guarded move pairs. -/
noncomputable def profiledRawJointGuardedCommonSemanticTree
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    SourceFreeBeliefSemanticTree
      (In₁ × In₂)
      (CommonPair A strategy hwin)
      (ProfiledRawJointIncidenceCode A (I := Unit)) where
  Semantic := ProfiledRawJointGuardedCommonSemanticPoint A strategy
  initial := initial
  step := ProfiledRawJointGuardedCommonSemanticPoint.step A strategy
  code := ProfiledRawJointGuardedCommonSemanticPoint.code A strategy
  move := ProfiledRawJointGuardedCommonSemanticPoint.move A strategy hwin

/-- Every semantic node carries an immediate witness of finite validity. -/
theorem profiledRawJointGuardedCommonSemanticTree_valid
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (node : TreeNode (In₁ × In₂)) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin
      ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
        ).code
          ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
            ).stateAt node))
      ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
        ).move
          ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
            ).stateAt node)) := by
  exact ⟨_, rfl, rfl⟩

/-- The semantic tree satisfies the source-free successor equation at every
node and for the complete finite input-pair child assignment. -/
theorem profiledRawJointGuardedCommonSemanticTree_next_code
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (node : TreeNode (In₁ × In₂)) (input : In₁ × In₂) :
    let raw :=
      profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
    raw.code (raw.step (raw.stateAt node) input) =
      profiledRawJointGuardedCommonNext A strategy hwin
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) input := by
  dsimp only
  exact ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
    _ input

/-! ## Common-code parity and whole-tree extraction -/

/-- Restrict the already proved hybrid code objective to common incidence
codes.  The tag is inserted only in the proof automaton; it is not a process
observation. -/
noncomputable def profiledRawJointGuardedCommonCodeParityDPA
    (initialCode : ProfiledRawJointIncidenceCode A (I := Unit)) :
    DetParityAutomaton (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  (profiledRawJointHybridCodeParityDPA A (.common initialCode)).comap
    ProfiledRawJointHybridCode.common

private def profiledRawJointGuardedCommonHybridBranch
    (branch : Nat → In₁ × In₂) :
    Nat → ProfiledRawJointHybridDirection (In₁ := In₁) (In₂ := In₂) :=
  fun n ↦ .simultaneous (branch n)

/-- The occurrence-sensitive tree and the old literal hybrid tree reach the
same common semantic world along a simultaneous branch. -/
theorem profiledRawJointGuardedCommonSemanticTree_stateAt_hybrid
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (branch : Nat → In₁ × In₂) : ∀ n,
    (profiledRawJointHybridSemanticTree A (initial.world A strategy)).stateAt
        (branchNode
          (profiledRawJointGuardedCommonHybridBranch branch) n) =
      .common
        (((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
          ).stateAt (branchNode branch n)).world A strategy) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode
            (profiledRawJointGuardedCommonHybridBranch branch) (n + 1) =
          branchNode (profiledRawJointGuardedCommonHybridBranch branch) n ++
            [.simultaneous (branch n)] from rfl,
        show branchNode branch (n + 1) =
          branchNode branch n ++ [branch n] from rfl,
        (profiledRawJointHybridSemanticTree A
          (initial.world A strategy)).stateAt_append,
        (profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
          ).stateAt_append,
        ih]
      rfl

/-- Successive bare common codes are exactly the tagged hybrid child-code
word. -/
theorem profiledRawJointGuardedCommonSemanticTree_childCodeWord
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (branch : Nat → In₁ × In₂) :
    OmegaWord.map ProfiledRawJointHybridCode.common
        ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
          ).childCodeWord branch) =
      (profiledRawJointHybridSemanticTree A (initial.world A strategy)
        ).childCodeWord
          (profiledRawJointGuardedCommonHybridBranch branch) := by
  funext n
  change
    ProfiledRawJointHybridCode.common
        (((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
          ).stateAt (branchNode branch (n + 1))).code A strategy) =
      ((profiledRawJointHybridSemanticTree A (initial.world A strategy)
        ).stateAt
          (branchNode
            (profiledRawJointGuardedCommonHybridBranch branch) (n + 1))).code A
  rw [profiledRawJointGuardedCommonSemanticTree_stateAt_hybrid A strategy hwin
    initial branch (n + 1)]
  rfl

/-- Every simultaneous branch of the guarded semantic tree satisfies the
finite common-code objective.  This is inherited from the literal hybrid
semantic acceptance theorem, before any representative quotient is formed. -/
theorem profiledRawJointGuardedCommonSemanticTree_accepts
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (branch : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy)).Accepts
        ((profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
          ).childCodeWord branch) := by
  rw [profiledRawJointGuardedCommonCodeParityDPA,
    DetParityAutomaton.comap_accepts_iff]
  rw [profiledRawJointGuardedCommonSemanticTree_childCodeWord A strategy hwin
    initial branch]
  exact profiledRawJointHybridSemanticTree_accepts A strategy hwin
    (initial.world A strategy)
    (profiledRawJointGuardedCommonHybridBranch branch)

/-- Complete source-free code-parity certificate for guarded common pairs.

Its `next_code` field is the whole-child-assignment theorem above.  Thus one
tree-automaton transition chooses a guarded pair before Nature selects any
input pair, while all children remain tied to that same finite label. -/
theorem profiledRawJointGuardedCommonSemanticTree_codeParityCertificate
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    let raw :=
      profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)
      raw := by
  dsimp only
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact profiledRawJointGuardedCommonSemanticTree_valid A strategy hwin
      initial node
  · intro node input
    exact profiledRawJointGuardedCommonSemanticTree_next_code A strategy hwin
      initial node input
  · intro branch
    exact profiledRawJointGuardedCommonSemanticTree_accepts A strategy hwin
      initial branch

/-- The finite occurrence-sensitive common policy returned by the generic
source-free interface.  Its state is the current incidence code paired with
the common-code parity control; its transition is indexed by the physical
input pair. -/
noncomputable abbrev ProfiledRawJointGuardedCommonRationalPolicy
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)

/-- **Unconditional finite-input rationalization.**

This is the exact existing interface instantiated by the guarded semantic
tree.  It uses `rationalRunBasis_of_finite` for `In₁ × In₂`; no
arbitrary-direction basis and no representative-successor congruence is
assumed. -/
theorem nonempty_profiledRawJointGuardedCommonRationalPolicy
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin initial) := by
  let raw :=
    profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
  let certificate :=
    profiledRawJointGuardedCommonSemanticTree_codeParityCertificate A strategy
      hwin initial
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)
    raw certificate
    (InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _)

/-! ## Reading one finite guarded label at a policy state -/

/-- Reachability in the one selected occurrence-sensitive common policy. -/
abbrev ProfiledRawJointGuardedCommonPolicyReachable
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)
    policy state

/-- At every reachable finite policy state, one jointly represented guarded
pair realizes the complete successor table for all physical input pairs. -/
theorem exists_profiledRawJointGuardedCommonPairAt
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial policy state) :
    ∃ pair : CommonPair A strategy hwin,
      ProfiledRawJointGuardedCommonMoveValid A strategy hwin state.1 pair ∧
        ∀ input,
          policy.successor state input =
            (pair.bothNextCode A strategy hwin input,
              (profiledRawJointGuardedCommonCodeParityDPA A
                (initial.code A strategy)).step state.2
                  (pair.bothNextCode A strategy hwin input)) := by
  obtain ⟨pair, hvalid, hnext⟩ :=
    SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)
      policy state hreachable
  refine ⟨pair, hvalid, ?_⟩
  intro input
  simpa only [profiledRawJointGuardedCommonNext] using hnext input

/-! ## Complete finite policy states -/

/-- Complete state type of the rationalized common tree. -/
noncomputable abbrev ProfiledRawJointGuardedCommonPolicyState
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonNext A strategy hwin)).State

/-! ## A total finite selector and packaged policy -/

/-- Totalize guarded-pair selection over the complete finite state space.
Unreachable states use the semantic root label as a harmless fallback.  All
operational correctness statements below are explicitly reachability-guarded. -/
noncomputable def profiledRawJointGuardedCommonPairAt
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State) :
    CommonPair A strategy hwin := by
  classical
  exact if h : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial policy state then
    Classical.choose
      (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial
        policy state h)
  else
    initial.move A strategy hwin

/-- On a reachable state, the total selector chooses a pair valid at the
state's incidence code. -/
theorem profiledRawJointGuardedCommonPairAt_valid
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial policy state) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin state.1
      (profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
        state) := by
  classical
  rw [profiledRawJointGuardedCommonPairAt, dif_pos hreachable]
  exact (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
      state hreachable)).1

/-- On a reachable state, the selected pair realizes the policy's complete
successor assignment for every physical input pair. -/
theorem profiledRawJointGuardedCommonPairAt_successor_eq
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State)
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial policy state)
    (input : In₁ × In₂) :
    policy.successor state input =
      ((profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
          state).bothNextCode A strategy hwin input,
        (profiledRawJointGuardedCommonCodeParityDPA A
          (initial.code A strategy)).step state.2
            ((profiledRawJointGuardedCommonPairAt A strategy hwin initial
              policy state).bothNextCode A strategy hwin input)) := by
  classical
  rw [profiledRawJointGuardedCommonPairAt, dif_pos hreachable]
  exact (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
      state hreachable)).2 input

/-- One extracted rational policy together with a literal total finite table
from policy states to guarded common pairs. -/
structure ProfiledRawJointGuardedCommonPolicyPackage
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) where
  policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin initial
  pairAt :
    (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy))
      (initial.code A strategy)
      (ProfiledRawJointGuardedCommonMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonNext A strategy hwin)).State →
        CommonPair A strategy hwin
  pairAt_valid : ∀ state,
    ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin initial
      policy state →
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin state.1
      (pairAt state)
  successor_eq : ∀ state,
    ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin initial
      policy state →
    ∀ input,
      policy.successor state input =
        ((pairAt state).bothNextCode A strategy hwin input,
          (profiledRawJointGuardedCommonCodeParityDPA A
            (initial.code A strategy)).step state.2
              ((pairAt state).bothNextCode A strategy hwin input))

/-- The occurrence-sensitive semantic tree yields the operational finite
common-policy package unconditionally. -/
theorem nonempty_profiledRawJointGuardedCommonPolicyPackage
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin initial) := by
  rcases nonempty_profiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial with ⟨policy⟩
  refine ⟨{
    policy := policy
    pairAt := profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
    pairAt_valid := ?_
    successor_eq := ?_ }⟩
  · intro state hreachable
    exact profiledRawJointGuardedCommonPairAt_valid A strategy hwin initial
      policy state hreachable
  · intro state hreachable input
    exact profiledRawJointGuardedCommonPairAt_successor_eq A strategy hwin
      initial policy state hreachable input

/-- Canonical choice of the operational common package.  Its runtime state
space remains the finite automaton state; the semantic initial point occurs
only in the proof-side construction of this constant package. -/
noncomputable def profiledRawJointGuardedCommonPolicyPackage
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy) :
    ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin initial :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)

namespace ProfiledRawJointGuardedCommonPolicyPackage

/-- The initial policy state is reachable. -/
theorem initial_reachable
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial) :
    ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin initial
      package.policy (package.policy.run []) :=
  ⟨[], rfl⟩

/-- Every successor of a reachable policy state is reachable in the same
single rational run. -/
theorem successor_reachable
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    {state}
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin initial
      package.policy (package.policy.successor state input) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [input], ?_⟩
  rw [← package.policy.successor_at node input, hnode]

/-- Guarded label selected at the policy successor. -/
noncomputable def nextPairAt
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    (state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial)
    (input : In₁ × In₂) : CommonPair A strategy hwin :=
  package.pairAt (package.policy.successor state input)

/-- The next selected pair is valid at the exact code emitted by the current
pair. -/
theorem nextPairAt_valid
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    {state}
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin
      (package.policy.successor state input).1
      (package.nextPairAt A strategy hwin state input) :=
  package.pairAt_valid _ (package.successor_reachable A strategy hwin
    hreachable input)

/-- Exact finite handoff: the next selected pair's advertised code is the
merge emitted by the current guarded roots. -/
theorem successor_code_eq_currentPair
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    (package : ProfiledRawJointGuardedCommonPolicyPackage A strategy hwin
      initial)
    {state}
    (hreachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
      initial package.policy state)
    (input : In₁ × In₂) :
    (package.policy.successor state input).1 =
      (package.pairAt state).bothNextCode A strategy hwin input := by
  exact congrArg Prod.fst (package.successor_eq state hreachable input)

end ProfiledRawJointGuardedCommonPolicyPackage

/-! ## A finite reachable-key carrier -/

/-- Runtime-relevant common control: a finite rational-policy state together
with proof-erased reachability in that one policy. -/
structure ProfiledRawJointGuardedCommonPolicyKey
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial) where
  state : ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial
  reachable : ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin
    initial policy state

noncomputable instance profiledRawJointGuardedCommonPolicyKeyFintype
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial) :
    Fintype
      (ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
        policy) := by
  classical
  let State :=
    ProfiledRawJointGuardedCommonPolicyState A strategy hwin initial
  let Reach :=
    ProfiledRawJointGuardedCommonPolicyReachable A strategy hwin initial
      policy
  let Rep := { state : State // Reach state }
  let equiv :
      ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial policy ≃
        Rep :=
    { toFun := fun key ↦ ⟨key.state, key.reachable⟩
      invFun := fun key ↦ ⟨key.1, key.2⟩
      left_inv := by intro key; cases key; rfl
      right_inv := by intro key; cases key; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

namespace ProfiledRawJointGuardedCommonPolicyKey

/-- Root key of the selected rational policy. -/
def root
    (initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial) :
    ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial policy :=
  ⟨policy.run [], ⟨[], rfl⟩⟩

/-- Follow the one rational policy on a physical simultaneous input pair. -/
def next
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial policy := by
  refine ⟨policy.successor key.state input, ?_⟩
  rcases key.reachable with ⟨node, hnode⟩
  refine ⟨node ++ [input], ?_⟩
  rw [← policy.successor_at node input, hnode]

/-! ### Prefix-independent acceptance of policy-key tails -/

/-- Prefix a finite direction word to an infinite direction branch.  This is
kept private: it is only the witness used to inherit parity below an arbitrary
reachable policy key. -/
private def branchAfterPrefix {Branch : Type u}
    (stem : List Branch) (tail : Nat → Branch) : Nat → Branch :=
  match stem with
  | [] => tail
  | first :: rest => fun
      | 0 => first
      | n + 1 => branchAfterPrefix rest tail n

/-- Removing the first direction from a prefixed branch removes the root
edge from each positive-depth branch node. -/
private theorem branchNode_branchAfterPrefix_cons {Branch : Type u}
    (first : Branch) (rest : List Branch) (tail : Nat → Branch) : ∀ n,
    branchNode (branchAfterPrefix (first :: rest) tail) (n + 1) =
      [first] ++ branchNode (branchAfterPrefix rest tail) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode (branchAfterPrefix (first :: rest) tail)
            (n + 1 + 1) =
          branchNode (branchAfterPrefix (first :: rest) tail) (n + 1) ++
            [branchAfterPrefix (first :: rest) tail (n + 1)] from rfl,
        ih]
      change
        ([first] ++ branchNode (branchAfterPrefix rest tail) n) ++
            [branchAfterPrefix rest tail n] =
          [first] ++ branchNode (branchAfterPrefix rest tail) (n + 1)
      simp only [branchNode, List.append_assoc]

/-- The branch prefixed by `stem` reaches exactly `stem` followed by the
ordinary depth-`n` node of the tail. -/
private theorem branchNode_branchAfterPrefix {Branch : Type u}
    (stem : List Branch) (tail : Nat → Branch) (n : Nat) :
    branchNode (branchAfterPrefix stem tail) (stem.length + n) =
      stem ++ branchNode tail n := by
  induction stem with
  | nil => simp only [branchAfterPrefix, List.length_nil, zero_add,
      List.nil_append]
  | cons first rest ih =>
      rw [List.length_cons]
      have hindex : rest.length + 1 + n = (rest.length + n) + 1 := by
        omega
      rw [hindex,
        branchNode_branchAfterPrefix_cons first rest tail (rest.length + n),
        ih]
      rfl

/-- Iteration of the finite policy key along an arbitrary infinite sequence
of simultaneous input pairs.  Time zero is the supplied reachable key. -/
def trace
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (inputs : Nat → In₁ × In₂) :
    Nat → ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy
  | 0 => key
  | n + 1 => (trace key inputs n).next A strategy hwin (inputs n)

@[simp] theorem trace_zero
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (inputs : Nat → In₁ × In₂) :
    trace A strategy hwin key inputs 0 = key :=
  rfl

@[simp] theorem trace_succ
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (inputs : Nat → In₁ × In₂) (n : Nat) :
    trace A strategy hwin key inputs (n + 1) =
      (trace A strategy hwin key inputs n).next A strategy hwin (inputs n) :=
  rfl

/-- If `prefix` witnesses reachability of the starting key, the iterated key
trace is literally the one rational run below that prefix. -/
theorem trace_state_eq_run_append
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (inputs : Nat → In₁ × In₂)
    (stem : TreeNode (In₁ × In₂))
    (hstem : policy.run stem = key.state) : ∀ n,
    (trace A strategy hwin key inputs n).state =
      policy.run (stem ++ branchNode inputs n) := by
  intro n
  induction n with
  | zero => simpa only [branchNode, List.append_nil] using hstem.symm
  | succ n ih =>
      change
        policy.successor
            (trace A strategy hwin key inputs n).state (inputs n) =
          policy.run (stem ++ branchNode inputs (n + 1))
      rw [ih, policy.successor_at]
      simp only [branchNode, List.append_assoc]

/-- **Reusable tail acceptance.**  From any reachable complete policy key,
every infinite sequence of simultaneous inputs has min-even common-code
priority along repeated `key.next` transitions.  The proof extends the
reachability prefix by the requested branch and then deletes that finite
prefix; no semantic representative is reselected. -/
theorem trace_priority_parity
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (inputs : Nat → In₁ × In₂) :
    NatSeqMinEvenParity (fun n ↦
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy)).priority
          (trace A strategy hwin key inputs n).state.2) := by
  rcases key.reachable with ⟨stem, hstem⟩
  let branch := branchAfterPrefix stem inputs
  have hfull := policy.accepts.2 branch
  change NatSeqMinEvenParity (fun n ↦
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy)).priority
        (policy.run (branchNode branch n)).2) at hfull
  have htail := (natSeqMinEvenParity_shift
    (fun n ↦
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy)).priority
          (policy.run (branchNode branch n)).2)
    stem.length).mpr hfull
  convert htail using 1
  funext n
  rw [branchNode_branchAfterPrefix stem inputs n]
  exact congrArg
    (fun state ↦
      (profiledRawJointGuardedCommonCodeParityDPA A
        (initial.code A strategy)).priority state.2)
    (trace_state_eq_run_append A strategy hwin key inputs stem hstem n)

/-- One guarded pair selected once per complete finite policy key.  This is a
choice from a finite-state transition, not from a semantic world. -/
noncomputable def pair
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy) : CommonPair A strategy hwin :=
  Classical.choose
    (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
      key.state key.reachable)

/-- The selected pair is valid at the key's current incidence code. -/
theorem pair_valid
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin key.state.1
      (key.pair A strategy hwin) :=
  (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
      key.state key.reachable)).1

/-- The one selected guarded pair realizes every physical-input successor of
this complete policy key. -/
theorem successor_eq
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (input : In₁ × In₂) :
    policy.successor key.state input =
      ((key.pair A strategy hwin).bothNextCode A strategy hwin input,
        (profiledRawJointGuardedCommonCodeParityDPA A
          (initial.code A strategy)).step key.state.2
            ((key.pair A strategy hwin).bothNextCode A strategy hwin
              input)) :=
  (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonPairAt A strategy hwin initial policy
      key.state key.reachable)).2 input

/-- In particular, the public code stored by the successor key is the merge
of the two actual guarded root targets. -/
theorem next_code
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin initial
      policy)
    (input : In₁ × In₂) :
    (key.next A strategy hwin input).state.1 =
      (key.pair A strategy hwin).bothNextCode A strategy hwin input := by
  exact congrArg Prod.fst (key.successor_eq A strategy hwin input)

end ProfiledRawJointGuardedCommonPolicyKey

end

end DetParityAutomaton

end DistributedSynthesis
