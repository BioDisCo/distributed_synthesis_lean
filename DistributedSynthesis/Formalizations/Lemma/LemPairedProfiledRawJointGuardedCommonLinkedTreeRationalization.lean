/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTreeRationalization

/-!
# Parent-linked rationalization of guarded common pairs

The incidence-code rationalization chooses a complete guarded pair at every
common occurrence, but its public child code does not remember which literal
child pair was chosen by the parent.  That is sufficient for common-only
parity, but insufficient at a later strict/common cross anchor: two semantic
occurrences can have the same incidence code while their second guarded
records differ.

This file applies the same source-free tree construction to a slightly richer
finite alphabet.  A move contains the current guarded pair together with its
complete table of literal child pairs.  A child code contains both the usual
incidence code and the pair selected for that child.  Thus every transition of
the rational policy preserves *all* properties of a literal parent/child
pair.  The parity automaton simply projects away the extra pair component.

All added data are finite.  They are proof/controller data only: no runtime
map accepts a graph, an orientation, a leader bit, or a semantic history.
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

private abbrev SemanticPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

/-! ## Finite linked codes and moves -/

/-- The ordinary common incidence code together with the guarded pair that
must be installed at that exact occurrence. -/
abbrev ProfiledRawJointGuardedCommonLinkedCode :=
  ProfiledRawJointIncidenceCode A (I := Unit) × CommonPair A strategy hwin

/-- One current guarded pair and the complete finite table of guarded pairs
to install after every possible simultaneous input. -/
abbrev ProfiledRawJointGuardedCommonLinkedMove :=
  CommonPair A strategy hwin ×
    ((In₁ × In₂) → CommonPair A strategy hwin)

namespace ProfiledRawJointGuardedCommonSemanticPoint

/-- Finite code of one literal common occurrence. -/
noncomputable def linkedCode
    (point : SemanticPoint A strategy) :
    ProfiledRawJointGuardedCommonLinkedCode A strategy hwin :=
  (point.code A strategy, point.move A strategy hwin)

/-- The whole literal child-pair table of one common occurrence. -/
noncomputable def linkedMove
    (point : SemanticPoint A strategy) :
    ProfiledRawJointGuardedCommonLinkedMove A strategy hwin :=
  (point.move A strategy hwin,
    fun input ↦ (point.step A strategy input).move A strategy hwin)

end ProfiledRawJointGuardedCommonSemanticPoint

/-- A linked move is valid at a linked code exactly when both were extracted
from one literal semantic occurrence. -/
def ProfiledRawJointGuardedCommonLinkedMoveValid
    (code : ProfiledRawJointGuardedCommonLinkedCode A strategy hwin)
    (move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin) : Prop :=
  ∃ point : SemanticPoint A strategy,
    point.linkedCode A strategy hwin = code ∧
      point.linkedMove A strategy hwin = move

/-- Source-free successor of one linked move.  Its second component is the
literal child pair selected by the parent's complete table. -/
noncomputable def profiledRawJointGuardedCommonLinkedNext
    (_code : ProfiledRawJointGuardedCommonLinkedCode A strategy hwin)
    (move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLinkedCode A strategy hwin :=
  (move.1.bothNextCode A strategy hwin input, move.2 input)

/-! ## Exact linked semantic tree -/

/-- The literal common unfolding with the parent-linked finite alphabet. -/
noncomputable def profiledRawJointGuardedCommonLinkedSemanticTree
    (initial : SemanticPoint A strategy) :
    SourceFreeBeliefSemanticTree
      (In₁ × In₂)
      (ProfiledRawJointGuardedCommonLinkedMove A strategy hwin)
      (ProfiledRawJointGuardedCommonLinkedCode A strategy hwin) where
  Semantic := SemanticPoint A strategy
  initial := initial
  step := ProfiledRawJointGuardedCommonSemanticPoint.step A strategy
  code := ProfiledRawJointGuardedCommonSemanticPoint.linkedCode A strategy hwin
  move := ProfiledRawJointGuardedCommonSemanticPoint.linkedMove A strategy hwin

/-- The linked source-free successor equation is exact for the complete child
table, not merely for its incidence projection. -/
theorem profiledRawJointGuardedCommonLinkedSemanticTree_next_code
    (initial : SemanticPoint A strategy)
    (node : TreeNode (In₁ × In₂)) (input : In₁ × In₂) :
    let raw :=
      profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin initial
    raw.code (raw.step (raw.stateAt node) input) =
      profiledRawJointGuardedCommonLinkedNext A strategy hwin
        (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) input := by
  dsimp only [profiledRawJointGuardedCommonLinkedSemanticTree,
    ProfiledRawJointGuardedCommonSemanticPoint.linkedCode,
    ProfiledRawJointGuardedCommonSemanticPoint.linkedMove,
    profiledRawJointGuardedCommonLinkedNext]
  apply Prod.ext
  · exact ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy
      hwin _ input
  · rfl

/-- Every literal linked label is valid at its literal linked code. -/
theorem profiledRawJointGuardedCommonLinkedSemanticTree_valid
    (initial : SemanticPoint A strategy)
    (node : TreeNode (In₁ × In₂)) :
    let raw :=
      profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin initial
    ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin
      (raw.code (raw.stateAt node)) (raw.move (raw.stateAt node)) := by
  dsimp only
  exact ⟨_, rfl, rfl⟩

/-! ## Projected parity objective -/

/-- The old common-code parity automaton ignores the linked pair component. -/
noncomputable def profiledRawJointGuardedCommonLinkedCodeParityDPA
    (initial : SemanticPoint A strategy) :
    DetParityAutomaton
      (ProfiledRawJointGuardedCommonLinkedCode A strategy hwin) :=
  (profiledRawJointGuardedCommonCodeParityDPA A
    (initial.code A strategy)).comap Prod.fst

/-- Projecting a linked child-code word gives the old common child-code word. -/
theorem profiledRawJointGuardedCommonLinkedSemanticTree_childCodeWord_fst
    (initial : SemanticPoint A strategy)
    (branch : Nat → In₁ × In₂) :
    OmegaWord.map Prod.fst
        ((profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin
          initial).childCodeWord branch) =
      (profiledRawJointGuardedCommonSemanticTree A strategy hwin initial
        ).childCodeWord branch := by
  funext n
  rfl

/-- Every branch of the linked semantic tree is accepted. -/
theorem profiledRawJointGuardedCommonLinkedSemanticTree_accepts
    (initial : SemanticPoint A strategy)
    (branch : Nat → In₁ × In₂) :
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial
      ).Accepts
      ((profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin
        initial).childCodeWord branch) := by
  rw [profiledRawJointGuardedCommonLinkedCodeParityDPA,
    DetParityAutomaton.comap_accepts_iff,
    profiledRawJointGuardedCommonLinkedSemanticTree_childCodeWord_fst]
  exact profiledRawJointGuardedCommonSemanticTree_accepts A strategy hwin
    initial branch

/-- Complete code-parity certificate for the parent-linked semantic tree. -/
theorem profiledRawJointGuardedCommonLinkedSemanticTree_certificate
    (initial : SemanticPoint A strategy) :
    let raw :=
      profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin initial
    SourceFreeBeliefCodeParityCertificate
      (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin
        initial)
      (initial.linkedCode A strategy hwin)
      (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonLinkedNext A strategy hwin)
      raw := by
  dsimp only
  refine {
    initial_code := rfl
    valid := ?_
    next_code := ?_
    accepts := ?_ }
  · intro node
    exact profiledRawJointGuardedCommonLinkedSemanticTree_valid A strategy hwin
      initial node
  · intro node input
    exact profiledRawJointGuardedCommonLinkedSemanticTree_next_code A strategy
      hwin initial node input
  · intro branch
    exact profiledRawJointGuardedCommonLinkedSemanticTree_accepts A strategy
      hwin initial branch

/-! ## One finite rational policy with literal parent/child linkage -/

noncomputable abbrev ProfiledRawJointGuardedCommonLinkedRationalPolicy
    (initial : SemanticPoint A strategy) :=
  SourceFreeBeliefCodeParityRationalPolicy
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonLinkedNext A strategy hwin)

/-- The linked semantic tree has one finite rational policy. -/
theorem nonempty_profiledRawJointGuardedCommonLinkedRationalPolicy
    (initial : SemanticPoint A strategy) :
    Nonempty
      (ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
        initial) := by
  let raw :=
    profiledRawJointGuardedCommonLinkedSemanticTree A strategy hwin initial
  let certificate :=
    profiledRawJointGuardedCommonLinkedSemanticTree_certificate A strategy hwin
      initial
  exact SourceFreeBeliefCodeParityCertificate.nonempty_rationalPolicy
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonLinkedNext A strategy hwin)
    raw certificate
    (InputFreeRunParityTreeAutomaton.rationalRunBasis_of_finite _)

abbrev ProfiledRawJointGuardedCommonLinkedPolicyReachable
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial) :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonLinkedNext A strategy hwin)
    policy

/-- Legality of one reachable linked policy state exposes one current pair and
one complete, jointly selected child-pair table. -/
theorem exists_profiledRawJointGuardedCommonLinkedMoveAt
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin
        initial)
      (initial.linkedCode A strategy hwin)
      (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonLinkedNext A strategy hwin)).State)
    (hreachable :
      ProfiledRawJointGuardedCommonLinkedPolicyReachable A strategy hwin
        initial policy state) :
    ∃ move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin,
      ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin state.1
          move ∧
        ∀ input,
          policy.successor state input =
            let childCode :=
              profiledRawJointGuardedCommonLinkedNext A strategy hwin state.1
                move input
            (childCode,
              (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin
                initial).step state.2 childCode) := by
  exact SourceFreeBeliefCodeParityRationalPolicy.exists_sourceFreeMove
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonLinkedNext A strategy hwin)
    policy state hreachable

namespace ProfiledRawJointGuardedCommonLinkedMoveValid

/-- A valid linked move's current pair is exactly the pair in the public
linked code. -/
theorem current_eq
    {code : ProfiledRawJointGuardedCommonLinkedCode A strategy hwin}
    {move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin}
    (hvalid : ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin
      code move) :
    move.1 = code.2 := by
  rcases hvalid with ⟨point, hcode, hmove⟩
  exact hmove ▸ hcode ▸ rfl

/-- Every relation holding between each literal common occurrence and all its
literal children is preserved by an arbitrary valid linked move. -/
theorem parent_child
    {code : ProfiledRawJointGuardedCommonLinkedCode A strategy hwin}
    {move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin}
    (hvalid : ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin
      code move)
    (R : CommonPair A strategy hwin → CommonPair A strategy hwin →
      (In₁ × In₂) → Prop)
    (hsemantic : ∀ point : SemanticPoint A strategy, ∀ input,
      R (point.move A strategy hwin)
        ((point.step A strategy input).move A strategy hwin) input)
    (input : In₁ × In₂) :
    R move.1 (move.2 input) input := by
  rcases hvalid with ⟨point, _hcode, hmove⟩
  rw [← hmove]
  exact hsemantic point input

/-- The child pair carried by a valid linked move is also an allowed child in
the existing local-shadow interface. -/
theorem child_allowed
    {code : ProfiledRawJointGuardedCommonLinkedCode A strategy hwin}
    {move : ProfiledRawJointGuardedCommonLinkedMove A strategy hwin}
    (hvalid : ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin
      code move)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessorAllowed A strategy hwin move.1 input
      (move.2 input) := by
  rcases hvalid with ⟨point, _hcode, hmove⟩
  rw [← hmove]
  refine ⟨point.world A strategy, input, rfl, rfl, ?_⟩
  exact ProfiledRawJointGuardedCommonSemanticPoint.step_code A strategy hwin
    point input

end ProfiledRawJointGuardedCommonLinkedMoveValid

/-- **No-mosaic transition law.**  At every reachable state, any property of
literal semantic parent/child pairs holds between the pair stored in the
current finite code and the pair stored in the policy successor. -/
theorem profiledRawJointGuardedCommonLinkedPolicy_parent_child
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial)
    (state : (sourceFreeBeliefCodeParityRunAutomaton
      (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin
        initial)
      (initial.linkedCode A strategy hwin)
      (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
      (profiledRawJointGuardedCommonLinkedNext A strategy hwin)).State)
    (hreachable :
      ProfiledRawJointGuardedCommonLinkedPolicyReachable A strategy hwin
        initial policy state)
    (R : CommonPair A strategy hwin → CommonPair A strategy hwin →
      (In₁ × In₂) → Prop)
    (hsemantic : ∀ point : SemanticPoint A strategy, ∀ input,
      R (point.move A strategy hwin)
        ((point.step A strategy input).move A strategy hwin) input)
    (input : In₁ × In₂) :
    R state.1.2 (policy.successor state input).1.2 input := by
  obtain ⟨move, hvalid, hnext⟩ :=
    exists_profiledRawJointGuardedCommonLinkedMoveAt A strategy hwin initial
      policy state hreachable
  have hrel := hvalid.parent_child A strategy hwin R hsemantic input
  have hcurrent := hvalid.current_eq A strategy hwin
  have hchild := congrArg (fun successor ↦ successor.1.2) (hnext input)
  dsimp only [profiledRawJointGuardedCommonLinkedNext] at hchild
  rw [← hcurrent, hchild]
  exact hrel

/-! ## Finite reachable keys and their jointly selected tables -/

/-- Complete finite state of one linked rational policy. -/
noncomputable abbrev ProfiledRawJointGuardedCommonLinkedPolicyState
    (initial : SemanticPoint A strategy) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin initial)
    (initial.linkedCode A strategy hwin)
    (ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin)
    (profiledRawJointGuardedCommonLinkedNext A strategy hwin)).State

/-- Runtime-relevant state: one finite policy state and proof-erased
reachability in that same rational run. -/
structure ProfiledRawJointGuardedCommonLinkedPolicyKey
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial) where
  state : ProfiledRawJointGuardedCommonLinkedPolicyState A strategy hwin
    initial
  reachable :
    ProfiledRawJointGuardedCommonLinkedPolicyReachable A strategy hwin initial
      policy state

noncomputable instance profiledRawJointGuardedCommonLinkedPolicyKeyFintype
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial) :
    Fintype
      (ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin initial
        policy) := by
  classical
  let State :=
    ProfiledRawJointGuardedCommonLinkedPolicyState A strategy hwin initial
  let Reach :=
    ProfiledRawJointGuardedCommonLinkedPolicyReachable A strategy hwin initial
      policy
  let Rep := { state : State // Reach state }
  let equiv :
      ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin initial
          policy ≃ Rep :=
    { toFun := fun key ↦ ⟨key.state, key.reachable⟩
      invFun := fun key ↦ ⟨key.1, key.2⟩
      left_inv := by intro key; cases key; rfl
      right_inv := by intro key; cases key; rfl }
  exact Fintype.ofEquiv Rep equiv.symm

namespace ProfiledRawJointGuardedCommonLinkedPolicyKey

/-- Root key of one selected linked rational policy. -/
def root
    (initial : SemanticPoint A strategy)
    (policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial) :
    ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin initial
      policy :=
  ⟨policy.run [], ⟨[], rfl⟩⟩

/-- Follow the policy on one physical simultaneous input pair. -/
def next
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin initial
      policy := by
  refine ⟨policy.successor key.state input, ?_⟩
  rcases key.reachable with ⟨node, hnode⟩
  refine ⟨node ++ [input], ?_⟩
  rw [← policy.successor_at node input, hnode]

/-- Current guarded pair, carried literally in the finite public code. -/
def pair
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy) : CommonPair A strategy hwin :=
  key.state.1.2

/-- One complete linked move selected once for this reachable finite state. -/
noncomputable def move
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy) :
    ProfiledRawJointGuardedCommonLinkedMove A strategy hwin :=
  Classical.choose
    (exists_profiledRawJointGuardedCommonLinkedMoveAt A strategy hwin initial
      policy key.state key.reachable)

/-- The selected complete linked move is valid at the key's code. -/
theorem move_valid
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy) :
    ProfiledRawJointGuardedCommonLinkedMoveValid A strategy hwin key.state.1
      (key.move A strategy hwin) :=
  (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonLinkedMoveAt A strategy hwin initial
      policy key.state key.reachable)).1

/-- The selected move's first component is the key's literal current pair. -/
theorem move_current
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy) :
    (key.move A strategy hwin).1 = key.pair A strategy hwin :=
  (key.move_valid A strategy hwin).current_eq A strategy hwin

/-- The selected move realizes the whole finite successor table. -/
theorem successor_eq
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) :
    policy.successor key.state input =
      let childCode :=
        profiledRawJointGuardedCommonLinkedNext A strategy hwin key.state.1
          (key.move A strategy hwin) input
      (childCode,
        (profiledRawJointGuardedCommonLinkedCodeParityDPA A strategy hwin
          initial).step key.state.2 childCode) :=
  (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonLinkedMoveAt A strategy hwin initial
      policy key.state key.reachable)).2 input

/-- Child pair chosen by the same complete move as all other input children. -/
noncomputable def childPair
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) : CommonPair A strategy hwin :=
  (key.move A strategy hwin).2 input

/-- Existing local-shadow child package, now backed by the exact parent-linked
table rather than by incidence-code matching alone. -/
noncomputable def successorChild
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonSuccessor A strategy hwin
      (key.move A strategy hwin).1 input :=
  ⟨key.childPair A strategy hwin input,
    (key.move_valid A strategy hwin).child_allowed A strategy hwin input⟩

@[simp] theorem successorChild_pair
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) :
    (key.successorChild A strategy hwin input).1 =
      key.childPair A strategy hwin input :=
  rfl

/-- The pair in the successor key is definitionally forced by the parent's
joint child table. -/
theorem next_pair
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (input : In₁ × In₂) :
    (key.next A strategy hwin input).pair A strategy hwin =
      key.childPair A strategy hwin input := by
  exact congrArg (fun successor ↦ successor.1.2)
    (key.successor_eq A strategy hwin input)

/-- Key-level no-mosaic law for any literal parent/child relation. -/
theorem parent_child
    {initial : SemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonLinkedRationalPolicy A strategy hwin
      initial}
    (key : ProfiledRawJointGuardedCommonLinkedPolicyKey A strategy hwin
      initial policy)
    (R : CommonPair A strategy hwin → CommonPair A strategy hwin →
      (In₁ × In₂) → Prop)
    (hsemantic : ∀ point : SemanticPoint A strategy, ∀ input,
      R (point.move A strategy hwin)
        ((point.step A strategy input).move A strategy hwin) input)
    (input : In₁ × In₂) :
    R (key.pair A strategy hwin)
      ((key.next A strategy hwin input).pair A strategy hwin) input := by
  have hrel := (key.move_valid A strategy hwin).parent_child A strategy hwin
    R hsemantic input
  rw [key.move_current A strategy hwin] at hrel
  rw [key.next_pair A strategy hwin input]
  exact hrel

end ProfiledRawJointGuardedCommonLinkedPolicyKey

end

end DetParityAutomaton

end DistributedSynthesis
