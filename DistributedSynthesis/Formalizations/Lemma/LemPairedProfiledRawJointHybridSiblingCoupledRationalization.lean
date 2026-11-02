/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridInitialRootPinnedPolicy
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointCommonBothRestart
import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointOneSidedActualChild
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenClassifiedAutomaton

/-!
# Pre-policy rationalization of a common/strict sibling pair

The common and strict interpretations of the ambiguous second round are
different proof-side states.  Rationalizing their block strategies after
selecting two independent policy moves is therefore unsound.  Before that
selection, however, they are projections of one literal raw semantic child:
the process-one family is definitionally shared by `both` and strict-left,
and the process-two family is definitionally shared by `both` and
strict-right.

This file performs the finite extraction at that earlier point.  Each
two-member semantic sibling family is passed once to the existing classified
finite-root narrowing.  The resulting literal finite table has one shared
blind sender and, in every receiver row, records both the exact opposite-side
target and its complete next information class.  It is therefore already a
valid move of `ProfiledOpenClassifiedFamilyAllowed`, the transition predicate
used by the two-sorted outer rationalization.

The Boolean below is only the proof index of the two semantic obligations.
It is folded into the receiver side of `finiteRootFamilyMonitor`; it is never
given to the blind sender or to either runtime process.  In particular no
graph, orientation, or strict-leader signal occurs in the extracted table.
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

/-! ## The three raw siblings before any finite policy is selected -/

/-- The literal raw family immediately before the ambiguous round. -/
def profiledRawJointHybridInitialSiblingParentFamily
    (first : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  profiledRawJointCommonWorldFamily A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first)

/-- The raw direction common to the `both`, strict-left, and strict-right
interpretations of that round.  The side is resolved only afterwards. -/
def profiledRawJointHybridInitialSiblingDirection
    (current : In₁ × In₂) :
    ProfiledRawJointFamilyDirection
      (I := Unit) (In₁ := In₁) (In₂ := In₂) :=
  profiledRawJointBothRestartDirection current

/-- The two-sided common child. -/
def profiledRawJointHybridInitialCommonSemanticSibling
    (first current : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  (profiledRawJointHybridInitialSiblingParentFamily A strategy first
    ).semanticChild A
      (profiledRawJointHybridInitialSiblingDirection current)

/-- Strict-left sibling: only the process-one/right family remains live. -/
def profiledRawJointHybridInitialStrictLeftSemanticSibling
    (first current : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  (profiledRawJointHybridInitialSiblingParentFamily A strategy first
    ).leftActualChild A
      (profiledRawJointHybridInitialSiblingDirection current)

/-- Strict-right mirror. -/
def profiledRawJointHybridInitialStrictRightSemanticSibling
    (first current : In₁ × In₂) :
    ProfiledRawJointSemanticFamily A strategy (I := Unit) :=
  (profiledRawJointHybridInitialSiblingParentFamily A strategy first
    ).rightActualChild A
      (profiledRawJointHybridInitialSiblingDirection current)

/-- Literal common world after the ambiguous round. -/
def profiledRawJointHybridInitialSiblingWorld
    (first current : In₁ × In₂) :
    ProfiledRawJointCommonBaseWorld A strategy :=
  profiledRawJointCommonWorldAfterBoth A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first) current

section
omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁]
    [Fintype In₂] [Fintype Out₁] [Fintype Out₂]

/-- The common child is the literal next common world, before any
representative or policy move is chosen. -/
theorem profiledRawJointHybridInitialCommonSemanticSibling_eq_world
    (first current : In₁ × In₂) :
    profiledRawJointHybridInitialCommonSemanticSibling A strategy first
        current =
      profiledRawJointCommonWorldFamily A
        (profiledRawJointHybridInitialSiblingWorld A strategy first current) :=
  profiledRawJointCommonWorld_semanticChild_eq_bothRestart A
    (ProfiledRawJointHybridInitialRootPinnedWorld A strategy first) current

/-- Process one's complete semantic member is literally present in the
common child. -/
@[simp] theorem profiledRawJointHybridInitialCommonSemanticSibling_right
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialCommonSemanticSibling A strategy first
      current).right () =
      some ((profiledRawJointHybridInitialSiblingWorld A strategy first
        current).procOneMember A) := by
  rw [profiledRawJointHybridInitialCommonSemanticSibling_eq_world]
  rfl

/-- The very same complete member is present in the indistinguishable
strict-left sibling. -/
@[simp] theorem profiledRawJointHybridInitialStrictLeftSemanticSibling_right
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialStrictLeftSemanticSibling A strategy first
      current).right () =
      some ((profiledRawJointHybridInitialSiblingWorld A strategy first
        current).procOneMember A) := by
  change
    ((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).leftActualChild A
        (profiledRawJointHybridInitialSiblingDirection current)).right () = _
  rw [← ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual
    A (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current)]
  exact profiledRawJointHybridInitialCommonSemanticSibling_right A strategy
    first current

/-- Process-two/common member. -/
@[simp] theorem profiledRawJointHybridInitialCommonSemanticSibling_left
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialCommonSemanticSibling A strategy first
      current).left () =
      some ((profiledRawJointHybridInitialSiblingWorld A strategy first
        current).procTwoMember A) := by
  rw [profiledRawJointHybridInitialCommonSemanticSibling_eq_world]
  rfl

/-- Process-two/strict-right mirror. -/
@[simp] theorem profiledRawJointHybridInitialStrictRightSemanticSibling_left
    (first current : In₁ × In₂) :
    (profiledRawJointHybridInitialStrictRightSemanticSibling A strategy first
      current).left () =
      some ((profiledRawJointHybridInitialSiblingWorld A strategy first
        current).procTwoMember A) := by
  change
    ((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).rightActualChild A
        (profiledRawJointHybridInitialSiblingDirection current)).left () = _
  rw [← ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual
    A (profiledRawJointHybridInitialSiblingParentFamily A strategy first)
      (profiledRawJointHybridInitialSiblingDirection current)]
  exact profiledRawJointHybridInitialCommonSemanticSibling_left A strategy
    first current

/-- The complete raw process-one lambda projection is shared before
rationalization, not merely its first output. -/
theorem profiledRawJointHybridInitial_common_strictLeft_rightLambda_eq
    (first current : In₁ × In₂) :
    ((profiledRawJointHybridInitialCommonSemanticSibling A strategy first
        current).move A).rightLambda =
      ((profiledRawJointHybridInitialStrictLeftSemanticSibling A strategy first
        current).move A).rightLambda := by
  funext index
  change
    (((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).semanticChild A
        (profiledRawJointHybridInitialSiblingDirection current)).right index
      ).map (fun member ↦ member.1.lambdaOfStrategy) =
    (((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).leftActualChild A
        (profiledRawJointHybridInitialSiblingDirection current)).right index
      ).map (fun member ↦ member.1.lambdaOfStrategy)
  rw [ProfiledRawJointSemanticFamily.semanticChild_right_eq_leftActual]

/-- Process-two mirror. -/
theorem profiledRawJointHybridInitial_common_strictRight_leftLambda_eq
    (first current : In₁ × In₂) :
    ((profiledRawJointHybridInitialCommonSemanticSibling A strategy first
        current).move A).leftLambda =
      ((profiledRawJointHybridInitialStrictRightSemanticSibling A strategy
        first current).move A).leftLambda := by
  funext index
  change
    (((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).semanticChild A
        (profiledRawJointHybridInitialSiblingDirection current)).left index
      ).map (fun member ↦ member.1.lambdaOfStrategy) =
    (((profiledRawJointHybridInitialSiblingParentFamily A strategy first
      ).rightActualChild A
        (profiledRawJointHybridInitialSiblingDirection current)).left index
      ).map (fun member ↦ member.1.lambdaOfStrategy)
  rw [ProfiledRawJointSemanticFamily.semanticChild_left_eq_rightActual]

end

/-! ## Two finite semantic families for one simultaneous extraction -/

/-- Both proof indices name the same process-one entry.  Keeping `Bool` here
makes explicit that the classified table was extracted for both sibling
obligations at once. -/
def profiledRawJointHybridInitialRightSiblingEntry
    (first current : In₁ × In₂) (_ : Bool) :
    ProcOnePairedEntryRep strategy :=
  (profiledRawJointHybridInitialSiblingWorld A strategy first current).procOne A

def profiledRawJointHybridInitialRightSiblingMinimum
    (first current : In₁ × In₂) (_ : Bool) : A.State :=
  (profiledRawJointHybridInitialSiblingWorld A strategy first current).root

def profiledRawJointHybridInitialLeftSiblingEntry
    (first current : In₁ × In₂) (_ : Bool) :
    ProcTwoPairedEntryRep strategy :=
  (profiledRawJointHybridInitialSiblingWorld A strategy first current).procTwo A

def profiledRawJointHybridInitialLeftSiblingMinimum
    (first current : In₁ × In₂) (_ : Bool) : A.State :=
  (profiledRawJointHybridInitialSiblingWorld A strategy first current).root

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointHybridInitialRightSibling_view_eq
    (first current : In₁ × In₂) (index : Bool) :
    currentView Proc.one
        (profiledRawJointHybridInitialRightSiblingEntry A strategy first
          current index).leftHistory =
      currentView Proc.one
        (profiledRawJointHybridInitialRightSiblingEntry A strategy first
          current false).leftHistory :=
  rfl

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂]
    [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂] in
theorem profiledRawJointHybridInitialLeftSibling_view_eq
    (first current : In₁ × In₂) (index : Bool) :
    currentView Proc.two
        (profiledRawJointHybridInitialLeftSiblingEntry A strategy first
          current index).rightHistory =
      currentView Proc.two
        (profiledRawJointHybridInitialLeftSiblingEntry A strategy first
          current false).rightHistory :=
  rfl

/-! ## One classified table, with exact target and next-family data -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A single finite classified right move extracted from the two sibling
obligations.  `Valid` contains both universal-thread acceptance and the
complete exact-target/next-class law. -/
theorem exists_profiledRawJointHybridInitialRightSiblingClassifiedMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (first current : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧
        ProfiledOpenClassifiedFamilyAllowed A (move.roots A)
          (move.successor A) := by
  obtain ⟨move, hvalid, _source, _hsource⟩ :=
    exists_valid_profiledOpenRightClassifiedMove_of_winning_family A strategy
      hwin
      (profiledRawJointHybridInitialRightSiblingEntry A strategy first current)
      (profiledRawJointHybridInitialRightSiblingMinimum A strategy first current)
      false
      (profiledRawJointHybridInitialRightSibling_view_eq A strategy first
        current)
      basis
  refine ⟨move, hvalid, ?_⟩
  exact ⟨move, hvalid, rfl, rfl⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Left/strict-right mirror. -/
theorem exists_profiledRawJointHybridInitialLeftSiblingClassifiedMove
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (first current : In₁ × In₂)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧
        ProfiledOpenClassifiedFamilyAllowed A (move.roots A)
          (move.successor A) := by
  obtain ⟨move, hvalid, _source, _hsource⟩ :=
    exists_valid_profiledOpenLeftClassifiedMove_of_winning_family A strategy
      hwin
      (profiledRawJointHybridInitialLeftSiblingEntry A strategy first current)
      (profiledRawJointHybridInitialLeftSiblingMinimum A strategy first current)
      false
      (profiledRawJointHybridInitialLeftSibling_view_eq A strategy first
        current)
      basis
  refine ⟨move, hvalid, ?_⟩
  exact ⟨move, hvalid, rfl, rfl⟩

/-! ## The table remains coupled after outer rationalization -/

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- At every reachable classified family state, the rational outer policy
first selects one literal valid table and only then projects its successor at
the environment direction.  Thus the common and strict sibling directions
cannot acquire independently rationalized lambdas. -/
theorem exists_profiledOpenClassifiedMove_at_reachableFamily
    (initialRoots : Finset (ProfiledOpenClassifiedAnchor A))
    (policy :
      (profiledOpenClassifiedFamilyRunAutomaton A initialRoots
        ).RationalTransitionPolicy)
    (roots : Finset (ProfiledOpenClassifiedAnchor A))
    (hreachable : TwoSortedFamilyPolicy.Reachable
      (profiledOpenClassifiedAnchorPriority A) initialRoots
      (ProfiledOpenClassifiedFamilyAllowed A) policy roots) :
    ∃ move : ProfiledOpenClassifiedMove A,
      move.Valid A ∧ move.roots A = roots ∧
        ∀ direction : ProfiledOpenClassifiedDirection A,
          policy.successor (.family roots) direction =
            .chosen (move.successor A direction).1
              (move.successor A direction).2 := by
  obtain ⟨next, hallowed, hsuccessor⟩ :=
    TwoSortedFamilyPolicy.exists_shared_family_transition
      (profiledOpenClassifiedAnchorPriority A) initialRoots
      (ProfiledOpenClassifiedFamilyAllowed A) policy roots hreachable
  obtain ⟨move, hvalid, hroots, hnext⟩ := hallowed
  subst next
  exact ⟨move, hvalid, hroots, hsuccessor⟩

end

end DetParityAutomaton

end DistributedSynthesis
