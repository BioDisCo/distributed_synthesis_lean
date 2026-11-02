/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralCombinedFreshPendingOnlyBoundary
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# Anti-mosaic acceptance of recursively refreshed literal tables

The pending-only carrier installs a new pair of opposite literal tables at
every receive.  This file records why repeating that operation does not
reintroduce the representative mosaic which the outer rationalization was
designed to remove.

Starting from the root of the one decorated common policy, we iterate the
already executable leader-free freshness maps along arbitrary input and graph
sequences.  Their unique current copy follows exactly one successor of that
same rational policy at every round.  Hence it is a
`SourceFreeBeliefCodeParityPolicyPath` and its child-code word is accepted.

The accepted letter at round `n` is then identified with the incidence code
of the exact literal child whose opposite tables are installed by the fresh
boundary key.  The proof uses occurrence identity
(`literalRightSeamFreshKey_childCode`), not an equal-code replacement.  No
global branch selector, canonical open interpretation, graph decoder,
orientation bit, leader bit, history, or semantic view is supplied to an
executable map.
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

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

private abbrev CrossValid :=
  ProfiledRawJointGuardedCommonLiteralCrossExtraValid A strategy hwin

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable {initial : CommonPoint A strategy}

private abbrev Package :=
  ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev State :=
  ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
    (CrossValid A strategy hwin)

private abbrev FreshOne :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessOneState A strategy hwin
    initial

private abbrev FreshTwo :=
  ProfiledRawJointGuardedCommonDecoratedFreshnessTwoState A strategy hwin
    initial

private abbrev DecoratedValid :=
  ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
    (CrossValid A strategy hwin)

private abbrev DecoratedNext :=
  ProfiledRawJointGuardedCommonDecoratedNext
    (A := A) (strategy := strategy) (hwin := hwin)
    (Extra := ProfiledRawJointGuardedCommonLiteralCrossExtra A)

private abbrev CodeDPA :=
  profiledRawJointGuardedCommonCodeParityDPA A (initial.code A strategy)

/-! ## The leader-free local freshness trace -/

/-- Iterate the two endpoint-local freshness maps.  `graph` is consumed only
by this proof-side product; each endpoint component is one of the already
defined local receive/nonreceive functions. -/
def literalCombinedFreshPendingFreshnessTrace
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    Nat → FreshOne A strategy hwin (initial := initial) ×
      FreshTwo A strategy hwin (initial := initial)
  | 0 => decoratedFreshnessBothInitial A strategy hwin
      (package.policy.run [])
  | n + 1 =>
      let current := literalCombinedFreshPendingFreshnessTrace package inputs
        graphs n
      decoratedFreshnessLocalStep A strategy hwin package current.1 current.2
        (inputs n) (graphs n)

@[simp] theorem literalCombinedFreshPendingFreshnessTrace_zero
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    package.literalCombinedFreshPendingFreshnessTrace A strategy hwin inputs
        graphs 0 =
      decoratedFreshnessBothInitial A strategy hwin
        (package.policy.run []) :=
  rfl

@[simp] theorem literalCombinedFreshPendingFreshnessTrace_succ
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) (n : Nat) :
    package.literalCombinedFreshPendingFreshnessTrace A strategy hwin inputs
        graphs (n + 1) =
      let current := package.literalCombinedFreshPendingFreshnessTrace A
        strategy hwin inputs graphs n
      decoratedFreshnessLocalStep A strategy hwin package current.1 current.2
        (inputs n) (graphs n) :=
  rfl

/-- The local freshness invariant is preserved along the entire trace. -/
theorem literalCombinedFreshPendingFreshnessTrace_aligned
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) : ∀ n,
    let current := package.literalCombinedFreshPendingFreshnessTrace A
      strategy hwin inputs graphs n
    DecoratedFreshnessAligned A strategy hwin current.1 current.2 := by
  intro n
  induction n with
  | zero =>
      exact decoratedFreshnessBothInitial_aligned A strategy hwin
        (package.policy.run [])
  | succ n ih =>
      rw [package.literalCombinedFreshPendingFreshnessTrace_succ A strategy
        hwin inputs graphs n]
      exact decoratedFreshnessLocalStep_aligned A strategy hwin package _ _ ih
        (inputs n) (graphs n)

/-- The unique current copy advances by one successor of the same decorated
policy, independently of the physical graph case. -/
theorem literalCombinedFreshPendingFreshnessTrace_current_succ
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) (n : Nat) :
    let current := package.literalCombinedFreshPendingFreshnessTrace A
      strategy hwin inputs graphs n
    let next := package.literalCombinedFreshPendingFreshnessTrace A strategy
      hwin inputs graphs (n + 1)
    decoratedFreshnessCurrent A strategy hwin next.1 next.2 =
      package.policy.successor
        (decoratedFreshnessCurrent A strategy hwin current.1 current.2)
        (inputs n) := by
  rw [package.literalCombinedFreshPendingFreshnessTrace_succ A strategy hwin
    inputs graphs n]
  exact decoratedFreshnessLocalStep_current_eq_successor A strategy hwin
    package _ _
      (package.literalCombinedFreshPendingFreshnessTrace_aligned A strategy
        hwin inputs graphs n)
      (inputs n) (graphs n)

/-! ## One coherent accepted policy path -/

/-- Read the unique current freshness copy as a path through the one selected
decorated policy. -/
def literalCombinedFreshPendingPolicyPath
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    SourceFreeBeliefCodeParityPolicyPath
      (CodeDPA A strategy (initial := initial)) (initial.code A strategy)
      (DecoratedValid A strategy hwin) (DecoratedNext A strategy hwin)
      package.policy where
  state := fun n ↦
    let current := package.literalCombinedFreshPendingFreshnessTrace A
      strategy hwin inputs graphs n
    decoratedFreshnessCurrent A strategy hwin current.1 current.2
  direction := inputs
  initial := rfl
  successor := by
    intro n
    exact package.literalCombinedFreshPendingFreshnessTrace_current_succ A
      strategy hwin inputs graphs n

/-- The code word produced by recursively refreshed local freshness copies is
accepted by the original common-code objective. -/
theorem literalCombinedFreshPendingPolicyPath_accepts
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    (CodeDPA A strategy (initial := initial)).Accepts
      ((package.literalCombinedFreshPendingPolicyPath A strategy hwin inputs
        graphs).childCodeWord
          (CodeDPA A strategy (initial := initial))
          (initial.code A strategy) (DecoratedValid A strategy hwin)
          (DecoratedNext A strategy hwin) package.policy) :=
  (package.literalCombinedFreshPendingPolicyPath A strategy hwin inputs
    graphs).accepts
      (CodeDPA A strategy (initial := initial)) (initial.code A strategy)
      (DecoratedValid A strategy hwin) (DecoratedNext A strategy hwin)
      package.policy

/-! ## The accepted letters are the freshly installed literal children -/

/-- Incidence-code word of the exact literal occurrences whose opposite
tables are installed at successive fresh boundary keys. -/
def literalCombinedFreshPendingInstalledChildCodeWord
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    OmegaWord (ProfiledRawJointIncidenceCode A (I := Unit)) :=
  fun n ↦
    let current := package.literalCombinedFreshPendingFreshnessTrace A
      strategy hwin inputs graphs n
    let state := decoratedFreshnessCurrent A strategy hwin current.1 current.2
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalRightSeamFreshKey A strategy hwin state
        (inputs n))).code A strategy

/-- Each accepted policy edge is literally the code of the exact child used
to construct the newly installed opposite tables. -/
theorem literalCombinedFreshPendingInstalledChildCodeWord_eq_policyPath
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    package.literalCombinedFreshPendingInstalledChildCodeWord A strategy hwin
        inputs graphs =
      (package.literalCombinedFreshPendingPolicyPath A strategy hwin inputs
        graphs).childCodeWord
          (CodeDPA A strategy (initial := initial))
          (initial.code A strategy) (DecoratedValid A strategy hwin)
          (DecoratedNext A strategy hwin) package.policy := by
  funext n
  let path := package.literalCombinedFreshPendingPolicyPath A strategy hwin
    inputs graphs
  have hreachable := path.reachable
    (CodeDPA A strategy (initial := initial)) (initial.code A strategy)
    (DecoratedValid A strategy hwin) (DecoratedNext A strategy hwin)
    package.policy n
  change
    (package.literalRightSeamChildPoint A strategy hwin
      (package.literalRightSeamFreshKey A strategy hwin (path.state n)
        (inputs n))).code A strategy = (path.state (n + 1)).1
  rw [package.literalRightSeamFreshKey_childCode A strategy hwin
    (path.state n) hreachable (inputs n)]
  exact congrArg Prod.fst (path.successor n).symm

/-- Recursive literal-table installation is anti-mosaic at the code-parity
level: the exact installed-child word is accepted without selecting a global
open interpretation or reselecting a semantic representative. -/
theorem literalCombinedFreshPendingInstalledChildCodeWord_accepts
    (package : Package A strategy hwin (initial := initial))
    (inputs : Nat → In₁ × In₂) (graphs : Nat → Graph) :
    (CodeDPA A strategy (initial := initial)).Accepts
      (package.literalCombinedFreshPendingInstalledChildCodeWord A strategy
        hwin inputs graphs) := by
  rw [package.literalCombinedFreshPendingInstalledChildCodeWord_eq_policyPath
    A strategy hwin inputs graphs]
  exact package.literalCombinedFreshPendingPolicyPath_accepts A strategy hwin
    inputs graphs

/-- The concrete pending-only boundary key is definitionally the same fresh
key used in the accepted installed-child word. -/
@[simp] theorem literalCombinedFreshPendingBoundaryKey_eq_freshKey
    (package : Package A strategy hwin (initial := initial))
    (one : ProfiledRawJointGuardedCommonLiteralCombinedFreshOneShared A
      strategy hwin package)
    (two : ProfiledRawJointGuardedCommonLiteralCombinedFreshTwoShared A
      strategy hwin package)
    (input : In₁ × In₂) :
    package.literalCombinedFreshPendingBoundaryKey A strategy hwin one two
        input =
      package.literalRightSeamFreshKey A strategy hwin
        (package.literalCombinedFreshPendingBoundarySource A strategy hwin one
          two) input :=
  rfl

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
