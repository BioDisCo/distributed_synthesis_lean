/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonDecoratedRationalization

/-!
# Operational package for a finitely decorated guarded common policy

The decorated semantic tree chooses its finite operational annotation before
the one outer rationalization.  This file turns the resulting rational policy
into a literal finite lookup table.  Every policy state has a total selected
`(guarded pair, extra)`; unreachable states use the decorated semantic root as
a harmless fallback, while all correctness laws are explicitly guarded by
reachability in the selected rational run.

The semantic annotation function is only a construction parameter.  Runtime
state consists solely of the finite rational-policy state, and the selected
annotation is exposed by the finite table `extraAt`.
-/

namespace DistributedSynthesis

universe u v x y s b

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

variable {Extra : Type b} [Fintype Extra]

private abbrev CommonPair :=
  ProfiledRawJointGuardedCommonPair A strategy hwin

private abbrev CommonCode :=
  ProfiledRawJointIncidenceCode A (I := Unit)

private abbrev CommonPoint :=
  ProfiledRawJointGuardedCommonSemanticPoint A strategy

/-! ## Complete finite policy states and total move selection -/

/-- Complete finite state type of the decorated rational common policy. -/
noncomputable abbrev ProfiledRawJointGuardedCommonDecoratedPolicyState
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop) :=
  (sourceFreeBeliefCodeParityRunAutomaton
    (profiledRawJointGuardedCommonCodeParityDPA A
      (initial.code A strategy))
    (initial.code A strategy)
    (ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
      ExtraValid)
    (ProfiledRawJointGuardedCommonDecoratedNext A strategy hwin)).State

/-- The operational decorated state space is literally finite. -/
noncomputable instance
    profiledRawJointGuardedCommonDecoratedPolicyStateFintype
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop) :
    Fintype
      (ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
        initial ExtraValid) := by
  infer_instance

/-- Totalize decorated-move selection over the complete finite state space.
The semantic root decoration is used only at unreachable states. -/
noncomputable def profiledRawJointGuardedCommonDecoratedMoveAt
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (policy :
      ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy hwin
        initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy
      hwin initial ExtraValid) :
    CommonPair A strategy hwin × Extra := by
  classical
  exact if h :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state then
    Classical.choose
      (exists_profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin
        initial ExtraValid policy state h)
  else
    (initial.move A strategy hwin, extra initial)

omit [Fintype Extra] in
/-- On a reachable state, the total decorated selector is valid at the
state's exact incidence code. -/
theorem profiledRawJointGuardedCommonDecoratedMoveAt_valid
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (policy :
      ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy hwin
        initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy
      hwin initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state) :
    ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin ExtraValid
      state.1
      (profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin initial
        extra ExtraValid policy state) := by
  classical
  rw [profiledRawJointGuardedCommonDecoratedMoveAt, dif_pos hreachable]
  exact (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin
      initial ExtraValid policy state hreachable)).1

omit [Fintype Extra] in
/-- On a reachable state, the selected decorated move realizes the policy's
unchanged complete child-code assignment for every physical input pair. -/
theorem profiledRawJointGuardedCommonDecoratedMoveAt_successor_eq
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (policy :
      ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy hwin
        initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy
      hwin initial ExtraValid)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state)
    (input : In₁ × In₂) :
    policy.successor state input =
      (((profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin initial
          extra ExtraValid policy state).1.bothNextCode A strategy hwin input),
        (profiledRawJointGuardedCommonCodeParityDPA A
          (initial.code A strategy)).step state.2
            ((profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin
              initial extra ExtraValid policy state).1.bothNextCode A strategy
                hwin input)) := by
  classical
  rw [profiledRawJointGuardedCommonDecoratedMoveAt, dif_pos hreachable]
  exact (Classical.choose_spec
    (exists_profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin
      initial ExtraValid policy state hreachable)).2 input

/-! ## Operational package -/

/-- One decorated rational policy together with a literal total finite table
from policy states to `(guarded pair, extra)`.  The semantic annotation
function is absent from the package and therefore absent from runtime state. -/
structure ProfiledRawJointGuardedCommonDecoratedPolicyPackage
    (initial : CommonPoint A strategy)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    where
  policy :
    ProfiledRawJointGuardedCommonDecoratedRationalPolicy A strategy hwin
      initial ExtraValid
  moveAt :
    ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin initial
      ExtraValid → CommonPair A strategy hwin × Extra
  moveAt_valid : ∀ state,
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state →
      ProfiledRawJointGuardedCommonDecoratedMoveValid A strategy hwin
        ExtraValid state.1 (moveAt state)
  successor_eq : ∀ state,
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid policy state →
      ∀ input,
        policy.successor state input =
          ((moveAt state).1.bothNextCode A strategy hwin input,
            (profiledRawJointGuardedCommonCodeParityDPA A
              (initial.code A strategy)).step state.2
                ((moveAt state).1.bothNextCode A strategy hwin input))

omit [Fintype Extra] in
/-- The semantic decorated tree yields an operational finite package. -/
theorem nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hextra : ∀ point : CommonPoint A strategy,
      ExtraValid (point.code A strategy) (point.move A strategy hwin)
        (extra point)) :
    Nonempty
      (ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
        initial ExtraValid) := by
  rcases nonempty_profiledRawJointGuardedCommonDecoratedRationalPolicy A
      strategy hwin initial extra ExtraValid hextra with ⟨policy⟩
  refine ⟨{
    policy := policy
    moveAt := profiledRawJointGuardedCommonDecoratedMoveAt A strategy hwin
      initial extra ExtraValid policy
    moveAt_valid := ?_
    successor_eq := ?_ }⟩
  · intro state hreachable
    exact profiledRawJointGuardedCommonDecoratedMoveAt_valid A strategy hwin
      initial extra ExtraValid policy state hreachable
  · intro state hreachable input
    exact profiledRawJointGuardedCommonDecoratedMoveAt_successor_eq A strategy
      hwin initial extra ExtraValid policy state hreachable input

/-- Canonical choice of the operational decorated package.  The semantic
annotation is consumed only while constructing this finite constant. -/
noncomputable def profiledRawJointGuardedCommonDecoratedPolicyPackage
    (initial : CommonPoint A strategy)
    (extra : CommonPoint A strategy → Extra)
    (ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop)
    (hextra : ∀ point : CommonPoint A strategy,
      ExtraValid (point.code A strategy) (point.move A strategy hwin)
        (extra point)) :
    ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy hwin
      initial ExtraValid :=
  Classical.choice
    (nonempty_profiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial extra ExtraValid hextra)

namespace ProfiledRawJointGuardedCommonDecoratedPolicyPackage

variable
  {initial : CommonPoint A strategy}
  {ExtraValid : CommonCode A → CommonPair A strategy hwin → Extra → Prop}

/-- Guarded common pair projected from the total finite decorated lookup. -/
def pairAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid) : CommonPair A strategy hwin :=
  (package.moveAt state).1

/-- Finite operational annotation projected from the same total lookup. -/
def extraAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state : ProfiledRawJointGuardedCommonDecoratedPolicyState A strategy hwin
      initial ExtraValid) : Extra :=
  (package.moveAt state).2

section
omit [Fintype Extra]

/-- The initial decorated policy state is reachable. -/
theorem initial_reachable
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid) :
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial ExtraValid package.policy (package.policy.run []) :=
  ⟨[], rfl⟩

/-- Every successor of a reachable decorated state remains reachable in the
same selected rational run. -/
theorem successor_reachable
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    {state}
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
      initial ExtraValid package.policy
        (package.policy.successor state input) := by
  rcases hreachable with ⟨node, hnode⟩
  refine ⟨node ++ [input], ?_⟩
  rw [← package.policy.successor_at node input, hnode]

/-- The projected guarded pair is valid at every reachable state. -/
theorem pairAt_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state) :
    ProfiledRawJointGuardedCommonMoveValid A strategy hwin state.1
      (package.pairAt A strategy hwin state) :=
  (package.moveAt_valid state hreachable).1

/-- The projected annotation satisfies its concrete source-free validity
predicate at every reachable state. -/
theorem extraAt_valid
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state) :
    ExtraValid state.1 (package.pairAt A strategy hwin state)
      (package.extraAt A strategy hwin state) :=
  (package.moveAt_valid state hreachable).2

/-- The all-input successor table depends only on the projected guarded pair;
the finite annotation is payload and does not alter the public transition. -/
theorem successor_eq_pairAt
    (package : ProfiledRawJointGuardedCommonDecoratedPolicyPackage A strategy
      hwin initial ExtraValid)
    (state)
    (hreachable :
      ProfiledRawJointGuardedCommonDecoratedPolicyReachable A strategy hwin
        initial ExtraValid package.policy state)
    (input : In₁ × In₂) :
    package.policy.successor state input =
      ((package.pairAt A strategy hwin state).bothNextCode A strategy hwin
          input,
        (profiledRawJointGuardedCommonCodeParityDPA A
          (initial.code A strategy)).step state.2
            ((package.pairAt A strategy hwin state).bothNextCode A strategy
              hwin input)) :=
  package.successor_eq state hreachable input

end

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
