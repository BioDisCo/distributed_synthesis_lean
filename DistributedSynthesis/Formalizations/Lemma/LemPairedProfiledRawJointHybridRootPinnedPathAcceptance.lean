/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridRootPinnedPersistentPhysicalClose
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefRootPinnedTailAcceptance

/-!
# Anti-mosaic path acceptance in the exact root-pinned hybrid policy

The finite carrier may retain the common and strict children of the first
ambiguous round as different states.  Correctness only needs every later
edge to belong to the one guarded policy chosen before that round.

This file states that invariant directly on complete guarded states.  A path
starting at any literal first child and following policy-image edges is
accepted from that child's actual code-DPA control.  The proof projects the
false-bit tail to the generic re-rooted policy; it neither selects a fresh
policy nor resets the objective automaton.
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

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (hwin : ∀ env : EnvironmentSequence In₁ In₂,
    A.Accepts (execution strategy env))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Policy-image edges preserve reachability in the same guarded run. -/
theorem profiledRawJointHybridInitialRootPinned_reachable_of_allowedTarget
    (first : In₁ × In₂)
    {source target :
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first}
    (hsource :
      ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin first
        source)
    (hedge : ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy
      hwin first source target) :
    ProfiledRawJointHybridInitialRootPinnedReachable A strategy hwin first
      target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hedge with ⟨childCode, hchild⟩
  refine ⟨node ++ [childCode], ?_⟩
  rw [← (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin
    first).policy.successor_at node childCode, hnode, hchild]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Any path beginning at a literal first child and using only image edges
of the same guarded policy is accepted from the exact objective control at
that child.  The emitted word is the sequence of positive-time hybrid codes.
-/
theorem profiledRawJointHybridInitialRootPinned_acceptsFrom_of_allowedPath
    (first : In₁ × In₂)
    (firstChild : ProfiledRawJointHybridCode A)
    (states : Nat →
      ProfiledRawJointHybridInitialRootPinnedGuardedState A strategy first)
    (hzero : states 0 =
      (profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
        ).policy.run [firstChild])
    (hstep : ∀ n,
      ProfiledRawJointHybridInitialRootPinnedAllowedTarget A strategy hwin
        first (states n) (states (n + 1))) :
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
      ).AcceptsFrom (states 0).2.2
        (fun n ↦ (states (n + 1)).2.1) := by
  classical
  let package :=
    profiledRawJointHybridInitialRootPinnedPolicy A strategy hwin first
  choose childCode hchild using hstep
  have hstates : ∀ n,
      states n = package.policy.run
        ([firstChild] ++ branchNode childCode n) := by
    intro n
    induction n with
    | zero => simpa using hzero
    | succ n ih =>
        calc
          states (n + 1) =
              package.policy.successor (states n) (childCode n) :=
            (hchild n).symm
          _ = package.policy.successor
              (package.policy.run ([firstChild] ++ branchNode childCode n))
              (childCode n) := by rw [ih]
          _ = package.policy.run
              (([firstChild] ++ branchNode childCode n) ++
                [childCode n]) :=
            package.policy.successor_at
              ([firstChild] ++ branchNode childCode n) (childCode n)
          _ = package.policy.run
              ([firstChild] ++ (branchNode childCode n ++
                [childCode n])) := by rw [List.append_assoc]
  have hfresh : ∀ n, (states n).1 = false := by
    intro n
    rw [hstates n]
    exact InputFreeRunParityTreeAutomaton.rootGuardedPolicy_fresh_false
      (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy first)
      (sourceFreeBeliefCodeParityRootAllowed
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (profiledRawJointHybridFiniteCodeNext A)
        (profiledRawJointHybridInitialExactRootPredicate A strategy first))
      package.policy firstChild (branchNode childCode n)
  let tailStates : Nat →
      (ProfiledRawJointHybridInitialRootPinnedRunAutomaton A strategy
        first).State := fun n ↦ (states n).2
  have htailZero : tailStates 0 =
      (package.tailCodePolicy
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (profiledRawJointHybridNext A) firstChild).run [] := by
    change (states 0).2 = (package.policy.run ([firstChild] ++ [])).2
    simpa using congrArg Prod.snd hzero
  have htailStep : ∀ n,
      package.TailAllowedTarget
        (profiledRawJointHybridCodeParityDPA A
          (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
        (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
        (ProfiledRawJointHybridProvenanceValid A strategy)
        (profiledRawJointHybridNext A) firstChild
        (tailStates n) (tailStates (n + 1)) := by
    intro n
    refine ⟨childCode n, ?_⟩
    change
      (package.policy.successor (false, (states n).2) (childCode n)).2 =
        (states (n + 1)).2
    have hstate : states n = (false, (states n).2) := by
      apply Prod.ext
      · exact hfresh n
      · rfl
    calc
      (package.policy.successor (false, (states n).2) (childCode n)).2 =
          (package.policy.successor (states n) (childCode n)).2 := by
        exact congrArg
          (fun state ↦ (package.policy.successor state (childCode n)).2)
          hstate.symm
      _ = (states (n + 1)).2 := congrArg Prod.snd (hchild n)
  have haccepts := package.acceptsFrom_of_tailAllowedTarget_path
    (profiledRawJointHybridCodeParityDPA A
      (ProfiledRawJointHybridInitialRootPinnedCode A strategy first))
    (ProfiledRawJointHybridInitialRootPinnedCode A strategy first)
    (ProfiledRawJointHybridProvenanceValid A strategy)
    (profiledRawJointHybridNext A) firstChild tailStates htailZero htailStep
  rw [hzero]
  simpa only [tailStates] using haccepts

end

end DetParityAutomaton

end DistributedSynthesis
