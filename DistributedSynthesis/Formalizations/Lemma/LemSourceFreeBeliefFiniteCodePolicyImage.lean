/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefFiniteCodeDirection
import DistributedSynthesis.Formalizations.Lemma.LemSourceFreeBeliefCodePolicyPathAcceptance

/-!
# The finite image of a child-code rational policy

After `sourceFreeBeliefFiniteCodeNext` replaces the possibly infinite raw
direction alphabet by the finite child-code alphabet, one rational policy has
a genuinely finite transition image.  This file exposes that image as a
finite successor set and as the relational predicate `AllowedTarget`.

An allowed edge remembers only that *some* child-code response of this one
policy has the advertised target.  It does not select a new rational policy
or splice independently accepted runs.  Consequently reachability is
preserved, and every root-started path made of allowed edges is one coherent
path of the original rational policy.  The generic path-acceptance theorem
then gives both parity of policy states and acceptance of the positive-time
child-code word.

No physical block, hierarchy side, leader observation, or initial-block
regularization occurs in this layer.
-/

namespace DistributedSynthesis

universe u v w z

section

variable {RawDirection : Type u} {Move : Type v} {BeliefCode : Type z}
variable [Fintype BeliefCode] [Nonempty RawDirection]

variable
  (D : DetParityAutomaton.{z, w} BeliefCode)
  (initialCode : BeliefCode)
  (Valid : BeliefCode → Move → Prop)
  (rawNext : BeliefCode → Move → RawDirection → BeliefCode)

namespace SourceFreeBeliefFiniteCodePolicyImage

/-- Rational policy obtained after quotienting raw directions by their finite
child code. -/
abbrev Policy :=
  SourceFreeBeliefCodeParityRationalPolicy D initialCode Valid
    (sourceFreeBeliefFiniteCodeNext rawNext)

/-- Complete finite state of that one rational policy. -/
abbrev State :=
  (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid
    (sourceFreeBeliefFiniteCodeNext rawNext)).State

/-- A target belongs to the finite image of the policy at `source` exactly
when one finite child-code response reaches it. -/
def AllowedTarget
    (policy : Policy D initialCode Valid rawNext)
    (source target : State D initialCode Valid rawNext) : Prop :=
  ∃ childCode : BeliefCode,
    policy.successor source childCode = target

/-- Materialization of all allowed targets as a finite set. -/
noncomputable def allowedTargets
    (policy : Policy D initialCode Valid rawNext)
    (source : State D initialCode Valid rawNext) :
    Finset (State D initialCode Valid rawNext) := by
  classical
  letI : Fintype (State D initialCode Valid rawNext) :=
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext rawNext)).stateFinite
  exact Finset.univ.image (policy.successor source)

/-- The finite set and the relational presentation have identical members. -/
theorem mem_allowedTargets_iff
    (policy : Policy D initialCode Valid rawNext)
    (source target : State D initialCode Valid rawNext) :
    target ∈ allowedTargets D initialCode Valid rawNext policy source ↔
      AllowedTarget D initialCode Valid rawNext policy source target := by
  classical
  simp [allowedTargets, AllowedTarget]

/-- Reachability inside the one selected rational run. -/
abbrev Reachable
    (policy : Policy D initialCode Valid rawNext)
    (state : State D initialCode Valid rawNext) : Prop :=
  SourceFreeBeliefCodeParityRationalPolicy.Reachable D initialCode Valid
    (sourceFreeBeliefFiniteCodeNext rawNext) policy state

/-- The policy root is reachable by the empty node. -/
theorem root_reachable
    (policy : Policy D initialCode Valid rawNext) :
    Reachable D initialCode Valid rawNext policy (policy.run []) :=
  ⟨[], rfl⟩

/-- Every edge in the finite policy image preserves reachability in that same
rational run. -/
theorem reachable_of_allowedTarget
    (policy : Policy D initialCode Valid rawNext)
    {source target : State D initialCode Valid rawNext}
    (hsource : Reachable D initialCode Valid rawNext policy source)
    (hedge : AllowedTarget D initialCode Valid rawNext policy source target) :
    Reachable D initialCode Valid rawNext policy target := by
  rcases hsource with ⟨node, hnode⟩
  rcases hedge with ⟨childCode, hchild⟩
  refine ⟨node ++ [childCode], ?_⟩
  rw [← policy.successor_at node childCode, hnode, hchild]

/-- Every state on a root-started allowed path is reachable in the one policy
tree. -/
theorem reachable_of_allowedTarget_path
    (policy : Policy D initialCode Valid rawNext)
    (states : Nat → State D initialCode Valid rawNext)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n,
      AllowedTarget D initialCode Valid rawNext policy (states n)
        (states (n + 1))) :
    ∀ n, Reachable D initialCode Valid rawNext policy (states n) := by
  intro n
  induction n with
  | zero =>
      rw [hzero]
      exact root_reachable D initialCode Valid rawNext policy
  | succ n ih =>
      exact reachable_of_allowedTarget D initialCode Valid rawNext policy ih
        (hstep n)

/-- A root-started allowed path has the parity of a literal branch of the one
rational policy.  This is the state-priority form used by finite controller
products. -/
theorem minEven_of_allowedTarget_path
    (policy : Policy D initialCode Valid rawNext)
    (states : Nat → State D initialCode Valid rawNext)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n,
      AllowedTarget D initialCode Valid rawNext policy (states n)
        (states (n + 1))) :
    NatSeqMinEvenParity (fun n ↦
      (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid
        (sourceFreeBeliefFiniteCodeNext rawNext)).priority (states n)) := by
  classical
  choose childCode hchild using hstep
  let path : SourceFreeBeliefCodeParityPolicyPath D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext rawNext) policy :=
    { state := states
      direction := childCode
      initial := hzero
      successor := fun n ↦ (hchild n).symm }
  have haccepts := policy.accepts.2 path.direction
  convert haccepts using 1
  funext n
  have hstate := path.state_eq_run D initialCode Valid
    (sourceFreeBeliefFiniteCodeNext rawNext) policy n
  exact congrArg
    (sourceFreeBeliefCodeParityRunAutomaton D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext rawNext)).priority
    (by simpa [path] using hstate)

/-- The positive-time belief-code word of every root-started allowed path is
accepted by the original code-observable DPA.  This is the anti-mosaic form:
targets may be selected relationally, but all edges remain responses of one
fixed rational policy. -/
theorem accepts_of_allowedTarget_path
    (policy : Policy D initialCode Valid rawNext)
    (states : Nat → State D initialCode Valid rawNext)
    (hzero : states 0 = policy.run [])
    (hstep : ∀ n,
      AllowedTarget D initialCode Valid rawNext policy (states n)
        (states (n + 1))) :
    D.Accepts (fun n ↦ (states (n + 1)).1) := by
  classical
  choose childCode hchild using hstep
  let path : SourceFreeBeliefCodeParityPolicyPath D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext rawNext) policy :=
    { state := states
      direction := childCode
      initial := hzero
      successor := fun n ↦ (hchild n).symm }
  simpa [SourceFreeBeliefCodeParityPolicyPath.childCodeWord, path] using
    path.accepts D initialCode Valid
      (sourceFreeBeliefFiniteCodeNext rawNext) policy

end SourceFreeBeliefFiniteCodePolicyImage

end

end DistributedSynthesis
