/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyStateRelativeThreadAlignment

/-!
# Splicing a finite fixed-policy macro prefix to an infinite tail

The activated controller selects one ordinary child policy at a literal
stage.  Its root macro is literally `policy.run []`.  By the time the
acknowledgement relay is flushed, finitely many exact macro closes may already
have occurred.  Re-rooting the policy at that later macro would lose the
accepted code lineage.

This file records the correct proof object.  `AlternatingPrefix` is the finite
chain of literal allowed targets from the selected policy root to the current
macro.  It can be extended by one checked close and spliced to any infinite
alternating continuation.  The resulting `AlternatingThread` still starts at
the original policy root, while its suffix is definitionally the supplied
post-flush continuation.  All data are proof-side; no process receives the
prefix length, side, root, graph, or a leader bit.
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

namespace ProfiledRawJointUnitFixedPolicyRoot

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
variable (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
  initialCode)

/-- A finite chain of literal alternating policy edges.  The first endpoint
is fixed in the type; the index is its current (last) endpoint. -/
inductive AlternatingPrefix
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy) :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy → Type _
  | refl : AlternatingPrefix seed seed
  | snoc {current next}
      (chain : AlternatingPrefix seed current)
      (step : AlternatingStep A policy current next) :
      AlternatingPrefix seed next

namespace AlternatingPrefix

variable {policy}
variable {seed current next :
  ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy}

/-- Number of checked macro edges in the finite prefix. -/
def length {current} : AlternatingPrefix A policy seed current → Nat
  | .refl => 0
  | .snoc chain _ => chain.length + 1

/-- The endpoint carried by the dependent index. -/
def endpoint {current}
    (_chain : AlternatingPrefix A policy seed current) :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy :=
  current

/-- Concatenate two finite checked policy paths.  This is the proof-side
operation used when a receiver already carries a root reached from the
activation seed and one further locally checked target is staged. -/
def append {middle current}
    (headChain : AlternatingPrefix A policy seed middle) :
    AlternatingPrefix A policy middle current →
      AlternatingPrefix A policy seed current
  | .refl => headChain
  | .snoc suffix edge => (append headChain suffix).snoc edge

/-- Existence-only presentation of a finite checked path from the activation
root.  Keeping the actual prefix under `Nonempty` makes it a proof invariant,
not executable controller state. -/
def Reachable
    (seed current :
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy) :
    Prop :=
  Nonempty (AlternatingPrefix A policy seed current)

section
omit [Inhabited Out₁] [Inhabited Out₂]

@[simp] theorem length_refl :
    (AlternatingPrefix.refl (A := A) (policy := policy)
      (seed := seed)).length = 0 :=
  rfl

@[simp] theorem length_snoc
    (chain : AlternatingPrefix A policy seed current)
    (step : AlternatingStep A policy current next) :
    (chain.snoc step).length = chain.length + 1 :=
  rfl

/-- Concatenation adds the two checked-path lengths. -/
@[simp] theorem length_append {middle current}
    (headChain : AlternatingPrefix A policy seed middle)
    (suffix : AlternatingPrefix A policy middle current) :
    (headChain.append A suffix).length =
      headChain.length + suffix.length := by
  induction suffix with
  | refl => simp [append]
  | snoc suffix edge ih => simp [append, ih, Nat.add_assoc]

/-- The seed is reachable without executing any physical round. -/
theorem reachable_refl : Reachable (policy := policy) A seed seed :=
  ⟨.refl⟩

/-- One checked policy edge extends activation-root reachability. -/
theorem Reachable.snoc
    (reachable : Reachable (policy := policy) A seed current)
    (edge : AlternatingStep A policy current next) :
    Reachable (policy := policy) A seed next := by
  rcases reachable with ⟨headChain⟩
  exact ⟨headChain.snoc edge⟩

/-- Finite checked reachability is transitive. -/
theorem Reachable.trans {middle current}
    (left : Reachable (policy := policy) A seed middle)
    (right : Reachable (policy := policy) A middle current) :
    Reachable (policy := policy) A seed current := by
  rcases left with ⟨headChain⟩
  rcases right with ⟨suffix⟩
  exact ⟨headChain.append A suffix⟩

end

/-- Splice the finite root-started prefix to an infinite continuation whose
time-zero root is its current endpoint. -/
noncomputable def toThread
    {current}
    (hseed : state A policy seed = policy.run []) :
    (chain : AlternatingPrefix A policy seed current) →
    (future : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy) →
    future 0 = current →
    (∀ n : Nat, AlternatingStep A policy (future n) (future (n + 1))) →
    AlternatingThread A policy
  | .refl, future, hzero, hstep =>
      { root := future
        initial := by simpa [hzero] using hseed
        step := hstep }
  | .snoc chain edge, future, hzero, hstep =>
      let extended : Nat →
          ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy
        | 0 => endpoint A chain
        | n + 1 => future n
      toThread hseed chain extended rfl (fun n ↦ by
        cases n with
        | zero => simpa [extended, endpoint, hzero] using edge
        | succ n => simpa [extended] using hstep n)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- At its finite-prefix offset, the spliced thread is exactly the supplied
future continuation. -/
theorem toThread_root_length_add
    (hseed : state A policy seed = policy.run [])
    (chain : AlternatingPrefix A policy seed current)
    (future : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy)
    (hzero : future 0 = current)
    (hstep : ∀ n : Nat,
      AlternatingStep A policy (future n) (future (n + 1))) : ∀ n : Nat,
    (toThread A hseed chain future hzero hstep).root
        (chain.length + n) = future n := by
  induction chain generalizing future with
  | refl =>
      intro n
      simp [toThread, length]
  | @snoc endpoint target chain edge ih =>
      intro n
      let extended : Nat →
          ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy
        | 0 => endpoint
        | k + 1 => future k
      have hextendedStep : ∀ k : Nat,
          AlternatingStep A policy (extended k) (extended (k + 1)) := by
        intro k
        cases k with
        | zero => simpa [extended, hzero] using edge
        | succ k => simpa [extended] using hstep k
      simp only [length, toThread]
      change
        (toThread A hseed chain extended rfl
          hextendedStep).root
            (chain.length + 1 + n) = future n
      rw [show chain.length + 1 + n = chain.length + (n + 1) by omega]
      rw [ih extended rfl hextendedStep (n + 1)]

/-- Endpoint specialization of `toThread_root_length_add`. -/
theorem toThread_root_length
    (hseed : state A policy seed = policy.run [])
    (chain : AlternatingPrefix A policy seed current)
    (future : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy)
    (hzero : future 0 = current)
    (hstep : ∀ n : Nat,
      AlternatingStep A policy (future n) (future (n + 1))) :
    (toThread A hseed chain future hzero hstep).root
        chain.length = current := by
  rw [show chain.length = chain.length + 0 by omega,
    chain.toThread_root_length_add A hseed future hzero hstep 0, hzero]

/-- The first positive post-prefix root is the first future target.  This is
the exact index used by state-relative physical block pasting. -/
theorem toThread_root_length_add_succ
    (hseed : state A policy seed = policy.run [])
    (chain : AlternatingPrefix A policy seed current)
    (future : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy)
    (hzero : future 0 = current)
    (hstep : ∀ n : Nat,
      AlternatingStep A policy (future n) (future (n + 1))) (n : Nat) :
    (toThread A hseed chain future hzero hstep).root
        (chain.length + n + 1) = future (n + 1) := by
  rw [show chain.length + n + 1 = chain.length + (n + 1) by omega]
  exact chain.toThread_root_length_add A hseed future hzero hstep (n + 1)

end

end AlternatingPrefix

end ProfiledRawJointUnitFixedPolicyRoot

end

end DetParityAutomaton

end DistributedSynthesis
