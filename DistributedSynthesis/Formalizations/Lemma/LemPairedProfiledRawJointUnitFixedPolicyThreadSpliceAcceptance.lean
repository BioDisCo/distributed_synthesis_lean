/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyThreadSplice

/-!
# State-relative acceptance after a finite fixed-policy prefix

The activation point selects a policy at its root, while the recurrent
physical tail may begin only after finitely many checked macro closes.  This
file composes the finite-prefix splice with the state-relative block-pasting
endpoint.  The finite prefix merely shifts the proof-side accepted lineage;
the physical checker still starts in its literal post-prefix DPA state.
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

namespace ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {initialCode : ProfiledRawJointIncidenceCode A (I := Unit)}
variable {policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
  initialCode}
variable {seed current :
  ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy}

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- A finite root-started macro prefix and exact post-prefix cut equations
give acceptance from the literal DPA state reached by the physical prefix. -/
theorem physicalTail_acceptsFrom_of_futureRootPriority
    (hseed :
      ProfiledRawJointUnitFixedPolicyRoot.state A policy seed = policy.run [])
    (chain : AlternatingPrefix A policy seed current)
    (future : Nat →
      ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy)
    (hzero : future 0 = current)
    (hstep : ∀ n : Nat,
      ProfiledRawJointUnitFixedPolicyRoot.AlternatingStep A policy
        (future n) (future (n + 1)))
    (physicalState : A.State)
    (physicalTail : OmegaWord (RoundRecord In₁ In₂ Graph Out₁ Out₂))
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_futureRootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority (A.runFrom physicalState physicalTail n))
          cuts k =
        profiledRawJointThreadRootPriority A
          (ProfiledRawJointUnitFixedPolicyRoot.threadRoot A policy
            (future (k + 1)))) :
    A.AcceptsFrom physicalState physicalTail := by
  let thread := chain.toThread A hseed future hzero hstep
  apply thread.physicalTail_acceptsFrom_of_threadRootPriority A policy
    physicalState physicalTail chain.length cuts cuts_strictMono cuts_zero
  intro k
  rw [chain.toThread_root_length_add_succ A hseed future hzero hstep k]
  exact blockMin_eq_futureRootPriority k

end ProfiledRawJointUnitFixedPolicyRoot.AlternatingPrefix

end

end DetParityAutomaton

end DistributedSynthesis
