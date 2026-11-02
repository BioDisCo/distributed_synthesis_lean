/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitFixedPolicyParity

/-!
# Exact code-thread alignment for a fixed raw-joint policy

The abstract fixed-policy parity package follows the canonical hidden
alternating-lineage monitor.  The operational construction, on the other
hand, names the actual right/left macro at every close.  This file identifies
the two pointwise: at positive code time `n + 1`, the hidden monitor is live
at exactly the slot carried by the actual macro `thread.root (n + 1)`.

The side below is proof-side objective data.  It is recovered from the
alternating thread and is never supplied to either local controller as a
leader or graph-orientation input.
-/

namespace DistributedSynthesis

universe u v w x y s

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

/-- Erase the macro package while retaining its literal active objective
slot. -/
def threadRoot :
    ProfiledRawJointUnitFixedPolicyRoot A strategy initialCode policy →
      ProfiledRawJointThreadRoot A
  | .inl source => .inl source.slot
  | .inr source => .inr source.slot

namespace AlternatingThread

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- The proof-side side and slot of every actual macro occur literally in its
finite policy-state code. -/
theorem root_active_slot
    (thread : AlternatingThread A policy) (n : Nat) :
    profiledRawJointOneSidedCurrentSlots A
        (side A policy (thread.root n))
        (thread.states A policy n).1 () =
      some (threadRoot A policy (thread.root n)) := by
  cases hroot : thread.root n with
  | inl source =>
      simpa [states, state, side, threadRoot,
        profiledRawJointOneSidedCurrentSlots, hroot] using source.active_slot
  | inr source =>
      simpa [states, state, side, threadRoot,
        profiledRawJointOneSidedCurrentSlots, hroot] using source.active_slot

/-- The policy root really carries the advertised initial public code. -/
theorem states_zero_code
    (thread : AlternatingThread A policy) :
    (thread.states A policy 0).1 = initialCode := by
  rw [thread.states_zero A policy]
  exact congrArg Prod.fst policy.accepts.1.1

/-- Exact positive-time run of the canonical code-only lineage monitor along
the actual fixed-policy macro thread. -/
theorem codeRun_eq_live_threadRoot
    (thread : AlternatingThread A policy) (n : Nat) :
    codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointOneSidedCurrentSlots A)
        (fun k ↦ (thread.states A policy (k + 1)).1)
        (side A policy (thread.root 0)) () (n + 1) =
      ((thread.states A policy (n + 1)).1,
        .live (side A policy (thread.root (n + 1))) ()
          (threadRoot A policy (thread.root (n + 1)))) := by
  induction n with
  | zero =>
      have hsource := thread.root_active_slot A policy 0
      rw [thread.states_zero_code A policy] at hsource
      have hchildAt := thread.root_active_slot A policy 1
      have hchild :
          profiledRawJointOneSidedCurrentSlots A
              (side A policy (thread.root 0)).other
              (thread.states A policy 1).1 () =
            some (threadRoot A policy (thread.root 1)) := by
        rw [← thread.side_succ A policy 0]
        exact hchildAt
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode ↦ nextCode)
            (profiledRawJointOneSidedCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledRawJointOneSidedCurrentSlots A))
            (initialCode, .initial)
            (Unit.unit, (thread.states A policy 1).1)
            (side A policy (thread.root 0), ()) = _
      rw [codedAlternatingIndexedLineageCodeStep_initial_of
        (profiledRawJointOneSidedCurrentSlots A)
        initialCode (thread.states A policy 1).1
        (side A policy (thread.root 0)) ()
        (threadRoot A policy (thread.root 0))
        (threadRoot A policy (thread.root 1)) hsource hchild]
      rw [thread.side_succ A policy 0]
  | succ n ih =>
      have hcurrent := thread.root_active_slot A policy (n + 1)
      have hchildAt := thread.root_active_slot A policy (n + 2)
      have hchild :
          profiledRawJointOneSidedCurrentSlots A
              (side A policy (thread.root (n + 1))).other
              (thread.states A policy (n + 2)).1 () =
            some (threadRoot A policy (thread.root (n + 2))) := by
        rw [← thread.side_succ A policy (n + 1)]
        exact hchildAt
      rw [show n + 2 = (n + 1) + 1 by omega]
      unfold codedAlternatingIndexedLineageCodeRun
      rw [codedAlternatingIndexedLineageRun_succ]
      change
        codedAlternatingIndexedLineageStep
            (fun _ (_ : Unit) nextCode ↦ nextCode)
            (profiledRawJointOneSidedCurrentSlots A)
            (codedAlternatingIndexedLineageCodeChild
              (profiledRawJointOneSidedCurrentSlots A))
            (codedAlternatingIndexedLineageCodeRun initialCode
              (profiledRawJointOneSidedCurrentSlots A)
              (fun k ↦ (thread.states A policy (k + 1)).1)
              (side A policy (thread.root 0)) () (n + 1))
            (Unit.unit, (thread.states A policy (n + 2)).1)
            (side A policy (thread.root 0), ()) = _
      rw [ih]
      rw [codedAlternatingIndexedLineageCodeStep_live_of
        (profiledRawJointOneSidedCurrentSlots A)
        (thread.states A policy (n + 1)).1
        (thread.states A policy (n + 2)).1
        (side A policy (thread.root (n + 1))) ()
        (threadRoot A policy (thread.root (n + 1)))
        (threadRoot A policy (thread.root (n + 2)))
        (side A policy (thread.root 0), ()) hcurrent hchild]
      rw [thread.side_succ A policy (n + 1)]

/-- At positive code time, the hidden thread priority is exactly the priority
of the actual macro's active slot. -/
theorem codeRun_priority_eq_threadRoot
    (thread : AlternatingThread A policy) (n : Nat) :
    (codedAlternatingIndexedLineageCodeThreadSystem initialCode
        (profiledRawJointOneSidedCurrentSlots A)
        (profiledRawJointThreadRootPriority A)).priority
      (codedAlternatingIndexedLineageCodeRun initialCode
        (profiledRawJointOneSidedCurrentSlots A)
        (fun k ↦ (thread.states A policy (k + 1)).1)
        (side A policy (thread.root 0)) () (n + 1)) =
      profiledRawJointThreadRootPriority A
        (threadRoot A policy (thread.root (n + 1))) := by
  rw [thread.codeRun_eq_live_threadRoot A policy n]
  rfl

end

/-- Canonical coupling constructor whose operational premise names the actual
macro slot directly.  The hidden side and the one-step code offset are filled
in by the exact alignment theorem above. -/
noncomputable def toPolicyEpochCouplingOfThreadRootPriority
    (thread : AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (rootOffset start : Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_threadRootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        profiledRawJointThreadRootPriority A
          (threadRoot A policy (thread.root (rootOffset + k + 1)))) :
    ProfiledRawJointUnitPolicyEpochCoupling A strategy initialCode policy G
      outputOne outputTwo env :=
  thread.toPolicyEpochCoupling A policy G outputOne outputTwo env
    (side A policy (thread.root 0)) (rootOffset + 1) start cuts
    cuts_strictMono cuts_zero (fun k ↦ by
      rw [blockMin_eq_threadRootPriority k]
      have halign := thread.codeRun_priority_eq_threadRoot A policy
        (rootOffset + k)
      rw [show rootOffset + 1 + k = (rootOffset + k) + 1 by omega]
      exact halign.symm)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- End-to-end acceptance in the literal actual-macro presentation. -/
theorem physicalTrace_accepts_of_threadRootPriority
    (thread : AlternatingThread A policy)
    (G : FiniteGlobalRoundMachine.{u, v, w} In₁ In₂)
    (outputOne : G.State → Out₁) (outputTwo : G.State → Out₂)
    (env : EnvironmentSequence In₁ In₂)
    (rootOffset start : Nat)
    (cuts : Nat → Nat) (cuts_strictMono : StrictMono cuts)
    (cuts_zero : cuts 0 = 0)
    (blockMin_eq_threadRootPriority : ∀ k : Nat,
      cutBlockMin
          (fun n ↦ A.priority
            (A.run (G.globalMachineTraceWord outputOne outputTwo env)
              (start + n)))
          cuts k =
        profiledRawJointThreadRootPriority A
          (threadRoot A policy (thread.root (rootOffset + k + 1)))) :
    A.Accepts (G.globalMachineTraceWord outputOne outputTwo env) :=
  (thread.toPolicyEpochCouplingOfThreadRootPriority A policy G outputOne
    outputTwo env rootOffset start cuts cuts_strictMono cuts_zero
    blockMin_eq_threadRootPriority).physicalTrace_accepts A

end AlternatingThread

end ProfiledRawJointUnitFixedPolicyRoot

end

end DetParityAutomaton

end DistributedSynthesis
