/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointHybridMegaChildFamily

/-!
# Total staging of live roots in the hybrid mega family

A pre-recurrent receiver remembers the literal child emitted by its most
recent receive.  To enter the recurrent carrier on a later `noRecv`, it also
needs the live root macro of that child.  The finite child code itself tells
us whether the required lane is present.

The two functions below are total: a malformed or unreachable child with no
required lane returns `none`.  On every reachable guarded-controller path,
the existing all-thread safety theorem proves that the relevant slot is
`some`, so the staged value is the exact policy root at `run []`.  No graph,
orientation, or leader information is inspected.
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
  (initialBank : ProfiledRawJointInitialControllerBank A strategy)

/-! ## Roots from an explicitly live slot -/

/-- The canonical right-policy root at a mega child whose right lane contains
`slot`. -/
noncomputable def profiledRawJointHybridMegaRightRootOfSlot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawRightSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.right () = some slot) :
    ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank child := by
  let source :=
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
  let policy :=
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      exact hslot }

/-- Left-policy mirror. -/
noncomputable def profiledRawJointHybridMegaLeftRootOfSlot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawLeftSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.left () = some slot) :
    ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank child := by
  let source :=
    profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
  let policy :=
    profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  exact {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := slot
    active_slot := by
      rw [hrootCode]
      exact hslot }

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridMegaRightRootOfSlot_state
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawRightSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.right () = some slot) :
    (profiledRawJointHybridMegaRightRootOfSlot A strategy hwin initialBank
      child slot hslot).state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
        ).run [] :=
  rfl

omit [Inhabited Out₁] [Inhabited Out₂] in
@[simp] theorem profiledRawJointHybridMegaLeftRootOfSlot_state
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawLeftSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.left () = some slot) :
    (profiledRawJointHybridMegaLeftRootOfSlot A strategy hwin initialBank child
      slot hslot).state =
      (profiledRawJointHybridMegaChildPolicy A strategy hwin initialBank child
        ).run [] :=
  rfl

/-! ## Total optional staging -/

/-- Inspect the finite incidence code and stage its right root exactly when
the right lane is live. -/
noncomputable def profiledRawJointHybridMegaRightRoot?
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Option
      (ProfiledRawJointHybridMegaRightMacro A strategy hwin initialBank child) :=
  match hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.right () with
  | none => none
  | some slot =>
      some (profiledRawJointHybridMegaRightRootOfSlot A strategy hwin
        initialBank child slot hslot)

/-- Left-lane mirror. -/
noncomputable def profiledRawJointHybridMegaLeftRoot?
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank) :
    Option
      (ProfiledRawJointHybridMegaLeftMacro A strategy hwin initialBank child) :=
  match hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.left () with
  | none => none
  | some slot =>
      some (profiledRawJointHybridMegaLeftRootOfSlot A strategy hwin
        initialBank child slot hslot)

section
omit [Inhabited Out₁] [Inhabited Out₂]

/-- Any explicit live right slot makes total staging succeed. -/
theorem profiledRawJointHybridMegaRightRoot?_isSome
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawRightSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.right () = some slot) :
    (profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank child
      ).isSome = true := by
  unfold profiledRawJointHybridMegaRightRoot?
  split <;> simp_all

/-- Existential form used when a front-state invariant consumes the staged
right root. -/
theorem exists_profiledRawJointHybridMegaRightRoot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawRightSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.right () = some slot) :
    ∃ root, profiledRawJointHybridMegaRightRoot? A strategy hwin initialBank
        child = some root := by
  unfold profiledRawJointHybridMegaRightRoot?
  split <;> simp_all

/-- Any explicit live left slot makes left staging succeed. -/
theorem profiledRawJointHybridMegaLeftRoot?_isSome
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawLeftSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.left () = some slot) :
    (profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank child
      ).isSome = true := by
  unfold profiledRawJointHybridMegaLeftRoot?
  split <;> simp_all

/-- Existential left-root staging form. -/
theorem exists_profiledRawJointHybridMegaLeftRoot
    (child : ProfiledRawJointHybridMegaChildCode A strategy hwin initialBank)
    (slot : ProfiledRawLeftSlot A)
    (hslot :
      ((profiledRawJointHybridMegaChildSource A strategy hwin initialBank child
        ).code A).family.left () = some slot) :
    ∃ root, profiledRawJointHybridMegaLeftRoot? A strategy hwin initialBank
        child = some root := by
  unfold profiledRawJointHybridMegaLeftRoot?
  split <;> simp_all

end

end

end DetParityAutomaton

end DistributedSynthesis
