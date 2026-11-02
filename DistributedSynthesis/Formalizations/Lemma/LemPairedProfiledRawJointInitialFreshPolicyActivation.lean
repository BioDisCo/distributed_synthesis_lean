/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointInitialGuardedKeyMonitor
import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledRawJointUnitRightPolicyHandoff

/-!
# Fresh ordinary raw-joint policy roots at guarded initial keys

Every guarded initial key represents a literal singleton semantic boundary.
Consequently a winning distributed strategy supplies a fresh ordinary
provenance policy at the key's incidence code.  The policy root has the lane
forced by that literal boundary: an initial-left key is process-one/right
live, while an initial-right key is process-two/left live.

The overlap component of the key is deliberately absent from the ordinary
policy macro.  It is consumed only by the exceptional first recurrent seam,
whose root-pinned policy is a separate construction.  This file merely gives
the reusable key-to-ordinary-root adapter used after that seam (and for the
finite controller bank).  All boundary histories and the lane proof remain
proof-side choices indexed by the finite key; no process receives a side,
orientation, graph, or strict-leader signal.
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

/-! ## The code itself fixes the live lane -/

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- A guarded initial-left key is right-live and left-empty.  The result is
read from the key's literal-boundary witness, not from a runtime side bit. -/
theorem profiledRawJointInitialLeftGuardedKey_right_live
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ∃ slot : ProfiledRawRightSlot A,
      key.1.1.family.right () = some slot ∧
        key.1.1.family.left () = none := by
  rcases key.2 with ⟨past, move, hkey⟩
  have hcode := congrArg Prod.fst hkey
  change key.1.1 =
    (profiledRawJointInitialLeftBoundaryState A strategy past move).code A
    at hcode
  rw [hcode]
  exact ⟨(profiledRawJointInitialLeftBoundaryWorld A strategy past move).procOneSlot
    A, rfl, rfl⟩

omit [Inhabited Out₁] [Inhabited Out₂] [Fintype In₁] [Fintype In₂] [Fintype Out₁]
    [Fintype Out₂] [DecidableEq In₁] [DecidableEq In₂] in
/-- Mirror: a guarded initial-right key is left-live and right-empty. -/
theorem profiledRawJointInitialRightGuardedKey_left_live
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ∃ slot : ProfiledRawLeftSlot A,
      key.1.1.family.left () = some slot ∧
        key.1.1.family.right () = none := by
  rcases key.2 with ⟨past, move, hkey⟩
  have hcode := congrArg Prod.fst hkey
  change key.1.1 =
    (profiledRawJointInitialRightBoundaryState A strategy past move).code A
    at hcode
  rw [hcode]
  exact ⟨(profiledRawJointInitialRightBoundaryWorld A strategy past move).procTwoSlot
    A, rfl, rfl⟩

/-! ## Dependent activation packages -/

/-- Proof-side activation selected at one finite initial-left key.  The
ordinary policy is rooted at the recovered semantic source, and its root is
packaged as the right macro required by the Unit controller bank. -/
structure ProfiledRawJointInitialLeftFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) where
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  source_boundary : ∃ past : List (In₁ × In₂), ∃ move : In₁ × In₂,
    source = profiledRawJointInitialLeftBoundaryState A strategy past move
  source_code : source.code A = key.1.1
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (source.code A)
  root : ProfiledRawJointUnitRightPolicyMacro A strategy (source.code A)
    policy

/-- Process-two/left mirror. -/
structure ProfiledRawJointInitialRightFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) where
  source : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit)
  source_boundary : ∃ past : List (In₂ × In₁), ∃ move : In₂ × In₁,
    source = profiledRawJointInitialRightBoundaryState A strategy past move
  source_code : source.code A = key.1.1
  policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (source.code A)
  root : ProfiledRawJointUnitLeftPolicyMacro A strategy (source.code A)
    policy

/-! ## Unconditional construction from the original winner -/

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every finite guarded initial-left key activates a fresh ordinary policy
at a genuinely right-live root. -/
theorem nonempty_profiledRawJointInitialLeftFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    Nonempty
      (ProfiledRawJointInitialLeftFreshPolicyActivation A strategy key) := by
  rcases key.2 with ⟨past, move, hkey⟩
  let source := profiledRawJointInitialLeftBoundaryState A strategy past move
  have hcode : source.code A = key.1.1 := by
    have hfst := congrArg Prod.fst hkey
    change key.1.1 = source.code A at hfst
    exact hfst.symm
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      source)
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  let world := profiledRawJointInitialLeftBoundaryWorld A strategy past move
  let root : ProfiledRawJointUnitRightPolicyMacro A strategy (source.code A)
      policy := {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := world.procOneSlot A
    active_slot := by
      rw [hrootCode]
      rfl }
  exact ⟨{
    source := source
    source_boundary := ⟨past, move, rfl⟩
    source_code := hcode
    policy := policy
    root := root }⟩

omit [DecidableEq In₁] [DecidableEq In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Every finite guarded initial-right key activates the mirror ordinary
policy at a genuinely left-live root. -/
theorem nonempty_profiledRawJointInitialRightFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    Nonempty
      (ProfiledRawJointInitialRightFreshPolicyActivation A strategy key) := by
  rcases key.2 with ⟨past, move, hkey⟩
  let source := profiledRawJointInitialRightBoundaryState A strategy past move
  have hcode : source.code A = key.1.1 := by
    have hfst := congrArg Prod.fst hkey
    change key.1.1 = source.code A at hfst
    exact hfst.symm
  let policy := Classical.choice
    (nonempty_profiledRawJointOneSidedProvenanceRationalPolicy A strategy hwin
      source)
  have hrootCode : (policy.run []).1 = source.code A := by
    have hroot := congrArg Prod.fst policy.accepts.1.1
    simpa [sourceFreeBeliefCodeParityRunAutomaton] using hroot
  let world := profiledRawJointInitialRightBoundaryWorld A strategy past move
  let root : ProfiledRawJointUnitLeftPolicyMacro A strategy (source.code A)
      policy := {
    state := policy.run []
    reachable := ⟨[], rfl⟩
    slot := world.procTwoSlot A
    active_slot := by
      rw [hrootCode]
      rfl }
  exact ⟨{
    source := source
    source_boundary := ⟨past, move, rfl⟩
    source_code := hcode
    policy := policy
    root := root }⟩

/-! ## Once-selected finite-key adapters -/

/-- Select the proof-side fresh policy package once for each finite left key.
Only `key` is a runtime bank index. -/
noncomputable def profiledRawJointInitialLeftFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialLeftGuardedKey A strategy) :
    ProfiledRawJointInitialLeftFreshPolicyActivation A strategy key :=
  Classical.choice
    (nonempty_profiledRawJointInitialLeftFreshPolicyActivation A strategy hwin
      key)

/-- Mirror selection. -/
noncomputable def profiledRawJointInitialRightFreshPolicyActivation
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (key : ProfiledRawJointInitialRightGuardedKey A strategy) :
    ProfiledRawJointInitialRightFreshPolicyActivation A strategy key :=
  Classical.choice
    (nonempty_profiledRawJointInitialRightFreshPolicyActivation A strategy hwin
      key)

end

end DetParityAutomaton

end DistributedSynthesis
