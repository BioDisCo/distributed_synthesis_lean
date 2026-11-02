/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonTailCoreTrace
import DistributedSynthesis.Formalizations.Lemma.LemArenaSuffixTransport

/-!
# Root-relative acceptance of an all-common guarded tail

Every runtime common control contains a reachable state of the one rational
common policy selected by its two-round seed.  Prefixing a witness of that
reachability to an arbitrary all-`.both` continuation embeds the supplied
control into the already verified forever-common physical word.  Removing
the resulting finite physical prefix yields `AcceptsFrom` for the literal
root-relative tail.

This is a proof-side completion argument.  The local machines are not given
the reachability stem, the selected representative, an orientation, or a
leader bit.
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

private abbrev CommonControl :=
  ProfiledRawJointGuardedInitialCommonControl A strategy hwin

/-! ## A proof-side completion of one reachable common control -/

/-- One finite policy path witnessing the reachability proof stored in a
runtime common control.  It is used only to embed the tail into an already
accepted forever-common word. -/
noncomputable def profiledRawJointGuardedCommonTailReachStem
    (root : CommonControl A strategy hwin) : List (In₁ × In₂) :=
  Classical.choose root.2.reachable

theorem profiledRawJointGuardedCommonTailReachStem_spec
    (root : CommonControl A strategy hwin) :
    (profiledRawJointGuardedInitialCommonPackage A strategy hwin root.1).policy.run
        (profiledRawJointGuardedCommonTailReachStem A strategy hwin root) =
      root.2.state :=
  Classical.choose_spec root.2.reachable

/-- Two seed pairs, then the finite reachability stem, then the requested
infinite common continuation. -/
noncomputable def profiledRawJointGuardedCommonTailCompletionInputs
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    Nat → In₁ × In₂
  | 0 => root.1.1
  | 1 => root.1.2
  | n + 2 => OmegaWord.prependList
      (profiledRawJointGuardedCommonTailReachStem A strategy hwin root) tail n

@[simp] theorem profiledRawJointGuardedCommonTailCompletionInputs_zero
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root tail
        0 = root.1.1 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailCompletionInputs_one
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root tail
        1 = root.1.2 :=
  rfl

@[simp] theorem profiledRawJointGuardedCommonTailCompletionInputs_add_two
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂)
    (n : Nat) :
    profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root tail
        (n + 2) =
      OmegaWord.prependList
        (profiledRawJointGuardedCommonTailReachStem A strategy hwin root) tail
        n :=
  rfl

/-! ## Finite-policy trace alignment -/

private theorem branchNode_eq_omegaPrefix_generic {Branch : Type u}
    (branch : Nat → Branch) : ∀ n,
    branchNode branch n = omegaPrefix branch n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show branchNode branch (n + 1) =
        branchNode branch n ++ [branch n] from rfl,
        omegaPrefix_succ, ih]

private theorem branchNode_prependList_length {Branch : Type u}
    (stem : List Branch) (tail : Nat → Branch) :
    branchNode (OmegaWord.prependList stem tail) stem.length = stem := by
  rw [branchNode_eq_omegaPrefix_generic]
  apply List.ext_get (by simp [omegaPrefix])
  intro n hn₁ hn₂
  unfold omegaPrefix
  rw [List.get_ofFn]
  exact OmegaWord.prependList_getElem_lt stem tail hn₂

private theorem profiledRawJointGuardedCommonPolicyKey_eq_of_state_eq
    {initial : ProfiledRawJointGuardedCommonSemanticPoint A strategy}
    {policy : ProfiledRawJointGuardedCommonRationalPolicy A strategy hwin
      initial}
    {left right : ProfiledRawJointGuardedCommonPolicyKey A strategy hwin
      initial policy}
    (hstate : left.state = right.state) : left = right := by
  cases left with
  | mk leftState leftReachable =>
      cases right with
      | mk rightState rightReachable =>
          cases hstate
          rfl

private theorem profiledRawJointGuardedCommonLocalControlTrace_eq_trace
    (root : CommonControl A strategy hwin) (inputs : Nat → In₁ × In₂) :
    ∀ n,
      profiledRawJointGuardedCommonLocalControlTrace A strategy hwin root
          inputs n =
        ⟨root.1,
          ProfiledRawJointGuardedCommonPolicyKey.trace A strategy hwin root.2
            inputs n⟩ := by
  intro n
  induction n with
  | zero =>
      cases root
      rfl
  | succ n ih =>
      rw [profiledRawJointGuardedCommonLocalControlTrace_succ,
        ih, ProfiledRawJointGuardedCommonPolicyKey.trace_succ]
      rfl

private theorem profiledRawJointGuardedCommonTailCompletion_reaches_root
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    let stem :=
      profiledRawJointGuardedCommonTailReachStem A strategy hwin root
    profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
        (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
          tail) stem.length = root := by
  dsimp only
  let stem :=
    profiledRawJointGuardedCommonTailReachStem A strategy hwin root
  let suffix := OmegaWord.prependList stem tail
  let seedRoot :=
    profiledRawJointGuardedInitialCommonControlRoot A strategy hwin root.1
  have hfromSeed :=
    profiledRawJointGuardedCommonLocalControlTrace_from_seed_eq_forever A
      strategy hwin
      (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
        tail) stem.length
  have hsuffix :
      (fun k ↦
        profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
          tail (k + 2)) = suffix := by
    rfl
  simp only [profiledRawJointGuardedCommonTailCompletionInputs_zero,
    profiledRawJointGuardedCommonTailCompletionInputs_one] at hfromSeed
  rw [hsuffix] at hfromSeed
  rw [← hfromSeed]
  rw [profiledRawJointGuardedCommonLocalControlTrace_eq_trace A strategy hwin]
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply profiledRawJointGuardedCommonPolicyKey_eq_of_state_eq A strategy
      hwin
    have hstate :=
      ProfiledRawJointGuardedCommonPolicyKey.trace_state_eq_run_append A
        strategy hwin seedRoot.2 suffix [] rfl stem.length
    rw [List.nil_append, branchNode_prependList_length stem tail] at hstate
    exact hstate.trans
      (profiledRawJointGuardedCommonTailReachStem_spec A strategy hwin root)

/-! ## Suffix alignment and root-relative `AcceptsFrom` -/

private theorem profiledRawJointGuardedCommonTailCompletion_control_add
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    let stem :=
      profiledRawJointGuardedCommonTailReachStem A strategy hwin root
    ∀ n,
      profiledRawJointGuardedForeverCommonControlTrace A strategy hwin
          (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin
            root tail) (stem.length + n) =
        profiledRawJointGuardedCommonLocalControlTrace A strategy hwin root tail
          n := by
  dsimp only
  let stem :=
    profiledRawJointGuardedCommonTailReachStem A strategy hwin root
  intro n
  induction n with
  | zero =>
      simpa using
        profiledRawJointGuardedCommonTailCompletion_reaches_root A strategy
          hwin root tail
  | succ n ih =>
      rw [show stem.length + (n + 1) = (stem.length + n) + 1 by omega,
        profiledRawJointGuardedForeverCommonControlTrace_succ,
        profiledRawJointGuardedCommonLocalControlTrace_succ, ih]
      congr 1
      simpa [profiledRawJointGuardedCommonTailCompletionInputs, stem,
        Nat.add_assoc] using
        (OmegaWord.prependList_length_add stem tail n)

/-- The finite prefix deletes exactly to the requested root-relative common
tail. -/
theorem profiledRawJointGuardedCommonTailCompletion_drop_eq
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    let stem :=
      profiledRawJointGuardedCommonTailReachStem A strategy hwin root
    OmegaWord.drop
        (profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
          (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin
            root tail))
        (2 + stem.length) =
      profiledRawJointGuardedCommonTailWordFrom A strategy hwin root tail := by
  dsimp only
  let stem :=
    profiledRawJointGuardedCommonTailReachStem A strategy hwin root
  funext n
  change
    profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin
        (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
          tail) (2 + stem.length + n) =
      profiledRawJointGuardedCommonTailWordFrom A strategy hwin root tail n
  rw [show 2 + stem.length + n = 2 + (stem.length + n) by omega]
  unfold profiledRawJointGuardedForeverCommonPhysicalWord
  rw [show 2 + (stem.length + n) =
    ([profiledRawJointGuardedForeverCommonFirstRound strategy
        (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
          tail),
      profiledRawJointGuardedForeverCommonSecondRound A strategy
        (profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root
          tail)] : List _).length + (stem.length + n) by rfl]
  rw [OmegaWord.prependList_length_add]
  unfold profiledRawJointGuardedForeverCommonTailWord
  unfold profiledRawJointGuardedCommonTailWordFrom
  rw [profiledRawJointGuardedCommonTailCompletion_control_add A strategy hwin
    root tail n]
  have hinput := OmegaWord.prependList_length_add stem tail n
  rw [profiledRawJointGuardedCommonTailCompletionInputs_add_two, hinput]

/-- The literal all-`.both` tail emitted from any reachable finite common
control is accepted from the exact DPA entry state advertised by that
control's selected semantic point. -/
theorem profiledRawJointGuardedCommonTailWordFrom_acceptsFrom
    (root : CommonControl A strategy hwin) (tail : Nat → In₁ × In₂) :
    A.AcceptsFrom
        ((((profiledRawJointGuardedCommonControlPoint A strategy hwin root
          ).world A strategy).procOne A).code.2)
        (profiledRawJointGuardedCommonTailWordFrom A strategy hwin root tail) := by
  let stem :=
    profiledRawJointGuardedCommonTailReachStem A strategy hwin root
  let completion :=
    profiledRawJointGuardedCommonTailCompletionInputs A strategy hwin root tail
  let word :=
    profiledRawJointGuardedForeverCommonPhysicalWord A strategy hwin completion
  have haccepts : A.Accepts word :=
    profiledRawJointGuardedForeverCommonPhysicalWord_accepts A strategy hwin
      completion
  have htail :
      A.AcceptsFrom (A.run word (2 + stem.length))
        (OmegaWord.drop word (2 + stem.length)) :=
    (A.acceptsFrom_runFrom_drop_iff A.initial word (2 + stem.length)).mpr
      haccepts
  have hcontrol :=
    profiledRawJointGuardedCommonTailCompletion_reaches_root A strategy hwin
      root tail
  have hrun :=
    profiledRawJointGuardedForeverCommon_run_add_two A strategy hwin completion
      stem.length
  have hstate :
      A.run word (2 + stem.length) =
        ((((profiledRawJointGuardedCommonControlPoint A strategy hwin root
          ).world A strategy).procOne A).code.2) := by
    rw [show 2 + stem.length = stem.length + 2 by omega]
    exact hrun.trans (congrArg
      (fun control ↦
        ((((profiledRawJointGuardedCommonControlPoint A strategy hwin control
          ).world A strategy).procOne A).code.2)) hcontrol)
  rw [hstate,
    profiledRawJointGuardedCommonTailCompletion_drop_eq A strategy hwin root
      tail] at htail
  exact htail

end

end DetParityAutomaton

end DistributedSynthesis
