/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointGuardedCommonLiteralBranchStagePhysicalPriority

/-!
# Constant exact internal projection for the literal seam

The Boolean resolving the outer acknowledged fork and the Boolean selecting a
member of the inner heterogeneous table have different jobs.  The blind
sender table has definitionally the same control transition and output for
both inner members.  Consequently the inner receiver may be initialized at
the exact (`true`) member in both outer candidates and remain there throughout
the table epoch.

This file proves the local fail-fast facts needed before changing the full
phase-live carrier:

* the exact inner member is preserved by every receive;
* the existing physical selector then reads the exact product coordinate;
* at every locally reachable round, the `.both` target of that coordinate has
  exactly the physical block-minimum priority of the true table play.

No executable transition receives a graph, orientation, hierarchy side,
leader bit, history, or semantic view.
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

private abbrev RightReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralRightSeamStagedReceiverState A strategy
    hwin package

private abbrev LeftReceiver (package : Package A strategy hwin
    (initial := initial)) :=
  ProfiledRawJointGuardedCommonLiteralLeftSeamStagedReceiverState A strategy
    hwin package

/-! ## The constant inner member is a closed local invariant -/

/-- A right-seam receiver initialized with the exact member stores `true`. -/
@[simp] theorem literalRightSeamStagedReceiverInitial_exact_anchor
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) :
    (package.literalRightSeamStagedReceiverInitial A strategy hwin key row
      true).2.2.1.1 = true :=
  rfl

/-- The branch-aware receive leaves the exact inner member unchanged. -/
theorem literalRightSeamBranchStagedReceiverRecv_exact_anchor
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hanchor : state.2.2.1.1 = true) :
    (package.literalRightSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.2.2.1.1 = true := by
  simpa [literalRightSeamBranchStagedReceiverRecv,
    profiledRawJointLiteralRightBothExactReceiverRecv] using hanchor

/-- Mirror exact initialization. -/
@[simp] theorem literalLeftSeamStagedReceiverInitial_exact_anchor
    (package : Package A strategy hwin (initial := initial))
    (key : ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin
      package)
    (row : PairedEntryRow) :
    (package.literalLeftSeamStagedReceiverInitial A strategy hwin key row
      true).2.2.1.1 = true :=
  rfl

/-- Mirror preservation of the exact inner member. -/
theorem literalLeftSeamBranchStagedReceiverRecv_exact_anchor
    (package : Package A strategy hwin (initial := initial))
    (state : LeftReceiver A strategy hwin package)
    (own : In₂) (delivered : In₁)
    (hanchor : state.2.2.1.1 = true) :
    (package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
      own delivered).2.2.2.1.1 = true := by
  simpa [literalLeftSeamBranchStagedReceiverRecv,
    profiledRawJointLiteralLeftBothExactReceiverRecv] using hanchor

/-! ## The physical selector is then the exact coordinate -/

/-- With the constant exact invariant, the current process-one output is the
true product coordinate, independently of the outer delayed member. -/
theorem literalRightSeamInternalPhysicalOutput_eq_exact
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralRightSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = true) :
    package.literalRightSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetLeftReceiverBothPhysicalOutput output.2.2 := by
  exact package.literalRightSeamInternalPhysicalOutput_true A strategy hwin
    state output hanchor

/-- Mirror exact-coordinate selector. -/
theorem literalLeftSeamInternalPhysicalOutput_eq_exact
    (package : Package A strategy hwin (initial := initial))
    (state : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointGuardedCommonLiteralLeftSeamFrontReceiverOutput A
        strategy hwin package)
    (hanchor : state.2.2.1.1 = true) :
    package.literalLeftSeamInternalPhysicalOutput A strategy hwin state
        output =
      profiledRawJointTargetRightReceiverBothPhysicalOutput output.2.2 := by
  exact package.literalLeftSeamInternalPhysicalOutput_true A strategy hwin
    state output hanchor

/-! ## Full-tag audit at a cross cut -/

/-- Regardless of the selected coordinate, a right-table target remains
tagged by the key of the table which emitted it.  In particular, switching to
the true coordinate removes the arbitrary-code inverse but does not silently
retag the target with a later freshness key. -/
@[simp] theorem literalRightSeamBranchChild_key
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin state.1)) :
    (package.literalRightSeamBranchChild A strategy hwin state output).1 =
      state.1 := by
  classical
  cases hanchor : state.2.2.1.1
  · rw [package.literalRightSeamBranchChild_false A strategy hwin state
      output hanchor]
    unfold literalRightSeamTaggedChildOfCode
    split <;> rfl
  · simp [literalRightSeamBranchChild, hanchor]

/-- Mirror target tags retain the emitting table's key. -/
@[simp] theorem literalLeftSeamBranchChild_key
    (package : Package A strategy hwin (initial := initial))
    (state : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin state.1)) :
    (package.literalLeftSeamBranchChild A strategy hwin state output).1 =
      state.1 := by
  classical
  cases hanchor : state.2.2.1.1
  · rw [package.literalLeftSeamBranchChild_false A strategy hwin state
      output hanchor]
    unfold literalLeftSeamTaggedChildOfCode
    split <;> rfl
  · simp [literalLeftSeamBranchChild, hanchor]

/-- **Exact boundary of the constant-true repair.**  If a target emitted by
the current right table were literally the canonical target of a newly
installed table, then the old table key would have to equal the new key.
Thus the missing cross-cut fact is key continuity; incidence-code equality or
exact-coordinate liveness alone cannot supply it. -/
theorem literalRightSeamBranchChild_eq_freshTarget_implies_key_eq
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (output :
      ProfiledRawJointLiteralRightBothExactProductReceiverOutput A strategy
        hwin (package.literalRightSeamInstalled A strategy hwin state.1))
    (freshKey :
      ProfiledRawJointGuardedCommonLiteralRightSeamKey A strategy hwin
        package)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂)
    (hchain :
      package.literalRightSeamBranchChild A strategy hwin state output =
        package.literalRightSeamTaggedTarget A strategy hwin freshKey row
          past input) :
    state.1 = freshKey := by
  have hkey := congrArg Sigma.fst hchain
  simpa using hkey

/-- Mirror key-continuity boundary. -/
theorem literalLeftSeamBranchChild_eq_freshTarget_implies_key_eq
    (package : Package A strategy hwin (initial := initial))
    (state : LeftReceiver A strategy hwin package)
    (output :
      ProfiledRawJointLiteralLeftBothExactProductReceiverOutput A strategy
        hwin (package.literalLeftSeamInstalled A strategy hwin state.1))
    (freshKey :
      ProfiledRawJointGuardedCommonLiteralLeftSeamKey A strategy hwin package)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁)
    (hchain :
      package.literalLeftSeamBranchChild A strategy hwin state output =
        package.literalLeftSeamTaggedTarget A strategy hwin freshKey row past
          input) :
    state.1 = freshKey := by
  have hkey := congrArg Sigma.fst hchain
  simpa using hkey

/-! ## Honest arbitrary-depth `.both` target and physical priority -/

/-- At every locally reachable exact right-table round, the target used by
the actual `.both` physical projection is a live exact slot and its thread
priority is the minimum priority of the same true table prefix. -/
theorem
    exists_literalRightSeamExactReceiverRecv_bothTargetPriority_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state : RightReceiver A strategy hwin package)
    (own : In₁) (delivered : In₂)
    (hanchor : state.2.2.1.1 = true)
    (hreach : package.LiteralRightSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ past : List (In₁ × In₂),
      ∃ slot : ProfiledRawRightSlot A,
        (((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target .both).1.family.right () =
            some slot) ∧
          profiledRawJointThreadRootPriority A (.inl slot) =
            literalRightSeamSelectedTableBlockPriority A strategy hwin
              (package.literalRightSeamInstalled A strategy hwin state.1)
              true (omegaOfList (past ++ [(own, delivered)])) past.length
                .both := by
  classical
  let installed := package.literalRightSeamInstalled A strategy hwin state.1
  let table :=
    profiledRawJointLiteralRightBothExactHeterogeneousLeftTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  obtain ⟨past, _hsender, _hreceiver, hround⟩ :=
    hlocal.exists_localRound_eq_treePlay table (own, delivered)
  let env : Nat → In₁ × In₂ := omegaOfList (past ++ [(own, delivered)])
  let play := profiledRawJointLiteralRightBothExactTruePlay A strategy hwin
    installed env
  have htarget :
      (((package.literalRightSeamBranchStagedReceiverRecv A strategy hwin
        state own delivered).1.2.2.target .both).1) =
        (((play past.length).2.1.target .both).1) := by
    have hat := congrArg
      (fun record ↦ (record.2.1.2.target .both).1) hround
    rw [hanchor] at hat
    simpa [literalRightSeamBranchStagedReceiverRecv,
      profiledRawJointLiteralRightBothExactReceiverRecv,
      profiledRawJointLiteralRightBothExactTruePlay,
      BlockRecordMonitor.projectReceiverPlay, play, table, installed,
      hanchor, env] using hat
  obtain ⟨slot, hslot, hpriority⟩ :=
    exists_profiledRawJointLiteralRightBothExactTruePlay_targetThreadPriority_eq_blockMin
      A strategy hwin installed env past.length .both
  refine ⟨past, slot, ?_, ?_⟩
  · rw [htarget]
    exact hslot
  · simpa [literalRightSeamSelectedTableBlockPriority, play, installed]
      using hpriority

/-- Mirror arbitrary-depth exact `.both` target law. -/
theorem
    exists_literalLeftSeamExactReceiverRecv_bothTargetPriority_of_tableReachable
    (package : Package A strategy hwin (initial := initial))
    (state : LeftReceiver A strategy hwin package)
    (own : In₂) (delivered : In₁)
    (hanchor : state.2.2.1.1 = true)
    (hreach : package.LiteralLeftSeamReceiverTableLocallyReachable A strategy
      hwin state) :
    ∃ past : List (In₂ × In₁),
      ∃ slot : ProfiledRawLeftSlot A,
        (((package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin
          state own delivered).1.2.2.target .both).1.family.left () =
            some slot) ∧
          profiledRawJointThreadRootPriority A (.inr slot) =
            literalLeftSeamSelectedTableBlockPriority A strategy hwin
              (package.literalLeftSeamInstalled A strategy hwin state.1)
              true (omegaOfList (past ++ [(own, delivered)])) past.length
                .both := by
  classical
  let installed := package.literalLeftSeamInstalled A strategy hwin state.1
  let table :=
    profiledRawJointLiteralLeftBothExactHeterogeneousRightTable A strategy hwin
      installed
  obtain ⟨sender, hlocal⟩ := hreach
  obtain ⟨past, _hsender, _hreceiver, hround⟩ :=
    hlocal.exists_localRound_eq_treePlay table (own, delivered)
  let env : Nat → In₂ × In₁ := omegaOfList (past ++ [(own, delivered)])
  let play := profiledRawJointLiteralLeftBothExactTruePlay A strategy hwin
    installed env
  have htarget :
      (((package.literalLeftSeamBranchStagedReceiverRecv A strategy hwin state
        own delivered).1.2.2.target .both).1) =
        (((play past.length).2.1.target .both).1) := by
    have hat := congrArg
      (fun record ↦ (record.2.1.2.target .both).1) hround
    rw [hanchor] at hat
    simpa [literalLeftSeamBranchStagedReceiverRecv,
      profiledRawJointLiteralLeftBothExactReceiverRecv,
      profiledRawJointLiteralLeftBothExactTruePlay,
      BlockRecordMonitor.projectReceiverPlay, play, table, installed,
      hanchor, env] using hat
  obtain ⟨slot, hslot, hpriority⟩ :=
    exists_profiledRawJointLiteralLeftBothExactTruePlay_targetThreadPriority_eq_blockMin
      A strategy hwin installed env past.length .both
  refine ⟨past, slot, ?_, ?_⟩
  · rw [htarget]
    exact hslot
  · simpa [literalLeftSeamSelectedTableBlockPriority, play, installed]
      using hpriority

end ProfiledRawJointGuardedCommonDecoratedPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
