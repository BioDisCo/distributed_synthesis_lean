/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderPhaseParity
import DistributedSynthesis.Formalizations.Lemma.LemFiniteRootFamilyNarrowing
import DistributedSynthesis.Formalizations.Lemma.LemPairedEntryTransitionFactorMirror

/-! Reuse simultaneous root-family narrowing for a finite set of histories
indistinguishable to the leader. The block monitors and their realizability
are explicit hypotheses; constructing monitors for all closing obligations
and composing phases remain open. -/
namespace Characterisation
open DistributedSynthesis DetParityAutomaton

/-- Output annotations are irrelevant to the full-information views. This
adapter permits use of the existing strategy restriction API on environment
histories. It does not assert that the annotations were produced by σ. -/
def annotateLeaderRoot {I₁ I₂ O₁ O₂ : Type*} [Inhabited O₁] [Inhabited O₂]
    (h : EnvHistory I₁ I₂) : History I₁ I₂ Graph O₁ O₂ :=
  h.map (fun r => ⟨r.inputOne,r.inputTwo,r.graph,default,default⟩)

theorem annotateLeaderRoot_view {I₁ I₂ O₁ O₂ : Type*}
    [Inhabited O₁] [Inhabited O₂] (p : Proc) (h : EnvHistory I₁ I₂) :
    currentView p (annotateLeaderRoot (O₁:=O₁) (O₂:=O₂) h) = currentView p h := by
  cases p <;> simp [currentView,viewPair,annotateLeaderRoot,List.foldl_map,advanceViews] <;> rfl

/-- The possible boundary histories within one particular leader view. -/
def LeaderBoundaryRoots {I₁ I₂ : Type*}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂) (p : Proc) :=
  {k : InputHistoryComponent P h // currentView p k.val = currentView p h}

instance leaderBoundaryRoots_nonempty {I₁ I₂ : Type*}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂) (p : Proc) :
    Nonempty (LeaderBoundaryRoots P h p) :=
  ⟨⟨⟨h,Relation.ReflTransGen.refl⟩,rfl⟩⟩

theorem bounded_leader_boundary_roots {I₁ I₂ : Type*}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂) (p : Proc) (B : Nat)
    [Finite (InputHistoryComponent P h)] (bound : Nat.card (InputHistoryComponent P h) ≤ B) :
    Finite (LeaderBoundaryRoots P h p) ∧ Nat.card (LeaderBoundaryRoots P h p) ≤ B := by
  letI fin : Finite (LeaderBoundaryRoots P h p) := by
    unfold LeaderBoundaryRoots
    infer_instance
  exact ⟨fin,(Nat.card_le_card_of_injective Subtype.val Subtype.val_injective).trans bound⟩

theorem holes_bounded_leader_boundary_roots {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (A : Set (Nat → Graph)) (regular : OmegaRegular A) (holes : GeometricHoles A) :
    ∃ d B, ∀ h : EnvHistory I₁ I₂, LivePrefix A (History.graphSequence h) →
      leaderBoundary (LivePrefix A) d h = true → ∀ p,
        Finite (LeaderBoundaryRoots (LivePrefix A) h p) ∧
          Nat.card (LeaderBoundaryRoots (LivePrefix A) h p) ≤ B := by
  obtain ⟨d,B,test,result⟩ := holes_agreed_bounded_leader_boundaries (I₁:=I₁) (I₂:=I₂)
    A regular holes
  refine ⟨d,B,fun h live boundary p => ?_⟩
  obtain ⟨fin,bound⟩ := (result h live).2 boundary
  letI : Finite (InputHistoryComponent (LivePrefix A) h) := fin
  exact bounded_leader_boundary_roots (LivePrefix A) h p B bound

/-- The receiver can recover the hidden root when the leader's first
message arrives. This justifies the root tag used by the imported family
monitor; it is not an added observation for either process. -/
theorem leader_one_boundary_root_readback {I₁ I₂ : Type*}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :
    ∃ read : View I₁ I₂ .two → LeaderBoundaryRoots P h .one,
      ∀ (k : LeaderBoundaryRoots P h .one) x y g,
        g = .right ∨ g = .both →
        read (currentView .two (k.val.val++[⟨x,y,g,(),()⟩])) = k := by
  classical
  let past : LeaderBoundaryRoots P h .one → EnvHistory I₁ I₂ := fun k => k.val.val
  have injective : Function.Injective past := by
    intro k l eq
    exact Subtype.ext (Subtype.ext eq)
  obtain ⟨read,correct⟩ := receiving_two_table_is_local
    (fun old (_ : I₁) (_ : I₂) => Function.invFun past old)
  refine ⟨read,fun k x y g delivered => ?_⟩
  rw [correct _ x y g delivered]
  exact Function.leftInverse_invFun injective k

theorem leader_two_boundary_root_readback {I₁ I₂ : Type*}
    (P : List Graph → Prop) (h : EnvHistory I₁ I₂) :
    ∃ read : View I₁ I₂ .one → LeaderBoundaryRoots P h .two,
      ∀ (k : LeaderBoundaryRoots P h .two) x y g,
        g = .left ∨ g = .both →
        read (currentView .one (k.val.val++[⟨x,y,g,(),()⟩])) = k := by
  classical
  let past : LeaderBoundaryRoots P h .two → EnvHistory I₁ I₂ := fun k => k.val.val
  have injective : Function.Injective past := by
    intro k l eq
    exact Subtype.ext (Subtype.ext eq)
  obtain ⟨read,correct⟩ := receiving_one_table_is_local
    (fun old (_ : I₁) (_ : I₂) => Function.invFun past old)
  refine ⟨read,fun k x y g delivered => ?_⟩
  rw [correct _ x y g delivered]
  exact Function.leftInverse_invFun injective k

section Controllers
variable {H I₁ I₂ O₁ O₂ : Type}
variable [Fintype H] [Inhabited H] [DecidableEq H]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]
variable [DecidableEq I₁] [DecidableEq I₂]

/-- One finite instruction table handles every hidden root simultaneously.
All root projections have the same leader output at every own-input word.
The root index is confined to the receiver's part of the instruction. -/
theorem leader_one_root_controller
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (same : ∀ i, currentView .one (past i) = currentView .one (past default))
    (M : H → BlockRecordMonitor I₂ I₁ O₂ O₁)
    (receiver : H → ReceiverBlockStrategy I₂ I₁ O₂)
    (wins : ∀ i env, (M i).WinsPlay
      (pairPlay (receiver i) (blockSenderOne σ (annotateLeaderRoot (past i))) env)) :
    ∃ table : FiniteRootFamilyTable M,
      (∀ i, NarrowedAllThreadsWin (M i)
        (finiteRootMemberController M table.toTransitionRationalTree i).labeledTree) ∧
      (∀ i j word,
        ((finiteRootMemberController M table.toTransitionRationalTree i).labeledTree word).1 =
        ((finiteRootMemberController M table.toTransitionRationalTree j).labeledTree word).1) := by
  let sender := blockSenderOne σ (annotateLeaderRoot (past default))
  have common : ∀ i, blockSenderOne σ (annotateLeaderRoot (past i)) = sender := by
    intro i
    apply blockSenderOne_eq_of_view_eq σ
    simpa only [annotateLeaderRoot_view] using same i
  have sharedWins : ∀ i env, (M i).WinsPlay (pairPlay (receiver i) sender env) := by
    intro i env
    simpa only [common i] using wins i env
  let table := finiteRootFamilyTable M receiver sender sharedWins
  have tableWins := finiteRootFamilyTable_wins M receiver sender sharedWins
  exact ⟨table,
    fun i => finiteRootMemberController_allThreadsWin M _ tableWins i,
    finiteRootMemberController_sender_eq M _⟩

/-- Symmetric reuse when process two is the agreed leader. -/
theorem leader_two_root_controller
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (same : ∀ i, currentView .two (past i) = currentView .two (past default))
    (M : H → BlockRecordMonitor I₁ I₂ O₁ O₂)
    (receiver : H → ReceiverBlockStrategy I₁ I₂ O₁)
    (wins : ∀ i env, (M i).WinsPlay
      (pairPlay (receiver i) (blockSenderTwo σ (annotateLeaderRoot (past i))) env)) :
    ∃ table : FiniteRootFamilyTable M,
      (∀ i, NarrowedAllThreadsWin (M i)
        (finiteRootMemberController M table.toTransitionRationalTree i).labeledTree) ∧
      (∀ i j word,
        ((finiteRootMemberController M table.toTransitionRationalTree i).labeledTree word).1 =
        ((finiteRootMemberController M table.toTransitionRationalTree j).labeledTree word).1) := by
  let sender := blockSenderTwo σ (annotateLeaderRoot (past default))
  have common : ∀ i, blockSenderTwo σ (annotateLeaderRoot (past i)) = sender := by
    intro i
    apply blockSenderTwo_eq_of_view_eq σ
    simpa only [annotateLeaderRoot_view] using same i
  have sharedWins : ∀ i env, (M i).WinsPlay (pairPlay (receiver i) sender env) := by
    intro i env
    simpa only [common i] using wins i env
  let table := finiteRootFamilyTable M receiver sender sharedWins
  have tableWins := finiteRootFamilyTable_wins M receiver sender sharedWins
  exact ⟨table,
    fun i => finiteRootMemberController_allThreadsWin M _ tableWins i,
    finiteRootMemberController_sender_eq M _⟩

end Controllers
end Characterisation
