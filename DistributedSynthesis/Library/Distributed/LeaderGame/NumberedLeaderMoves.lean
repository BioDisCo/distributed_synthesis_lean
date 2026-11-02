/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundaryPhaseSemantics
import DistributedSynthesis.Library.Distributed.LeaderPhases.ClosingOfferMinima
import DistributedSynthesis.Library.Automata.TreeNonemptiness
import DistributedSynthesis.Library.Distributed.ThreadCompilation

/-! Finite local moves indexed by numbered boundary data. Leader groups
are rows of the observation matrix, so the alphabet contains no literal
history or view. The local thread test reuses the original finite parity
nonemptiness algorithm. The global game correspondence is not asserted. -/
namespace Characterisation
open DistributedSynthesis

abbrev ShapeLeaderGroup {H : Type} (shape : InputShape H) (p : Proc) :=
  {row : H → Bool // ∃ h, shape p h = row}

instance shapeLeaderGroup_fintype {H : Type} [Fintype H] [DecidableEq H]
    (shape : InputShape H) (p : Proc) : Fintype (ShapeLeaderGroup shape p) := by
  unfold ShapeLeaderGroup
  exact Fintype.subtype (Finset.univ.filter fun row => ∃ h, shape p h = row)
    (by intro row; simp only [Finset.mem_filter,Finset.mem_univ,true_and])

instance shapeLeaderGroup_decidableEq {H : Type} [Fintype H] [DecidableEq H]
    (shape : InputShape H) (p : Proc) : DecidableEq (ShapeLeaderGroup shape p) := by
  unfold ShapeLeaderGroup
  infer_instance

def shapeLeaderGroup {H : Type} (shape : InputShape H) (p : Proc) (h : H) : ShapeLeaderGroup shape p :=
  ⟨shape p h,⟨h,rfl⟩⟩

theorem shapeLeaderGroup_exact {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (p : Proc) (h k : H) :
    shapeLeaderGroup shape p h = shapeLeaderGroup shape p k ↔
      currentView p (past h) = currentView p (past k) := by
  constructor
  · intro equal
    have rows := congrArg Subtype.val equal
    have atK := congrFun rows k
    change shape p h k = shape p k k at atK
    apply (rep p h k).mp
    rw [atK]
    exact (rep p k k).mpr rfl
  · intro views
    apply Subtype.ext
    funext j
    apply Bool.eq_iff_iff.mpr
    change shape p h j = true ↔ shape p k j = true
    rw [rep,rep,views]

/-- The matrix-defined groups have distinct concrete leader views in every
realization. Representatives are used only in this proof-side decoder. -/
theorem shapeLeaderGroup_views {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape) (p : Proc) :
    ∃ base : ShapeLeaderGroup shape p → View I₁ I₂ p,
      Function.Injective base ∧
      ∀ h, currentView p (past h) = base (shapeLeaderGroup shape p h) := by
  classical
  let pick : ShapeLeaderGroup shape p → H := fun g => g.property.choose
  have picked : ∀ g, shapeLeaderGroup shape p (pick g) = g := by
    intro g
    exact Subtype.ext g.property.choose_spec
  let base := fun g => currentView p (past (pick g))
  refine ⟨base,?_,?_⟩
  · intro g j equal
    have groups := (shapeLeaderGroup_exact past shape rep p (pick g) (pick j)).mpr equal
    rwa [picked,picked] at groups
  · intro h
    exact (shapeLeaderGroup_exact past shape rep p h (pick (shapeLeaderGroup shape p h))).mp
      (picked _).symm

section ThreadTest
variable {RIn SIn ROut SOut : Type}
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut) [DecidableEq M.State]

/-- The executable test is the existing finite parity-tree search, applied
to the existing executable universal-thread compilation. -/
def leaderThreadTest : Bool :=
  @TreeNonemptiness.nonempty _ _ (ThreadCompilation.monitor M) (ThreadCompilation.stateDecidableEq M)

theorem leaderThreadTest_correct :
    leaderThreadTest M = true ↔ ∃ tree, NarrowedAllThreadsWin M tree := by
  rw [leaderThreadTest,TreeNonemptiness.nonempty_correct]
  apply exists_congr
  intro tree
  exact ((ThreadCompilation.monitor M).acceptsTree_iff_winningTree tree).trans
    (ThreadCompilation.winningTree_iff M tree)

end ThreadTest

section Numbered
variable {GQ I₁ I₂ O₁ O₂ : Type} {d K B C : Nat}
variable [Fintype GQ] [DecidableEq GQ]
variable [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
variable [DecidableEq I₁] [DecidableEq I₂] [DecidableEq O₁] [DecidableEq O₂]
variable (M : Recognizer Graph GQ) [DecidablePred (· ∈ M.accept)]
variable (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
variable [DecidableEq objective.State]
variable (rank : objective.State → Fin (C+1))

abbrev LeaderAnnotation := (GraphRootState GQ d K × objective.State) × (Unit → Fin (C+1))
abbrev NumberedLeaderHeader := SwitchInterface (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B

instance numberedLeaderHeader_fintype : Fintype (NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := by
  unfold NumberedLeaderHeader SwitchInterface LeaderAnnotation InputShape
  infer_instance

/-- Graph and objective state advance together at each physical output. -/
noncomputable def leaderStateStep
    (q : GraphRootState GQ d K × objective.State)
    (input : I₁ × I₂ × Graph) (output : O₁ × O₂) :
    GraphRootState GQ d K × objective.State :=
  (chooseGraphRootNext M q.1 input.2.2,objective.step q.2 (input,output))

/-- Reuse the checked closing-minimum accumulator. It includes every output,
including the closing output, and starts from the incoming objective state. -/
noncomputable def leaderAnnotationStep :
    LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective →
      (I₁ × I₂ × Graph) → (O₁ × O₂) →
      LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective :=
  closingMinimumStep (leaderStateStep M objective)
    (fun q input output _ => rank (objective.step q.2 (input,output)))

def resetLeaderMinimum
    (q : LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) :
    LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective :=
  (q.1,fun _ => Fin.last C)

variable (header : NumberedLeaderHeader (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)

abbrev NumberedLeaderOutcome := LeaderHandover
  (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B C

instance numberedLeaderOutcome_decidableEq :
    DecidableEq (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective) := by
  letI : DecidableEq (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) := by
    unfold LeaderAnnotation
    infer_instance
  letI : DecidableEq (SwitchInterface (LeaderAnnotation (GQ:=GQ) (d:=d) (K:=K) (C:=C) objective) B) := by
    unfold SwitchInterface InputShape
    infer_instance
  unfold NumberedLeaderOutcome LeaderHandover
  infer_instance

def numberedLeaderSlot (i : Fin header.1.val) : Fin (B+1) := ⟨i.val,lt_trans i.isLt header.1.isLt⟩

/-- A complete local guard built solely from the finite numbered header,
the advertised outcomes, and the initial contingent closing bank. -/
noncomputable def numberedRightGuard
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d) :
    BlockRecordMonitor I₂ I₁ (RollingReceiverOutput (Fin header.1.val) I₁ I₂ O₁ O₂ d)
      (ShapeLeaderGroup header.2.1 .one → O₁) :=
  let group := shapeLeaderGroup header.2.1 .one
  let step := leaderAnnotationStep M objective rank
  let initial := fun i => resetLeaderMinimum objective (header.2.2 i)
  let source := fun i => (header.2.2 i).1.1
  phaseOfferMonitor (jointLeaderMonitor group header.2.1
    (jointPhaseObjective objective (fun i => (header.2.2 i).1.2) group) bank) id
    ((source,(fun _ => true),initial),bank,true)
    (jointGraphLeaderNext group M step (fun st => chooseGraphRootNext M st .right))
    (jointGraphLeaderCollect M step header.2.1 (numberedLeaderSlot objective header) (fun q => q.2 ())) permitted

/-- The local table type is finite and contains no actual source histories,
absolute depth, or unbounded duration. -/
abbrev NumberedRightTable
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :=
  Σ bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d,
    RunParityTreeAutomaton.StateControlledTreeTable
      (numberedRightGuard M objective rank header permitted bank).threadBlockMonitor.toRunAutomaton

instance numberedRightTable_finite
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    Finite (NumberedRightTable M objective rank header permitted) := by
  classical
  letI : Fintype (ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d) := closingPlanBank_fintype d
  letI : ∀ bank : ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d,
      Fintype (RunParityTreeAutomaton.StateControlledTreeTable
        (numberedRightGuard M objective rank header permitted bank).threadBlockMonitor.toRunAutomaton) :=
    fun _ => inferInstance
  unfold NumberedRightTable
  infer_instance

/-- A finite search over initial banks and the original parity-tree test.
This typed construction still inherits noncomputable finite automaton data
from the current objective construction; no uniform numeric compiler is
claimed by this definition. -/
noncomputable def numberedRightLegal
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) : Bool := by
  classical
  letI : Fintype (ClosingPlanBank (Fin header.1.val) I₁ I₂ O₁ O₂ d) := closingPlanBank_fintype d
  exact decide (∃ bank, leaderThreadTest (numberedRightGuard M objective rank header permitted bank) = true)

theorem numberedRightLegal_correct
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    numberedRightLegal M objective rank header permitted = true ↔
      ∃ bank tree, NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted bank) tree := by
  classical
  simp only [numberedRightLegal,decide_eq_true_eq,leaderThreadTest_correct]

variable [Inhabited I₁] [Inhabited I₂] [Inhabited O₁] [Inhabited O₂]

omit [Inhabited I₂] [Inhabited O₁] [Inhabited O₂] in
/-- The finite local test passes exactly when a member of the fixed finite
table alphabet is accepted. This is the original state-controlled extraction,
applied to the complete numbered guard. -/
theorem numberedRightLegal_iff_table
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective)) :
    numberedRightLegal M objective rank header permitted = true ↔
      ∃ table : NumberedRightTable M objective rank header permitted,
        NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted table.1)
          table.2.toTransitionRationalTree.labeledTree := by
  rw [numberedRightLegal_correct]
  constructor
  · rintro ⟨bank,tree,winning⟩
    let guard := numberedRightGuard M objective rank header permitted bank
    have accepted := (guard.threadBlockMonitor.acceptsTree_iff_winningTree tree).mpr
      ((guard.threadBlockMonitor_winningTree_iff tree).mpr winning)
    letI := guard.threadBlockMonitor.alphabetFinite
    obtain ⟨table,correct⟩ := guard.threadBlockMonitor.toRunAutomaton.exists_stateControlledTreeTable_accepted
      ⟨tree,accepted⟩
    exact ⟨⟨bank,table⟩,(guard.threadBlockMonitor_winningTree_iff _).mp
      ((guard.threadBlockMonitor.acceptsTree_iff_winningTree _).mp correct)⟩
  · rintro ⟨table,winning⟩
    exact ⟨table.1,table.2.toTransitionRationalTree.labeledTree,winning⟩

/-- Every passing numbered table has one distributed implementation on
every realization of its matrix. The closing banks and one-way outputs use
the same implementation, and its infinite rightward plays satisfy the
objective from the advertised incoming states. -/
theorem numberedRightTable_readback
    (permitted : Finset (NumberedLeaderOutcome (GQ:=GQ) (d:=d) (K:=K) (B:=B) (C:=C) objective))
    (table : NumberedRightTable M objective rank header permitted)
    (winning : NarrowedAllThreadsWin (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree)
    (past : Fin header.1.val → EnvHistory I₁ I₂)
    (shape : RepresentsInputShape past header.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L) :
    let tree := narrowedInducedTree (numberedRightGuard M objective rank header permitted table.1)
      table.2.toTransitionRationalTree.labeledTree
    let receiver := receiverOfTree tree
    let leader := senderOfTree tree
    ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
      (∀ node h, closingPlanOfStrategy σ (rollingSourceHistory past node h) (d+1) =
        receiverClosingBank table.1 receiver node h) ∧
      (∀ node r h,
        σ.one (currentView .one (rollingSourceHistory past (node++[r]) h)) =
          leader (senderWord node) r.2 (shapeLeaderGroup header.2.1 .one h) ∧
        σ.two (currentView .two (rollingSourceHistory past (node++[r]) h)) = (receiver node r).1 h) ∧
      ∀ h (env : Nat → I₂ × I₁), objective.AcceptsFrom (header.2.2 h).1.2
        (continuationTrace (strategyContinuationPolicy σ past) h
          (fun n => ((env n).2,(env n).1,.right))) := by
  let guard := numberedRightGuard M objective rank header permitted table.1
  let tree := narrowedInducedTree guard table.2.toTransitionRationalTree.labeledTree
  let group := shapeLeaderGroup header.2.1 .one
  let physical := jointPhaseObjective objective (fun i => (header.2.2 i).1.2) group
  let monitor := jointLeaderMonitor group header.2.1 physical table.1
  have guarded : ∀ env, guard.WinsPlay (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    rw [pairPlay,treeOfPair_ofTree (senderOblivious_narrowedInducedTree guard _)]
    exact (guard.lift_winningTree_iff tree).mp
      (narrowedInducedTree_winningTree_of_allThreadsWin guard winning) env
  have checked : ∀ env, monitor.WinsPlay (pairPlay (receiverOfTree tree) (senderOfTree tree) env) := by
    intro env
    have parts := (phaseOfferMonitor_wins_iff _ _ _ _ _ _ _).mp (guarded env)
    simpa only [phasePhysicalPlay,id_eq,Prod.eta] using parts.1
  obtain ⟨σ,plans,outputs⟩ := jointLeaderMonitor_readback group header.2.1 physical table.1
    past shape L depth (shapeLeaderGroup_exact past header.2.1 shape .one)
    (receiverOfTree tree) (senderOfTree tree) checked
  refine ⟨σ,plans,outputs,?_⟩
  apply jointPhaseObjective_readback objective (fun i => (header.2.2 i).1.2) past group
    (receiverOfTree tree) (senderOfTree tree) σ outputs
  intro env
  exact ((jointLeaderMonitor_wins_iff group header.2.1 physical table.1 _).mp (checked env)).1

end Numbered
end Characterisation
