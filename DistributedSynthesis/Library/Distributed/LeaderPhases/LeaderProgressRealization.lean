/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.HandoverHistoryLifting

/-! Derive global handover progress from one physical winning strategy.
Only finite edge data are required of its boundary-family realization:
literal predecessors, increasing physical depths, and exact phase minima.
Infinite hidden-thread acceptance is a conclusion. -/
namespace Characterisation
open DistributedSynthesis

theorem take_branchNode {α : Type} (word : Nat → α) (n m : Nat) (bound : n ≤ m) :
    (branchNode word m).take n = branchNode word n := by
  apply List.ext_getElem
  · simp [branchNode_eq_ofFn,Nat.min_eq_left bound]
  · intro i _ _
    simp only [branchNode_eq_ofFn,List.getElem_take,List.getElem_ofFn]

def historyPhaseMinimum {α : Type} (score : List α → Nat)
    (start finish : Nat) (history : List α) : Nat :=
  rangeMin (fun i => score (history.take (start+i+1))) 0 (finish-start-1)

theorem historyPhaseMinimum_exact {α : Type} (score : List α → Nat)
    (physical : Nat → α) (cuts : Nat → Nat) (mono : StrictMono cuts)
    (n : Nat) (history : List α) (exactHistory : branchNode physical (cuts (n+1)) = history) :
    historyPhaseMinimum score (cuts n) (cuts (n+1)) history =
      cutBlockMin (fun t => score (branchNode physical (t+1))) cuts n := by
  unfold historyPhaseMinimum cutBlockMin
  apply rangeMin_congr
  intro i within
  have strict := mono (show n < n+1 by omega)
  rw [← exactHistory,take_branchNode physical _ _ (by omega)]
  simp only [Nat.zero_add]

/-- A single family is fixed at each public node for all hidden threads.
Its choice is not permitted to depend on which hidden slot is followed.
For a model instantiation, score is the actual objective priority after
the outputs of the original strategy on this entire finite history. -/
structure LeaderProgressRealization {α Q Move : Type} {B C : Nat}
    (score : List α → Nat) (offers : Move → LeaderHandover Q B C → Bool)
    (tree : LabeledTree (LeaderHandover Q B C) Move) where
  past : TreeNode (LeaderHandover Q B C) → Fin (B+1) → List α
  cut : TreeNode (LeaderHandover Q B C) → Nat
  depth : ∀ node i, (past node i).length = cut node
  initial : cut [] = 0
  advances : ∀ node outcome, offers (tree node) outcome = true →
    cut node < cut (node++[outcome])
  parents : ∀ node outcome, offers (tree node) outcome = true →
    ∀ i : Fin outcome.1.1.val,
      (past node (outcome.2.1 i)).IsPrefix
        (past (node++[outcome]) (handoverSlot outcome i))
  minima : ∀ node outcome, offers (tree node) outcome = true →
    ∀ i : Fin outcome.1.1.val,
      (outcome.2.2 i).val = historyPhaseMinimum score (cut node)
        (cut (node++[outcome])) (past (node++[outcome]) (handoverSlot outcome i))

/-- The local predecessor/minimum equations suffice to transport physical
winning to every infinite compatible handover thread. No winning-successor
predicate or independently restarted continuation is used in this proof. -/
theorem leaderProgress_of_realization {α Q Move : Type} {B C : Nat}
    (score : List α → Nat) (offers : Move → LeaderHandover Q B C → Bool)
    (tree : LabeledTree (LeaderHandover Q B C) Move)
    (realization : LeaderProgressRealization score offers tree)
    (winning : ∀ physical : Nat → α,
      NatSeqMinEvenParity (fun t => score (branchNode physical (t+1)) ))
    (initial : HandoverCode B C) (branch : Nat → LeaderHandover Q B C)
    (thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
      (observableThreadWord tree branch)) :
    NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  let cuts n := realization.cut (branchNode branch n)
  let family n := realization.past (branchNode branch n)
  have offered : ∀ n, offers (tree (branchNode branch n)) (branch n) = true :=
    fun n => (thread.edge n).1
  have mono : StrictMono cuts := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact realization.advances _ _ (offered n)
  have zero : cuts 0 = 0 := realization.initial
  let plain : HiddenCodeContinuityThread initial HandoverEdge (fun n => (branch n,())) :=
    ⟨thread.code,thread.initial,fun n => (thread.edge n).2⟩
  have parents : ∀ n (i : Fin (branch n).1.1.val),
      (family n ((branch n).2.1 i)).IsPrefix
        (family (n+1) (handoverSlot (branch n) i)) := by
    intro n i
    exact realization.parents _ _ (offered n) i
  obtain ⟨physical,history⟩ := handover_thread_lifts_history initial (fun n => (branch n,()))
    family cuts (fun n i => realization.depth _ i) mono parents plain
  have exactMin : ∀ n, (thread.code (n+1)).2.val =
      cutBlockMin (fun t => score (branchNode physical (t+1))) cuts n := by
    intro n
    obtain ⟨i,_,next⟩ := (thread.edge n).2
    have label := congrArg (fun code : HandoverCode B C => code.2.val) next
    have slot := congrArg Prod.fst next
    have minimum := realization.minima _ _ (offered n) i
    have actual : branchNode physical (cuts (n+1)) =
        family (n+1) (handoverSlot (branch n) i) := by
      simpa only [plain,slot] using history (n+1)
    exact label.trans (minimum.trans (historyPhaseMinimum_exact score physical cuts mono n _ actual))
  rw [funext exactMin]
  exact (natSeqMinEvenParity_cutBlockMin _ mono zero).mpr (winning physical)

/-- One finite public controller preserves the original strategy's global
parity, once its finite phase offers have a faithful boundary realization.
The original state-controlled extraction is applied only once, to the
complete tree of leader handovers. -/
theorem finite_global_leader_of_realization {α Q Move : Type} {B C : Nat}
    [Fintype Q] [Fintype Move] [Inhabited (LeaderHandover Q B C)]
    (score : List α → Nat) (offers : Move → LeaderHandover Q B C → Bool)
    (initial : HandoverCode B C) (initialFamily : LeaderHandover Q B C)
    (Legal : SwitchInterface Q B → Move → Prop) [DecidableRel Legal]
    (tree : LabeledTree (LeaderHandover Q B C) Move)
    (realization : LeaderProgressRealization score offers tree)
    (legal : ObservableMovesValid initialFamily (fun family move => Legal family.1 move) tree)
    (winning : ∀ physical : Nat → α,
      NatSeqMinEvenParity (fun t => score (branchNode physical (t+1)) )) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (globalLeaderProgressMonitor offers initial initialFamily Legal).toRunAutomaton,
      (globalLeaderProgressMonitor offers initial initialFamily Legal).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  exact finite_global_leader_progress offers initial initialFamily Legal tree legal
    (leaderProgress_of_realization score offers tree realization winning initial)

end Characterisation
