/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.SupportedPublicTree
import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderProgressRealization

/-! A global leader monitor whose legality obligations follow actual offers.
The hidden predecessor thread still carries the whole-phase minima. -/
namespace Characterisation
open DistributedSynthesis

section Monitor
variable {Q Move : Type} {B C : Nat}
variable [Fintype Q] [Fintype Move] [Inhabited (LeaderHandover Q B C)]
variable (offers : Move → LeaderHandover Q B C → Bool)
variable (initial : HandoverCode B C) (initialFamily : LeaderHandover Q B C)
variable (Legal : SwitchInterface Q B → Move → Prop) [DecidableRel Legal]

noncomputable def supportedLeaderProgressMonitor :=
  supportedPublicTreeMonitor
    (hiddenCodeContinuitySystem (handoverPriorityDPA B C) initial
      (OfferedHandoverEdge offers)).universalRunDPA
    offers initialFamily (fun family move => Legal family.1 move)

/-- Every hidden thread is supported at every prefix. The monitor enforces
legality even if there are no infinite hidden continuations from a node. -/
theorem supportedLeaderProgress_winning_iff
    (tree : LabeledTree (LeaderHandover Q B C) Move) :
    (supportedLeaderProgressMonitor offers initial initialFamily Legal).WinningTree tree ↔
      SupportedMovesValid offers initialFamily (fun family move => Legal family.1 move) tree ∧
      ∀ branch : Nat → LeaderHandover Q B C,
        ∀ thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
          (observableThreadWord tree branch),
          NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [supportedLeaderProgressMonitor, supportedPublicTreeMonitor_winning_iff]
  constructor
  · rintro ⟨legal, accepted⟩
    refine ⟨legal, fun branch thread => ?_⟩
    have supported := publicSupport_branch_of_offered offers tree branch (fun n => (thread.edge n).1)
    have threads := (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      (handoverPriorityDPA B C) initial (OfferedHandoverEdge offers)
      (observableThreadWord tree branch)).mp (accepted branch supported)
    exact (handoverPriorityDPA_accepts_iff _).mp (threads thread)
  · rintro ⟨legal, progress⟩
    refine ⟨legal, fun branch _ => ?_⟩
    apply (hiddenCodeContinuitySystem_universalRunDPA_accepts_iff
      (handoverPriorityDPA B C) initial (OfferedHandoverEdge offers)
      (observableThreadWord tree branch)).mpr
    intro thread
    exact (handoverPriorityDPA_accepts_iff _).mpr (progress branch thread)

/-- Reuse global state-controlled extraction once, after proving legality
on supported nodes and parity of coherent threads. No legal fallback move
is required at an impossible observation. -/
theorem finite_supported_leader_progress
    (tree : LabeledTree (LeaderHandover Q B C) Move)
    (legal : SupportedMovesValid offers initialFamily (fun family move => Legal family.1 move) tree)
    (progress : ∀ branch : Nat → LeaderHandover Q B C,
      ∀ thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
        (observableThreadWord tree branch),
        NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val)) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (supportedLeaderProgressMonitor offers initial initialFamily Legal).toRunAutomaton,
      (supportedLeaderProgressMonitor offers initial initialFamily Legal).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  let M := supportedLeaderProgressMonitor offers initial initialFamily Legal
  have winning : M.WinningTree tree :=
    (supportedLeaderProgress_winning_iff offers initial initialFamily Legal tree).mpr ⟨legal, progress⟩
  obtain ⟨table, accepted⟩ := M.toRunAutomaton.exists_stateControlledTreeTable_accepted
    ⟨tree, (M.acceptsTree_iff_winningTree tree).mpr winning⟩
  exact ⟨table, (M.acceptsTree_iff_winningTree table.toTransitionRationalTree.labeledTree).mp accepted⟩

end Monitor

/-- Finite histories need to realize only supported nodes. Their depths may
grow without a bound, and every supported edge has a literal predecessor.
This is a local realization condition, not an assertion that such a tree
has already been constructed from the graph-hole hypothesis. -/
structure SupportedLeaderProgressRealization {α Q Move : Type} {B C : Nat}
    (score : List α → Nat) (offers : Move → LeaderHandover Q B C → Bool)
    (tree : LabeledTree (LeaderHandover Q B C) Move) where
  past : TreeNode (LeaderHandover Q B C) → Fin (B+1) → List α
  cut : TreeNode (LeaderHandover Q B C) → Nat
  depth : ∀ node, publicSupport offers tree node = true →
    ∀ i, (past node i).length = cut node
  initial : cut [] = 0
  advances : ∀ node, publicSupport offers tree node = true →
    ∀ outcome, offers (tree node) outcome = true → cut node < cut (node++[outcome])
  parents : ∀ node, publicSupport offers tree node = true →
    ∀ outcome, offers (tree node) outcome = true →
    ∀ i : Fin outcome.1.1.val,
      (past node (outcome.2.1 i)).IsPrefix (past (node++[outcome]) (handoverSlot outcome i))
  minima : ∀ node, publicSupport offers tree node = true →
    ∀ outcome, offers (tree node) outcome = true →
    ∀ i : Fin outcome.1.1.val,
      (outcome.2.2 i).val = historyPhaseMinimum score (cut node)
        (cut (node++[outcome])) (past (node++[outcome]) (handoverSlot outcome i))

/-- Prefix lifting and exact block minima establish global parity without
asking for any history realization below unsupported observations. -/
theorem leaderProgress_of_supported_realization {α Q Move : Type} {B C : Nat}
    (score : List α → Nat) (offers : Move → LeaderHandover Q B C → Bool)
    (tree : LabeledTree (LeaderHandover Q B C) Move)
    (realization : SupportedLeaderProgressRealization score offers tree)
    (winning : ∀ physical : Nat → α,
      NatSeqMinEvenParity (fun t => score (branchNode physical (t+1))))
    (initial : HandoverCode B C) (branch : Nat → LeaderHandover Q B C)
    (thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
      (observableThreadWord tree branch)) :
    NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  let cuts n := realization.cut (branchNode branch n)
  let family n := realization.past (branchNode branch n)
  have offered : ∀ n, offers (tree (branchNode branch n)) (branch n) = true :=
    fun n => (thread.edge n).1
  have supported := publicSupport_branch_of_offered offers tree branch offered
  have mono : StrictMono cuts := by
    apply strictMono_nat_of_lt_succ
    intro n
    exact realization.advances _ (supported n) _ (offered n)
  have zero : cuts 0 = 0 := realization.initial
  let plain : HiddenCodeContinuityThread initial HandoverEdge (fun n => (branch n,())) :=
    ⟨thread.code, thread.initial, fun n => (thread.edge n).2⟩
  have parents : ∀ n (i : Fin (branch n).1.1.val),
      (family n ((branch n).2.1 i)).IsPrefix
        (family (n+1) (handoverSlot (branch n) i)) := by
    intro n i
    exact realization.parents _ (supported n) _ (offered n) i
  obtain ⟨physical, history⟩ := handover_thread_lifts_history initial (fun n => (branch n,()))
    family cuts (fun n i => realization.depth _ (supported n) i) mono parents plain
  have exactMin : ∀ n, (thread.code (n+1)).2.val =
      cutBlockMin (fun t => score (branchNode physical (t+1))) cuts n := by
    intro n
    obtain ⟨i, _, next⟩ := (thread.edge n).2
    have label := congrArg (fun code : HandoverCode B C => code.2.val) next
    have slot := congrArg Prod.fst next
    have minimum := realization.minima _ (supported n) _ (offered n) i
    have actual : branchNode physical (cuts (n+1)) =
        family (n+1) (handoverSlot (branch n) i) := by
      simpa only [plain, slot] using history (n+1)
    exact label.trans (minimum.trans (historyPhaseMinimum_exact score physical cuts mono n _ actual))
  rw [funext exactMin]
  exact (natSeqMinEvenParity_cutBlockMin _ mono zero).mpr (winning physical)

end Characterisation
