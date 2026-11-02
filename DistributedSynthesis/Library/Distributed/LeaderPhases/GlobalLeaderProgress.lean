/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.LeaderHandoverProgress

/-! One global finite controller preserves parity through repeated leader
handovers. This uses the original public-tree/hidden-history construction,
with concrete predecessor edges from joint handover outcomes. -/
namespace Characterisation
open DistributedSynthesis

def OfferedHandoverEdge {Q Move : Type} {B C : Nat}
    (offers : Move → LeaderHandover Q B C → Bool)
    (old : HandoverCode B C) (move : Move) (nextFamily : LeaderHandover Q B C)
    (next : HandoverCode B C) : Prop :=
  offers move nextFamily = true ∧ HandoverEdge old nextFamily () next

section Trees
variable {Q Move : Type} {B C : Nat}
variable [Fintype Q] [Fintype Move] [Inhabited (LeaderHandover Q B C)]
variable (offers : Move → LeaderHandover Q B C → Bool)
variable (initial : HandoverCode B C) (initialFamily : LeaderHandover Q B C)
variable (Legal : SwitchInterface Q B → Move → Prop) [DecidableRel Legal]

/-- Public state contains the joint boundary outcome and the determinized
progress monitor. The actual root and priority thread remain hidden. Legal
must express realizability of the whole phase, including any infinite tail. -/
noncomputable def globalLeaderProgressMonitor :=
  hiddenCodeContinuityTreeMonitor (handoverPriorityDPA B C) initial
    (OfferedHandoverEdge offers) initialFamily (fun family move => Legal family.1 move)

theorem globalLeaderProgress_winning_iff (tree : LabeledTree (LeaderHandover Q B C) Move) :
    (globalLeaderProgressMonitor offers initial initialFamily Legal).WinningTree tree ↔
      ObservableMovesValid initialFamily (fun family move => Legal family.1 move) tree ∧
        ∀ branch : Nat → LeaderHandover Q B C,
          ∀ thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
            (observableThreadWord tree branch),
            NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val) := by
  rw [globalLeaderProgressMonitor,hiddenCodeContinuityTreeMonitor_winning_iff]
  simp only [handoverPriorityDPA_accepts_iff,HiddenCodeContinuityThread.childCodeWord]

/-- Rationalize once globally, preserving all compatible hidden histories
on every branch. This is stronger than choosing a new winning continuation
independently at each boundary. The finite phase alphabet and its legality
are explicit parameters, not supplied by this theorem. -/
theorem finite_global_leader_progress
    (tree : LabeledTree (LeaderHandover Q B C) Move)
    (legal : ObservableMovesValid initialFamily (fun family move => Legal family.1 move) tree)
    (progress : ∀ branch : Nat → LeaderHandover Q B C,
      ∀ thread : HiddenCodeContinuityThread initial (OfferedHandoverEdge offers)
        (observableThreadWord tree branch),
        NatSeqMinEvenParity (fun n => (thread.code (n+1)).2.val)) :
    ∃ table : RunParityTreeAutomaton.StateControlledTreeTable
        (globalLeaderProgressMonitor offers initial initialFamily Legal).toRunAutomaton,
      (globalLeaderProgressMonitor offers initial initialFamily Legal).WinningTree
        table.toTransitionRationalTree.labeledTree := by
  apply exists_stateControlled_hiddenCodeContinuityTree (handoverPriorityDPA B C)
    initial (OfferedHandoverEdge offers) initialFamily (fun family move => Legal family.1 move)
    tree legal
  intro branch thread
  exact (handoverPriorityDPA_accepts_iff _).mpr (progress branch thread)

end Trees

/-- Acceptance of the global monitor gives physical parity on any one
compatible history, using the original block-minimum theorem. -/
theorem handoverProgress_physical_parity {Q : Type} {B C : Nat}
    (initial : HandoverCode B C) (word : Nat → LeaderHandover Q B C × Unit)
    (accepted : (handoverProgressSystem initial).universalRunDPA.Accepts word)
    (thread : HiddenCodeContinuityThread initial HandoverEdge word)
    (priority cuts : Nat → Nat) (mono : StrictMono cuts) (zero : cuts 0 = 0)
    (minimum : ∀ n, (thread.code (n+1)).2.val = cutBlockMin priority cuts n) :
    NatSeqMinEvenParity priority := by
  have winning := (handoverProgress_accepts_iff initial word).mp accepted thread
  have eq := funext minimum
  rw [eq] at winning
  exact (natSeqMinEvenParity_cutBlockMin priority mono zero).mp winning

end Characterisation
