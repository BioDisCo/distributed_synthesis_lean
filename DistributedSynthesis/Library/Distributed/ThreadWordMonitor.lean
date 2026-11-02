/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.WordTreeMonitor
import DistributedSynthesis.Library.Distributed.ThreadCompilation

/-! # Packaging any exact universal-thread DPA as a tree checker -/
namespace DistributedSynthesis.ThreadWordMonitor
variable {RIn SIn ROut SOut : Type*}
  [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut] [DecidableEq RIn] [DecidableEq SIn]
  (M : BlockRecordMonitor RIn SIn ROut SOut)
  [DecidableEq M.State]
  (D : DetParityAutomaton (BlockRecordMonitor.ThreadLetter M))

local instance : Fintype (NarrowedBlockLabel RIn SIn ROut SOut M.State) := inferInstance

theorem winning_iff (hD : ∀ word, D.Accepts word ↔ ∀ q : Nat → M.State,
    M.IsThread word q → NatSeqMinEvenParity (fun n => M.priority (q n)))
    (tree : LabeledTree SIn (NarrowedBlockLabel RIn SIn ROut SOut M.State)) :
    (WordTreeMonitor.monitor D).WinningTree tree ↔ NarrowedAllThreadsWin M tree := by
  rw [WordTreeMonitor.winning_iff, ← M.threadBlockMonitor_winningTree_iff]
  have hMon : WordTreeMonitor.monitor M.threadDPA = M.threadBlockMonitor := by
    have hfin : (WordTreeMonitor.monitor M.threadDPA).alphabetFinite =
        M.threadBlockMonitor.alphabetFinite := Subsingleton.elim _ _
    dsimp only [WordTreeMonitor.monitor, BlockRecordMonitor.threadBlockMonitor] at hfin ⊢
    rw [hfin]
  rw [← hMon]
  rw [WordTreeMonitor.winning_iff]
  apply forall_congr'
  intro branch
  exact (hD _).trans (M.threadDPA_accepts_iff _).symm

/-- A label may supply only the response fields used by the thread monitor. -/
theorem winning_iff_map {Label : Type*} [Fintype Label]
    (D' : DetParityAutomaton (Label × SIn))
    (f : Label → NarrowedBlockLabel RIn SIn ROut SOut M.State)
    (hD : ∀ word, D'.Accepts word ↔ ∀ q : Nat → M.State,
      M.IsThread (OmegaWord.map (fun a => (f a.1,a.2)) word) q →
        NatSeqMinEvenParity (fun n => M.priority (q n)))
    (tree : LabeledTree SIn Label) :
    (WordTreeMonitor.monitor D').WinningTree tree ↔
      NarrowedAllThreadsWin M (fun node => f (tree node)) := by
  rw [WordTreeMonitor.winning_iff,
    ← winning_iff M M.threadDPA (M.threadDPA_accepts_iff ·), WordTreeMonitor.winning_iff]
  apply forall_congr'
  intro branch
  exact (hD _).trans (M.threadDPA_accepts_iff _).symm
end DistributedSynthesis.ThreadWordMonitor
