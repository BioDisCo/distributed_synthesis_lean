/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainMonitorCorrect
import DistributedSynthesis.Library.Distributed.EncodedCheckerLabels
import DistributedSynthesis.Library.Distributed.EncodedThreadStream
import DistributedSynthesis.Library.Distributed.ThreadWordMonitor

/-! # Set-started numeric chain checkers in the journal interface

The retained set is the set at the handoff, not the evolving set of current
threads. Its canonical finite-subset code determines the prestart transitions.
-/
namespace DistributedSynthesis.EncodedChainCheckerAssembly
open EncodedRoundObjectives EncodedOrdinaryThreads EncodedChainThreads DetParityAutomaton
variable (d : Data)
local notation "A" => EncodedRoundObjectives.automaton d
local instance : DecidableEq (A).State := inferInstanceAs (DecidableEq (Fin (stateCount d)))
local instance (T : Finset (ChainThread A)) : DecidableEq (chainSetMonitor A T).State :=
  inferInstanceAs (DecidableEq (Option (Option (ChainThread A))))
local instance : Inhabited (Fin (inputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo d)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Fintype (EncodedCheckerLabels.ChainLabel d) := JournalCheckers.chainLabelFintype A

def handoff (T : Finset (ChainThread A)) : List Nat :=
  FiniteSubsets.encode (T.map (chainEquiv d).toEmbedding)
theorem decoded_handoff (T : Finset (ChainThread A)) :
    EncodedChainMonitor.decodedSet d (handoff d T) = T := by
  ext th
  rw [EncodedChainMonitor.mem_decodedSet]
  change (chainEquiv d th).val ∈ FiniteSubsets.encode (T.map (chainEquiv d).toEmbedding) ↔ _
  rw [← FiniteSubsets.mem_decode,FiniteSubsets.decode_encode]
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]

theorem label_decode (l : EncodedCheckerLabels.ChainLabel d) :
    semanticLabel d (EncodedCheckerLabels.chain d l) (EncodedCheckerLabels.chainMode d l) = l := by
  cases l <;> simp only [semanticLabel,EncodedCheckerLabels.chain,EncodedCheckerLabels.chainMode,
    label,EncodedJournalLabels.decode_encode,EncodedCheckerLabels.chainLift,
    Bool.cond_true,Bool.cond_false,GlobalJournalLabel.revLeft,GlobalJournalLabel.revRight]

abbrev Letter := EncodedCheckerLabels.ChainLabel d × (Fin (inputTwo d) ⊕ Fin (inputOne d))
def packed (a : Letter d) : BlockRecordMonitor.ThreadLetter (chainSetMonitor A ∅) :=
  (packChainSetLabel a.1,a.2)
def baseEdges (T : Finset (ChainThread A)) (a : Letter d) :=
  EncodedChainMonitor.edges (EncodedChainMonitor.context d (handoff d T)
    (EncodedCheckerLabels.chainMode d a.1) (EncodedCheckerLabels.chain d a.1) a.2)
def config : EncodedThreadStream.Config :=
  (EncodedChainMonitor.stateCount d,0,EncodedChainMonitor.priorities d)
def dpa (T : Finset (ChainThread A)) := EncodedThreadStream.automaton (config d) (baseEdges d T)

theorem edges_correct (T : Finset (ChainThread A)) (q t : (chainSetMonitor A T).State)
    (a : Letter d) :
    ((EncodedChainMonitor.monitorNumber d q).val,(EncodedChainMonitor.monitorNumber d t).val) ∈ baseEdges d T a ↔
      ∃ r : (Fin (inputOne d) × Fin (inputTwo d)) × ChainThread A,
        t = (chainSetMonitor A T).step q (narrowedRecord (chainSetMonitor A T) (packed d a).1 q (r,a.2)) := by
  have h := EncodedChainMonitor.edges_correct d (handoff d T)
    (EncodedCheckerLabels.chainMode d a.1) (EncodedCheckerLabels.chain d a.1) a.2 q t
  rw [decoded_handoff,label_decode] at h
  simpa only [EncodedChainMonitor.monitorNumber_val] using h

theorem source_config (T : Finset (ChainThread A)) :
    (Fintype.card (chainSetMonitor A T).State,
      (EncodedChainMonitor.monitorNumber d (chainSetMonitor A T).initial).val,
      EncodedChainMonitor.priorities d) = config d := by
  change (Fintype.card (Option (Option (ChainThread A))),_,_) = _
  rw [EncodedChainMonitor.monitorNumber_val,EncodedChainMonitor.monitorCard]
  rfl

theorem accepts_iff (T : Finset (ChainThread A)) (word : OmegaWord (Letter d)) :
    (dpa d T).Accepts word ↔ ∀ q : Nat → (chainSetMonitor A T).State,
      (chainSetMonitor A T).IsThread (OmegaWord.map (packed d) word) q →
        NatSeqMinEvenParity (fun n => (chainSetMonitor A T).priority (q n)) := by
  have hp (q : (chainSetMonitor A T).State) :
      (EncodedChainMonitor.priorities d).getD (EncodedChainMonitor.monitorNumber d q).val 0 =
        (chainSetMonitor A T).priority q := by
    rw [EncodedChainMonitor.monitorNumber_val]
    have h := EncodedChainMonitor.priorities_correct d (handoff d T) q
    rw [decoded_handoff] at h
    exact h
  have hr := EncodedChainMonitor.priorities_range d (handoff d T)
  rw [decoded_handoff] at hr
  have h := EncodedThreadStream.accepts_iff (chainSetMonitor A T)
    (EncodedChainMonitor.monitorNumber d) (EncodedChainMonitor.priorities d) hp hr
    (baseEdges d T) (packed d) (fun q a t => edges_correct d T q t a) word
  exact (Iff.of_eq (congrArg (fun c =>
    (EncodedThreadStream.automaton c (baseEdges d T)).Accepts word) (source_config d T))).symm.trans h

def perSet (T : Finset (ChainThread A)) := WordTreeMonitor.monitor (dpa d T)
theorem perSet_winning_iff (T : Finset (ChainThread A))
    (tree : LabeledTree (Fin (inputTwo d) ⊕ Fin (inputOne d)) (EncodedCheckerLabels.ChainLabel d)) :
    (perSet d T).WinningTree tree ↔ ∀ th ∈ T, ChainAllThreadsWin A tree th :=
  (ThreadWordMonitor.winning_iff_map (chainSetMonitor A T) (dpa d T)
    (fun l => (packed d (l,Sum.inl ⟨0,Nat.succ_pos _⟩)).1)
    (accepts_iff d T) tree).trans (chainSetAllThreadsWin_iff T tree)

def checker : (EncodedRoundObjectives.automaton d).ChainThreadChecker := by
  letI := JournalCheckers.chainLabelFintype A
  exact {
    monitor := JournalCheckers.family ∅ (perSet d)
    start := fun T => ⟨T,(perSet d T).initial⟩
    winning_iff := fun T tree => (JournalCheckers.family_winningTree_iff ∅ T (perSet d) tree).trans
      (perSet_winning_iff d T tree) }
end DistributedSynthesis.EncodedChainCheckerAssembly
