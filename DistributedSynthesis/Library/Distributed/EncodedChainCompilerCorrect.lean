/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainCompiler

/-! # Correctness of the numeric deterministic chain checker -/
namespace DistributedSynthesis.EncodedChainCompiler
set_option maxHeartbeats 800000
open EncodedRoundObjectives EncodedChainThreads EncodedChainMonitor DetParityAutomaton
variable (x : Input)
local notation "A" => EncodedRoundObjectives.automaton (Prod.fst x)
local notation "M" => chainSetMonitor A (decodedSet (Prod.fst x) (Prod.snd x))
local instance : DecidableEq (A).State :=
  inferInstanceAs (DecidableEq (Fin (EncodedRoundObjectives.stateCount x.1)))
local instance : DecidableEq (M).State :=
  inferInstanceAs (DecidableEq (Option (Option (ChainThread A))))
local instance : Inhabited (Fin (inputOne x.1)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (inputTwo x.1)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputOne x.1)) := ⟨⟨0,Nat.succ_pos _⟩⟩
local instance : Inhabited (Fin (outputTwo x.1)) := ⟨⟨0,Nat.succ_pos _⟩⟩

def semanticLetter (a : Fin (rows x).length) : BlockRecordMonitor.ThreadLetter M :=
  (packChainSetLabel (semanticLabel x.1 (rowLetter x a).2.2.1 (rowLetter x a).1),
    decodeBranch x.1 (rowLetter x a))

theorem sourceData_eq : EncodedThreadCompiler.sourceData M (monitorNumber x.1)
    (priorities x.1) (rows x) = threadInput x := by
  unfold EncodedThreadCompiler.sourceData threadInput
  change (Fintype.card (Option (Option (ChainThread A))), (monitorNumber x.1 none).val,_,_) = _
  rw [monitorNumber_val,monitorCard]
  rfl

theorem row_correct (q t : (M).State) (a : Fin (rows x).length) :
    ((monitorNumber x.1 q).val,(monitorNumber x.1 t).val) ∈ (rows x)[a.val]?.getD [] ↔
      ∃ r : (Fin (inputOne x.1) × Fin (inputTwo x.1)) × ChainThread A,
        t = (M).step q (narrowedRecord M (semanticLetter x a).1 q (r,(semanticLetter x a).2)) := by
  rw [row_get,monitorNumber_val,monitorNumber_val]
  have h := EncodedChainMonitor.edges_correct x.1 x.2 (rowLetter x a).1
    (rowLetter x a).2.2.1 (decodeBranch x.1 (rowLetter x a)) q t
  rw [context_decode x (rowLetter x a) (rowLetter_mem x a)] at h
  exact h

theorem accepts_iff (word : OmegaWord (Fin (rows x).length)) :
    (EncodedThreadCompiler.automaton (threadInput x)).Accepts word ↔
      ∀ q : Nat → (M).State, (M).IsThread (OmegaWord.map (semanticLetter x) word) q →
        NatSeqMinEvenParity (fun n => (M).priority (q n)) := by
  have hp (q : (M).State) : (priorities x.1).getD (monitorNumber x.1 q).val 0 = (M).priority q := by
    rw [monitorNumber_val]
    exact priorities_correct x.1 x.2 q
  have h := EncodedThreadCompiler.accepts_iff M (monitorNumber x.1) (priorities x.1) hp
    (priorities_range x.1 x.2) (rows x) (semanticLetter x)
    (fun q a t => row_correct x q t a) word
  have hc := sourceData_eq x
  exact (EncodedThreadCompiler.config_accepts_congr (priorities x.1) (rows x)
    (congrArg Prod.fst hc) (congrArg (fun x => x.2.1) hc) word).symm.trans h
end DistributedSynthesis.EncodedChainCompiler
