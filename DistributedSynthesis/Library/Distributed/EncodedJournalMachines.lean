/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedThreadStream
import DistributedSynthesis.Library.Distributed.EncodedChainMonitor

/-! # Uniform numeric configurations and steps of the journal checkers -/
namespace DistributedSynthesis.EncodedJournalMachines
open EncodedRoundObjectives

def ordinaryConfig (d : Data) (boundary : Nat) : EncodedThreadStream.Config :=
  (stateCount d * stateCount d, EncodedOrdinaryThreads.initial d boundary, EncodedOrdinaryThreads.priorities d)
def chainConfig (d : Data) : EncodedThreadStream.Config :=
  (EncodedChainMonitor.stateCount d,0,EncodedChainMonitor.priorities d)
def ordinarySize (d : Data) := EncodedThreadStream.size (ordinaryConfig d 0)
def chainSize (d : Data) := EncodedThreadStream.size (chainConfig d)
def ordinaryInitial (d : Data) (b : Nat) := EncodedThreadStream.initial (ordinaryConfig d b)
def chainInitial (d : Data) := EncodedThreadStream.initial (chainConfig d)
def ordinaryNext (x : EncodedOrdinaryThreads.Context × Nat × Nat) :=
  EncodedThreadStream.next (ordinaryConfig x.1.1 0,EncodedOrdinaryThreads.edges x.1 x.2.2,x.2.1)
def chainNext (x : EncodedChainMonitor.Context × Nat) :=
  EncodedThreadStream.next (chainConfig x.1.1.1,EncodedChainMonitor.edges x.1,x.2)

theorem ordinaryConfig_primrec : Primrec₂ ordinaryConfig :=
  (Primrec.nat_mul.comp (stateCount_primrec.comp Primrec.fst) (stateCount_primrec.comp Primrec.fst)).pair
    ((EncodedOrdinaryThreads.initial_primrec.comp Primrec.fst Primrec.snd).pair
      (EncodedOrdinaryThreads.priorities_primrec.comp Primrec.fst))
theorem chainConfig_primrec : Primrec chainConfig := EncodedChainMonitor.stateCount_primrec.pair
  ((Primrec.const 0).pair EncodedChainMonitor.priorities_primrec)
theorem ordinarySize_primrec : Primrec ordinarySize :=
  EncodedThreadStream.size_primrec.comp (ordinaryConfig_primrec.comp Primrec.id (Primrec.const 0))
theorem chainSize_primrec : Primrec chainSize := EncodedThreadStream.size_primrec.comp chainConfig_primrec
theorem ordinaryInitial_primrec : Primrec₂ ordinaryInitial :=
  EncodedThreadStream.initial_primrec.comp ordinaryConfig_primrec
theorem chainInitial_primrec : Primrec chainInitial := EncodedThreadStream.initial_primrec.comp chainConfig_primrec
theorem ordinaryNext_primrec : Primrec ordinaryNext := EncodedThreadStream.next_primrec.comp
  ((ordinaryConfig_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 0)).pair
    ((EncodedOrdinaryThreads.edges_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.fst.comp Primrec.snd)))
theorem chainNext_primrec : Primrec chainNext := EncodedThreadStream.next_primrec.comp
  ((chainConfig_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))).pair
    ((EncodedChainMonitor.edges_primrec.comp Primrec.fst).pair Primrec.snd))
end DistributedSynthesis.EncodedJournalMachines
