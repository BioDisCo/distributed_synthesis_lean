/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderPhysical

/-! Eliminate the initial-bank choice by complete finite search. Replacing
the initial bank changes the collector template's promised outputs; every
subsequent bank remains a receiver output in the local leader game. -/
namespace Characterisation.EncodedInitialLeaderBanks
open DistributedSynthesis
attribute [local irreducible] Primrec
local instance : Primcodable EncodedGraphMemory.Data := inferInstance
local instance : Primcodable EncodedLeaderPhysical.Data := inferInstance

def replaceReplayBank (d : EncodedScheduledCollector.ReplayData) (bank : EncodedClosingBanks.Bank) :
    EncodedScheduledCollector.ReplayData := (d.1,bank,d.2.2)
def replaceMemoryBank (d : EncodedGraphMemory.Data) (bank : EncodedClosingBanks.Bank) :
    EncodedGraphMemory.Data := ((replaceReplayBank d.1.1 bank,d.1.2),d.2)
def withBank (d : EncodedLeaderPhysical.Data) (bank : EncodedClosingBanks.Bank) : EncodedLeaderPhysical.Data :=
  (d.1,replaceMemoryBank d.2.1 bank,d.2.2)
def banks (d : EncodedLeaderPhysical.Data) :=
  EncodedClosingBanks.banks (EncodedGraphMemory.bankData (EncodedLeaderPhysical.memory d))
    (EncodedGraphMemory.outputs (EncodedLeaderPhysical.memory d))
def solve (d : EncodedLeaderPhysical.Data) :=
  decide (∃ bank ∈ banks d, EncodedLeaderPhysical.solve (withBank d bank) = true)

theorem replaceReplayBank_primrec : Primrec₂ replaceReplayBank := (Primrec.fst.comp Primrec.fst).pair
  (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
theorem replaceMemoryBank_primrec : Primrec₂ replaceMemoryBank :=
  ((replaceReplayBank_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).pair
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair (Primrec.snd.comp Primrec.fst)
theorem withBank_primrec : Primrec₂ withBank := (Primrec.fst.comp Primrec.fst).pair
  ((replaceMemoryBank_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).pair
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
theorem banks_primrec : Primrec banks := EncodedClosingBanks.banks_primrec.comp
  (EncodedGraphMemory.bankData_primrec.comp EncodedLeaderPhysical.memory_primrec)
  (EncodedGraphMemory.outputs_primrec.comp EncodedLeaderPhysical.memory_primrec)
theorem solve_primrec : Primrec solve := (FiniteSearch.exists_mem banks_primrec
  (Primrec.eq.comp (EncodedLeaderPhysical.solve_primrec.comp withBank_primrec) (Primrec.const true)).primrecRel).decide

theorem solve_iff (d : EncodedLeaderPhysical.Data) : solve d = true ↔
    ∃ bank ∈ banks d, EncodedLeaderPhysical.solve (withBank d bank) = true := by
  simp only [solve,decide_eq_true_eq]

end Characterisation.EncodedInitialLeaderBanks
