/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedInitialLeaderBanks
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeftLeaderPhysical

/-! Search the existing complete bank enumeration using the left local test. -/
namespace Characterisation.EncodedInitialLeftLeaderBanks
open DistributedSynthesis EncodedInitialLeaderBanks
attribute [local irreducible] Primrec
local instance initialLeftMemoryCode : Primcodable EncodedGraphMemory.Data := inferInstance
local instance initialLeftDataCode : Primcodable EncodedLeaderPhysical.Data := inferInstance

def solve (d : EncodedLeaderPhysical.Data) :=
  decide (∃ bank ∈ banks d, EncodedLeftLeaderPhysical.solve (withBank d bank) = true)

theorem solve_primrec : Primrec solve := (FiniteSearch.exists_mem banks_primrec
  (Primrec.eq.comp (EncodedLeftLeaderPhysical.solve_primrec.comp withBank_primrec) (Primrec.const true)).primrecRel).decide

theorem solve_iff (d : EncodedLeaderPhysical.Data) : solve d = true ↔
    ∃ bank ∈ banks d, EncodedLeftLeaderPhysical.solve (withBank d bank) = true := by
  simp only [solve,decide_eq_true_eq]

end Characterisation.EncodedInitialLeftLeaderBanks
