/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirect
import DistributedSynthesis.Library.Automata.EncodedParityProductCorrect
import DistributedSynthesis.Formalizations.ComponentGames.LiveStates

/- Numeric graph-automaton input and executable live-prefix recognition. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 200000

def graphInput (d : EncodedParityTables.Data) : DetParityAutomaton Graph where
  State := Fin (EncodedParityTables.size d)
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial d % EncodedParityTables.size d, Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q g := ⟨EncodedParityTables.next d q.val (EncodedNoDirect.graphCode g).val,
    Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := EncodedParityTables.priority d q.val

instance graphInputDecidableEq (d : EncodedParityTables.Data) :
    DecidableEq (graphInput d).State := inferInstanceAs (DecidableEq (Fin (EncodedParityTables.size d)))
instance prefixAcceptDecidable (d : EncodedParityTables.Data) :
    DecidablePred (· ∈ (prefixRecognizer (graphInput d)).accept) :=
  acceptingContinuationDecidable (graphInput d)

end Characterisation.ComponentGames
