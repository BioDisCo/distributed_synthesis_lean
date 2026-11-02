/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.PitermanComputable

/-! Public compiler client: no synthesis imports and no correctness certificate
supplied by the caller. Runtime transition tests are in `PitermanTransition`. -/
namespace DistributedSynthesis.Tests.PitermanCompilation
open NondetBuchiAutomaton.Piterman

variable {Alphabet : Type*} (A : NondetBuchiAutomaton Alphabet) [DecidableEq A.State]
variable (decStep : ∀ q a q', Decidable (A.step q a q'))
variable (decAccept : DecidablePred A.accepting)

/-- An ordinary definition, not a noncomputable wrapper around the old compiler. -/
def compiled : NondetBuchiToDPACompilation A :=
  Computable.compilation A decStep decAccept

example (word : OmegaWord Alphabet) :
    (compiled A decStep decAccept).dpa.Accepts word ↔ A.Accepts word :=
  (compiled A decStep decAccept).correct word

example (state : CompactTreeData.LiveState A) (letter : Alphabet) :
    Computable.transitionPlan A decStep decAccept state.val state.property letter =
      CompactTreeData.livePlan A state letter :=
  Computable.transitionPlan_eq_livePlan A decStep decAccept state letter

example : (compiled A decStep decAccept).dpa = CompactTreeData.automaton A :=
  Computable.automatonData_eq A decStep decAccept

end DistributedSynthesis.Tests.PitermanCompilation
