/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.LTLTranslation
import DistributedSynthesis.Library.Automata.Piterman
import DistributedSynthesis.Library.Automata.Compilers

/-! Public compiler interfaces and their language-correctness field. -/
open DistributedSynthesis

noncomputable section

#guard_msgs (drop info) in
#check NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler
#guard_msgs (drop info) in
#check PositiveLTL.canonicalLTLToDPACompiler

-- Instantiate the extracted interface directly, without the backend.
example {Letter : Type} (A : NondetBuchiAutomaton Letter) :
    NondetBuchiToDPACompilation A :=
  (NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler Letter).compile A

example {AP Letter : Type} [DecidableEq AP]
    (interp : AP → Letter → Prop)
    (dec : ∀ a b, Decidable (interp a b))
    (φ : LTL AP) (w : OmegaWord Letter) :
    ((PositiveLTL.canonicalLTLToDPACompiler interp dec).compile φ).Accepts w ↔
      LTL.Satisfies interp w φ :=
  (PositiveLTL.canonicalLTLToDPACompiler interp dec).correct φ w
