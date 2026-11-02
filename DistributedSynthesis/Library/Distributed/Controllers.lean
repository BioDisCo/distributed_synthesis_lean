/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyController
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyReceiptMemory
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedStateEncoding
import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedAutomatonMonitor

/-! # Finite distributed controllers
Existing paired Mealy/Moore interfaces, receipt-memory extension, correlated
state encoding, and finite automaton monitors. These implement finite
controllers; no extraction from arbitrary perfect-recall winners is asserted.
This comprehensive compatibility API retains the physical-adapter dependencies.
For controller types and the Mealy-to-Moore timing bridge alone, import
`Distributed.PhysicalControllers` or `Distributed.MealyControllers`; those
modules do not depend on synthesis, parity games, or epoch adapters. -/
