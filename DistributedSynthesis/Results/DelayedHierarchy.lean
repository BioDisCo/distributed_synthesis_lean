/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DelayedHierarchy
import DistributedSynthesis.Formalizations.Lemma.LemSummaryGameHierarchy

/-! # Delayed hierarchy and its summary-game adapter

After a right round, equality of process two's full views implies equality of
process one's views before that round. After a left round the roles are
reversed. After a round delivering both messages, equality of process one's
full views implies equality of both processes' previous views. In each statement
the two histories being compared have the indicated final graph.

`DetParityAutomaton.summaryGameDelayOneViewHierarchy_holds` transports the
information comparison to the summary game. At every game history, one process's
pending full view determines its own observation history and the other process's
observation history with the final observation removed. Its premise is equality
of pending full views; equality of finite summary observations is not asserted
to suffice. -/
