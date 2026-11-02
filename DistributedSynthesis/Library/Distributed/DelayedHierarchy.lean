/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Views
import DistributedSynthesis.Formalizations.Lemma.LemDelayonehierarchy

/-! # One-round delayed view hierarchy
Unconditional constructor-level facts `delayOneHierarchy_left/right/both`.
These compare full views with settled prefixes, not finite summary observations,
and do not imply finite winning replacement or synthesis decidability. -/
