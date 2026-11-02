/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteLetterLTL
import DistributedSynthesis.Formalizations.Lemma.LemEncodedFiniteLTL

/-! # Finite-table LTL and computable syntax
Current-letter, consecutive-letter, and initial-boundary constraints; postfix
encoding and primitive-recursive assembly. Independent of the particular
counter-machine reduction. The semantic table API uses classical finite
enumeration; the encoded API carries explicit primitive-recursiveness proofs. -/
