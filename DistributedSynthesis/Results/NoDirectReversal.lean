/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmMainCanonical
import DistributedSynthesis.Library.Distributed.NoDirectJournal
import DistributedSynthesis.Library.Distributed.EncodedNoDirect
import DistributedSynthesis.Library.Distributed.EncodedNoDirectComputable

/-! # No-direct-reversal fragment

There is a primitive-recursive algorithm deciding whether an encoded LTL
specification is realizable when consecutive rounds may not change directly
from left-only delivery to right-only delivery, or conversely. A round delivering
both messages may separate the two directions. Both processes have finite,
nonempty input and output alphabets, supplied as part of the instance; private
input streams are unrestricted, and strategies have full-view perfect recall.
The formula may contain the next operator.

`EncodedNoDirectComputable.realizable_computable` states computability of this
realizability predicate. Its `solve_primrec` and `solve_correct` theorems prove
primitive recursiveness and correctness of the Boolean solver. The semantic
reduction to journal-tree nonemptiness is exposed separately through
`NoDirectJournal.realizable_iff_nonempty`.

The `main_result_for_ltl_noDirect_fragment_synthesis_finiteAlphabets`
is a classical `noncomputable def` returning `Decidable`. The algorithmic
assertion is provided by the encoded solver above. Other full-network endpoints
in the imported module retain their certificate hypotheses. -/
