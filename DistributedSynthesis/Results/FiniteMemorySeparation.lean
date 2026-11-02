/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemScalingLTLWinner

/-! # Perfect recall does not admit universal finite winning replacement

There is a fixed LTL specification over finite output alphabets that two
perfect-recall processes can realize against every graph sequence, although
no pair of finite physical controllers can realize it. Both input alphabets
are singletons. The theorem
`ScalingSafety.ResidueLTL.ltl_realizable_not_finite` states the existence of
the winning strategy pair and the nonexistence of a finite winning controller.

The imported development also gives a safety parity-automaton version of the
separation. These results show that restricting the search to finite controllers
can lose realizable specifications; they do not alone prove undecidability. -/
