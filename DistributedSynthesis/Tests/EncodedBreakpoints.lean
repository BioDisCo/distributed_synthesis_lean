/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLBreakpoints

namespace DistributedSynthesis.Tests.EncodedBreakpoints
open EncodedFiniteLTL

#guard FiniteSubsets.normalize 3 [2, 0, 2, 99] = [0, 2]
#guard FiniteSubsets.pairs 0 = [([], [])]
#guard (FiniteSubsets.pairs 2).length = 16

-- Empty frontiers remain empty, including when the pending code is invalid.
#guard EncodedBreakpoints.step (0, [], [], ([], [99]), ([], []))
#guard EncodedBreakpoints.step (2, [truth, truth], [1, 1], ([], [1]), ([], []))
#guard EncodedBreakpoints.step (2, [truth, truth], [1, 1], ([0], []), ([], []))
#guard !EncodedBreakpoints.step (1, [falsity], [0], ([0], []), ([], []))

-- A reset uses the entire chosen successor set and keeps only odd targets.
#guard EncodedBreakpoints.step (3, [binary 3 (atom 1) (atom 2)], [0, 2, 1],
  ([0], []), ([1, 2], [2]))
#guard !EncodedBreakpoints.step (3, [binary 3 (atom 1) (atom 2)], [0, 2, 1],
  ([0], []), ([1, 2], [1]))

-- Impossible with ONE support table; separate choices for the two updates
-- would incorrectly admit this transition.
#guard !EncodedBreakpoints.step (3, [binary 4 (atom 1) (atom 2)], [0, 1, 1],
  ([0], [0]), ([1], [2]))
#guard EncodedBreakpoints.step (3, [binary 4 (atom 1) (atom 2)], [0, 1, 1],
  ([0], [0]), ([1], [1]))
-- Lists are codes for sets: order, repetition and out-of-bound entries do not matter.
#guard EncodedBreakpoints.step (3, [binary 3 (atom 1) (atom 2)], [0, 1, 1],
  ([0, 0, 99], [0, 99]), ([2, 1, 2, 99], [1, 2]))
#guard EncodedBreakpoints.step (3, [atom 1], [0, 1, 1],
  ([0], [99]), ([1], [1]))

#guard EncodedLTLBreakpoints.transition (((atom 7), [7]), ([0], []), ([], []))
#guard !EncodedLTLBreakpoints.transition (((atom 7), []), ([0], []), ([], []))
-- Until may continue forever as a transition, but its pending set remains nonempty.
def eventuallySeven : Code Nat := binary 6 truth (atom 7)
#guard EncodedLTLBreakpoints.transition ((eventuallySeven, []), ([0], []), ([0], [0]))
#guard EncodedLTLBreakpoints.transition ((eventuallySeven, []), ([0], [0]), ([0], [0]))
#guard !EncodedLTLBreakpoints.accepting eventuallySeven ([0], [0])
#guard EncodedLTLBreakpoints.transition ((eventuallySeven, [7]), ([0], [0]), ([], []))
#guard EncodedLTLBreakpoints.accepting eventuallySeven ([], [])

example : PrimrecPred EncodedBreakpoints.step := EncodedBreakpoints.step_primrec
example : Primrec (EncodedLTLBreakpoints.compile (A := Nat)) := EncodedLTLBreakpoints.compile_primrec

example (c : Code Nat) (word : OmegaWord (List Nat)) :
    (EncodedLTLBreakpoints.buchi c).Accepts word ↔
      LTL.Satisfies EncodedLTLAutomaton.interp word (EncodedFiniteLTL.decode c) :=
  EncodedLTLBreakpoints.accepts_iff c word

end DistributedSynthesis.Tests.EncodedBreakpoints
