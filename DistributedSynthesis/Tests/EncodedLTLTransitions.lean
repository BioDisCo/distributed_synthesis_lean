/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLTransitions

namespace DistributedSynthesis.Tests.EncodedLTLTransitions
open EncodedFiniteLTL

def p : Code Nat := atom 7
def q : Code Nat := atom 8

def rows (source : Code Nat) (v : List Nat) : List (PosBool Nat) :=
  (DistributedSynthesis.EncodedLTLTransitions.row (source, v)).map EncodedPositiveBoolean.decode

#guard rows p [7] = [.verum]
#guard rows p [] = [.falsum]
#guard rows (unary 2 p) [7] = [.falsum]
#guard rows (unary 2 p) [] = [.verum]
#guard rows (unary 5 p) [] = [.atom 1, .falsum]
#guard rows (binary 3 p p) [7] = [.conj .verum .verum, .verum, .verum]
-- Next points to the first occurrence of a repeated subformula.
#guard rows (binary 3 (unary 5 p) (unary 5 p)) [7] =
  [.conj (.atom 2) (.atom 2), .atom 2, .verum, .atom 2, .verum]
-- Until/release continue at the root state, index zero.
#guard rows (binary 6 p q) [7] = [.disj .falsum (.conj .verum (.atom 0)), .verum, .falsum]
#guard rows (binary 7 p q) [8] = [.conj .verum (.disj .falsum (.atom 0)), .falsum, .verum]
#guard rows (unary 2 (binary 6 p q)) [7] =
  [.conj .verum (.disj .falsum (.atom 0)), .falsum, .verum]
-- The total source decoder's underflow recovery and surplus rejection survive.
#guard rows [] [7] = [.falsum]
#guard rows [.inr 5, .inr 2] [] = [.verum]
#guard rows (p ++ q) [7, 8] = [.falsum]
#guard DistributedSynthesis.EncodedLTLTransitions.table p ([] : List (List Nat)) = []
#guard (DistributedSynthesis.EncodedLTLTransitions.table p [[7], []]).map
    (List.map EncodedPositiveBoolean.decode) = [[.verum], [.falsum]]
#guard DistributedSynthesis.EncodedLTLTransitions.trueAtoms [(7, 0), (8, 1), (7, 0)] 0 = [7, 7]
#guard DistributedSynthesis.EncodedLTLTransitions.trueAtoms [(7, 0), (8, 1)] 2 = ([] : List Nat)

example : Primrec₂ (DistributedSynthesis.EncodedLTLTransitions.table (A := Nat)) :=
  DistributedSynthesis.EncodedLTLTransitions.table_primrec

example (ctx : DistributedSynthesis.EncodedLTLTransitions.Context Nat)
    (s : (PositiveLTL.ofLTL (EncodedFiniteLTL.decode ctx.1)).Subformula)
    (n : Nat) (h : .inl n ∈ DistributedSynthesis.EncodedLTLTransitions.transition ctx (EncodedPositiveLTL.quote s.val)) :
    n < (EncodedPositiveLTL.states ctx.1).length :=
  DistributedSynthesis.EncodedLTLTransitions.transition_bounded ctx s n h

end DistributedSynthesis.Tests.EncodedLTLTransitions
