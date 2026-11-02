/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLAutomaton

namespace DistributedSynthesis.Tests.EncodedSupports
open EncodedFiniteLTL EncodedSupportTables

#guard EncodedSupports.enumerate (truth : Code Nat) = [[]]
#guard EncodedSupports.enumerate (falsity : Code Nat) = []
#guard EncodedSupports.enumerate (atom 2) = [[2]]
#guard EncodedSupports.enumerate (binary 3 (atom 1) (atom 2)) = [[1, 2]]
#guard EncodedSupports.enumerate (binary 4 (atom 1) (atom 2)) = [[2], [1], [1, 2]]
-- A valid empty support must not be confused with no valid support.
#guard EncodedSupports.enumerate (binary 4 truth (atom 2)) = [[], [2]]
#guard EncodedSupports.enumerate (binary 3 (atom 2) (atom 2)) = [[2], [2], [2, 2]]
-- The semantics of malformed codes is the existing total Boolean decoder's.
#guard EncodedSupports.enumerate ([] : Code Nat) = []
#guard EncodedSupports.enumerate ([.inr 5, .inr 0] : Code Nat) = []
#guard EncodedSupports.enumerate ([.inr 5, .inr 0, .inr 4] : Code Nat) = [[]]
#guard EncodedSupports.enumerate ((atom 1) ++ (atom 2)) = []
#guard EncodedSupports.atoms (binary 3 (atom 2) (unary 5 (atom 3))) = [2]

def row : Row := [binary 4 (atom 1) (atom 2), atom 2, truth]
#guard enumerateTables row [] = [[]]
#guard enumerateTables [falsity] [0] = []
#guard enumerateTables row [99] = []
#guard (enumerateTables row [0, 1]).length = 3
#guard [(0, [1]), (1, [2])] ∈ enumerateTables row [0, 1]
#guard [(0, [1])] ∉ enumerateTables row [0, 1]
#guard [(1, [1]), (0, [2])] ∉ enumerateTables row [0, 1]

def chosen : Table := [(0, [1]), (1, [2])]
#guard advance [0, 1, 1] [] chosen = ([1, 2], [1, 2])
#guard advance [0, 1, 1] [0] chosen = ([1, 2], [1])
#guard advance [0, 1, 1] [1] chosen = ([1, 2], [2])
#guard advance [0, 2, 1] [] chosen = ([1, 2], [2])
#guard advance [0, 0, 0] [] chosen = ([1, 2], [])

def p : Code Nat := atom 7
def u : Code Nat := binary 6 p p
def repeatedUntil : Code Nat := binary 3 u u
-- The second occurrence points to the first, not to itself.
#guard EncodedPositiveLTL.index repeatedUntil (EncodedPositiveLTL.normalize u) = 1
#guard (EncodedPositiveLTL.occurrence repeatedUntil ⟨4, by decide⟩).val =
  (EncodedPositiveLTL.occurrence repeatedUntil ⟨1, by decide⟩).val
#guard (EncodedLTLAutomaton.supportTables (repeatedUntil, [7]) [4]).any
  (fun table => (4, [1]) ∈ table)
#guard !(EncodedLTLAutomaton.supportTables (repeatedUntil, [7]) [4]).any
  (fun table => (4, [4]) ∈ table)

example : Primrec (EncodedSupports.enumerate (A := Nat)) := EncodedSupports.enumerate_primrec
example : Primrec₂ enumerateTables := enumerateTables_primrec
example : Primrec₂ (EncodedLTLAutomaton.supportTables (A := Nat)) :=
  EncodedLTLAutomaton.supportTables_primrec

example (c : Code Nat) (word : OmegaWord (List Nat)) :
    (EncodedLTLAutomaton.automaton c).Accepts word ↔
      LTL.Satisfies EncodedLTLAutomaton.interp word (EncodedFiniteLTL.decode c) :=
  EncodedLTLAutomaton.accepts_iff c word

example (c : Code Nat) :
    AlternatingParityAutomaton.SelfOrDecreasing (EncodedLTLAutomaton.automaton c)
      (EncodedLTLAutomaton.measure c) := EncodedLTLAutomaton.weak c

end DistributedSynthesis.Tests.EncodedSupports
