/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirectParity
import DistributedSynthesis.Library.Distributed.EncodedThreadBuchi

/-! Public numeric compiler clients and small executable regressions.
The complete LTL determinizer has enormous exhaustive carriers; runtime tests
use a one-state Büchi input, not full synthesis on an LTL formula.
-/

namespace DistributedSynthesis.Tests.EncodedCompilers
open EncodedPitermanAutomaton
set_option synthInstance.maxSize 1024

#guard initialCode 1 0 = ([1, 0], [0, 1], [0, 0], [[0], []], 1, 0)
#guard size 1 = 1025
#guard retrieve 1 (locate 1 (some (initialCode 1 0))) == some (initialCode 1 0)
#guard next (1, [(0, 0)], [0]) 0 = 0
#guard next (1, [(0, 0)], [0]) (locate 1 (some (initialCode 1 0))) =
  locate 1 (some (initialCode 1 0))
#guard next (1, [], [0]) (locate 1 (some (initialCode 1 0))) = 0
#guard priority 1 0 = 1
#guard priority 1 (locate 1 (some (initialCode 1 0))) = 0
#guard treePriority ([], [], [], [], 0, 0) = 1
#guard treePriority ([], [], [], [], 3, 1) = 2
#guard treePriority ([], [], [], [], 2, 2) = 3

def oneStateTables := EncodedPitermanCompiler.compile (1, 0, [0], [[(0, 0)], []])
#guard EncodedParityTables.size oneStateTables = 1025
#guard (EncodedParityTables.rows oneStateTables).length = 2
#guard EncodedParityTables.next oneStateTables (EncodedParityTables.initial oneStateTables) 0 =
  EncodedParityTables.initial oneStateTables
#guard EncodedParityTables.next oneStateTables (EncodedParityTables.initial oneStateTables) 1 = 0

open EncodedThreadBuchi in
#guard step (([0, 1, 3], [(0, 1)]), (0, none), (1, some 1))
open EncodedThreadBuchi in
#guard !step (([0, 1, 3], [(0, 0)]), (0, none), (0, some 0))
open EncodedThreadBuchi in
#guard step (([0, 1, 3], [(1, 2)]), (1, some 1), (2, some 1))
open EncodedThreadBuchi in
#guard !step (([0, 1, 3], [(1, 2)]), (1, some 1), (2, some 3))
open EncodedThreadBuchi in
#guard !step (([0, 1, 3], [(2, 1)]), (2, some 3), (1, some 3))
#guard EncodedThreadBuchi.accepting [0, 1, 3] (1, some 1)
#guard !EncodedThreadBuchi.accepting [0, 1, 3] (2, some 1)
#guard !EncodedThreadBuchi.accepting [0, 1, 3] (1, none)
#guard (EncodedThreadBuchi.states 3 [0, 1, 3]).length = 12
#guard (EncodedThreadBuchi.compile (3, 0, [0, 1, 3], [[(0, 1)]])).2.1 = (0, none)

example : Primrec EncodedPitermanCompiler.compile := EncodedPitermanCompiler.compile_primrec
example : Primrec (EncodedLTLParity.compile (A := Nat)) := EncodedLTLParity.compile_primrec
example : Primrec EncodedNoDirectParity.compile := EncodedNoDirectParity.compile_primrec
example : Primrec EncodedThreadBuchi.compile := EncodedThreadBuchi.compile_primrec

example (x : EncodedLTLParity.Input Nat) (word : OmegaWord (Fin x.2.length)) :
    (EncodedLTLParity.automaton x).Accepts word ↔
      LTL.Satisfies EncodedLTLAutomaton.interp (fun t => x.2[word t]) (EncodedFiniteLTL.decode x.1) :=
  EncodedLTLParity.accepts_iff x word
example (d : EncodedNoDirect.Instance) :
    EncodedNoDirect.Realizable d ↔ NoDirectJournal.Realizable (EncodedNoDirectParity.automaton d) :=
  EncodedNoDirectParity.realizable_iff d

end DistributedSynthesis.Tests.EncodedCompilers
