/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryCompiler

/-! Numeric journal regression tests. Small objective tables avoid executing
the enormous exhaustive LTL determinizer. Unequal input/output cardinalities
make orientation errors observable. -/
namespace DistributedSynthesis.Tests.EncodedJournal
open EncodedRoundObjectives EncodedOrdinaryThreads

#guard EncodedJournalLabels.specs (2,2,3,2,3) =
  [(3,3), (24,2), (24,3), (8,2), (2,2), (24,3), (24,2), (12,3),
   (96,2), (32,2), (12,3), (96,3), (96,2), (8,2), (48,3), (96,3)]
#guard EncodedJournalLabels.allCodes (1,1,1,1,1) = [List.replicate 16 [0]]

def alphabets : EncodedNoDirect.Instance where
  inputOneSizeMinusOne := 1
  inputTwoSizeMinusOne := 2
  outputOneSizeMinusOne := 1
  outputTwoSizeMinusOne := 2
  truthTable := []
  formula := []
def objective : Data :=
  (alphabets, (1,0,[5,1],List.replicate (EncodedNoDirect.letters alphabets).length [1,1]))
def tieObjective : Data :=
  (alphabets, (1,0,[1,1],List.replicate (EncodedNoDirect.letters alphabets).length [1,1]))
def code : EncodedJournalLabels.Code :=
  [[0,1,2], List.range 24, [], [], [1,0], List.range 24]

#guard roundCode ((objective,false,code),0,1,2) = (1,2,0,1,2)
#guard roundCode ((objective,true,code),0,2,1) = (1,2,1,0,2)
#guard next ((objective,false,code),0,1,2) = 3
#guard next ((objective,true,code),0,2,1) = 3
-- A tie retains the old minimum state, not the newly reached state.
#guard next ((tieObjective,false,code),0,1,2) = 2
#guard next ((tieObjective,true,code),0,2,1) = 2
#guard next ((tieObjective,false,code),1,1,2) = 3
#guard priorities objective = [5,5,1,1]
#guard initial objective 1 = 3
#guard (edges (objective,false,code) 2).length = 8
#guard (edges (objective,true,code) 1).length = 12
#guard (0,3) ∈ edges (objective,false,code) 2
#guard (0,2) ∉ edges (objective,false,code) 2
#guard (0,2) ∈ edges (tieObjective,true,code) 1
-- Missing fields are normalized by decoding, rather than being undefined.
#guard roundCode ((objective,false,[]),0,1,2) = (1,2,0,0,0)

def singletonInstance : EncodedNoDirect.Instance := ⟨0,0,0,0,[],[]⟩
def singletonObjective : Data := (singletonInstance,(0,0,[1],[[0],[0],[0]]))
#guard (EncodedOrdinaryCompiler.alphabet (singletonObjective,false,0)).length = 1
#guard EncodedOrdinaryCompiler.baseRows (singletonObjective,false,0) = [[(0,0)]]
#guard (EncodedOrdinaryCompiler.compile (singletonObjective,false,0)).1 = [(0,none),(0,some 1)]
#guard (EncodedOrdinaryCompiler.compile (singletonObjective,false,0)).2.2.1 = [(0,some 1)]
#guard (EncodedOrdinaryCompiler.compile (singletonObjective,true,0)).2.2.2 =
  [[((0,none),(0,none)), ((0,none),(0,some 1)), ((0,some 1),(0,some 1))]]

example : Primrec EncodedJournalLabels.allCodes := EncodedJournalLabels.allCodes_primrec
example : Primrec EncodedOrdinaryCompiler.compile := EncodedOrdinaryCompiler.compile_primrec
example (d : Data) (l : DetParityAutomaton.GlobalJournalLabel (automaton d)) :
    EncodedJournalLabels.decode (automaton d) (stateNumber d)
      (EncodedJournalLabels.encode (automaton d) (stateNumber d) l) = l :=
  EncodedJournalLabels.decode_encode _ _ l
example (d : Data) (l : DetParityAutomaton.GlobalJournalLabel (automaton d)) :
    ∃ c ∈ EncodedOrdinaryCompiler.labels d, label d c = l :=
  EncodedOrdinaryCompiler.labels_complete d l
example (d : EncodedNoDirect.Instance) :
    automaton (fromInstance d) = EncodedNoDirectParity.automaton d := automaton_fromInstance d

end DistributedSynthesis.Tests.EncodedJournal
