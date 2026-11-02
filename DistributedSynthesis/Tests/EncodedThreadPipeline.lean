/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedThreadStream
import DistributedSynthesis.Library.Distributed.EncodedReversalForgivingCorrect
import DistributedSynthesis.Library.Distributed.EncodedChainCompiler
import DistributedSynthesis.Library.Distributed.EncodedJournalAssembly
import DistributedSynthesis.Library.Distributed.EncodedJournalSubsetsCorrect
import DistributedSynthesis.Tests.EncodedJournal

/-! Small numeric tests for duplicate priorities, direct reversals and handoffs.
Complete large determinized tables are not materialized in these tests. -/
namespace DistributedSynthesis.Tests.EncodedThreadPipeline
open EncodedJournal

def boundaryCode : EncodedJournalLabels.Code := (List.range 16).map (List.replicate 96)
#guard EncodedJournalBoundary.closeRound ((objective,false,boundaryCode),0,1,2) = (1,2,2,1,2)
#guard EncodedJournalBoundary.closeRound ((objective,true,boundaryCode),0,1,2) = (1,2,2,0,2)
#guard EncodedJournalBoundary.reverseRound ((objective,false,boundaryCode),0,1,2) = (1,2,1,1,2)
#guard EncodedJournalBoundary.reverseRound ((objective,true,boundaryCode),0,1,2) = (1,2,0,0,1)
#guard EncodedJournalBoundary.chainCloseRound ((objective,true,boundaryCode),0,1,2) = (1,2,2,0,2)
#guard EncodedJournalBoundary.chainCloseRound ((objective,false,boundaryCode),0,1,2) = (1,2,2,0,0)
-- Closing emits the old minimum; reversing includes the new state first.
#guard EncodedJournalBoundary.close ((objective,false,boundaryCode),0,1,2) = 2
#guard EncodedJournalBoundary.reverse ((objective,false,boundaryCode),0,1,2) = 15
#guard EncodedJournalBoundary.reverse ((tieObjective,false,boundaryCode),0,1,2) = 10
#guard EncodedJournalBoundary.both ((objective,false,boundaryCode),1,1,2) = 2
#guard EncodedJournalSubsets.openBlock ((objective,false,boundaryCode),2,2) = [3]
#guard EncodedJournalSubsets.step ((objective,false,boundaryCode),[0,0,1],2) = [3]
#guard EncodedJournalSubsets.close ((objective,false,boundaryCode),[0,1,0],0) = [2,3]
#guard EncodedJournalSubsets.reverse ((objective,false,boundaryCode),[0,1],1) = [15]
#guard EncodedJournalSubsets.chainStep ((objective,true,false,boundaryCode),[0,4],2) = [3,7]
#guard EncodedJournalSubsets.chainStep ((objective,true,true,boundaryCode),[0,4],1) = [15]
#guard EncodedJournalSubsets.chainClose ((objective,true,boundaryCode),[0,1,4],0) = [2,3]
#guard EncodedJournalSubsets.reverse ((objective,true,boundaryCode),[],2) = []
#guard EncodedJournalSubsets.chainStep ((objective,false,false,boundaryCode),[],2) = []

example : Primrec EncodedJournalSubsets.chainStep := EncodedJournalSubsets.chainStep_primrec
example : Primrec EncodedJournalSubsets.reverse := EncodedJournalSubsets.reverse_primrec
example (d : EncodedRoundObjectives.Data) :
    NoDirectJournal.Realizable (EncodedRoundObjectives.automaton d) ↔
      ∃ tree, (EncodedJournalAssembly.compile (EncodedReversalForgiving.compile d)).toRunAutomaton.acceptsTree tree :=
  EncodedJournalAssembly.realizable_iff_nonempty d

#guard FiniteCodeNumbering.unique ([1,2,1,3,2] : List Nat) = [1,3,2]
#guard FiniteCodeNumbering.name ([1,2,1,3,2] : List Nat) 2 = 2
#guard EncodedThreadNumbering.codes (2,[1,1]) = [(0,none),(0,some 1),(1,none),(1,some 1)]
#guard (EncodedThreadNumbering.compile (2,0,[1,1],[[(0,1),(1,1)]])).1 = 4
#guard (EncodedThreadNumbering.compile (2,0,[1,1],[[(0,1),(1,1)]])).2.1 = 0
#guard (EncodedThreadNumbering.compile (2,0,[1,1],[[(0,1),(1,1)]])).2.2.1 = [1,1,3,3]
#guard EncodedThreadStream.size (1,0,[]) = 1025
#guard EncodedThreadStream.next ((1,0,[]),[],0) = 0
#guard EncodedThreadStream.priority (1,0,[]) 0 = 2
#guard EncodedParityTables.priorities (EncodedParityOperations.complement (1,0,[],[])) = [1,1]

def reversing : EncodedRoundObjectives.Data := (singletonInstance,(1,0,[1,2],[[1,1],[0,1],[0,0]]))
#guard EncodedReversalForgiving.initial reversing = 1
#guard EncodedRoundObjectives.stateCount (EncodedReversalForgiving.compile reversing) = 9
#guard EncodedReversalForgiving.next (reversing,1,(0,0,0,0,0)) = 6
#guard EncodedReversalForgiving.next (reversing,6,(0,0,1,0,0)) = 0
#guard EncodedReversalForgiving.next (reversing,6,(0,0,0,0,0)) = 6
#guard EncodedReversalForgiving.next (reversing,6,(0,0,2,0,0)) = 4
#guard EncodedReversalForgiving.next (reversing,4,(0,0,1,0,0)) = 3
#guard EncodedReversalForgiving.next (reversing,3,(0,0,0,0,0)) = 0
#guard EncodedReversalForgiving.next (reversing,0,(0,0,2,0,0)) = 0
#guard EncodedReversalForgiving.priority reversing 0 = 0
#guard EncodedReversalForgiving.priority reversing 6 = 2

def chainCode : EncodedJournalLabels.Code := List.replicate 8 [] ++ List.replicate 8 (List.range 96)
#guard EncodedChainThreads.chainCount objective = 16
#guard EncodedChainThreads.next ((objective,true,false,chainCode),3,1,2) = 3
#guard EncodedChainThreads.next ((objective,true,true,chainCode),3,1,2) = 15
#guard EncodedChainThreads.next ((objective,false,false,chainCode),3,1,2) = 15
#guard EncodedChainThreads.next ((objective,false,true,chainCode),3,1,2) = 3
#guard EncodedChainMonitor.next (((objective,[3]),(true,false,chainCode,2)),0,(1,0,3)) = 5
#guard EncodedChainMonitor.next (((objective,[3]),(true,false,chainCode,2)),0,(1,0,0)) = 1
#guard EncodedChainMonitor.next (((objective,[3]),(true,false,chainCode,2)),5,(1,0,0)) = 5
#guard EncodedChainMonitor.next (((objective,[3]),(true,true,chainCode,1)),5,(0,2,0)) = 17
#guard EncodedChainMonitor.next (((objective,[3]),(true,true,chainCode,1)),1,(0,2,3)) = 1
#guard EncodedChainMonitor.priority objective 0 = 0
#guard EncodedChainMonitor.priority objective 1 = 0
#guard EncodedChainMonitor.priority objective 5 = 1
#guard (EncodedChainMonitor.receivers objective).length = 96
#guard (EncodedChainMonitor.edges ((objective,[3]),(true,false,chainCode,2))).length = 1728

example : Primrec EncodedReversalForgiving.compile := EncodedReversalForgiving.compile_primrec
example : Primrec EncodedThreadCompiler.compile := EncodedThreadCompiler.compile_primrec
example : Primrec EncodedThreadStream.next := EncodedThreadStream.next_primrec
example : Primrec EncodedChainCompiler.compile := EncodedChainCompiler.compile_primrec
example (d : EncodedRoundObjectives.Data) (w : OmegaWord (EncodedRoundObjectives.Letter d)) :
    (EncodedRoundObjectives.automaton (EncodedReversalForgiving.compile d)).Accepts w ↔
      (EncodedRoundObjectives.automaton d).reversalForgiving.Accepts w := EncodedReversalForgiving.accepts_iff d w
end DistributedSynthesis.Tests.EncodedThreadPipeline
