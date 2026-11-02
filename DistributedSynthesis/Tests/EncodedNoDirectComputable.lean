/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirectComputable
import DistributedSynthesis.Tests.EncodedJournal

/-! Public clients of the closed numeric synthesis pipeline.
Runtime checks cover small outer transitions; full exhaustive determinized
carriers are intentionally not materialized by these tests.
-/
namespace DistributedSynthesis.Tests.EncodedNoDirectComputable
open EncodedJournal

#guard EncodedJournalTransitions.initial objective = (0,0,[],[])
#guard EncodedJournalTransitions.shift objective = 12
#guard EncodedJournalTransitions.priority objective (0,1,[],[]) = 1
#guard EncodedJournalTransitions.priority objective (1,0,[0],[]) = 14
#guard EncodedJournalTransitions.priority objective (3,0,[0],[0]) = 14
#guard EncodedJournalTransitions.priority objective EncodedJournalTransitions.sink = 12
#guard EncodedJournalTransitions.step (objective,(0,0,[],[]),code,(0,2)) = (0,2,[],[])
#guard EncodedJournalTransitions.step (objective,(0,0,[],[]),code,(0,3)) = EncodedJournalTransitions.sink
#guard EncodedJournalTransitions.step (objective,(1,0,[0,1],[]),code,(0,3)) = (0,3,[],[])
#guard EncodedJournalTransitions.step (objective,(2,0,[0],[]),code,(0,3)) = EncodedJournalTransitions.sink
#guard EncodedJournalTransitions.step (objective,(3,0,[0,1],[4]),code,(0,3)) = (0,3,[],[])
#guard EncodedJournalTransitions.step (objective,(4,0,[],[4]),code,(0,2)) = EncodedJournalTransitions.sink
#guard EncodedJournalTransitions.step (objective,EncodedJournalTransitions.sink,code,(1,2)) = EncodedJournalTransitions.sink
#guard EncodedJournalTransitions.step (objective,EncodedJournalTransitions.sink,code,(2,1)) = EncodedJournalTransitions.sink
#guard EncodedJournalTables.branches objective = [(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(2,0),(2,1)]
#guard EncodedJournalTables.labels singletonObjective = [List.replicate 16 [0]]

example : Primrec EncodedJournalTransitions.step := EncodedJournalTransitions.step_primrec
example : Primrec EncodedJournalTables.compile := EncodedJournalTables.compile_primrec
example : Primrec DistributedSynthesis.EncodedNoDirectComputable.compile := DistributedSynthesis.EncodedNoDirectComputable.compile_primrec
example : Primrec DistributedSynthesis.EncodedNoDirectComputable.solve := DistributedSynthesis.EncodedNoDirectComputable.solve_primrec
example : Primrec EncodedNoDirect.solve := DistributedSynthesis.EncodedNoDirectComputable.original_solve_primrec
example : ComputablePred EncodedNoDirect.Realizable := DistributedSynthesis.EncodedNoDirectComputable.realizable_computable
example (d : EncodedNoDirect.Instance) : DistributedSynthesis.EncodedNoDirectComputable.solve d = true ↔ EncodedNoDirect.Realizable d :=
  DistributedSynthesis.EncodedNoDirectComputable.solve_correct d
end DistributedSynthesis.Tests.EncodedNoDirectComputable
