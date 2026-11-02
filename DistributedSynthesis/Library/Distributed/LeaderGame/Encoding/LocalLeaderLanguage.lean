/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderMoves

/-! Local leader synthesis depends on the physical play language. The
monitor state used in a follower's response table may therefore change
when the objective is compiled. The proof passes through actual receiver
and leader strategies and reuses the existing narrowing construction. -/
namespace Characterisation
open DistributedSynthesis

section
variable {RIn SIn ROut SOut : Type}
variable [Fintype RIn] [Fintype SIn] [Fintype ROut] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn]
variable [Inhabited RIn] [Inhabited SIn] [Inhabited ROut]
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut) [DecidableEq M.State]

theorem leaderThreadTest_iff_strategies : leaderThreadTest M = true ↔
    ∃ (receiver : ReceiverBlockStrategy RIn SIn ROut) (leader : SenderBlockStrategy SIn SOut),
      ∀ env, M.WinsPlay (pairPlay receiver leader env) := by
  rw [leaderThreadTest_correct]
  constructor
  · rintro ⟨table,winning⟩
    let tree := narrowedInducedTree M table
    refine ⟨receiverOfTree tree,senderOfTree tree,?_⟩
    intro env
    rw [pairPlay,treeOfPair_ofTree (senderOblivious_narrowedInducedTree M table)]
    exact (M.lift_winningTree_iff tree).mp
      (narrowedInducedTree_winningTree_of_allThreadsWin M winning) env
  · rintro ⟨receiver,leader,winning⟩
    let family := fun _ : Unit => M
    let table := finiteRootFamilyTable family (fun _ => receiver) leader (fun _ => winning)
    exact ⟨(finiteRootMemberController family table.toTransitionRationalTree ()).labeledTree,
      finiteRootMemberController_allThreadsWin family _
        (finiteRootFamilyTable_wins family (fun _ => receiver) leader (fun _ => winning)) ()⟩

variable (N : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut) [DecidableEq N.State]

/-- No correspondence between the two monitor state spaces is required.
Both tests quantify over the same physical strategies and input streams. -/
theorem leaderThreadTest_language_congr
    (same : ∀ play, M.WinsPlay play ↔ N.WinsPlay play) :
    leaderThreadTest M = leaderThreadTest N := by
  apply Bool.eq_iff_iff.mpr
  rw [leaderThreadTest_iff_strategies,leaderThreadTest_iff_strategies]
  apply exists_congr
  intro receiver
  apply exists_congr
  intro leader
  exact forall_congr' (fun env => same (pairPlay receiver leader env))

end
end Characterisation
