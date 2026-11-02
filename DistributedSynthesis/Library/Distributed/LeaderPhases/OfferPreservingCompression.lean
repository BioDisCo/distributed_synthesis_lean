/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.NarrowedPhaseOffers

/-! Restrict joint offers before narrowing, using the existing finite-memory
guard. The resulting finite controller retains physical acceptance, including
infinite phases, and its exact offers stay inside the prescribed finite set.
Constructing the model-specific collector is a separate obligation. -/
namespace Characterisation
open DistributedSynthesis

section
variable {RIn SIn ROut Extra SOut Memory Outcome : Type}
variable [Fintype Memory] [DecidableEq Outcome]
variable (M : BlockRecordMonitor.{0,0,0,0,0} RIn SIn ROut SOut)
variable (project : Extra → ROut) (initial : Memory)
variable (next : Memory → RealizedBlockRound RIn SIn Extra SOut → Memory)
variable (collect : Memory → RealizedBlockRound RIn SIn Extra SOut → Finset Outcome)
variable (allowed : Finset Outcome)

def phaseOfferMonitor : BlockRecordMonitor.{0,0,0,0,0} RIn SIn Extra SOut :=
  leaderMemoryMonitor M project initial next (fun mem letter => decide (collect mem letter ⊆ allowed))

theorem phaseOfferMonitor_wins_iff (play : Nat → RealizedBlockRound RIn SIn Extra SOut) :
    (phaseOfferMonitor M project initial next collect allowed).WinsPlay play ↔
      M.WinsPlay (phasePhysicalPlay project play) ∧
      ∀ n, collect (phaseMemoryRun initial next play n) (play n) ⊆ allowed := by
  simp only [phaseOfferMonitor, leaderMemoryMonitor_wins_iff, decide_eq_true_eq]

variable [Fintype RIn] [Fintype SIn] [Fintype Extra] [Fintype SOut]
variable [DecidableEq RIn] [DecidableEq SIn] [Inhabited RIn] [Inhabited SIn]

/-- Every offer extracted from a winning guarded table passes the same
joint restriction. An outcome is never justified by different words for
its different entries. -/
theorem phaseOfferMonitor_offers_subset
    (T : TransitionRationalTree.{0,0,0} SIn
      (NarrowedBlockLabel RIn SIn Extra SOut
        (phaseOfferMonitor M project initial next collect allowed).State))
    (wins : NarrowedAllThreadsWin (phaseOfferMonitor M project initial next collect allowed)
      T.labeledTree) :
    narrowedPhaseOffers (phaseOfferMonitor M project initial next collect allowed) T
      (fun q letter => collect q.2.1 letter) ⊆ allowed := by
  let G := phaseOfferMonitor M project initial next collect allowed
  let tree := narrowedInducedTree G T.labeledTree
  have winning : ∀ env, G.WinsPlay (treePlay tree env) :=
    (G.lift_winningTree_iff tree).mp (narrowedInducedTree_winningTree_of_allThreadsWin G wins)
  intro outcome offered
  obtain ⟨node, input, present⟩ := (mem_narrowedPhaseOffers_iff G T _ outcome).mp offered
  obtain ⟨env, old, fresh⟩ := rollingBranch_realizes_step node input
  have control : narrowedControl G T.labeledTree node = G.run (treePlay tree env) node.length := by
    have eq := G.lift_control_branchNode tree env node.length
    change G.lift.control (narrowedInducedTree G T.labeledTree) _ = _ at eq
    rw [old, lift_control_narrowedInducedTree] at eq
    exact eq
  have memory := (leaderMemoryMonitor_run M project initial next
    (fun mem letter => decide (collect mem letter ⊆ allowed)) (treePlay tree env) node.length).2
  have letter : treePlay tree env node.length =
      narrowedRecord G (T.labeledTree (senderWord node))
        (narrowedControl G T.labeledTree node) input := by
    simp only [treePlay, tree, narrowedInducedTree, blockLabelApply, old, fresh, narrowedRecord]
  have checks := ((phaseOfferMonitor_wins_iff M project initial next collect allowed _).mp
    (winning env)).2 node.length
  rw [← memory, letter] at checks
  apply checks
  simpa only [control] using present

variable [Inhabited Extra]

/-- A phase that already obeys a finite joint offer restriction has a
finite narrowed implementation obeying that restriction. Its offered set
is computed exactly, and its infinite physical plays still win. -/
theorem finite_phase_preserving_offers
    (receiver : ReceiverBlockStrategy RIn SIn Extra) (leader : SenderBlockStrategy SIn SOut)
    (physical : ∀ env, M.WinsPlay (phasePhysicalPlay project (pairPlay receiver leader env)))
    (restricted : ∀ env n,
      collect (phaseMemoryRun initial next (pairPlay receiver leader env) n)
        (pairPlay receiver leader env n) ⊆ allowed) :
    ∃ table : FiniteRootFamilyTable
        (fun _ : Unit => phaseOfferMonitor M project initial next collect allowed),
      let G := phaseOfferMonitor M project initial next collect allowed
      let T := finiteRootMemberController (fun _ : Unit => G) table.toTransitionRationalTree ()
      NarrowedAllThreadsWin G T.labeledTree ∧
      narrowedPhaseOffers G T (fun q letter => collect q.2.1 letter) ⊆ allowed ∧
      ∀ env, M.WinsPlay (phasePhysicalPlay project
        (treePlay (narrowedInducedTree G T.labeledTree) env)) := by
  obtain ⟨table, wins⟩ := leaderMemory_finite_table M project initial next
    (fun mem letter => decide (collect mem letter ⊆ allowed)) receiver leader physical
    (by simpa only [decide_eq_true_eq] using restricted)
  refine ⟨table, wins, phaseOfferMonitor_offers_subset M project initial next collect allowed _ wins, ?_⟩
  intro env
  apply ((phaseOfferMonitor_wins_iff M project initial next collect allowed _).mp ?_).1
  exact ((phaseOfferMonitor M project initial next collect allowed).lift_winningTree_iff _).mp
    (narrowedInducedTree_winningTree_of_allThreadsWin _ wins) env

end
end Characterisation
