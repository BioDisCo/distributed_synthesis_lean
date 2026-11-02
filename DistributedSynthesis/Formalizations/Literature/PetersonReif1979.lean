/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStaticHierarchySynthesis
import DistributedSynthesis.Formalizations.Theorem.ThmShadowRealizability
import DistributedSynthesis.Formalizations.Literature.ParityGameSolvability

/-!
# Peterson--Reif (1979): belief sufficiency under hierarchical information

**Source.**  G. L. Peterson and J. H. Reif, *Multiple-Person Alternation*,
FOCS 1979; J. H. Reif, *The Complexity of Two-Player Games of Incomplete
Information*, JCSS 29(2), 1984.  The two-versus-nature hierarchical form
used here is the completeness step of Berwanger--Mathew--van den Bogaard,
Acta Informatica 55(8), 2018 (`berwanger2018hierarchical`), Theorem 10.

**Statement** (`BeliefSufficiency G`, the development's concrete
belief-table formulation of the classical projection step): in a finite concurrent game with *static* hierarchical
information, whenever some perfect-recall distributed strategy wins, the
follower can be replaced by a belief-measurable table: there is
`f2 : Belief → Action2` realizable together with a leader strategy.

This formulation is designed for the checked knowledge-arena engine.  It
is not claimed to occur verbatim in Peterson--Reif; a literature discharge
must prove the specialization from the cited fixed-hierarchy synthesis
result.  The preferred main endpoint instead imports Berwanger Theorem 10
at its published, higher-level statement.

**Status: OPEN OPTIONAL CERTIFICATE.**  This is the deep import of the
development's internal engine decomposition.  Everything around it is machine-checked: soundness
(the leader knowledge-arena readback,
`finiteStateRealizable_of_leaderArena_winner`), the leader-side
completeness R2 (`evenWins_of_followerTableRealizable`), decidability
wiring, and the crossing/shadow transports.  Its classical proof is the
tree-automaton projection of the follower strategy.

**Consumption** (what discharging it relieves, re-stated below):
* the static synthesis theorem
  (`static_synthesis_of_beliefSufficiency`), and
* together with the forward shadow transfer, the composed completeness
  certificate of the dynamic engine
  (`shadow_completeness_of_beliefSufficiency`), hence the star-route
  synthesis endpoint's R1′ hypothesis.
-/

namespace DistributedSynthesis

namespace Literature

namespace PetersonReif

universe u

/-- The development's Peterson--Reif-shaped belief-sufficiency interface
for a statically hierarchical finite concurrent game. -/
abbrev BeliefSufficiency (G : FiniteConcurrentGame.{u}) : Prop :=
  G.FollowerBeliefSufficiency

/-- Discharging belief sufficiency (together with a parity-game decision
procedure for the leader arena) proves the static hierarchical synthesis
theorem. -/
theorem static_synthesis_of_beliefSufficiency (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Observation1]
    [Inhabited G.Observation2]
    (hreif : BeliefSufficiency G) (hd : G.LeaderArenaWinDecidable) :
    G.StaticHierarchyFiniteStateSolvable :=
  G.staticHierarchyFiniteStateSolvable_of_followerBeliefSufficiency hreif hd

/-- **The static synthesis theorem from the lower-level interfaces**:
the concrete belief-sufficiency certificate plus a parity solver. -/
theorem static_synthesis_of_beliefSufficiency_and_solver
    (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Observation1]
    [Inhabited G.Observation2]
    (hreif : BeliefSufficiency G) (solver : ParitySolving.Solver.{u}) :
    G.StaticHierarchyFiniteStateSolvable :=
  static_synthesis_of_beliefSufficiency G hreif
    (ParitySolving.leaderArenaWinDecidable_of_solver solver G)

/-- Belief sufficiency at the (statically hierarchical, proven) shadow game,
together with the forward realizability transfer of the shadow
construction, discharges the composed completeness certificate of the
dynamic engine. -/
theorem shadow_completeness_of_beliefSufficiency (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Action2]
    [Inhabited G.Observation1] [Inhabited G.Observation2]
    (hhier : G.DynamicHierarchy)
    (hfwd :
      G.commonSignalCrossingEliminationGame.HistoryRealizable ->
        G.commonSignalShadowGame.HistoryRealizable)
    (hreif : BeliefSufficiency G.commonSignalShadowGame) :
    G.ShadowLeaderArenaComplete :=
  G.shadowLeaderArenaComplete_of_forwardTransfer_and_reif hhier hfwd hreif

end PetersonReif

end Literature

end DistributedSynthesis
