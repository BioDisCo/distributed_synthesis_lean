/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmStaticHierarchySynthesis

/-!
# McNaughton (1993), Emerson--Jutla (1991): solving finite parity games

**Source.**  R. McNaughton, *Infinite Games Played on Finite Graphs*, APAL
65(2), 1993; E. A. Emerson and C. S. Jutla, *Tree Automata, Mu-Calculus and
Determinacy*, FOCS 1991; algorithmic form also in Zielonka
(`zielonka1998infinite`).

**Statement** (`Solver`): for every parity game on a finite arena with a
decidable edge relation, membership of a position in Even's positional
winning region is decidable.

**Status: OPEN CERTIFICATE (must be discharged constructively).**  A
classical instance (`Classical.propDecidable`) type-checks but would void
the algorithmic content of every `Decidable` endpoint of the development;
a discharge must construct the decision procedure (Zielonka recursion, or
positional-strategy enumeration with cycle analysis).  Positional
determinacy itself is already machine-checked
(`Literature.Zielonka.positional_determinacy`).

**Consumption.**  A solver decides the leader knowledge arenas of the
static engine (`leaderArenaWinDecidable_of_solver`), discharging the
`LeaderArenaWinDecidable` hypotheses of the static synthesis theorem, the
dynamic engine, and the star-route synthesis endpoint.
-/

namespace DistributedSynthesis

namespace Literature

namespace ParitySolving

universe u

/-- A decision procedure for Even's positional winning region on finite
parity arenas with decidable edges. -/
abbrev Solver : Type (u + 1) :=
  ∀ (game : CountableParityGame.{u}) [Fintype game.Position]
    [DecidableRel game.step] (position : game.Position),
    Decidable (position ∈ game.PositionalWinningRegion ParityPlayer.even)

/-- Noncomputable logical wiring from a parity solver to the static
engine's leader knowledge arenas.  The position space is finite
structurally.  The edge relation is currently handed to the solver through
`Classical.propDecidable`; consequently this definition is suitable for
relative theorem composition, but it is not an executable implementation of
leader-arena solving.  Constructive extraction requires an explicit
decidable implementation of the arena edge relation. -/
@[reducible]
noncomputable def leaderArenaWinDecidable_of_solver
    (solver : Solver.{u}) (G : FiniteConcurrentGame.{u})
    [Inhabited G.Action1] [Inhabited G.Observation1]
    [Inhabited G.Observation2] :
    G.LeaderArenaWinDecidable := fun f2 =>
  letI : DecidableEq G.State := Classical.decEq _
  letI : Fintype (G.leaderArena f2).Position :=
    (inferInstance : Fintype (G.LeaderArenaPos f2))
  letI : DecidableRel (G.leaderArena f2).step :=
    fun _ _ => Classical.propDecidable _
  solver (G.leaderArena f2) (G.leaderArenaInitial f2)

end ParitySolving

end Literature

end DistributedSynthesis
