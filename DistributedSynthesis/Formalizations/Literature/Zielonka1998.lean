/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmZielonkaCountableParity

/-!
# Zielonka (1998): positional determinacy of parity games

**Source.**  W. Zielonka, *Infinite Games on Finitely Coloured Graphs with
Applications to Automata on Infinite Trees*, Theoretical Computer Science
200(1-2), 1998 (`zielonka1998infinite`); positional determinacy also due to
Emerson--Jutla (FOCS 1991) and Mostowski (1991).

**Statement.**  In every parity game with finitely many priorities, each
position is won positionally by one of the two players.

**Status: PROVEN.**  Machine-checked in this development
(`ThmZielonkaCountableParity.lean`) for countable arenas with finite
priority range; this file only re-exports it under its literature name.
-/

namespace DistributedSynthesis

namespace Literature

namespace Zielonka

universe u

/-- Positional determinacy of countable parity games with finitely many
priorities.  Re-export of the checked `positionalGameDetermined`. -/
theorem positional_determinacy (G : CountableParityGame.{u}) :
    G.PositionalGameDeterminedStatement :=
  G.positionalGameDetermined

end Zielonka

end Literature

end DistributedSynthesis
