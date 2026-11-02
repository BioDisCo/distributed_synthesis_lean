/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmDynamicHierarchyFiniteState

/-!
# Finite-state synthesis certificates

A finite-memory extraction hypothesis equates history-dependent and
finite-state realizability. Together with a decision procedure for
finite-state realizability, it yields a `FiniteStateSynthesisCertificate`.
Both inputs are explicit hypotheses of the constructions below.
-/

namespace DistributedSynthesis

universe u

namespace FiniteConcurrentGame

variable (G : FiniteConcurrentGame.{u})

/-- **Realizability collapses under a finite-memory extraction.**  Perfect-recall
realizability and finite-state realizability are then equivalent: finite-state
realizers are perfect-recall realizers unconditionally
(`historyRealizable_of_finiteStateRealizable`), and the extraction supplies the
converse. -/
theorem historyRealizable_iff_finiteStateRealizable_of_complete
    (hcomplete : G.HistoryRealizable -> G.FiniteStateRealizable) :
    G.HistoryRealizable ↔ G.FiniteStateRealizable :=
  ⟨hcomplete, G.historyRealizable_of_finiteStateRealizable⟩

/-- Realizability is decidable once a finite-memory extraction is available and
finite-state realizability is decidable: the extraction identifies the two
notions, transporting the decision. -/
def decidableHistoryRealizable_of_complete
    (hcomplete : G.HistoryRealizable -> G.FiniteStateRealizable)
    (hdec : Decidable G.FiniteStateRealizable) :
    Decidable G.HistoryRealizable :=
  decidable_of_iff _
    (G.historyRealizable_iff_finiteStateRealizable_of_complete hcomplete).symm

/-- **The certificate reduces to its two ingredients.**  A finite-memory
extraction together with a decision procedure for finite-state realizability
assembles a `FiniteStateSynthesisCertificate`.  This isolates the remaining
engine work to `complete` and the bounded-memory search. -/
def finiteStateSynthesisCertificate_of_complete
    (hcomplete : G.HistoryRealizable -> G.FiniteStateRealizable)
    (hdec : Decidable G.FiniteStateRealizable) :
    G.FiniteStateSynthesisCertificate where
  complete := hcomplete
  decision := G.decidableHistoryRealizable_of_complete hcomplete hdec

end FiniteConcurrentGame

end DistributedSynthesis
