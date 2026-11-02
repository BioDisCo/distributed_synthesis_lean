/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmAPASupportNormalForm
import DistributedSynthesis.Formalizations.Theorem.ThmDPAEmptiness

/-!
# Emptiness of alternating parity word automata

The concrete rank-monitor/Piterman compiler reduces APA language nonemptiness
to the checked finite-DPA emptiness procedure.
-/

namespace DistributedSynthesis

universe u v

namespace AlternatingParityAutomaton

/-- Nonemptiness of an alternating parity word automaton over a finite alphabet is decidable. -/
noncomputable def languageNonemptyDecidable
    {Alphabet : Type u}
    [Fintype Alphabet]
    (A : AlternatingParityAutomaton.{u, v} Alphabet) :
    Decidable (∃ word : OmegaWord Alphabet, A.Accepts word) := by
  classical
  let D : DetParityAutomaton.{u, v} Alphabet :=
    ((APARunToDPACompiler.rankMonitorPiterman Alphabet).compile A).dpa
  letI : Decidable (∃ word : OmegaWord Alphabet, D.Accepts word) :=
    D.languageNonemptyDecidable
  exact
    decidable_of_iff
      (∃ word : OmegaWord Alphabet, D.Accepts word)
      (by
        constructor
        · rintro ⟨word, hword⟩
          exact
            ⟨word,
              (APARunToDPACompiler.rankMonitorPiterman_correct A word).mp hword⟩
        · rintro ⟨word, hword⟩
          exact
            ⟨word,
              (APARunToDPACompiler.rankMonitorPiterman_correct A word).mpr hword⟩)

end AlternatingParityAutomaton

end DistributedSynthesis
