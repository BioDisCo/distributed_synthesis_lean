/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmPitermanDeterminization

/-! # Piterman determinization
Public access to the compact-Safra construction and
`DistributedSynthesis.NondetBuchiAutomaton.Piterman.CompactTreeData.toDPACompiler`.
The implementation depends on the generic compiler interfaces, not the
mixed automata/synthesis backend. Its transitive project imports
are checked by scripts/check_library.py.
The unrestricted semantic compiler remains noncomputable. For executable
certified compilation with supplied transition and acceptance deciders, import
`DistributedSynthesis.Library.Automata.PitermanComputable` and use `Piterman.Computable.compilation`. -/
