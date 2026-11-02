/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedOrbitParity

namespace DistributedSynthesis.Tests.EncodedOrbitParity
open DistributedSynthesis.EncodedOrbitParity

#guard FiniteSearch.tables 0 0 = [[]]
#guard FiniteSearch.tables 0 1 = []
#guard FiniteSearch.tables 2 2 = [[0, 0], [0, 1], [1, 0], [1, 1]]
#guard (FiniteSearch.tables 3 4).length = 81

example : Primrec₂ FiniteSearch.tables := FiniteSearch.tables_primrec

example {alphabet size : Nat} (policy : Fin size → Fin alphabet) :
    List.ofFn (fun q => (policy q).val) ∈ FiniteSearch.tables alphabet size :=
  FiniteSearch.ofFn_mem_tables policy

-- Self loops; a missing transition defaults to state zero.
#guard solve (0, [0], [0], 0)
#guard !(solve (0, [0], [1], 0))
#guard solve (0, [], [], 0)
-- A transient priority does not determine infinite-run acceptance.
#guard solve (1, [1, 1], [1, 2], 0)
#guard !(solve (1, [1, 1], [0, 3], 0))
-- Minimum recurring priority, not maximum priority or a reachable transient.
#guard !(solve (1, [1, 0], [2, 1], 0))
#guard solve (1, [1, 0], [2, 3], 0)
-- Unreachable components must not influence the answer.
#guard solve (2, [0, 2, 1], [2, 1, 0], 0)
#guard !(solve (2, [0, 2, 1], [0, 3, 1], 1))
-- A return of length exactly the state count must be included.
#guard solve (2, [1, 2, 0], [4, 2, 3], 0)
-- Malformed successor/initial indices use the documented modulo convention.
#guard solve (1, [99, 99], [1, 2], 98)
#guard !(solve (1, [99, 99], [2, 1], 98))

example : Primrec solve := solve_primrec
example : ComputablePred Accepts := accepts_computable

example {Q : Type*} {n : Nat} (e : Q ≃ Fin (n + 1)) (f : Q → Q)
    (p : Q → Nat) (x : Q) :
    solve (encode e f p x) = true ↔ NatSeqMinEvenParity (fun k => p ((f^[k]) x)) :=
  encode_correct e f p x

def cycle (q : Fin 3) : Fin 3 := ⟨(q.val + 1) % 3, Nat.mod_lt _ (by decide)⟩
def cyclePriority (q : Fin 3) : Nat := if q.val = 1 then 2 else 3

#guard ofFin cycle cyclePriority 0 = (2, [1, 2, 0], [3, 2, 3], 0)
#guard solve (ofFin cycle cyclePriority 0)

end DistributedSynthesis.Tests.EncodedOrbitParity
