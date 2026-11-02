/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLStates

namespace DistributedSynthesis.Tests.EncodedLTLFrontend
open EncodedPositiveLTL

def p : EncodedFiniteLTL.Code Nat := EncodedFiniteLTL.atom 7
def q : EncodedFiniteLTL.Code Nat := EncodedFiniteLTL.atom 8
def lit (b : Bool) (a : Nat) : PositiveLTL Nat := .lit ⟨b, a⟩

#guard normalize p = quote (lit true 7)
#guard normalize (EncodedFiniteLTL.unary 2 p) = quote (lit false 7)
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.unary 2 p)) = quote (lit true 7)
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.binary 3 p q)) =
  quote (.disj (lit false 7) (lit false 8))
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.binary 4 p q)) =
  quote (.conj (lit false 7) (lit false 8))
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.unary 5 p)) = quote (.next (lit false 7))
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.binary 6 p q)) =
  quote (.release (lit false 7) (lit false 8))
#guard normalize (EncodedFiniteLTL.unary 2 (EncodedFiniteLTL.binary 7 p q)) =
  quote (.until (lit false 7) (lit false 8))
#guard normalize ([] : EncodedFiniteLTL.Code Nat) = EncodedFiniteLTL.falsity
#guard normalize (p ++ q) = EncodedFiniteLTL.falsity
#guard normalize ([.inr 5] : EncodedFiniteLTL.Code Nat) = EncodedFiniteLTL.falsity
#guard normalize ([.inr 5, .inr 2] : EncodedFiniteLTL.Code Nat) = EncodedFiniteLTL.truth

def repeated := EncodedFiniteLTL.binary 3 p p
#guard states repeated = [normalize repeated, normalize p, normalize p]
#guard index repeated (normalize p) = 1
#guard index repeated (normalize q) = 3
#guard (EncodedLTLStates.compile (EncodedFiniteLTL.binary 6 p q)).2 = [1, 4, 4]
#guard (EncodedLTLStates.compile (EncodedFiniteLTL.binary 7 p q)).2 = [0, 4, 4]

example : Primrec (normalize (A := Nat)) := normalize_primrec
example : Primrec (states (A := Nat)) := states_primrec
example : Primrec (EncodedLTLStates.compile (A := Nat)) := EncodedLTLStates.compile_primrec

example (c : EncodedFiniteLTL.Code Nat)
    (s : (PositiveLTL.ofLTL (EncodedFiniteLTL.decode c)).Subformula) :
    (states c)[(number c s).val]? = some (quote s.val) := number_lookup c s

end DistributedSynthesis.Tests.EncodedLTLFrontend
