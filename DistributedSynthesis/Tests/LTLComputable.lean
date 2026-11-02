/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.LTLComputable

namespace DistributedSynthesis.Tests.LTLComputable

def interp (atom letter : Bool) : Prop := atom = letter
def interpDecidable (atom letter : Bool) : Decidable (interp atom letter) :=
  inferInstanceAs (Decidable (atom = letter))

def step := DistributedSynthesis.LTLComputable.step interp interpDecidable
def pos : PositiveLTL Bool := .lit ⟨true, true⟩
def neg : PositiveLTL Bool := .lit ⟨false, true⟩

#guard step true .verum = .verum
#guard step true .falsum = .falsum
#guard step true pos = .verum
#guard step false pos = .falsum
#guard step true neg = .falsum
#guard step false neg = .verum
#guard step false (.next pos) = .atom pos
#guard step true (.conj pos neg) = .conj .verum .falsum
#guard step false (.disj pos neg) = .disj .falsum .verum
#guard step true (.until pos neg) =
  .disj .falsum (.conj .verum (.atom (.until pos neg)))
#guard step false (.release pos neg) =
  .conj .verum (.disj .falsum (.atom (.release pos neg)))

def count (root : PositiveLTL Bool) : Nat :=
  letI := DistributedSynthesis.LTLComputable.subformulaFintype root
  Fintype.card root.Subformula

#guard count (.conj pos pos) = 2
#guard count (.until pos neg) = 3

/-- Build and check a transition into the finite subformula carrier. -/
def transitionAtoms : List (PositiveLTL Bool) :=
  let root := PositiveLTL.until pos neg
  let A := DistributedSynthesis.LTLComputable.apa interp interpDecidable root
  ((A.step A.initial false).atoms.map Subtype.val)

#guard transitionAtoms = [.until pos neg]

/-- Ordinary executable client; the enormous determinized carrier is not enumerated here. -/
def compile (φ : LTL Bool) : DetParityAutomaton Bool :=
  DistributedSynthesis.LTLComputable.compile interp interpDecidable φ

example (φ : LTL Bool) (word : OmegaWord Bool) :
    (compile φ).Accepts word ↔ LTL.Satisfies interp word φ :=
  DistributedSynthesis.LTLComputable.correct interp interpDecidable φ word

end DistributedSynthesis.Tests.LTLComputable
