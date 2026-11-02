/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.TreeNonemptiness

namespace DistributedSynthesis.Tests.TreeNonemptiness

def constant (p : Nat) : DeterministicBlockMonitor Unit Unit where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step := fun _ _ _ => ()
  priority := fun _ => p

def constantResult (p : Nat) : Bool :=
  @DistributedSynthesis.TreeNonemptiness.nonempty _ _ (constant p) (inferInstanceAs (DecidableEq Unit))

#guard constantResult 0
#guard !constantResult 1
#guard constantResult 2

def controlled : DeterministicBlockMonitor Unit Bool where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Bool
  stateFinite := inferInstance
  initial := false
  step := fun _ label _ => label
  priority := fun q => if q then 0 else 1

def adversarial : DeterministicBlockMonitor Bool Unit where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Bool
  stateFinite := inferInstance
  initial := false
  step := fun _ _ direction => direction
  priority := fun q => if q then 1 else 0

#guard @DistributedSynthesis.TreeNonemptiness.nonempty _ _ controlled (inferInstanceAs (DecidableEq Bool))
#guard !(@DistributedSynthesis.TreeNonemptiness.nonempty _ _ adversarial (inferInstanceAs (DecidableEq Bool)))

def transient (p₀ p₁ : Nat) : DeterministicBlockMonitor Unit Unit where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Bool
  stateFinite := inferInstance
  initial := false
  step := fun _ _ _ => true
  priority := fun q => if q then p₁ else p₀

def transientResult (p₀ p₁ : Nat) : Bool :=
  @DistributedSynthesis.TreeNonemptiness.nonempty _ _ (transient p₀ p₁) (inferInstanceAs (DecidableEq Bool))

#guard transientResult 1 2
#guard !transientResult 0 1

def noBranches : DeterministicBlockMonitor Empty Unit where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step := fun _ _ d => nomatch d
  priority := fun _ => 1

def noLabels : DeterministicBlockMonitor Unit Empty where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Unit
  stateFinite := inferInstance
  initial := ()
  step := fun _ label _ => nomatch label
  priority := fun _ => 0

#guard @DistributedSynthesis.TreeNonemptiness.nonempty _ _ noBranches (inferInstanceAs (DecidableEq Unit))
#guard !(@DistributedSynthesis.TreeNonemptiness.nonempty _ _ noLabels (inferInstanceAs (DecidableEq Unit)))

#guard @decide _ (FiniteOrbitParity.parityDecidable Bool.not false (fun q => if q then 2 else 3))
#guard !(@decide _ (FiniteOrbitParity.parityDecidable Bool.not false (fun q => if q then 2 else 1)))

end DistributedSynthesis.Tests.TreeNonemptiness
