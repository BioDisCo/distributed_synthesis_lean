/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.GraphAdversaries.Inputs
import Mathlib.Topology.GDelta.Basic

/-! Public model for graph-adversary synthesis. Alphabets and formulas use the
existing numeric encoding; the graph promise does not constrain private inputs.
The aliases are definitionally equal to the proved characterization model. -/
namespace DistributedSynthesis.GraphAdversaries

/-- A finite LTL synthesis instance: positive cardinalities for both private
input alphabets and both output alphabets, a finite truth table for the atomic
propositions, and an encoded LTL formula, possibly containing next. -/
abbrev Instance := EncodedNoDirect.Instance

/-- There are two perfect-recall local strategies satisfying instance `d` for
every pair of private input streams and every graph sequence in `A`. The graph
promise constrains only communication; it imposes no restriction on the inputs. -/
abbrev Realizable (A : Set (Nat → Graph)) (d : Instance) : Prop :=
  Characterisation.WithInputs.Realizable A d

/-- The allowed infinite graph sequences form the language of some finite
deterministic parity automaton over the three communication graphs. -/
abbrev OmegaRegular (A : Set (Nat → Graph)) : Prop := Characterisation.OmegaRegular A

/-- The interval-hole formulation of nowhere denseness of the geometric image.
Every nonempty relatively open region of `[0,1]` contains a nonempty
relatively open region disjoint from the geometric image of `A`. These holes
are defined using graph sequences alone, independently of private inputs. -/
abbrev GeometricHoles (A : Set (Nat → Graph)) : Prop := Characterisation.GeometricHoles A

/-- Map an infinite graph sequence to the point determined by its nested
geometric prefix intervals in `[0,1]`. Different sequences may represent the
same point. -/
noncomputable abbrev geometricMap := Characterisation.geometricMap

/-- The geometric hole condition is exactly Mathlib's nowhere denseness,
in the relative topology on `[0,1]`. -/
theorem geometricHoles_iff_isNowhereDense (A : Set (Nat → Graph)) :
    GeometricHoles A ↔ IsNowhereDense (geometricMap '' A) :=
  Characterisation.geometricHoles_iff A

namespace SingletonInputs
/-- A synthesis instance with singleton input alphabets and finite, nonempty
output alphabets, together with its atomic truth table and encoded formula. -/
abbrev Instance := Characterisation.SynthesisInstance

/-- Realizability by two local strategies against every graph sequence in `A`,
when neither process receives a varying external input. -/
abbrev Realizable (A : Set (Nat → Graph)) (d : Instance) : Prop :=
  Characterisation.Realizable A d
end SingletonInputs

end DistributedSynthesis.GraphAdversaries
