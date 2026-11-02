/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Proposition.PropHandoffsuccessortests

/-!
# Failure of handoff has a finite separating witness
-/

namespace DistributedSynthesis

universe u v w x y z

/--
Lemma `lem:handofffailurewitness`: if the successor tests are not
single-valued, the failure is witnessed by one finite tuple and two realized
different target atoms.
-/
theorem handoff_failure_has_finite_separating_witness
    {EdgeType : Proc -> Type u}
    {Atom : Proc -> Type v}
    {In₁ : Type w} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}
    (tests : HandoffTests EdgeType Atom In₁ In₂ Out₁ Out₂)
    (hfailure : ¬ AtMostOneHandoffSuccessor tests) :
    Nonempty (HandoffSeparatingWitness EdgeType Atom In₁ In₂ Out₁ Out₂ tests) :=
  not_unique_successors_give_witness tests hfailure

end DistributedSynthesis
