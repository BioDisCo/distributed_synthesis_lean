/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.Views
import Mathlib.Logic.Equiv.Sum

/-! Computable equality for the existing perfect-recall view type.
The instances are opt-in; no new view or input-tag representation is defined. -/
namespace DistributedSynthesis.DecidableViews

scoped instance inputTagDecidableEq {I J : Type} [DecidableEq I] [DecidableEq J] : DecidableEq (PSum I J) :=
  fun a b => decidable_of_iff ((Equiv.psumEquivSum I J) a = (Equiv.psumEquivSum I J) b)
    (Equiv.psumEquivSum I J).injective.eq_iff

deriving instance DecidableEq for View

attribute [-instance] instDecidableEqView
attribute [scoped instance] instDecidableEqView

end DistributedSynthesis.DecidableViews
