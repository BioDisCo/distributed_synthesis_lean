/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Lemma.LemEndpointwindowpreimage

/-!
# No geometric shift into the interior
-/

namespace DistributedSynthesis

universe u v

/--
Corollary `cor:nogeometricshift`: in a concrete three-edge expansion,
successor endpoint windows pull back to bounded old endpoint windows.
Thus endpoint tests are not shifted through the interior one old edge at a
time.
-/
theorem no_geometric_shift_into_interior
    {OldEdge : Type u} {NewEdge : Type v}
    (block : OldEdge -> List NewEdge)
    (hlen : ∀ edge, (block edge).length = 3)
    (c : Nat)
    (old₁ old₂ : TypedPath OldEdge)
    (hpref :
      prefixAtMost (endpointPullbackBound c) old₁ =
        prefixAtMost (endpointPullbackBound c) old₂)
    (hsuff :
      suffixAtMost (endpointPullbackBound c) old₁ =
        suffixAtMost (endpointPullbackBound c) old₂) :
    prefixAtMost c (expandPath block old₁) =
        prefixAtMost c (expandPath block old₂) ∧
      suffixAtMost c (expandPath block old₁) =
        suffixAtMost c (expandPath block old₂) :=
  endpoint_windows_pull_back_to_endpoint_windows block hlen old₁ old₂ c hpref hsuff

end DistributedSynthesis
