/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenPointedRealization

/-!
# Literal representatives for injective semantic root families

Canonical finite view classes normally choose an arbitrary semantic history
for every finite root.  If the input family contains the same root more than
once, that choice can silently switch between distinct literal histories.

After root deduplication the root map is injective.  The lemmas below record
the exact consequence needed by the indexed unfolding: at every surviving
index, the canonical realization's chosen entry and minimum are literally
the entry and minimum at that index.  Thus deduplication does not merely
preserve the finite root set; it removes the representative-splicing gap.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited I] [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Right semantic families -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRightSemanticSourceEntry_eq_of_root_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hrootInjective : Function.Injective fun index =>
      profiledOpenRightRootOfWinning A strategy hwin (entry index)
        (minimum index) basis)
    (index : I)
    (hmem : profiledOpenRightRootOfWinning A strategy hwin (entry index)
        (minimum index) basis ∈
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1) :
    profiledOpenRightSemanticSourceEntry A strategy hwin entry minimum pivot
        hview basis ⟨_, hmem⟩ = entry index := by
  unfold profiledOpenRightSemanticSourceEntry
  apply congrArg entry
  apply hrootInjective
  exact profiledOpenRightRootRepresentative_spec A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) ⟨_, hmem⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenRightSemanticSourceMinimum_eq_of_root_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcOnePairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.one (entry index).leftHistory =
        currentView Proc.one (entry pivot).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hrootInjective : Function.Injective fun index =>
      profiledOpenRightRootOfWinning A strategy hwin (entry index)
        (minimum index) basis)
    (index : I)
    (hmem : profiledOpenRightRootOfWinning A strategy hwin (entry index)
        (minimum index) basis ∈
      (profiledOpenRightSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1) :
    profiledOpenRightSemanticSourceMinimum A strategy hwin entry minimum
        pivot hview basis ⟨_, hmem⟩ = minimum index := by
  unfold profiledOpenRightSemanticSourceMinimum
  apply congrArg minimum
  apply hrootInjective
  exact profiledOpenRightRootRepresentative_spec A
    (fun index => profiledOpenRightRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) ⟨_, hmem⟩

/-! ## Left semantic families -/

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticSourceEntry_eq_of_root_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hrootInjective : Function.Injective fun index =>
      profiledOpenLeftRootOfWinning A strategy hwin (entry index)
        (minimum index) basis)
    (index : I)
    (hmem : profiledOpenLeftRootOfWinning A strategy hwin (entry index)
        (minimum index) basis ∈
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1) :
    profiledOpenLeftSemanticSourceEntry A strategy hwin entry minimum pivot
        hview basis ⟨_, hmem⟩ = entry index := by
  unfold profiledOpenLeftSemanticSourceEntry
  apply congrArg entry
  apply hrootInjective
  exact profiledOpenLeftRootRepresentative_spec A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) ⟨_, hmem⟩

omit [Inhabited Out₁] [Inhabited Out₂] in
theorem profiledOpenLeftSemanticSourceMinimum_eq_of_root_injective
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : I → ProcTwoPairedEntryRep strategy)
    (minimum : I → A.State) (pivot : I)
    (hview : ∀ index,
      currentView Proc.two (entry index).rightHistory =
        currentView Proc.two (entry pivot).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis)
    (hrootInjective : Function.Injective fun index =>
      profiledOpenLeftRootOfWinning A strategy hwin (entry index)
        (minimum index) basis)
    (index : I)
    (hmem : profiledOpenLeftRootOfWinning A strategy hwin (entry index)
        (minimum index) basis ∈
      (profiledOpenLeftSemanticSourceClass A strategy hwin entry minimum
        pivot hview basis).1) :
    profiledOpenLeftSemanticSourceMinimum A strategy hwin entry minimum pivot
        hview basis ⟨_, hmem⟩ = minimum index := by
  unfold profiledOpenLeftSemanticSourceMinimum
  apply congrArg minimum
  apply hrootInjective
  exact profiledOpenLeftRootRepresentative_spec A
    (fun index => profiledOpenLeftRootOfWinning A strategy hwin
      (entry index) (minimum index) basis) ⟨_, hmem⟩

end

end DetParityAutomaton

end DistributedSynthesis
