/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmAutomataBackend

/-!
# The empty coherent history has no last round

The canonical coherent configuration carrier contains the empty history.
Consequently, not every coherent configuration admits an append decomposition.
-/

namespace DistributedSynthesis

universe u v w a b

/--
The append-decomposition field cannot be required from the whole coherent
configuration carrier.  With the canonical history-derived containment order,
the empty history itself is coherent, but no empty list is an appended history.

-/
theorem not_all_canonical_coherent_histories_append
    {In₁ : Type u}
    {In₂ : Type v}
    {Out₁ : Type w}
    {Out₂ : Type a}
    {AState : Type b}
    (automatonOfHistory :
      History In₁ In₂ Graph Out₁ Out₂ -> AState) :
    ¬
      (∀ c :
        CoherentContinuationConfiguration
          (fun _ : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState =>
            historyCurrentContainmentOrder
              (History.empty : History In₁ In₂ Graph Out₁ Out₂))
          historyCurrentContainmentOrder automatonOfHistory,
        ∃ (pref : History In₁ In₂ Graph Out₁ Out₂),
          ∃ (r : RoundRecord In₁ In₂ Graph Out₁ Out₂),
            c.1.history = History.append pref r) := by
  intro hall
  let c : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState :=
    { history := History.empty
      automatonState := automatonOfHistory History.empty
      receiptOne :=
        (currentView Proc.one
          (History.empty : History In₁ In₂ Graph Out₁ Out₂)).receiptTag
      receiptTwo :=
        (currentView Proc.two
          (History.empty : History In₁ In₂ Graph Out₁ Out₂)).receiptTag }
  have hcoh :
      ContinuationConfigurationAContinuationDataCoherent
        (fun _ : ContinuationConfiguration In₁ In₂ Out₁ Out₂ AState =>
          historyCurrentContainmentOrder
            (History.empty : History In₁ In₂ Graph Out₁ Out₂))
        historyCurrentContainmentOrder automatonOfHistory c := by
    simp [ContinuationConfigurationAContinuationDataCoherent,
      ContinuationConfigurationReceiptOrderCoherent, c]
  rcases hall ⟨c, hcoh⟩ with ⟨pref, r, happend⟩
  simp [c, History.empty, History.append] at happend


end DistributedSynthesis
