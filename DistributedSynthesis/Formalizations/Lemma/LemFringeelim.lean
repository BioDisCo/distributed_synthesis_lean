/- Project authors: see AUTHORS.md at the repository root. -/

/-!
# Finite-fringe elimination

This file formalizes the strategy-translation and game-semantics core of
`lem:fringeelim` from `paper.tex`.
-/

namespace DistributedSynthesis

universe u v w

/-- Original strategies can depend on the history observations, older fringe values, and the current fringe value. -/
abbrev FringeStrategy (H : Type u) (R : Type v) (Out : Type w) :=
  List H -> List R -> R -> Out

/-- Fringe-free strategies choose a contingent action as a function of the current fringe value. -/
abbrev ContingentStrategy (H : Type u) (R : Type v) (Out : Type w) :=
  List H -> R -> Out

/-- Replace direct fringe dependence by contingent action selection. -/
def contingentify
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : FringeStrategy H R Out) :
    ContingentStrategy H R Out :=
  fun history currentFringe => σ history (recoverPast history) currentFringe

/-- Realize a contingent strategy back as an original strategy. -/
def realizeContingent
    {H : Type u} {R : Type v} {Out : Type w}
    (σ : ContingentStrategy H R Out) :
    FringeStrategy H R Out :=
  fun history _pastFringe currentFringe => σ history currentFringe

@[simp]
theorem contingentify_apply
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : FringeStrategy H R Out)
    (history : List H) (currentFringe : R) :
    contingentify recoverPast σ history currentFringe =
      σ history (recoverPast history) currentFringe := rfl

@[simp]
theorem realizeContingent_apply
    {H : Type u} {R : Type v} {Out : Type w}
    (σ : ContingentStrategy H R Out)
    (history : List H) (pastFringe : List R) (currentFringe : R) :
    realizeContingent σ history pastFringe currentFringe =
      σ history currentFringe := rfl

/-- Realizing a contingentified strategy preserves the chosen output whenever the older fringe values are recovered from the history. -/
theorem realizeContingent_contingentify_apply
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : FringeStrategy H R Out)
    (history : List H) (pastFringe : List R) (currentFringe : R)
    (hrecover : pastFringe = recoverPast history) :
    realizeContingent (contingentify recoverPast σ) history pastFringe currentFringe =
      σ history pastFringe currentFringe := by
  simp [contingentify, realizeContingent, hrecover]

/-- Contingentification followed by realization is definitionally the same contingent strategy. -/
theorem contingentify_realizeContingent
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : ContingentStrategy H R Out) :
    contingentify recoverPast (realizeContingent σ) = σ := by
  funext history currentFringe
  simp [contingentify, realizeContingent]

/-- Evaluate an original fringe-dependent strategy along a trace of observations. -/
def originalOutputsFrom
    {H : Type u} {R : Type v} {Out : Type w}
    (σ : FringeStrategy H R Out) :
    List H -> List R -> List (H × R) -> List Out
  | _history, _pastFringe, [] => []
  | history, pastFringe, (h, r) :: trace =>
      let newHistory := history ++ [h]
      σ newHistory pastFringe r ::
        originalOutputsFrom σ newHistory (pastFringe ++ [r]) trace

/-- Evaluate a contingent strategy along the same observation trace. -/
def contingentOutputsFrom
    {H : Type u} {R : Type v} {Out : Type w}
    (σ : ContingentStrategy H R Out) :
    List H -> List (H × R) -> List Out
  | _history, [] => []
  | history, (h, r) :: trace =>
      let newHistory := history ++ [h]
      σ newHistory r :: contingentOutputsFrom σ newHistory trace

/--
`recoverPast` is coherent along a trace if at each step it recovers exactly the
older fringe values from the accumulated history.
-/
def RecoveredBy
    {H : Type u} {R : Type v}
    (recoverPast : List H -> List R) :
    List H -> List R -> List (H × R) -> Prop
  | _history, _pastFringe, [] => True
  | history, pastFringe, (h, r) :: trace =>
      recoverPast (history ++ [h]) = pastFringe ∧
        RecoveredBy recoverPast (history ++ [h]) (pastFringe ++ [r]) trace

/--
Along any trace on which older fringe values are recoverable from the history,
contingentification preserves the round-by-round chosen outputs.
-/
theorem originalOutputs_eq_contingentOutputs
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : FringeStrategy H R Out)
    (history : List H) (pastFringe : List R) (trace : List (H × R))
    (hrecovered : RecoveredBy recoverPast history pastFringe trace) :
    originalOutputsFrom σ history pastFringe trace =
      contingentOutputsFrom (contingentify recoverPast σ) history trace := by
  induction trace generalizing history pastFringe with
  | nil =>
      simp [originalOutputsFrom, contingentOutputsFrom]
  | cons hr trace ih =>
      rcases hr with ⟨h, r⟩
      rcases hrecovered with ⟨hhead, htail⟩
      simp [originalOutputsFrom, contingentOutputsFrom, contingentify, hhead]
      exact ih (history := history ++ [h]) (pastFringe := pastFringe ++ [r]) htail

/-- Top-level version of output preservation starting from the empty play prefix. -/
theorem originalOutputs_eq_contingentOutputs_empty
    {H : Type u} {R : Type v} {Out : Type w}
    (recoverPast : List H -> List R)
    (σ : FringeStrategy H R Out)
    (trace : List (H × R))
    (hrecovered : RecoveredBy recoverPast [] [] trace) :
    originalOutputsFrom σ [] [] trace =
      contingentOutputsFrom (contingentify recoverPast σ) [] trace :=
  originalOutputs_eq_contingentOutputs recoverPast σ [] [] trace hrecovered

universe u₁ u₂ v₁ v₂ w₁ w₂

/-- Paired original strategies for the two processes. -/
structure FringeStrategyPair
    (H₁ : Type u₁) (H₂ : Type u₂)
    (R₁ : Type v₁) (R₂ : Type v₂)
    (Out₁ : Type w₁) (Out₂ : Type w₂) where
  one : FringeStrategy H₁ R₁ Out₁
  two : FringeStrategy H₂ R₂ Out₂

/-- Paired contingent strategies for the fringe-free transformed game. -/
structure ContingentStrategyPair
    (H₁ : Type u₁) (H₂ : Type u₂)
    (R₁ : Type v₁) (R₂ : Type v₂)
    (Out₁ : Type w₁) (Out₂ : Type w₂) where
  one : ContingentStrategy H₁ R₁ Out₁
  two : ContingentStrategy H₂ R₂ Out₂

/-- One finite play observation step for both processes. -/
structure FringeObservationStep
    (H₁ : Type u₁) (H₂ : Type u₂)
    (R₁ : Type v₁) (R₂ : Type v₂) where
  historyOne : H₁
  historyTwo : H₂
  fringeOne : R₁
  fringeTwo : R₂

/-- Contingentify both components of a paired strategy. -/
def contingentifyPair
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) :
    ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂ :=
  {
    one := contingentify recoverOne σ.one
    two := contingentify recoverTwo σ.two
  }

/-- Realize both components of a paired contingent strategy. -/
def realizeContingentPair
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) :
    FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂ :=
  {
    one := realizeContingent σ.one
    two := realizeContingent σ.two
  }

/-- Evaluate paired original strategies along a finite observation trace. -/
def originalPairOutputsFrom
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) :
    List H₁ -> List H₂ -> List R₁ -> List R₂ ->
      List (FringeObservationStep H₁ H₂ R₁ R₂) -> List (Out₁ × Out₂)
  | _histOne, _histTwo, _pastOne, _pastTwo, [] => []
  | histOne, histTwo, pastOne, pastTwo, step :: trace =>
      let newHistOne := histOne ++ [step.historyOne]
      let newHistTwo := histTwo ++ [step.historyTwo]
      let outputOne := σ.one newHistOne pastOne step.fringeOne
      let outputTwo := σ.two newHistTwo pastTwo step.fringeTwo
      (outputOne, outputTwo) ::
        originalPairOutputsFrom σ
          newHistOne newHistTwo
          (pastOne ++ [step.fringeOne]) (pastTwo ++ [step.fringeTwo])
          trace

/-- Evaluate paired contingent strategies along the same finite observation trace. -/
def contingentPairOutputsFrom
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) :
    List H₁ -> List H₂ ->
      List (FringeObservationStep H₁ H₂ R₁ R₂) -> List (Out₁ × Out₂)
  | _histOne, _histTwo, [] => []
  | histOne, histTwo, step :: trace =>
      let newHistOne := histOne ++ [step.historyOne]
      let newHistTwo := histTwo ++ [step.historyTwo]
      let outputOne := σ.one newHistOne step.fringeOne
      let outputTwo := σ.two newHistTwo step.fringeTwo
      (outputOne, outputTwo) ::
        contingentPairOutputsFrom σ newHistOne newHistTwo trace

/-- Both players' older fringe values are recoverable along a paired trace. -/
def PairRecoveredBy
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂) :
    List H₁ -> List H₂ -> List R₁ -> List R₂ ->
      List (FringeObservationStep H₁ H₂ R₁ R₂) -> Prop
  | _histOne, _histTwo, _pastOne, _pastTwo, [] => True
  | histOne, histTwo, pastOne, pastTwo, step :: trace =>
      recoverOne (histOne ++ [step.historyOne]) = pastOne ∧
      recoverTwo (histTwo ++ [step.historyTwo]) = pastTwo ∧
        PairRecoveredBy recoverOne recoverTwo
          (histOne ++ [step.historyOne]) (histTwo ++ [step.historyTwo])
          (pastOne ++ [step.fringeOne]) (pastTwo ++ [step.fringeTwo])
          trace

/--
Along every paired trace where older fringe values are recoverable, paired
contingentification preserves the output word.
-/
theorem originalPairOutputs_eq_contingentPairOutputs
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (histOne : List H₁) (histTwo : List H₂)
    (pastOne : List R₁) (pastTwo : List R₂)
    (trace : List (FringeObservationStep H₁ H₂ R₁ R₂))
    (hrecovered :
      PairRecoveredBy recoverOne recoverTwo histOne histTwo pastOne pastTwo trace) :
    originalPairOutputsFrom σ histOne histTwo pastOne pastTwo trace =
      contingentPairOutputsFrom
        (contingentifyPair recoverOne recoverTwo σ)
        histOne histTwo trace := by
  induction trace generalizing histOne histTwo pastOne pastTwo with
  | nil =>
      simp [originalPairOutputsFrom, contingentPairOutputsFrom]
  | cons step trace ih =>
      rcases hrecovered with ⟨hrecoverOne, hrecoverTwo, htail⟩
      simp [originalPairOutputsFrom, contingentPairOutputsFrom, contingentifyPair,
        contingentify, hrecoverOne, hrecoverTwo]
      exact ih
        (histOne := histOne ++ [step.historyOne])
        (histTwo := histTwo ++ [step.historyTwo])
        (pastOne := pastOne ++ [step.fringeOne])
        (pastTwo := pastTwo ++ [step.fringeTwo])
        htail

/-- Realizing a contingent pair preserves outputs on every trace. -/
theorem originalPairOutputs_realizeContingentPair_eq
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (histOne : List H₁) (histTwo : List H₂)
    (pastOne : List R₁) (pastTwo : List R₂)
    (trace : List (FringeObservationStep H₁ H₂ R₁ R₂)) :
    originalPairOutputsFrom
        (realizeContingentPair σ) histOne histTwo pastOne pastTwo trace =
      contingentPairOutputsFrom σ histOne histTwo trace := by
  induction trace generalizing histOne histTwo pastOne pastTwo with
  | nil =>
      simp [originalPairOutputsFrom, contingentPairOutputsFrom]
  | cons step trace ih =>
      simp [originalPairOutputsFrom, contingentPairOutputsFrom,
        realizeContingentPair, realizeContingent]
      exact ih
        (histOne := histOne ++ [step.historyOne])
        (histTwo := histTwo ++ [step.historyTwo])
        (pastOne := pastOne ++ [step.fringeOne])
        (pastTwo := pastTwo ++ [step.fringeTwo])

/-- A finite-trace winning condition for paired output words. -/
abbrev OutputTraceSpec (Out₁ : Type w₁) (Out₂ : Type w₂) :=
  List (Out₁ × Out₂) -> Prop

/-- Original paired strategies win on all recoverable finite traces. -/
def OriginalWinsRecoverable
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) : Prop :=
  ∀ trace : List (FringeObservationStep H₁ H₂ R₁ R₂),
    PairRecoveredBy recoverOne recoverTwo [] [] [] [] trace ->
      spec (originalPairOutputsFrom σ [] [] [] [] trace)

/-- Transformed paired strategies win on all recoverable finite traces. -/
def ContingentWinsRecoverable
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂) : Prop :=
  ∀ trace : List (FringeObservationStep H₁ H₂ R₁ R₂),
    PairRecoveredBy recoverOne recoverTwo [] [] [] [] trace ->
      spec (contingentPairOutputsFrom σ [] [] trace)

/--
The original-to-transformed direction of finite-fringe elimination: replace
each direct action by a finite contingent action over the current fringe.
-/
theorem fringeElim_original_to_contingent
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (hwins : OriginalWinsRecoverable recoverOne recoverTwo spec σ) :
    ContingentWinsRecoverable recoverOne recoverTwo spec
      (contingentifyPair recoverOne recoverTwo σ) := by
  intro trace hrecovered
  rw [← originalPairOutputs_eq_contingentPairOutputs
    recoverOne recoverTwo σ [] [] [] [] trace hrecovered]
  exact hwins trace hrecovered

/--
The transformed-to-original direction of finite-fringe elimination: evaluate
the contingent action at the current actual fringe.
-/
theorem fringeElim_contingent_to_original
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂)
    (σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂)
    (hwins : ContingentWinsRecoverable recoverOne recoverTwo spec σ) :
    OriginalWinsRecoverable recoverOne recoverTwo spec
      (realizeContingentPair σ) := by
  intro trace hrecovered
  rw [originalPairOutputs_realizeContingentPair_eq σ [] [] [] [] trace]
  exact hwins trace hrecovered

/-- Paper-facing equivalence form of `lem:fringeelim` for recoverable traces. -/
theorem fringeElim_winning_iff
    {H₁ : Type u₁} {H₂ : Type u₂}
    {R₁ : Type v₁} {R₂ : Type v₂}
    {Out₁ : Type w₁} {Out₂ : Type w₂}
    (recoverOne : List H₁ -> List R₁)
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂) :
    (∃ σ : FringeStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂,
      OriginalWinsRecoverable recoverOne recoverTwo spec σ) ↔
    (∃ σ : ContingentStrategyPair H₁ H₂ R₁ R₂ Out₁ Out₂,
      ContingentWinsRecoverable recoverOne recoverTwo spec σ) := by
  constructor
  · rintro ⟨σ, hwins⟩
    exact ⟨contingentifyPair recoverOne recoverTwo σ,
      fringeElim_original_to_contingent recoverOne recoverTwo spec σ hwins⟩
  · rintro ⟨σ, hwins⟩
    exact ⟨realizeContingentPair σ,
      fringeElim_contingent_to_original recoverOne recoverTwo spec σ hwins⟩

end DistributedSynthesis
