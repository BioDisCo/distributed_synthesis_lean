/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemDelayedhierarchywinning

/-!
# One-sided (degenerate-blind) fringe elimination

The θ̄-game is *asymmetric*: the informed (receiver) side carries the transient acknowledgement
fringe, recoverable with delay one (`lem:delayonehierarchy`); the blind (sender) side is
`b_old`-invariant (`lem:noorientationconsensus`) and so carries **no fringe to eliminate**.  This
file specializes `fringeElim_winning_iff` to that shape by modelling the blind side's fringe type as
`Unit`.

The key fact (`punitRecover_head`, `pairRecoveredBy_punitLeft_iff`) is that with the blind fringe
degenerate, the blind side's recoverability conjunct of `PairRecoveredBy` holds **automatically**:
a list of `Unit`s is determined by its length, and the canonical blind recoverer returns the
length-matched list.  Consequently fringe elimination needs only the *informed* side to be
recoverable -- the one-sided form the θ̄-game's orientation-dependent hierarchy provides, clearing
the "frozen `b_old` never recovered" wall that blocked the symmetric adapter.
-/

namespace DistributedSynthesis

universe u₁ u₂ v₂ w₁ w₂

variable {H₁ : Type u₁} {H₂ : Type u₂} {R₂ : Type v₂} {Out₁ : Type w₁} {Out₂ : Type w₂}

/-- A list of `Unit`s is its own length's worth of `()`. -/
theorem list_punit_eq_replicate (l : List Unit) :
    l = List.replicate l.length () := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [List.length_cons, List.replicate]
      exact congrArg (a :: ·) ih

/-- The canonical **blind recoverer** for a degenerate (`Unit`) fringe: it returns the settled-past
`Unit` list, read as the length-matched replicate of the history minus its current entry. -/
def punitRecover (h : List H₁) : List Unit :=
  List.replicate (h.length - 1) ()

/-- One-sided recoverability: only the **informed** (side-two) fringe values are recovered along the
trace.  The blind (`Unit`) side is omitted -- it is discharged automatically
(`pairRecoveredBy_punitLeft_iff`). -/
def RecoveredByTwo
    (recoverTwo : List H₂ -> List R₂) :
    List H₂ -> List R₂ ->
      List (FringeObservationStep H₁ H₂ Unit R₂) -> Prop
  | _histTwo, _pastTwo, [] => True
  | histTwo, pastTwo, step :: trace =>
      recoverTwo (histTwo ++ [step.historyTwo]) = pastTwo ∧
        RecoveredByTwo recoverTwo (histTwo ++ [step.historyTwo])
          (pastTwo ++ [step.fringeTwo]) trace

/-- The blind recoverer, evaluated at the *current* history `histOne ++ [x]`, returns exactly the
length-`histOne.length` `Unit` list -- i.e. the accumulated blind past whenever it has that length.
This is the blind side's recoverability, holding by construction for a degenerate fringe. -/
theorem punitRecover_head (histOne : List H₁) (x : H₁) :
    punitRecover (histOne ++ [x]) = List.replicate histOne.length () := by
  simp [punitRecover]

/-- **The blind (`Unit`) recoverability conjunct is automatic.**  Along any trace, whenever the
blind past `pastOne` already has the history's length, `PairRecoveredBy` with the canonical blind
recoverer holds iff the *informed* side's recoverability holds -- the blind conjuncts are discharged
by `punitRecover_head` and `list_punit_eq_replicate`. -/
theorem pairRecoveredBy_punitLeft_iff
    (recoverTwo : List H₂ -> List R₂)
    (histOne : List H₁) (histTwo : List H₂)
    (pastOne : List Unit) (pastTwo : List R₂)
    (hlen : pastOne.length = histOne.length)
    (trace :
      List (FringeObservationStep H₁ H₂ Unit R₂)) :
    PairRecoveredBy punitRecover recoverTwo histOne histTwo pastOne pastTwo trace ↔
      RecoveredByTwo recoverTwo histTwo pastTwo trace := by
  induction trace generalizing histOne histTwo pastOne pastTwo with
  | nil => exact Iff.rfl
  | cons step rest ih =>
      unfold PairRecoveredBy RecoveredByTwo
      have hblind : punitRecover (histOne ++ [step.historyOne]) = pastOne := by
        rw [punitRecover_head, list_punit_eq_replicate pastOne, hlen]
      have hlen' :
          (pastOne ++ [step.fringeOne]).length = (histOne ++ [step.historyOne]).length := by
        simp [hlen]
      rw [ih (histOne ++ [step.historyOne]) (histTwo ++ [step.historyTwo])
        (pastOne ++ [step.fringeOne]) (pastTwo ++ [step.fringeTwo]) hlen']
      constructor
      · rintro ⟨_, hrec2, htail⟩; exact ⟨hrec2, htail⟩
      · rintro ⟨hrec2, htail⟩; exact ⟨hblind, hrec2, htail⟩

/-- **One-sided fringe elimination (degenerate blind side).**  With the blind fringe modelled as
`Unit`, a fringe-dependent strategy pair wins on all informed-recoverable traces iff its
contingentification does -- the blind recoverability is automatic, so only the informed
(`RecoveredByTwo`) side is required.  This is `fringeElim_winning_iff` in the asymmetric,
orientation-dependent form the θ̄-game supplies, with the blind side's frozen `b_old` absorbed by
invariance rather than recovered. -/
theorem fringeElim_winning_iff_punitLeft
    (recoverTwo : List H₂ -> List R₂)
    (spec : OutputTraceSpec Out₁ Out₂) :
    (∃ σ : FringeStrategyPair H₁ H₂ Unit R₂ Out₁ Out₂,
        ∀ trace : List (FringeObservationStep H₁ H₂ Unit R₂),
          RecoveredByTwo recoverTwo [] [] trace ->
            spec (originalPairOutputsFrom σ [] [] [] [] trace)) ↔
      (∃ σ : ContingentStrategyPair H₁ H₂ Unit R₂ Out₁ Out₂,
        ∀ trace : List (FringeObservationStep H₁ H₂ Unit R₂),
          RecoveredByTwo recoverTwo [] [] trace ->
            spec (contingentPairOutputsFrom σ [] [] trace)) := by
  have hpair :
      ∀ trace : List (FringeObservationStep H₁ H₂ Unit R₂),
        PairRecoveredBy punitRecover recoverTwo [] [] [] [] trace ↔
          RecoveredByTwo recoverTwo [] [] trace :=
    fun trace =>
      pairRecoveredBy_punitLeft_iff (H₁ := H₁) recoverTwo [] [] [] [] rfl trace
  have hO :
      ∀ σ : FringeStrategyPair H₁ H₂ Unit R₂ Out₁ Out₂,
        OriginalWinsRecoverable punitRecover recoverTwo spec σ ↔
          ∀ trace, RecoveredByTwo recoverTwo [] [] trace ->
            spec (originalPairOutputsFrom σ [] [] [] [] trace) := by
    intro σ; unfold OriginalWinsRecoverable
    exact forall_congr' fun trace => imp_congr_left (hpair trace)
  have hC :
      ∀ σ : ContingentStrategyPair H₁ H₂ Unit R₂ Out₁ Out₂,
        ContingentWinsRecoverable punitRecover recoverTwo spec σ ↔
          ∀ trace, RecoveredByTwo recoverTwo [] [] trace ->
            spec (contingentPairOutputsFrom σ [] [] trace) := by
    intro σ; unfold ContingentWinsRecoverable
    exact forall_congr' fun trace => imp_congr_left (hpair trace)
  exact (exists_congr hO).symm.trans
    ((fringeElim_winning_iff punitRecover recoverTwo spec).trans (exists_congr hC))

section InformedRecovery

universe o

variable {O₂ : Type o}

/-- One-sided **informed self-embedding**: each step's informed observation
(`DelayOneObs O₂ R₂ = O₂ × List R₂`) exposes the settled past fringe list in its second component --
the delay-one hierarchy of the *informed* (receiver) side (`lem:delayonehierarchy`). -/
def SelfEmbeddingTwo
    (pastTwo : List R₂)
    (trace :
      List (FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂)) : Prop :=
  match trace with
  | [] => True
  | step :: rest =>
      step.historyTwo.2 = pastTwo ∧ SelfEmbeddingTwo (pastTwo ++ [step.fringeTwo]) rest

/-- **The informed side's `RecoveredByTwo` is discharged by the delay-one embedder.**  When the
informed history is a delay-one observation (`DelayOneObs`), the embedder `recoverEmbedded` reads the
settled past off the current observation (`recoverEmbedded_concat`), so informed recoverability holds
exactly when the informed observations self-embed -- `lem:delayonehierarchy` for the receiver side.
This is the informed half of the θ̄-game's asymmetric hierarchy; together with the automatic blind
half (`fringeElim_winning_iff_punitLeft`) it supplies the recoverability fringe elimination needs. -/
theorem recoveredByTwo_recoverEmbedded_iff
    (histTwo : List (DelayOneObs O₂ R₂)) (pastTwo : List R₂)
    (trace :
      List (FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂)) :
    RecoveredByTwo recoverEmbedded histTwo pastTwo trace ↔
      SelfEmbeddingTwo pastTwo trace := by
  induction trace generalizing histTwo pastTwo with
  | nil => exact Iff.rfl
  | cons step rest ih =>
      unfold RecoveredByTwo SelfEmbeddingTwo
      rw [recoverEmbedded_concat, ih]

/-- **Delay-one one-sided fringe elimination.**  The abstract endpoint the θ̄-game instantiates: for
a game with a degenerate (`Unit`) blind fringe and an informed side whose observations are delay-one
(`DelayOneObs`), a fringe-*dependent* strategy pair wins on every *informed-self-embedding* play iff a
fringe-*free* (contingent) one does.  The blind recoverability is automatic
(`fringeElim_winning_iff_punitLeft`) and the informed recoverability is the delay-one hierarchy
(`recoveredByTwo_recoverEmbedded_iff`).  This is exactly the asymmetric, orientation-dependent
finite-memory extraction the `{←,→,↔}` model needs -- the fringe-free winner is summary-observable. -/
theorem fringeElim_winning_iff_delayOne
    (spec : OutputTraceSpec Out₁ Out₂) :
    (∃ σ : FringeStrategyPair H₁ (DelayOneObs O₂ R₂) Unit R₂ Out₁ Out₂,
        ∀ trace : List (FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂),
          SelfEmbeddingTwo [] trace ->
            spec (originalPairOutputsFrom σ [] [] [] [] trace)) ↔
      (∃ σ : ContingentStrategyPair H₁ (DelayOneObs O₂ R₂) Unit R₂ Out₁ Out₂,
        ∀ trace : List (FringeObservationStep H₁ (DelayOneObs O₂ R₂) Unit R₂),
          SelfEmbeddingTwo [] trace ->
            spec (contingentPairOutputsFrom σ [] [] trace)) := by
  have h :=
    fringeElim_winning_iff_punitLeft (H₁ := H₁) (H₂ := DelayOneObs O₂ R₂) (R₂ := R₂)
      (recoverEmbedded (O := O₂) (R := R₂)) spec
  simp only [recoveredByTwo_recoverEmbedded_iff] at h
  exact h

end InformedRecovery

end DistributedSynthesis
