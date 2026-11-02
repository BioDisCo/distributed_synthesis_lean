/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSaturationStabilization

/-!
# Factorization of the saturation tower through the master path code

The tower of `LemSaturationStabilization` stabilizes once all its levels
factor through one fixed finite quotient.  This file fixes that quotient
to the **master path code** `E_d`: the finite summary-window value of the
enriched base summary at the closure radius (`enrichedCode`).  Two
generic theorems reduce stabilization to a single model-specific
obligation:

* **Refinement** (`saturationLevel_refines`): level-`k + 1` summaries
  determine level-`k` summaries, for every `k`.  Coarse output windows
  are functions of fine ones, so window profiles coarsen along the tower
  (`windowProfileValue_coarsen`); no model input is needed.
* **Factorization** (`saturationLevel_factors_of_congruence`): under the
  **enriched-code successor congruence**
  (`EnrichedCodeSuccessorCongruence`) -- old paths with equal master
  codes admit, for every closing parameter and boundary-label pair, the
  same successor master codes over locally uniform substitutions --
  every tower level factors through `enrichedCode`.

Both feed `exists_saturationStabilizesAt_of_finite_quotient`, so the
congruence alone yields stabilization
(`exists_saturationStabilizesAt_of_enrichedCodeSuccessorCongruence`) and
with it the candidate-set reversal-closure certificate
(`enrichedCodeClosureCertificate`).  The congruence is the exact Lean
form of the finite-count justification behind
`prop:journalatomsreversalclosure`: `E_d` is the master partition
bounding all productive refinements.  If the congruence fails for the
concrete reversal schemes, the finite-bound argument of the paper is not
justified.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

/-! ### Window-profile exchange and coarsening -/

section ProfileExchange

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
variable [Fintype NewEdge] [DecidableEq NewEdge]

/-- Two old paths whose locally uniform substitutions exchange -- every
output of one admits an output of the other with the same finite window
-- have equal window profiles. -/
theorem windowProfileValue_eq_of_exchange
    (Snew : PathSummarySemigroup.{v, x} NewEdge) [DecidableEq Snew.Summary]
    (radius : Nat) (hlaw : PathSummaryLawful Snew)
    {old₁ old₂ : TypedPath OldEdge}
    (hexch : ∀ (left right : Label) (out : TypedPath NewEdge),
      scheme.LocalFrom left old₁ out right ->
        ∃ out', scheme.LocalFrom left old₂ out' right ∧
          finiteSummaryWindowAbstraction Snew radius out' =
            finiteSummaryWindowAbstraction Snew radius out)
    (hexch' : ∀ (left right : Label) (out : TypedPath NewEdge),
      scheme.LocalFrom left old₂ out right ->
        ∃ out', scheme.LocalFrom left old₁ out' right ∧
          finiteSummaryWindowAbstraction Snew radius out' =
            finiteSummaryWindowAbstraction Snew radius out) :
    pathSummaryValue (windowProfileSemigroup scheme Snew radius) old₁ =
      pathSummaryValue (windowProfileSemigroup scheme Snew radius) old₂ := by
  funext left right
  ext m
  unfold windowProfileSemigroup
  rw [scheme.mem_profileSummaryValue_iff _ _ _
      (finiteSummaryWindowAbstraction_nil Snew radius)
      (finiteSummaryWindowAbstraction_append Snew radius hlaw),
    scheme.mem_profileSummaryValue_iff _ _ _
      (finiteSummaryWindowAbstraction_nil Snew radius)
      (finiteSummaryWindowAbstraction_append Snew radius hlaw)]
  constructor
  · rintro ⟨out, hlocal, rfl⟩
    exact hexch left right out hlocal
  · rintro ⟨out, hlocal, rfl⟩
    exact hexch' left right out hlocal

/-- **Window profiles coarsen**: if the fine summary of output words
determines the coarse one, equal fine window profiles give equal coarse
window profiles. -/
theorem windowProfileValue_coarsen
    (Sfine : PathSummarySemigroup.{v, x} NewEdge)
    (Scoarse : PathSummarySemigroup.{v, y} NewEdge)
    [DecidableEq Sfine.Summary] [DecidableEq Scoarse.Summary]
    (radius : Nat)
    (hfine : PathSummaryLawful Sfine) (hcoarse : PathSummaryLawful Scoarse)
    (hdet : ∀ out out' : TypedPath NewEdge,
      pathSummaryValue Sfine out = pathSummaryValue Sfine out' ->
        pathSummaryValue Scoarse out = pathSummaryValue Scoarse out')
    {old₁ old₂ : TypedPath OldEdge}
    (hprofile :
      pathSummaryValue (windowProfileSemigroup scheme Sfine radius) old₁ =
        pathSummaryValue (windowProfileSemigroup scheme Sfine radius) old₂) :
    pathSummaryValue (windowProfileSemigroup scheme Scoarse radius) old₁ =
      pathSummaryValue (windowProfileSemigroup scheme Scoarse radius) old₂ := by
  have key : ∀ p q : TypedPath OldEdge,
      pathSummaryValue (windowProfileSemigroup scheme Sfine radius) p =
          pathSummaryValue (windowProfileSemigroup scheme Sfine radius) q ->
        ∀ (left right : Label) (out : TypedPath NewEdge),
          scheme.LocalFrom left p out right ->
            ∃ out', scheme.LocalFrom left q out' right ∧
              finiteSummaryWindowAbstraction Scoarse radius out' =
                finiteSummaryWindowAbstraction Scoarse radius out := by
    intro p q hpq left right out hlocal
    have hmem : finiteSummaryWindowAbstraction Sfine radius out ∈
        pathSummaryValue (windowProfileSemigroup scheme Sfine radius) p
          left right :=
      (scheme.mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil Sfine radius)
          (finiteSummaryWindowAbstraction_append Sfine radius hfine)
          p left right _).mpr ⟨out, hlocal, rfl⟩
    rw [hpq] at hmem
    obtain ⟨out', hlocal', heq⟩ :=
      (scheme.mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil Sfine radius)
          (finiteSummaryWindowAbstraction_append Sfine radius hfine)
          q left right _).mp hmem
    refine ⟨out', hlocal', ?_⟩
    exact Prod.ext (hdet out' out (congrArg Prod.fst heq))
      (Prod.ext (congrArg (fun value => value.2.1) heq)
        (congrArg (fun value => value.2.2) heq))
  exact windowProfileValue_eq_of_exchange scheme Scoarse radius hcoarse
    (key old₁ old₂ hprofile) (key old₂ old₁ hprofile.symm)

end ProfileExchange

/-! ### The master path code and the tower -/

section Factorization

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (radius : Nat)

/-- The master path code `E_d`: the finite summary-window value of the
enriched base summary at the closure radius. -/
def enrichedCode (d : Proc) (path : TypedPath (EdgeType d)) :
    FiniteSummaryWindowValue (base d).Summary (EdgeType d) radius :=
  finiteSummaryWindowAbstraction (base d) radius path

/-- **Levels refine, generically**: level-`k + 1` summaries determine
level-`k` summaries.  Proved once and for all by coarsening the window
profiles along the tower; no model-specific input. -/
theorem saturationLevel_refines
    (hbase : ∀ d, PathSummaryLawful (base d)) :
    ∀ (k : Nat) (d : Proc) (old new : TypedPath (EdgeType d)),
      pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) old =
          pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d)
            new ->
        pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new := by
  intro k
  induction k with
  | zero =>
      intro d old new h
      letI : DecidableEq
          (saturationLevel schemeAt base radius 0 d.other).Summary :=
        Classical.decEq _
      have hlevel : saturationLevel schemeAt base radius 1 d =
          (base d).prod
            (PathSummarySemigroup.pi fun param : Param d =>
              windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius 0 d.other) radius) := rfl
      rw [hlevel, PathSummarySemigroup.pathSummaryValue_prod,
        PathSummarySemigroup.pathSummaryValue_prod] at h
      exact congrArg Prod.fst h
  | succ k ih =>
      intro d old new h
      letI : DecidableEq
          (saturationLevel schemeAt base radius k d.other).Summary :=
        Classical.decEq _
      letI : DecidableEq
          (saturationLevel schemeAt base radius (k + 1) d.other).Summary :=
        Classical.decEq _
      have hfine : saturationLevel schemeAt base radius (k + 2) d =
          (base d).prod
            (PathSummarySemigroup.pi fun param : Param d =>
              windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius (k + 1) d.other)
                radius) := rfl
      have hcoarse : saturationLevel schemeAt base radius (k + 1) d =
          (base d).prod
            (PathSummarySemigroup.pi fun param : Param d =>
              windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius k d.other) radius) := rfl
      rw [hfine, PathSummarySemigroup.pathSummaryValue_prod,
        PathSummarySemigroup.pathSummaryValue_prod] at h
      rw [hcoarse, PathSummarySemigroup.pathSummaryValue_prod,
        PathSummarySemigroup.pathSummaryValue_prod]
      have hfst := congrArg Prod.fst h
      dsimp only at hfst
      refine Prod.ext hfst ?_
      have hsnd := congrArg Prod.snd h
      dsimp only at hsnd ⊢
      funext param
      rw [PathSummarySemigroup.pathSummaryValue_pi,
        PathSummarySemigroup.pathSummaryValue_pi]
      have hp := congrFun hsnd param
      rw [PathSummarySemigroup.pathSummaryValue_pi,
        PathSummarySemigroup.pathSummaryValue_pi] at hp
      exact windowProfileValue_coarsen (schemeAt d param)
        (saturationLevel schemeAt base radius (k + 1) d.other)
        (saturationLevel schemeAt base radius k d.other) radius
        (saturationLevel_lawful schemeAt base radius hbase (k + 1) d.other)
        (saturationLevel_lawful schemeAt base radius hbase k d.other)
        (fun out out' hval => ih d.other out out' hval) hp

/-- Level-`k` summaries determine base summaries. -/
theorem saturationLevel_refines_base
    (hbase : ∀ d, PathSummaryLawful (base d)) :
    ∀ (k : Nat) (d : Proc) (old new : TypedPath (EdgeType d)),
      pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new ->
        pathSummaryValue (base d) old = pathSummaryValue (base d) new := by
  intro k
  induction k with
  | zero => exact fun d old new h => h
  | succ k ih =>
      intro d old new h
      exact ih d old new
        (saturationLevel_refines schemeAt base radius hbase k d old new h)

/--
**The enriched-code successor congruence** -- the single model-specific
obligation of the saturation route: two old paths with the same master
code admit, for every closing parameter and boundary-label pair, the
same successor master codes over the locally uniform substitutions.
-/
def EnrichedCodeSuccessorCongruence : Prop :=
  ∀ (d : Proc) (param : Param d) (left right : Label)
    (old new : TypedPath (EdgeType d)),
    enrichedCode base radius d old = enrichedCode base radius d new ->
      ∀ c : FiniteSummaryWindowValue (base d.other).Summary
          (EdgeType d.other) radius,
        (∃ out, (schemeAt d param).LocalFrom left old out right ∧
            enrichedCode base radius d.other out = c) ↔
          ∃ out, (schemeAt d param).LocalFrom left new out right ∧
            enrichedCode base radius d.other out = c

/--
**The profile-factor form of the congruence**
(`enrichedCode_eq_implies_windowProfileValue_eq`): equal master codes
imply equal window-profile summaries valued in base windows of the other
side.  By profile exactness this is equivalent to
`EnrichedCodeSuccessorCongruence`
(`enrichedCodeSuccessorCongruence_iff_profileFactor`); it exposes the
algebraic construction required of the enriched base: the base summary
must determine the per-label-pair transducer profile.
-/
def EnrichedCodeProfileFactor [∀ d, DecidableEq (base d).Summary] : Prop :=
  ∀ (d : Proc) (param : Param d) (old new : TypedPath (EdgeType d)),
    enrichedCode base radius d old = enrichedCode base radius d new ->
      pathSummaryValue
          (windowProfileSemigroup (schemeAt d param) (base d.other) radius)
          old =
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d param) (base d.other) radius)
          new

omit [(d : Proc) → Fintype (Param d)] [(d : Proc) → DecidableEq (Param d)] in
/-- The congruence and its profile-factor form are equivalent. -/
theorem enrichedCodeSuccessorCongruence_iff_profileFactor
    [∀ d, DecidableEq (base d).Summary]
    (hbase : ∀ d, PathSummaryLawful (base d)) :
    EnrichedCodeSuccessorCongruence schemeAt base radius ↔
      EnrichedCodeProfileFactor schemeAt base radius := by
  constructor
  · intro hcong d param old new hcode
    have key : ∀ p q : TypedPath (EdgeType d),
        enrichedCode base radius d p = enrichedCode base radius d q ->
        ∀ (left right : Label) (out : TypedPath (EdgeType d.other)),
          (schemeAt d param).LocalFrom left p out right ->
            ∃ out', (schemeAt d param).LocalFrom left q out' right ∧
              finiteSummaryWindowAbstraction (base d.other) radius out' =
                finiteSummaryWindowAbstraction (base d.other) radius out := by
      intro p q hpq left right out hlocal
      obtain ⟨out', hlocal', hc⟩ :=
        (hcong d param left right p q hpq
          (enrichedCode base radius d.other out)).mp ⟨out, hlocal, rfl⟩
      exact ⟨out', hlocal', hc⟩
    exact windowProfileValue_eq_of_exchange (schemeAt d param) (base d.other)
      radius (hbase d.other) (key old new hcode) (key new old hcode.symm)
  · intro hfactor d param left right old new hcode c
    have hprofile :
        pathSummaryValue
            ((schemeAt d param).profileSummarySemigroup
              (finiteSummaryWindowAbstraction (base d.other) radius)
              (windowOne (base d.other) radius)
              (windowMul (base d.other) radius)) old =
          pathSummaryValue
            ((schemeAt d param).profileSummarySemigroup
              (finiteSummaryWindowAbstraction (base d.other) radius)
              (windowOne (base d.other) radius)
              (windowMul (base d.other) radius)) new :=
      hfactor d param old new hcode
    unfold enrichedCode
    rw [<- (schemeAt d param).mem_profileSummaryValue_iff _ _ _
        (finiteSummaryWindowAbstraction_nil (base d.other) radius)
        (finiteSummaryWindowAbstraction_append (base d.other) radius
          (hbase d.other)) old left right c,
      <- (schemeAt d param).mem_profileSummaryValue_iff _ _ _
        (finiteSummaryWindowAbstraction_nil (base d.other) radius)
        (finiteSummaryWindowAbstraction_append (base d.other) radius
          (hbase d.other)) new left right c,
      hprofile]

/-- **Factorization**: under the congruence, every tower level factors
through the master code. -/
theorem saturationLevel_factors_of_congruence
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hcong : EnrichedCodeSuccessorCongruence schemeAt base radius) :
    ∀ (k : Nat) (d : Proc) (old new : TypedPath (EdgeType d)),
      enrichedCode base radius d old = enrichedCode base radius d new ->
        pathSummaryValue (saturationLevel schemeAt base radius k d) old =
          pathSummaryValue (saturationLevel schemeAt base radius k d) new := by
  intro k
  induction k with
  | zero => exact fun d old new hcode => congrArg Prod.fst hcode
  | succ k ih =>
      intro d old new hcode
      letI : DecidableEq
          (saturationLevel schemeAt base radius k d.other).Summary :=
        Classical.decEq _
      have hlevel : saturationLevel schemeAt base radius (k + 1) d =
          (base d).prod
            (PathSummarySemigroup.pi fun param : Param d =>
              windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius k d.other) radius) := rfl
      rw [hlevel, PathSummarySemigroup.pathSummaryValue_prod,
        PathSummarySemigroup.pathSummaryValue_prod]
      have hfst := congrArg Prod.fst hcode
      dsimp only [enrichedCode, finiteSummaryWindowAbstraction] at hfst
      refine Prod.ext hfst ?_
      dsimp only
      funext param
      rw [PathSummarySemigroup.pathSummaryValue_pi,
        PathSummarySemigroup.pathSummaryValue_pi]
      have key : ∀ p q : TypedPath (EdgeType d),
          enrichedCode base radius d p = enrichedCode base radius d q ->
          ∀ (left right : Label) (out : TypedPath (EdgeType d.other)),
            (schemeAt d param).LocalFrom left p out right ->
              ∃ out', (schemeAt d param).LocalFrom left q out' right ∧
                finiteSummaryWindowAbstraction
                    (saturationLevel schemeAt base radius k d.other) radius
                    out' =
                  finiteSummaryWindowAbstraction
                    (saturationLevel schemeAt base radius k d.other) radius
                    out := by
        intro p q hpq left right out hlocal
        obtain ⟨out', hlocal', hc⟩ :=
          (hcong d param left right p q hpq
            (enrichedCode base radius d.other out)).mp ⟨out, hlocal, rfl⟩
        refine ⟨out', hlocal', ?_⟩
        exact Prod.ext (ih d.other out' out hc)
          (Prod.ext (congrArg (fun value => value.2.1) hc)
            (congrArg (fun value => value.2.2) hc))
      exact windowProfileValue_eq_of_exchange (schemeAt d param)
        (saturationLevel schemeAt base radius k d.other) radius
        (saturationLevel_lawful schemeAt base radius hbase k d.other)
        (key old new hcode) (key new old hcode.symm)

/-- **Stabilization from the congruence alone**: the master code is a
fixed finite quotient, factorization and refinement feed the pigeonhole,
and some tower level stabilizes. -/
theorem exists_saturationStabilizesAt_of_enrichedCodeSuccessorCongruence
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hcong : EnrichedCodeSuccessorCongruence schemeAt base radius) :
    ∃ k, SaturationStabilizesAt schemeAt base radius k :=
  exists_saturationStabilizesAt_of_finite_quotient schemeAt base radius
    (enrichedCode base radius)
    (fun k d old new =>
      saturationLevel_factors_of_congruence schemeAt base radius hbase hcong
        k d old new)
    (fun k d old new =>
      saturationLevel_refines schemeAt base radius hbase k d old new)

/-- Base-level window compatibility lifts to every tower level. -/
theorem summaryWindowCompatible_saturationLevel
    (hbase : ∀ d, PathSummaryLawful (base d))
    {BaseAtom : Proc -> Type v'}
    {baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d}
    (compatible : ∀ d, SummaryWindowCompatible (base d) radius (baseAtomOf d))
    (k : Nat) (d : Proc) :
    SummaryWindowCompatible (saturationLevel schemeAt base radius k d) radius
      (baseAtomOf d) := by
  intro old new h
  apply compatible d
  have hsummary := congrArg SummaryWindowValue.summary h
  have hpref := congrArg SummaryWindowValue.pref h
  have hsuff := congrArg SummaryWindowValue.suff h
  simp only [summaryWindowAbstraction] at hsummary hpref hsuff ⊢
  simp only [SummaryWindowValue.mk.injEq]
  exact ⟨saturationLevel_refines_base schemeAt base radius hbase k d old new
    hsummary, hpref, hsuff⟩

variable {In₁ : Type v} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/--
**The reversal-closure certificate from the congruence.**  Each closing
tuple's parameter is read off its bits and letter, level-uniformly; the
stable level is chosen from the congruence-driven stabilization.  This
is the one-arrow interface from the model-specific congruence to
`JournalAtomsReversalClosureCertificate`.
-/
noncomputable def enrichedCodeClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hcong : EnrichedCodeSuccessorCongruence schemeAt base radius)
    (paramOf : (d : Proc) -> DirectReversalBits ->
      ClosingLetter In₁ In₂ Out₁ Out₂ -> Param d)
    (baseAtomOf : (d : Proc) -> TypedPath (EdgeType d) -> BaseAtom d)
    (continuationOf : (d : Proc) -> TypedPath (EdgeType d) -> Continuation d)
    (baseSound : ∀ d, OneDirectionalSound (baseAtomOf d) (continuationOf d))
    (compatible : ∀ d, SummaryWindowCompatible (base d) radius (baseAtomOf d))
    (hradius : endpointPullbackBound radius ≤ radius) :
    JournalAtomsReversalClosureCertificate EdgeType BaseAtom
      In₁ In₂ Out₁ Out₂ Continuation :=
  saturatedSetClosureCertificate schemeAt base radius hbase
    (exists_saturationStabilizesAt_of_enrichedCodeSuccessorCongruence
      schemeAt base radius hbase hcong).choose_spec
    (fun d tuple => paramOf d tuple.bits tuple.letter)
    baseAtomOf continuationOf baseSound
    (fun d =>
      summaryWindowCompatible_saturationLevel schemeAt base radius hbase
        compatible _ d)
    hradius

end Factorization

end DistributedSynthesis
