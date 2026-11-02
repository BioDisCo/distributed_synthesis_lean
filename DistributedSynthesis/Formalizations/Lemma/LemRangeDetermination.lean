/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemAlternatingProfileDepth

/-!
# Range determination: the positive collapse lemma

The formal shape of the replace-not-accumulate verdict: after a
reversal, only one fresh bit is hidden, and the substituted word
restarts from its finite entry data.  The tower consequence is that the
profile of a *range word* -- an output of the substitution relation --
is determined by its own base window code, with no memory of deeper
nesting.

`RangeDetermination` states exactly this: any two outputs of the
substitution (any sides' closing parameters, any old paths) with equal
base window codes have equal cross-side window profiles at the base
level.  Crucially the quantification is over range words only; nothing
is assumed about arbitrary typed paths.

The main theorem (`saturationStabilizesAt_one_of_rangeDetermination`):
range determination collapses the tower at level one.  Level-two
entries are level-one codes of outputs; the code-zero exchange supplied
by level-one equality lifts to a code-one exchange because outputs are
range words, so their profile components are already pinned by range
determination.  With stabilization at level one,
`rangeDeterminationClosureCertificate` produces the complete
reversal-closure certificate directly -- no enriched-code congruence
and no pigeonhole are needed on this route.

The remaining model-specific input is `RangeDetermination` for
`automatonSchemeFamily` at the concrete enriched base: the calculation
whether a substituted word's profile depends only on its `(M_A x Q_d)`
entry state and the fresh acknowledgement bit, both carried by the base
monitors.  If that calculation fails, the failure is a concrete
`AlternatingProfileDepthWitness` seed.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

section RangeDetermination

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (radius : Nat)

/--
**Range determination**: the base window code of a substituted word
determines its cross-side window profiles at the base level.  This is
the tower form of "the profile after a reversal depends only on the
entry state and the fresh acknowledgement bit": the quantification is
over outputs of the substitution relation only.
-/
def RangeDetermination : Prop :=
  ∀ (d : Proc) (pu pv : Param d) (u v : TypedPath (EdgeType d))
    (out out' : TypedPath (EdgeType d.other)),
    out ∈ (schemeAt d pu).SuccessorWords u ->
    out' ∈ (schemeAt d pv).SuccessorWords v ->
    finiteSummaryWindowAbstraction (base d.other) radius out =
      finiteSummaryWindowAbstraction (base d.other) radius out' ->
    ∀ param' : Param d.other,
      letI : DecidableEq (base d.other.other).Summary := Classical.decEq _
      pathSummaryValue
          (windowProfileSemigroup (schemeAt d.other param')
            (base d.other.other) radius) out =
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d.other param')
            (base d.other.other) radius) out'

/-- **The collapse**: range determination gives summary determination
at level one -- level-one values determine level-two values. -/
theorem summaryDetermines_one_of_rangeDetermination
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hrange : RangeDetermination schemeAt base radius) :
    SummaryDetermines schemeAt base radius 1 := by
  intro d u v h1
  obtain ⟨hb, hp0⟩ :=
    (saturationLevel_succ_value_eq_iff schemeAt base radius 0 d u v).mp h1
  refine (saturationLevel_succ_value_eq_iff schemeAt base radius 1 d u v).mpr
    ⟨hb, fun param => ?_⟩
  letI : DecidableEq
      (saturationLevel schemeAt base radius 1 d.other).Summary :=
    Classical.decEq _
  letI : DecidableEq
      (saturationLevel schemeAt base radius 0 d.other).Summary :=
    Classical.decEq _
  letI : DecidableEq (base d.other).Summary := Classical.decEq _
  have key : ∀ p q : TypedPath (EdgeType d),
      pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) p =
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) q ->
      ∀ (left right : Label) (out : TypedPath (EdgeType d.other)),
        (schemeAt d param).LocalFrom left p out right ->
          ∃ out', (schemeAt d param).LocalFrom left q out' right ∧
            finiteSummaryWindowAbstraction
                (saturationLevel schemeAt base radius 1 d.other) radius
                out' =
              finiteSummaryWindowAbstraction
                (saturationLevel schemeAt base radius 1 d.other) radius
                out := by
    intro p q hpq left right out hlocal
    have hmem : finiteSummaryWindowAbstraction
        (saturationLevel schemeAt base radius 0 d.other) radius out ∈
        pathSummaryValue
          (windowProfileSemigroup (schemeAt d param)
            (saturationLevel schemeAt base radius 0 d.other) radius) p
          left right :=
      ((schemeAt d param).mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil _ radius)
          (finiteSummaryWindowAbstraction_append _ radius (hbase d.other))
          p left right _).mpr ⟨out, hlocal, rfl⟩
    rw [hpq] at hmem
    obtain ⟨out', hlocal', heq0⟩ :=
      ((schemeAt d param).mem_profileSummaryValue_iff _ _ _
          (finiteSummaryWindowAbstraction_nil _ radius)
          (finiteSummaryWindowAbstraction_append _ radius (hbase d.other))
          q left right _).mp hmem
    refine ⟨out', hlocal', ?_⟩
    have hb0 : pathSummaryValue (base d.other) out' =
        pathSummaryValue (base d.other) out := congrArg Prod.fst heq0
    have hpre := congrArg (fun value => value.2.1) heq0
    have hsuf := congrArg (fun value => value.2.2) heq0
    have hval1 : pathSummaryValue
        (saturationLevel schemeAt base radius 1 d.other) out' =
        pathSummaryValue (saturationLevel schemeAt base radius 1 d.other)
          out := by
      refine (saturationLevel_succ_value_eq_iff schemeAt base radius 0
        d.other out' out).mpr ⟨hb0, fun param' => ?_⟩
      exact hrange d param param q p out' out ⟨left, right, hlocal'⟩
        ⟨left, right, hlocal⟩ heq0 param'
    exact Prod.ext hval1 (Prod.ext hpre hsuf)
  exact windowProfileValue_eq_of_exchange (schemeAt d param)
    (saturationLevel schemeAt base radius 1 d.other) radius
    (saturationLevel_lawful schemeAt base radius hbase 1 d.other)
    (key u v (hp0 param)) (key v u (hp0 param).symm)

/-- **Stabilization at level one from range determination.** -/
theorem saturationStabilizesAt_one_of_rangeDetermination
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hrange : RangeDetermination schemeAt base radius) :
    SaturationStabilizesAt schemeAt base radius 1 :=
  saturationStabilizesAt_of_summaryDetermines schemeAt base radius
    (summaryDetermines_one_of_rangeDetermination schemeAt base radius hbase
      hrange)

variable {In₁ : Type v} {In₂ : Type x} {Out₁ : Type y} {Out₂ : Type z}

/--
**The reversal-closure certificate from range determination.**  The
positive route in one arrow: no enriched-code congruence and no
pigeonhole -- stabilization holds at level one outright.
-/
noncomputable def rangeDeterminationClosureCertificate
    {BaseAtom : Proc -> Type v'} {Continuation : Proc -> Type r}
    (hbase : ∀ d, PathSummaryLawful (base d))
    (hrange : RangeDetermination schemeAt base radius)
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
    (saturationStabilizesAt_one_of_rangeDetermination schemeAt base radius
      hbase hrange)
    (fun d tuple => paramOf d tuple.bits tuple.letter)
    baseAtomOf continuationOf baseSound
    (fun d =>
      summaryWindowCompatible_saturationLevel schemeAt base radius hbase
        compatible 1 d)
    hradius

end RangeDetermination

end DistributedSynthesis
