/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemEnrichedBaseSemigroup

/-!
# The alternating-profile-depth witness

The refutation socket for the saturation route.  The verdict under test:
run-consistent alternating nesting is not bounded -- first-order belief
stays one bit, but the order of mutual uncertainty can grow indefinitely
(the acknowledgement/email-game phenomenon), realized by a small DPA
colouring part of the view-pair path.

An `AlternatingProfileDepthWitness` packages, per depth `k`, a pair of
typed paths that the level-`k` windows identify and the level-`k + 1`
windows separate.  From such a witness:

* no tower level ever stabilizes
  (`not_saturationStabilizesAt_of_witness`);
* `EnrichedCodeSuccessorCongruence` fails at the witness's base
  (`not_enrichedCodeSuccessorCongruence_of_witness`);
* at an atom-enriched base, no symmetric `MonitorDeterminesProfile`
  instantiation exists for that family
  (`not_monitorDeterminesProfile_of_witness`).

Constructing the witness is made mechanical by the decomposition
lemmas: `summaryWindowAbstraction_eq_iff` splits window equality into
value and endpoint-window equalities, and
`saturationLevel_succ_value_eq_iff` splits a level-`k + 1` value
equality into the base equality plus one window-profile equality per
closing parameter.  A depth pair is therefore exhibited by: equal
windows, equal base values, equal level-`k` profiles, and one closing
parameter with one boundary-label pair whose achievable output-window
sets differ -- the last via profile exactness
(`mem_profileSummaryValue_iff`).

If the concrete construction of the witness for the tiny colouring DPA
fails, the failure point is the absorption law between the two
alternating profile operators that a positive proof would need.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

section DepthWitness

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (radius : Nat)

/-! ### Decomposition lemmas for building depth pairs -/

/-- Window equality splits into value equality and endpoint-window
equalities. -/
theorem summaryWindowAbstraction_eq_iff {E : Type u}
    (S : PathSummarySemigroup.{u, v} E) (c : Nat) (u v : TypedPath E) :
    summaryWindowAbstraction S c u = summaryWindowAbstraction S c v ↔
      pathSummaryValue S u = pathSummaryValue S v ∧
        prefixAtMost c u = prefixAtMost c v ∧
        suffixAtMost c u = suffixAtMost c v := by
  constructor
  · intro h
    exact ⟨congrArg SummaryWindowValue.summary h,
      congrArg SummaryWindowValue.pref h,
      congrArg SummaryWindowValue.suff h⟩
  · rintro ⟨hval, hpre, hsuf⟩
    simp only [summaryWindowAbstraction, SummaryWindowValue.mk.injEq]
    exact ⟨hval, hpre, hsuf⟩

/-- A level-`k + 1` value equality is the base equality plus one
window-profile equality per closing parameter. -/
theorem saturationLevel_succ_value_eq_iff (k : Nat) (d : Proc)
    (u v : TypedPath (EdgeType d)) :
    (pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d) u =
        pathSummaryValue (saturationLevel schemeAt base radius (k + 1) d)
          v) ↔
      (pathSummaryValue (base d) u = pathSummaryValue (base d) v ∧
        ∀ param : Param d,
          letI : DecidableEq
              (saturationLevel schemeAt base radius k d.other).Summary :=
            Classical.decEq _
          pathSummaryValue
              (windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius k d.other) radius) u =
            pathSummaryValue
              (windowProfileSemigroup (schemeAt d param)
                (saturationLevel schemeAt base radius k d.other) radius)
              v) := by
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
  constructor
  · intro h
    have hfst := congrArg Prod.fst h
    have hsnd := congrArg Prod.snd h
    dsimp only at hfst hsnd
    refine ⟨hfst, fun param => ?_⟩
    have hp := congrFun hsnd param
    rw [PathSummarySemigroup.pathSummaryValue_pi,
      PathSummarySemigroup.pathSummaryValue_pi] at hp
    exact hp
  · rintro ⟨hbase, hprofile⟩
    refine Prod.ext hbase ?_
    dsimp only
    funext param
    rw [PathSummarySemigroup.pathSummaryValue_pi,
      PathSummarySemigroup.pathSummaryValue_pi]
    exact hprofile param

/-! ### The witness and the kill theorems -/

/--
**The alternating-profile-depth witness**: per depth `k`, a side, a
window margin, and a pair of typed paths that level-`k` windows
identify and level-`k + 1` windows separate.  The email-game chain
embedded into the concrete window-profile refinement.
-/
structure AlternatingProfileDepthWitness where
  side : Nat -> Proc
  bound : Nat -> Nat
  oldPath : (k : Nat) -> TypedPath (EdgeType (side k))
  newPath : (k : Nat) -> TypedPath (EdgeType (side k))
  window_eq : ∀ k : Nat,
    summaryWindowAbstraction
        (saturationLevel schemeAt base radius k (side k)) (bound k)
        (oldPath k) =
      summaryWindowAbstraction
        (saturationLevel schemeAt base radius k (side k)) (bound k)
        (newPath k)
  window_ne : ∀ k : Nat,
    summaryWindowAbstraction
        (saturationLevel schemeAt base radius (k + 1) (side k)) (bound k)
        (oldPath k) ≠
      summaryWindowAbstraction
        (saturationLevel schemeAt base radius (k + 1) (side k)) (bound k)
        (newPath k)

/-- **Kill 1**: a witness refutes stabilization at every level. -/
theorem not_saturationStabilizesAt_of_witness
    (w : AlternatingProfileDepthWitness schemeAt base radius) (k : Nat) :
    ¬ SaturationStabilizesAt schemeAt base radius k :=
  fun h =>
    w.window_ne k
      (h (w.side k) (w.bound k) (w.oldPath k) (w.newPath k) (w.window_eq k))

/-- **Kill 2**: a witness refutes the enriched-code successor
congruence at its base. -/
theorem not_enrichedCodeSuccessorCongruence_of_witness
    (hbase : ∀ d, PathSummaryLawful (base d))
    (w : AlternatingProfileDepthWitness schemeAt base radius) :
    ¬ EnrichedCodeSuccessorCongruence schemeAt base radius := by
  intro hcong
  obtain ⟨k, hk⟩ :=
    exists_saturationStabilizesAt_of_enrichedCodeSuccessorCongruence
      schemeAt base radius hbase hcong
  exact not_saturationStabilizesAt_of_witness schemeAt base radius w k hk

end DepthWitness

section MonitorRefutation

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)
variable (S0 : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))
variable (family : (d : Proc) ->
  DeterministicMonitorFamily.{u, max u w, max u w} (EdgeType d))
variable (radius : Nat)

/-- **Kill 3**: a witness at an atom-enriched base refutes the
symmetric `MonitorDeterminesProfile` instantiation for that family. -/
theorem not_monitorDeterminesProfile_of_witness
    [inst : ∀ d, DecidableEq
      (enrichedBaseSemigroup (S0 d) (family d)).Summary]
    (hlaw : ∀ d, PathSummaryLawful (S0 d))
    (w : AlternatingProfileDepthWitness schemeAt
      (fun d => enrichedBaseSemigroup (S0 d) (family d)) radius) :
    ¬ ∀ (d : Proc) (param : Param d),
        MonitorDeterminesProfile (schemeAt d param)
          (enrichedBaseSemigroup (S0 d.other) (family d.other)) radius
          (family d) := by
  intro hdet
  have hfactor :=
    enrichedCodeProfileFactor_of_monitorDeterminesProfile schemeAt S0 family
      radius hdet
  have hcong :=
    (enrichedCodeSuccessorCongruence_iff_profileFactor schemeAt
        (fun d => enrichedBaseSemigroup (S0 d) (family d)) radius
        (fun d => enrichedBaseSemigroup_lawful (S0 d) (family d)
          (hlaw d))).mpr
      hfactor
  exact not_enrichedCodeSuccessorCongruence_of_witness schemeAt
    (fun d => enrichedBaseSemigroup (S0 d) (family d)) radius
    (fun d => enrichedBaseSemigroup_lawful (S0 d) (family d) (hlaw d)) w
    hcong

end MonitorRefutation

end DistributedSynthesis
