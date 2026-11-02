/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemSaturationFactorization

/-!
# The atom-enriched base semigroup and the profile monitor

The master code `E_d` of `def:atomenrichedsummarywindow` is the raw
summary-window value together with the terminal states of a finite
deterministic monitor family.  To serve as the `base` of the saturation
tower, this abstraction is packaged as a `PathSummarySemigroup`:

* `monitorTransitionSemigroup` -- the compositional carrier of a monitor
  family is its transition function, multiplied by composition; applying
  the path value to the initial states recovers `runMonitor`
  (`monitorTransition_value`).
* `enrichedBaseSemigroup` -- the raw summary paired with the monitor
  transitions.  Its finite window value determines the paper's
  atom-enriched summary-window value
  (`enrichedBase_code_determines_atomEnriched`), so `enrichedCode` at
  this base refines `E_d`.

The sharp experiment (`enrichedCode_eq_implies_windowProfileValue_eq`)
is then reduced to one question about the monitor family:

* `profileMonitor` -- the window-profile fold IS a deterministic finite
  monitor over old edges (`runMonitor_profileMonitor`), so the profile
  is finite-state information about the old path.
* `MonitorDeterminesProfile` -- the family pins down the profile; the
  profile monitor itself does so tautologically
  (`monitorDeterminesProfile_profileMonitor`).
* `enrichedCodeProfileFactor_of_monitorDeterminesProfile` -- at the
  enriched base, if for every side and closing parameter the family
  determines that parameter's window profile (valued in the OTHER
  side's enriched windows), then `EnrichedCodeProfileFactor` holds and
  the whole set route closes through `enrichedCodeClosureCertificate`.

This makes the remaining mathematics exact: the profile monitor for
side `d` is valued in windows over the enriched base of side `d.other`,
so instantiating `MonitorDeterminesProfile` symmetrically is the
fixed-point/collapse question of the full model -- whether the concrete
`A.step` block structure lets a fixed finite family determine its own
cross-side profiles.
-/

namespace DistributedSynthesis

universe u v w x y

/-! ### The monitor-transition semigroup and the enriched base -/

section MonitorSemigroup

variable {EdgeType : Type u}

/-- The transition-function semigroup of a deterministic monitor
family. -/
noncomputable def monitorTransitionSemigroup
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType) :
    PathSummarySemigroup.{u, max w x} EdgeType where
  Summary := (i : family.index) -> family.state i -> family.state i
  summaryFinite := by
    classical
    letI : (i : family.index) -> Fintype (family.state i) :=
      family.stateFinite
    infer_instance
  empty := fun _ s => s
  ofEdge edge := fun i s => family.step i s edge
  multiply f g := fun i s => g i (f i s)

theorem monitorTransitionSemigroup_lawful
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType) :
    PathSummaryLawful (monitorTransitionSemigroup family) where
  assoc _ _ _ := rfl
  one_mul _ := rfl
  mul_one _ := rfl

/-- The path value of the transition semigroup is the transition
function of the whole path. -/
theorem monitorTransition_value
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType)
    (path : TypedPath EdgeType) (i : family.index) (s : family.state i) :
    pathSummaryValue (monitorTransitionSemigroup family) path i s =
      path.foldl (family.step i) s := by
  induction path using List.reverseRecOn with
  | nil => rfl
  | append_singleton path edge ih =>
      simp only [pathSummaryValue, List.foldl_append, List.foldl_cons,
        List.foldl_nil] at ih ⊢
      show family.step i
          ((path.foldl (fun acc e =>
              (monitorTransitionSemigroup family).multiply acc
                ((monitorTransitionSemigroup family).ofEdge e))
            (monitorTransitionSemigroup family).empty) i s) edge =
        family.step i (path.foldl (family.step i) s) edge
      rw [ih]

/-- The atom-enriched base semigroup: the raw summary paired with the
monitor transition functions. -/
noncomputable def enrichedBaseSemigroup (S : PathSummarySemigroup.{u, v} EdgeType)
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType) :
    PathSummarySemigroup.{u, max v w x} EdgeType :=
  S.prod (monitorTransitionSemigroup family)

theorem enrichedBaseSemigroup_lawful
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType)
    (hlaw : PathSummaryLawful S) :
    PathSummaryLawful (enrichedBaseSemigroup S family) :=
  hlaw.prod (monitorTransitionSemigroup_lawful family)

/-- The finite window value of the enriched base determines the paper's
atom-enriched summary-window value (`def:atomenrichedsummarywindow`):
`enrichedCode` at this base refines `E_d`. -/
theorem enrichedBase_code_determines_atomEnriched
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType)
    (c : Nat) {u v : TypedPath EdgeType}
    (h : finiteSummaryWindowAbstraction (enrichedBaseSemigroup S family) c u =
      finiteSummaryWindowAbstraction (enrichedBaseSemigroup S family) c v) :
    finiteAtomEnrichedSummaryWindowAbstraction S family c u =
      finiteAtomEnrichedSummaryWindowAbstraction S family c v := by
  have hsum := congrArg Prod.fst h
  dsimp only [finiteSummaryWindowAbstraction] at hsum
  rw [show enrichedBaseSemigroup S family =
      S.prod (monitorTransitionSemigroup family) from rfl,
    PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsum
  have hS := congrArg Prod.fst hsum
  have hM := congrArg Prod.snd hsum
  dsimp only at hS hM
  have hpre := congrArg (fun value => value.2.1) h
  have hsuf := congrArg (fun value => value.2.2) h
  dsimp only [finiteSummaryWindowAbstraction] at hpre hsuf
  unfold finiteAtomEnrichedSummaryWindowAbstraction
  refine Prod.ext ?_ ?_
  · exact Prod.ext hS (Prod.ext hpre hsuf)
  · funext i
    have happ := congrFun (congrFun hM i) (family.init i)
    rw [monitorTransition_value, monitorTransition_value] at happ
    exact happ

end MonitorSemigroup

/-! ### The profile monitor -/

section ProfileMonitor

variable {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
variable (Snew : PathSummarySemigroup.{v, x} NewEdge)
variable [Fintype NewEdge] [DecidableEq NewEdge] [DecidableEq Snew.Summary]
variable (radius : Nat)

/-- The window-profile fold as a deterministic finite monitor over old
edges: the profile of an old path is finite-state information. -/
noncomputable def profileMonitor : DeterministicMonitorFamily OldEdge where
  index := PUnit
  indexFinite := inferInstance
  state _ :=
    LabelProfile Label (FiniteSummaryWindowValue Snew.Summary NewEdge radius)
  stateFinite _ := by
    classical
    infer_instance
  init _ := identityProfile (windowOne Snew radius)
  step _ profile edge :=
    profileComp (windowMul Snew radius) profile
      (scheme.edgeProfile (finiteSummaryWindowAbstraction Snew radius) edge)

/-- Running the profile monitor computes the window-profile summary. -/
theorem runMonitor_profileMonitor (path : TypedPath OldEdge) :
    runMonitor (profileMonitor scheme Snew radius) PUnit.unit path =
      pathSummaryValue (windowProfileSemigroup scheme Snew radius) path := by
  induction path using List.reverseRecOn with
  | nil => rfl
  | append_singleton path edge ih =>
      simp only [runMonitor, pathSummaryValue, List.foldl_append,
        List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih]
      rfl

/-- A monitor family determines the window profile if joint terminal
states pin down the profile summary. -/
def MonitorDeterminesProfile
    (family : DeterministicMonitorFamily OldEdge) : Prop :=
  ∀ u v : TypedPath OldEdge,
    (∀ i, runMonitor family i u = runMonitor family i v) ->
      pathSummaryValue (windowProfileSemigroup scheme Snew radius) u =
        pathSummaryValue (windowProfileSemigroup scheme Snew radius) v

/-- The profile monitor determines its own profile. -/
theorem monitorDeterminesProfile_profileMonitor :
    MonitorDeterminesProfile scheme Snew radius
      (profileMonitor scheme Snew radius) := by
  intro u v h
  have happ := h PUnit.unit
  rw [runMonitor_profileMonitor, runMonitor_profileMonitor] at happ
  exact happ

end ProfileMonitor

/-! ### The experiment reduction at the enriched base -/

section ExperimentReduction

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

omit [(d : Proc) → Fintype (Param d)] [(d : Proc) → DecidableEq (Param d)] in
/--
**The experiment reduction**: at the atom-enriched base, if for every
side and closing parameter the monitor family determines that
parameter's window profile (valued in the other side's enriched
windows), then equal master codes imply equal window-profile summaries
-- `EnrichedCodeProfileFactor`, hence `EnrichedCodeSuccessorCongruence`,
stabilization, and the full reversal-closure certificate.
-/
theorem enrichedCodeProfileFactor_of_monitorDeterminesProfile
    [inst : ∀ d, DecidableEq
      (enrichedBaseSemigroup (S0 d) (family d)).Summary]
    (hdet : ∀ (d : Proc) (param : Param d),
      MonitorDeterminesProfile (schemeAt d param)
        (enrichedBaseSemigroup (S0 d.other) (family d.other)) radius
        (family d)) :
    EnrichedCodeProfileFactor schemeAt
      (fun d => enrichedBaseSemigroup (S0 d) (family d)) radius := by
  intro d param old new hcode
  apply hdet d param
  intro i
  have hsum := congrArg Prod.fst hcode
  dsimp only [enrichedCode, finiteSummaryWindowAbstraction] at hsum
  rw [show enrichedBaseSemigroup (S0 d) (family d) =
      (S0 d).prod (monitorTransitionSemigroup (family d)) from rfl,
    PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsum
  have hM0 := congrArg Prod.snd hsum
  dsimp only at hM0
  have hM := congrFun (congrFun hM0 i) ((family d).init i)
  rw [monitorTransition_value, monitorTransition_value] at hM
  exact hM

end ExperimentReduction

end DistributedSynthesis
