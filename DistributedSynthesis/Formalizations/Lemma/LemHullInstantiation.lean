/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemRangeWordMonitor

/-!
# Hull instantiation: the model path relation and the initial monitor

The two remaining regularity facts of the hull program.

**Model fact 1** (`automatonPathSubstitution_iff_localFrom`): the
paper's path-level direct-reversal relation -- the threaded composition
of the per-edge relations `Θ_q` of `lem:automatonedgetypesubstitution`
(`AutomatonPathSubstitution`) -- coincides with the concrete scheme's
locally uniform substitution.  Hence every path standing in the paper's
reversal relation to a predecessor is a one-step range word
(`automatonPathSubstitution_mem_successorWords`) and lies in the
regular hull (`mem_rangeHull_of_automatonPathSubstitution`).  The
residual glue is only that the journal/play machinery produces exactly
`AutomatonPathSubstitution` -- the paper-side definition of the
transduction, discharged at the final model instantiation.

**The `Init` monitor** (`singleEdgeMonitor`): initial block paths are
single edges (path lengths `1, 3, 3^2, ...`); the three-state monitor
recognizes `∃ e, w = [e] ∧ P e` for any edge predicate `P`
(`singleEdgeMonitor_recognizes`).

**Assembly** (`rangeHull_reachWindowDetermined_of_recognizers`): if the
enriched base family contains recognizers for `Init` and for
`IsSuccessorWordFrom` -- the latter witnessed by `rangeWordMonitor` via
`isSuccessorWordFrom_automatonSchemeFamily_iff` -- then
`ReachWindowDetermined` holds for the regular hull at the enriched
base, completing every regularity input of
`entryRestartClosureCertificate` except the restart exchange itself.
-/

namespace DistributedSynthesis

universe u v w x y

/-! ### Model fact 1: the paper path relation is the scheme relation -/

section PathSubstitution

variable {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
variable {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype Out₁] [Fintype Out₂]
variable (A : DetParityAutomaton Alphabet)
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

/-- The paper's path-level direct-reversal relation: the threaded
composition of the per-edge relations `Θ_q` of
`lem:automatonedgetypesubstitution` along the old path. -/
def AutomatonPathSubstitution (x₁ : In₁) (x₂ : In₂) :
    BoundaryLabel Out₁ Out₂ -> List (AutomatonEdgeType A.State) ->
      List (AutomatonEdgeType A.State) -> BoundaryLabel Out₁ Out₂ -> Prop
  | a, [], out, b => out = [] ∧ b = a
  | a, q :: rest, out, b =>
      ∃ (l : OwnedLabel Out₁ Out₂ q.srcOwner)
        (r : OwnedLabel Out₁ Out₂ q.tgtOwner)
        (triple : AutomatonEdgeTriple A.State)
        (restOut : List (AutomatonEdgeType A.State)),
        l.val = a ∧
          AutomatonEdgeSubstitutionRelation A letter x₁ x₂ q l triple r ∧
          AutomatonPathSubstitution x₁ x₂ r.val rest restOut b ∧
          out = EdgeBlock3.toList triple ++ restOut

/-- **Model fact 1, bridge form**: the paper's path relation coincides
with the scheme's locally uniform substitution. -/
theorem automatonPathSubstitution_iff_localFrom (x₁ : In₁) (x₂ : In₂)
    (a b : BoundaryLabel Out₁ Out₂)
    (u out : List (AutomatonEdgeType A.State)) :
    AutomatonPathSubstitution A letter x₁ x₂ a u out b ↔
      (automatonSubstitutionScheme A letter x₁ x₂).LocalFrom a u out b := by
  induction u generalizing a out with
  | nil => exact Iff.rfl
  | cons q rest ih =>
      constructor
      · rintro ⟨l, r, triple, restOut, hl, ⟨iat, ias, htriple⟩, hrest, hout⟩
        exact ⟨EdgeBlock3.toList triple, restOut, r.val, (l, r, iat, ias),
          hl, by rw [htriple]; rfl, rfl, (ih r.val restOut).mp hrest, hout⟩
      · rintro ⟨emitted, restOut, mid, ⟨l, r, iat, ias⟩, hl, hemit, hmid,
          hrest, hout⟩
        refine ⟨l, r,
          automatonSubstitutionTriple A letter x₁ x₂ q l r iat ias,
          restOut, hl, ⟨iat, ias, rfl⟩, ?_, ?_⟩
        · rw [<- hmid] at hrest
          exact (ih r.val restOut).mpr hrest
        · rw [hout, hemit]
          rfl

/-- Every path in the paper's reversal relation to a predecessor is a
one-step range word. -/
theorem automatonPathSubstitution_mem_successorWords
    {x₁ : In₁} {x₂ : In₂} {a b : BoundaryLabel Out₁ Out₂}
    {u out : List (AutomatonEdgeType A.State)}
    (h : AutomatonPathSubstitution A letter x₁ x₂ a u out b) :
    out ∈ (automatonSubstitutionScheme A letter x₁ x₂).SuccessorWords u :=
  ⟨a, b, (automatonPathSubstitution_iff_localFrom A letter x₁ x₂ a b u
    out).mp h⟩

end PathSubstitution

section PathSubstitutionHull

variable {Alphabet : Type u} {In₁ In₂ Out₁ Out₂ : Type v}
variable [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Fintype (BoundaryLabel Out₁ Out₂)]
variable [DecidableEq (BoundaryLabel Out₁ Out₂)]
variable (A : DetParityAutomaton Alphabet) [DecidableEq A.State]
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

omit [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
    [Fintype (BoundaryLabel Out₁ Out₂)] [DecidableEq (BoundaryLabel Out₁ Out₂)]
    [DecidableEq A.State] in
/-- **Model fact 1, hull form**: paths produced by the paper's reversal
relation lie in the regular hull. -/
theorem mem_rangeHull_of_automatonPathSubstitution
    (Init : (d : Proc) -> TypedPath (AutomatonEdgeType A.State) -> Prop)
    (d : Proc) {x₁ : In₁} {x₂ : In₂} {a b : BoundaryLabel Out₁ Out₂}
    {u out : List (AutomatonEdgeType A.State)}
    (h : AutomatonPathSubstitution A letter x₁ x₂ a u out b) :
    RangeHull (EdgeType := fun _ => AutomatonEdgeType A.State)
      (Param := fun _ => ReversalClosingParam In₁ In₂)
      (automatonSchemeFamily A letter) Init d.other out :=
  mem_rangeHull_of_successorWords (automatonSchemeFamily A letter) Init
    (d := d) (p := (x₁, x₂))
    (automatonPathSubstitution_mem_successorWords A letter h)

end PathSubstitutionHull

/-! ### The initial-path monitor -/

section InitMonitor

variable {EdgeType : Type u} [Fintype EdgeType]

/-- The single-edge monitor: `some none` = empty word,
`some (some e)` = exactly the word `[e]`, `none` = longer. -/
def singleEdgeMonitor : DeterministicMonitorFamily.{u, u, u} EdgeType where
  index := PUnit
  indexFinite := inferInstance
  state _ := Option (Option EdgeType)
  stateFinite _ := by
    classical
    infer_instance
  init _ := some none
  step _ st e :=
    match st with
    | some none => some (some e)
    | _ => none

private theorem singleEdgeMonitor_fold_none (l : List EdgeType) :
    l.foldl ((singleEdgeMonitor (EdgeType := EdgeType)).step PUnit.unit)
        none = none := by
  induction l with
  | nil => rfl
  | cons e l ih => exact ih

/-- Run characterization of the single-edge monitor. -/
theorem runMonitor_singleEdgeMonitor (w : List EdgeType) :
    runMonitor (singleEdgeMonitor (EdgeType := EdgeType)) PUnit.unit w =
      match w with
      | [] => some none
      | [e] => some (some e)
      | _ => none := by
  rcases w with - | ⟨e, - | ⟨e₂, rest⟩⟩
  · rfl
  · rfl
  · show (rest.foldl _ none) = none
    exact singleEdgeMonitor_fold_none rest

/-- The single-edge monitor recognizes single-edge initial paths with
any edge predicate. -/
theorem singleEdgeMonitor_recognizes (P : EdgeType -> Prop)
    (w : List EdgeType) :
    (∃ e, w = [e] ∧ P e) ↔
      ∃ e, runMonitor (singleEdgeMonitor (EdgeType := EdgeType))
          PUnit.unit w = some (some e) ∧ P e := by
  rw [runMonitor_singleEdgeMonitor]
  rcases w with - | ⟨e, - | ⟨e₂, rest⟩⟩
  · constructor
    · rintro ⟨e, he, -⟩
      simp at he
    · rintro ⟨e, he, -⟩
      have he' : (some none : Option (Option EdgeType)) = some (some e) := he
      simp at he'
  · constructor
    · rintro ⟨e', he', hP⟩
      injection he' with h1 h2
      exact ⟨e', by rw [h1], hP⟩
    · rintro ⟨e', he', hP⟩
      injection he' with h1
      injection h1 with h2
      exact ⟨e', by rw [h2], hP⟩
  · constructor
    · rintro ⟨e', he', -⟩
      simp at he'
    · rintro ⟨e', he', -⟩
      simp at he'

end InitMonitor

/-! ### Assembly: recognizers give window determination for the hull -/

section Assembly

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
variable (Init : (d : Proc) -> TypedPath (EdgeType d) -> Prop)

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → Fintype (EdgeType d)]
    [(d : Proc) → DecidableEq (EdgeType d)] [(d : Proc) → Fintype (Param d)]
    [(d : Proc) → DecidableEq (Param d)] in
/--
**Window determination for the hull from recognizers**: if the
enriched base family recognizes `Init` and `IsSuccessorWordFrom`, then
`ReachWindowDetermined` holds for the regular hull at the enriched
base.  With `singleEdgeMonitor` and `rangeWordMonitor` in the family,
both recognizer hypotheses discharge for the concrete model.
-/
theorem rangeHull_reachWindowDetermined_of_recognizers
    (hinit : ∀ d : Proc, ∃ (i : (family d).index)
      (Acc : (family d).state i -> Prop),
      ∀ w, Init d w ↔ Acc (runMonitor (family d) i w))
    (hrange : ∀ e : Proc, ∃ (i : (family e.other).index)
      (Acc : (family e.other).state i -> Prop),
      ∀ w, IsSuccessorWordFrom schemeAt e w ↔
        Acc (runMonitor (family e.other) i w)) :
    ReachWindowDetermined (RangeHull schemeAt Init)
      (fun d => enrichedBaseSemigroup (S0 d) (family d)) := by
  apply rangeHull_reachWindowDetermined
  · intro d u v hval
    obtain ⟨i, Acc, hAcc⟩ := hinit d
    rw [hAcc, hAcc,
      enrichedBase_value_determines_runMonitor (S0 d) (family d) hval i]
  · intro e u v hval
    obtain ⟨i, Acc, hAcc⟩ := hrange e
    rw [hAcc, hAcc,
      enrichedBase_value_determines_runMonitor (S0 e.other) (family e.other)
        hval i]

end Assembly

end DistributedSynthesis
