/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemAutomatonSubstitutionScheme
import DistributedSynthesis.Formalizations.Lemma.LemRangeHull

/-!
# The range-word recognizer monitor

Model fact 2 of the regular-hull program: a finite deterministic
monitor decides membership in the one-step range
`⋃_{p, u} SuccessorWords_p (u)` of the concrete direct-reversal
substitution.

The recognizer is the 3-periodic block checker.  Its state is the
position within the current block (pending one or two edges) together
with the finite set of *feasible* pairs (closing input pair, incoming
threaded boundary label).  A completed block filters the feasible set
through the existential block match (`RangeBlockMatch`): some source
owner, source state, and owned labels produce exactly the observed
three-edge `automatonSubstitutionTriple` block, consuming the incoming
label and emitting the outgoing one.  Acceptance means: at a block
boundary with a nonempty feasible set.

* `localFrom_length` (generic): locally uniform substitution outputs
  have length exactly `3 * |source|`, so non-multiples of three are
  rejected for free.
* `rangeRec_foldCorrect`: the fold from any feasible set accepts
  exactly the words that are locally uniform substitution outputs of
  some source, starting from some feasible pair.
* `isSuccessorWordFrom_automatonSchemeFamily_iff`: acceptance of
  `rangeWordMonitor` decides `IsSuccessorWordFrom` for the concrete
  scheme family -- the second input of
  `rangeHull_reachWindowDetermined`.
* `enrichedBase_value_determines_runMonitor` (generic): any monitor of
  the enriched base family is determined by base summaries, so adding
  `rangeWordMonitor` to the base family discharges
  `ReachWindowDetermined`'s range half.
-/

namespace DistributedSynthesis

universe u v w x y

/-! ### Output length of locally uniform substitutions -/

theorem FiniteSubstitutionScheme.localFrom_length
    {OldEdge : Type u} {NewEdge : Type v} {Label : Type w}
    (scheme : FiniteSubstitutionScheme OldEdge NewEdge Label)
    {left right : Label} {u : List OldEdge} {out : List NewEdge}
    (h : scheme.LocalFrom left u out right) :
    out.length = 3 * u.length := by
  induction u generalizing left out with
  | nil =>
      obtain ⟨rfl, -⟩ := h
      rfl
  | cons q u ih =>
      obtain ⟨emitted, restOutput, mid, choice, -, hemit, -, hrest, rfl⟩ := h
      subst hemit
      simp only [List.length_append, List.length_cons, ih hrest,
        EdgeBlock3.toList, List.length_nil]
      ring

/-! ### The recognizer -/

section Recognizer

variable {Alphabet : Type u} {In₁ : Type v} {In₂ : Type w}
variable {Out₁ : Type x} {Out₂ : Type y}
variable [Fintype In₁] [Fintype In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Fintype (BoundaryLabel Out₁ Out₂)]
variable (A : DetParityAutomaton Alphabet)
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

/-- Feasibility pairs: a closing input pair together with the incoming
threaded boundary label of the next block. -/
abbrev RangeFeasPair := (In₁ × In₂) × BoundaryLabel Out₁ Out₂

/-- Recognizer states: at a block boundary, or one or two edges into
the current block, always carrying the feasible set. -/
abbrev RangeRecState (State : Type u) :=
  Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) ⊕
    (AutomatonEdgeType State ×
      Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
        (Out₁ := Out₁) (Out₂ := Out₂))) ⊕
    (AutomatonEdgeType State × AutomatonEdgeType State ×
      Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
        (Out₁ := Out₁) (Out₂ := Out₂)))

theorem Proc.ne_other (c : Proc) : c ≠ c.other := by
  cases c <;> decide

/-- One block matches: some source owner, state, and owned labels
produce exactly the observed three edges, consuming `lab` and emitting
`lab'`. -/
def RangeBlockMatch (x₁ : In₁) (x₂ : In₂)
    (lab lab' : BoundaryLabel Out₁ Out₂)
    (e₁ e₂ e₃ : AutomatonEdgeType A.State) : Prop :=
  ∃ (c : Proc) (s : A.State) (l : OwnedLabel Out₁ Out₂ c)
    (r : OwnedLabel Out₁ Out₂ c.other)
    (iat : OwnedLabel Out₁ Out₂ c.other) (ias : OwnedLabel Out₁ Out₂ c),
    l.val = lab ∧ r.val = lab' ∧
      automatonSubstitutionTriple A letter x₁ x₂
          ⟨c, c.other, Proc.ne_other c, s⟩ l r iat ias =
        (e₁, e₂, e₃)

open Classical in
/-- The feasible-set update of one completed block. -/
noncomputable def rangeBlockStep
    (feas : Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)))
    (e₁ e₂ e₃ : AutomatonEdgeType A.State) :
    Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)) :=
  Finset.univ.filter fun next =>
    ∃ prev ∈ feas, prev.1 = next.1 ∧
      RangeBlockMatch A letter prev.1.1 prev.1.2 prev.2 next.2 e₁ e₂ e₃

omit [Fintype Out₁] [Fintype Out₂] in
theorem mem_rangeBlockStep
    {feas : Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))}
    {e₁ e₂ e₃ : AutomatonEdgeType A.State}
    {next : RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂)} :
    next ∈ rangeBlockStep A letter feas e₁ e₂ e₃ ↔
      ∃ prev ∈ feas, prev.1 = next.1 ∧
        RangeBlockMatch A letter prev.1.1 prev.1.2 prev.2 next.2 e₁ e₂ e₃ := by
  classical
  simp [rangeBlockStep]

/-- The single-edge step of the recognizer. -/
noncomputable def rangeRecStep :
    RangeRecState (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A.State ->
      AutomatonEdgeType A.State ->
      RangeRecState (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A.State
  | Sum.inl feas, e => Sum.inr (Sum.inl (e, feas))
  | Sum.inr (Sum.inl (e₁, feas)), e => Sum.inr (Sum.inr (e₁, e, feas))
  | Sum.inr (Sum.inr (e₁, e₂, feas)), e =>
      Sum.inl (rangeBlockStep A letter feas e₁ e₂ e)

/-- Acceptance: at a block boundary with a nonempty feasible set. -/
def rangeRecAccepts :
    RangeRecState (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
        A.State -> Prop
  | Sum.inl feas => feas.Nonempty
  | Sum.inr _ => False

/-- The recognizer as a deterministic monitor. -/
noncomputable def rangeWordMonitor :
    DeterministicMonitorFamily (AutomatonEdgeType A.State) where
  index := PUnit
  indexFinite := inferInstance
  state _ :=
    RangeRecState (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁) (Out₂ := Out₂)
      A.State
  stateFinite _ := by
    classical
    infer_instance
  init _ := Sum.inl Finset.univ
  step _ := rangeRecStep A letter

/-! ### Correctness -/

/-- The empty-word case. -/
theorem rangeRec_fold_nil
    (feas : Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))) :
    rangeRecAccepts A
        (([] : List (AutomatonEdgeType A.State)).foldl
          (rangeRecStep A letter) (Sum.inl feas)) ↔
      ∃ pl ∈ feas, ∃ (u : List (AutomatonEdgeType A.State))
        (b : BoundaryLabel Out₁ Out₂),
        (automatonSubstitutionScheme A letter pl.1.1 pl.1.2).LocalFrom
          pl.2 u [] b := by
  simp only [List.foldl_nil]
  constructor
  · rintro ⟨pl, hpl⟩
    exact ⟨pl, hpl, [], pl.2, rfl, rfl⟩
  · rintro ⟨pl, hpl, -, -, -⟩
    exact ⟨pl, hpl⟩

private theorem rangeRec_foldCorrect_aux :
    ∀ (n : Nat) (out : List (AutomatonEdgeType A.State)),
      out.length ≤ n ->
      ∀ feas : Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
        (Out₁ := Out₁) (Out₂ := Out₂)),
        (rangeRecAccepts A
            (out.foldl (rangeRecStep A letter) (Sum.inl feas)) ↔
          ∃ pl ∈ feas, ∃ (u : List (AutomatonEdgeType A.State))
            (b : BoundaryLabel Out₁ Out₂),
            (automatonSubstitutionScheme A letter pl.1.1 pl.1.2).LocalFrom
              pl.2 u out b) := by
  intro n
  induction n with
  | zero =>
      intro out hlen feas
      rw [List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hlen)]
      exact rangeRec_fold_nil A letter feas
  | succ n ih =>
      intro out hlen feas
      rcases out with - | ⟨e₁, - | ⟨e₂, - | ⟨e₃, rest⟩⟩⟩
      · exact rangeRec_fold_nil A letter feas
      · simp only [List.foldl_cons, List.foldl_nil, rangeRecStep]
        constructor
        · exact fun h => h.elim
        · rintro ⟨pl, -, u, b, hlocal⟩
          have := (automatonSubstitutionScheme A letter
            pl.1.1 pl.1.2).localFrom_length hlocal
          simp only [List.length_cons, List.length_nil] at this
          omega
      · simp only [List.foldl_cons, List.foldl_nil, rangeRecStep]
        constructor
        · exact fun h => h.elim
        · rintro ⟨pl, -, u, b, hlocal⟩
          have := (automatonSubstitutionScheme A letter
            pl.1.1 pl.1.2).localFrom_length hlocal
          simp only [List.length_cons, List.length_nil] at this
          omega
      · have hfold :
            (e₁ :: e₂ :: e₃ :: rest).foldl (rangeRecStep A letter)
                (Sum.inl feas) =
              rest.foldl (rangeRecStep A letter)
                (Sum.inl (rangeBlockStep A letter feas e₁ e₂ e₃)) := by
          simp only [List.foldl_cons, rangeRecStep]
        have hrest : rest.length ≤ n := by
          simp only [List.length_cons] at hlen
          omega
        rw [hfold, ih rest hrest (rangeBlockStep A letter feas e₁ e₂ e₃)]
        constructor
        · rintro ⟨next, hnext, u', b, hlocal⟩
          obtain ⟨prev, hprev, hparam, c, s, l, r, iat, ias, hl, hr,
            htriple⟩ := (mem_rangeBlockStep A letter).mp hnext
          refine ⟨prev, hprev,
            ⟨c, c.other, Proc.ne_other c, s⟩ :: u', b,
            [e₁, e₂, e₃], rest, next.2, (l, r, iat, ias), hl, ?_, hr,
            ?_, rfl⟩
          · show [e₁, e₂, e₃] =
              EdgeBlock3.toList
                (automatonSubstitutionTriple A letter prev.1.1 prev.1.2
                  ⟨c, c.other, Proc.ne_other c, s⟩ l r iat ias)
            rw [htriple]
            rfl
          · rw [hparam]
            exact hlocal
        · rintro ⟨pl, hpl, u, b, hlocal⟩
          rcases u with - | ⟨q, u'⟩
          · obtain ⟨h, -⟩ := hlocal
            exact absurd h (List.cons_ne_nil _ _)
          · obtain ⟨c, t, hct, s⟩ := q
            obtain ⟨emitted, restOutput, mid, ⟨l, r, iat, ias⟩, hleft,
              hemit, hright, hrest', houtput⟩ := hlocal
            have ht : t = c.other := by
              cases c <;> cases t <;> first | exact absurd rfl hct | rfl
            subst ht
            subst hemit
            have hcomp :
                e₁ = (automatonSubstitutionTriple A letter pl.1.1 pl.1.2
                    ⟨c, c.other, hct, s⟩ l r iat ias).1 ∧
                e₂ = (automatonSubstitutionTriple A letter pl.1.1 pl.1.2
                    ⟨c, c.other, hct, s⟩ l r iat ias).2.1 ∧
                e₃ = (automatonSubstitutionTriple A letter pl.1.1 pl.1.2
                    ⟨c, c.other, hct, s⟩ l r iat ias).2.2 ∧
                rest = restOutput := by
              have := houtput
              simp only [automatonSubstitutionScheme, EdgeBlock3.toList,
                List.cons_append, List.nil_append, List.cons.injEq] at this
              tauto
            obtain ⟨he₁, he₂, he₃, hrest₂⟩ := hcomp
            refine ⟨(pl.1, mid), ?_, u', b, ?_⟩
            · refine (mem_rangeBlockStep A letter).mpr
                ⟨pl, hpl, rfl, c, s, l, r, iat, ias, hleft, hright, ?_⟩
              rw [he₁, he₂, he₃]
            · rw [<- hrest₂] at hrest'
              exact hrest'

/-- **Recognizer correctness**: the fold from a feasible set accepts
exactly the locally uniform substitution outputs of some source
starting from some feasible pair. -/
theorem rangeRec_foldCorrect (out : List (AutomatonEdgeType A.State))
    (feas : Finset (RangeFeasPair (In₁ := In₁) (In₂ := In₂)
      (Out₁ := Out₁) (Out₂ := Out₂))) :
    rangeRecAccepts A
        (out.foldl (rangeRecStep A letter) (Sum.inl feas)) ↔
      ∃ pl ∈ feas, ∃ (u : List (AutomatonEdgeType A.State))
        (b : BoundaryLabel Out₁ Out₂),
        (automatonSubstitutionScheme A letter pl.1.1 pl.1.2).LocalFrom
          pl.2 u out b :=
  rangeRec_foldCorrect_aux A letter out.length out (le_refl _) feas

/-- **The monitor decides the one-step range**: acceptance of
`rangeWordMonitor` is membership in
`⋃_{p, u} SuccessorWords_p (u)`. -/
theorem rangeWordMonitor_decides (out : List (AutomatonEdgeType A.State)) :
    (∃ (p : In₁ × In₂) (u : List (AutomatonEdgeType A.State)),
        out ∈ (automatonSubstitutionScheme A letter p.1 p.2).SuccessorWords
          u) ↔
      rangeRecAccepts A
        (runMonitor (rangeWordMonitor A letter) PUnit.unit out) := by
  have hrun : runMonitor (rangeWordMonitor A letter) PUnit.unit out =
      out.foldl (rangeRecStep A letter) (Sum.inl Finset.univ) := rfl
  rw [hrun, rangeRec_foldCorrect]
  constructor
  · rintro ⟨p, u, a, b, hlocal⟩
    exact ⟨(p, a), Finset.mem_univ _, u, b, hlocal⟩
  · rintro ⟨pl, -, u, b, hlocal⟩
    exact ⟨pl.1, u, pl.2, b, hlocal⟩

end Recognizer

/-! ### Bridge to the hull and the base family -/

section Bridge

universe s

variable {Alphabet : Type u} {In₁ In₂ Out₁ Out₂ : Type v}
variable [Fintype In₁] [Fintype In₂] [DecidableEq In₁] [DecidableEq In₂]
variable [Fintype Out₁] [Fintype Out₂]
variable [Fintype (BoundaryLabel Out₁ Out₂)]
variable [DecidableEq (BoundaryLabel Out₁ Out₂)]
variable (A : DetParityAutomaton Alphabet)
variable (letter : EdgeExtensionLetter Alphabet In₁ In₂ Out₁ Out₂)

omit [DecidableEq In₁] [DecidableEq In₂] [DecidableEq (BoundaryLabel Out₁ Out₂)] in
/-- The recognizer decides `IsSuccessorWordFrom` for the concrete
scheme family, on either side. -/
theorem isSuccessorWordFrom_automatonSchemeFamily_iff (e : Proc)
    (out : TypedPath (AutomatonEdgeType A.State)) :
    IsSuccessorWordFrom
        (EdgeType := fun _ => AutomatonEdgeType A.State)
        (Param := fun _ => ReversalClosingParam In₁ In₂)
        (automatonSchemeFamily A letter) e out ↔
      rangeRecAccepts A
        (runMonitor (rangeWordMonitor A letter) PUnit.unit out) :=
  rangeWordMonitor_decides A letter out

/-- Any monitor of the enriched base family is determined by base
summaries: adding the recognizer to the family discharges the range
half of `ReachWindowDetermined`. -/
theorem enrichedBase_value_determines_runMonitor
    {EdgeType : Type u}
    (S : PathSummarySemigroup.{u, v} EdgeType)
    (family : DeterministicMonitorFamily.{u, w, x} EdgeType)
    {p q : TypedPath EdgeType}
    (h : pathSummaryValue (enrichedBaseSemigroup S family) p =
      pathSummaryValue (enrichedBaseSemigroup S family) q)
    (i : family.index) :
    runMonitor family i p = runMonitor family i q := by
  have hsum := h
  rw [show enrichedBaseSemigroup S family =
      S.prod (monitorTransitionSemigroup family) from rfl,
    PathSummarySemigroup.pathSummaryValue_prod,
    PathSummarySemigroup.pathSummaryValue_prod] at hsum
  have hM := congrArg Prod.snd hsum
  dsimp only at hM
  have happ := congrFun (congrFun hM i) (family.init i)
  rw [monitorTransition_value, monitorTransition_value] at happ
  exact happ

end Bridge

end DistributedSynthesis
