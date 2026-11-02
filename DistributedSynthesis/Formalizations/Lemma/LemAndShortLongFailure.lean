/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemAffineShortLongExchange

/-!
# A non-affine reachable short--long failure

This is the falsification half of the micro-instance experiment.  The DPA
update is the genuinely non-affine Boolean operation

`s' = s && left && right`.

At radius two and with the XOR raw summary and trivial entry monitors, the
reachable words `100` and `100111100` have the same full concrete code.  This
first gives a failure on the regular hull.  More decisively, `100` and the
depth-three word `100000000000000000000001100` also have the same full code,
and arise from genuinely iteratively reachable sources at the same reversal
parity.  The depth-three word has a same-boundary continuation with prefix
`10` and XOR summary zero, while every continuation of `100` with that prefix
has XOR summary one.  Thus `AutomatonEntryRestartExchange` fails for the
trivial entry abstraction even under the genuine-reachability guard.

This does not refute existence of a better finite entry quotient: such a
quotient may separate the two source words.  It does show that the affine
replace-not-accumulate identity was not a generic property of the concrete
range recognizer and raw summary alone.
-/

namespace DistributedSynthesis

namespace AndShortLong

open AffineShortLong

local instance boundaryLabelDecidableEq :
    DecidableEq (BoundaryLabel Bool Bool) :=
  (Equiv.psumEquivSum Bool Bool).decidableEq

local instance boundaryLabelFintype :
    Fintype (BoundaryLabel Bool Bool) where
  elems := [PSum.inl false, PSum.inl true,
    PSum.inr false, PSum.inr true].toFinset
  complete label := by
    cases label with
    | inl bit => cases bit <;> simp
    | inr bit => cases bit <;> simp

local instance edgeFintype : Fintype (AutomatonEdgeType Bool) where
  elems := [edge Proc.one false, edge Proc.one true,
    edge Proc.two false, edge Proc.two true].toFinset
  complete q := by
    rw [edge_eta q]
    cases q.srcOwner <;> cases q.state <;> simp

local instance ownedLabelFintype (p : Proc) :
    Fintype (OwnedLabel Bool Bool p) where
  elems := [ownedOf p false, ownedOf p true].toFinset
  complete label := by
    have hlabel : label = ownedOf p (boundaryBit label.val) := by
      apply Subtype.ext
      exact (owned_val_eq_boundaryOf p label).trans
        (ownedOf_val p (boundaryBit label.val)).symm
    rw [hlabel]
    cases boundaryBit label.val <;> simp

private abbrev FeasPair :=
  RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
    (Out₁ := Bool) (Out₂ := Bool)

private abbrev PendingOne := AutomatonEdgeType Bool × Finset FeasPair
private abbrev PendingTwo :=
  AutomatonEdgeType Bool × AutomatonEdgeType Bool × Finset FeasPair

local instance pendingOneDecidableEq : DecidableEq PendingOne :=
  instDecidableEqProd

local instance pendingTwoDecidableEq : DecidableEq PendingTwo :=
  instDecidableEqProd

local instance pendingEitherDecidableEq :
    DecidableEq (PendingOne ⊕ PendingTwo) :=
  instDecidableEqSum

local instance rangeRecDecidableEq :
    DecidableEq (Finset FeasPair ⊕ (PendingOne ⊕ PendingTwo)) :=
  instDecidableEqSum

abbrev Alphabet := Bool × Bool

def letter : EdgeExtensionLetter Alphabet PUnit.{1} PUnit.{1} Bool Bool :=
  AffineShortLong.letter

/-- The non-affine Boolean AND automaton. -/
abbrev automaton : DetParityAutomaton Alphabet where
  State := Bool
  stateFinite := inferInstance
  initial := true
  step s a := s && a.1 && a.2
  priority _ := 0

abbrev xorSummary : PathSummarySemigroup (AutomatonEdgeType Bool) :=
  AffineShortLong.xorSummary

abbrev trivialEntryMonitors (_ : Proc) :
    DeterministicMonitorFamily (AutomatonEdgeType Bool) :=
  AffineShortLong.trivialEntryMonitors Proc.one

/-- The depth-one reachable word used in the collision. -/
def short (d : Proc) : List (AutomatonEdgeType Bool) :=
  [edge d true, edge d.other false, edge d false]

/-- A depth-two reachable word with the same concrete radius-two code. -/
def long (d : Proc) : List (AutomatonEdgeType Bool) :=
  [edge d true, edge d.other false, edge d false,
   edge d.other true, edge d true, edge d.other true,
   edge d true, edge d.other false, edge d false]

/-! The repository's recognizer is deliberately noncomputable because its
generic finite alphabets use classical enumeration.  For this concrete
four-label instance we expose the identical computable transition, so the
finite equality can be certified by `native_decide` and then transported back
extensionally.  This is deliberately a compiler-checked falsification probe;
the structural reachability and refutation lemmas themselves use no opaque
model assumption. -/

def rangeBlockMatchComputable
    (lab lab' : BoundaryLabel Bool Bool)
    (e₁ e₂ e₃ : AutomatonEdgeType Bool) : Bool :=
  decide (∃ (c : Proc) (s l r iat ias : Bool),
    lab = boundaryOf c l ∧ lab' = boundaryOf c.other r ∧
      automatonSubstitutionTriple automaton letter PUnit.unit
        PUnit.unit (edge c s) (ownedOf c l) (ownedOf c.other r)
          (ownedOf c.other iat) (ownedOf c ias) = (e₁, e₂, e₃))

theorem rangeBlockMatchComputable_eq_true_iff
    (lab lab' : BoundaryLabel Bool Bool)
    (e₁ e₂ e₃ : AutomatonEdgeType Bool) :
    rangeBlockMatchComputable lab lab' e₁ e₂ e₃ = true ↔
      RangeBlockMatch automaton letter PUnit.unit PUnit.unit
        lab lab' e₁ e₂ e₃ := by
  simp only [rangeBlockMatchComputable, decide_eq_true_eq]
  constructor
  · rintro ⟨c, s, l, r, iat, ias, hl, hr, htriple⟩
    exact ⟨c, s, ownedOf c l, ownedOf c.other r,
      ownedOf c.other iat, ownedOf c ias, by simpa using hl.symm,
      by simpa using hr.symm, htriple⟩
  · rintro ⟨c, s, l, r, iat, ias, hl, hr, htriple⟩
    have hl' : l = ownedOf c (boundaryBit l.val) := by
      apply Subtype.ext
      exact (owned_val_eq_boundaryOf c l).trans
        (ownedOf_val c (boundaryBit l.val)).symm
    have hr' : r = ownedOf c.other (boundaryBit r.val) := by
      apply Subtype.ext
      exact (owned_val_eq_boundaryOf c.other r).trans
        (ownedOf_val c.other (boundaryBit r.val)).symm
    have hiat' : iat = ownedOf c.other (boundaryBit iat.val) := by
      apply Subtype.ext
      exact (owned_val_eq_boundaryOf c.other iat).trans
        (ownedOf_val c.other (boundaryBit iat.val)).symm
    have hias' : ias = ownedOf c (boundaryBit ias.val) := by
      apply Subtype.ext
      exact (owned_val_eq_boundaryOf c ias).trans
        (ownedOf_val c (boundaryBit ias.val)).symm
    refine ⟨c, s, boundaryBit l.val, boundaryBit r.val,
      boundaryBit iat.val, boundaryBit ias.val, ?_, ?_, ?_⟩
    · exact hl.symm.trans (owned_val_eq_boundaryOf c l)
    · exact hr.symm.trans (owned_val_eq_boundaryOf c.other r)
    · simpa only [← hl', ← hr', ← hiat', ← hias'] using htriple

def rangeBlockStepComputable
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (e₁ e₂ e₃ : AutomatonEdgeType Bool) :
    Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)) :=
  Finset.univ.filter fun next =>
    decide (∃ prev, prev ∈ feas ∧ prev.1 = next.1 ∧
      rangeBlockMatchComputable prev.2 next.2 e₁ e₂ e₃ = true)

def rangeRecStepComputable :
    RangeRecState (In₁ := PUnit) (In₂ := PUnit)
        (Out₁ := Bool) (Out₂ := Bool) Bool ->
      AutomatonEdgeType Bool ->
      RangeRecState (In₁ := PUnit) (In₂ := PUnit)
        (Out₁ := Bool) (Out₂ := Bool) Bool
  | Sum.inl feas, e => Sum.inr (Sum.inl (e, feas))
  | Sum.inr (Sum.inl (e₁, feas)), e => Sum.inr (Sum.inr (e₁, e, feas))
  | Sum.inr (Sum.inr (e₁, e₂, feas)), e =>
      Sum.inl (rangeBlockStepComputable feas e₁ e₂ e)

theorem rangeBlockStep_eq_computable
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (e₁ e₂ e₃ : AutomatonEdgeType Bool) :
    rangeBlockStep automaton letter feas e₁ e₂ e₃ =
      rangeBlockStepComputable feas e₁ e₂ e₃ := by
  classical
  ext next
  rw [mem_rangeBlockStep]
  simp only [rangeBlockStepComputable, Finset.mem_filter, Finset.mem_univ,
    decide_eq_true_eq, true_and,
    rangeBlockMatchComputable_eq_true_iff]

theorem rangeRecStep_eq_computable
    (st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool)
    (e : AutomatonEdgeType Bool) :
    rangeRecStep automaton letter st e = rangeRecStepComputable st e := by
  rcases st with feas | pending
  · rfl
  · rcases pending with pending | pending
    · rfl
    · rcases pending with ⟨e₁, e₂, feas⟩
      simp only [rangeRecStep, rangeRecStepComputable]
      rw [rangeBlockStep_eq_computable]

theorem rangeRec_fold_eq_computable
    (word : List (AutomatonEdgeType Bool))
    (st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool) :
    word.foldl (rangeRecStep automaton letter) st =
      word.foldl rangeRecStepComputable st := by
  induction word generalizing st with
  | nil => rfl
  | cons e word ih =>
      simp only [List.foldl_cons]
      rw [rangeRecStep_eq_computable]
      exact ih _

/-- The machine-checked full source-code collision found by the finite probe. -/
theorem rangeRec_short_long (d : Proc) :
    ∀ st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool,
      (short d).foldl (rangeRecStep automaton letter) st =
        (long d).foldl (rangeRecStep automaton letter) st := by
  intro st
  rw [rangeRec_fold_eq_computable, rangeRec_fold_eq_computable]
  cases d <;> native_decide +revert

/-- The machine-checked full source-code collision found by the finite probe. -/
theorem concreteCode_short_long (d : Proc) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (short d) =
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (long d) := by
  classical
  unfold finiteSummaryWindowAbstraction
  apply Prod.ext
  · rw [show concreteBase automaton letter xorSummary trivialEntryMonitors d =
        xorSummary.prod (monitorTransitionSemigroup
          (concreteMonitorFamily automaton letter trivialEntryMonitors d)) from rfl,
      PathSummarySemigroup.pathSummaryValue_prod,
      PathSummarySemigroup.pathSummaryValue_prod]
    apply Prod.ext
    · cases d <;> rfl
    · funext i st
      change pathSummaryValue
          (monitorTransitionSemigroup
            (concreteMonitorFamily automaton letter trivialEntryMonitors d))
          (short d) i st =
        pathSummaryValue
          (monitorTransitionSemigroup
            (concreteMonitorFamily automaton letter trivialEntryMonitors d))
          (long d) i st
      rw [monitorTransition_value, monitorTransition_value]
      rcases i with i | i
      · rcases i with i | i
        · rcases i with ⟨⟩
          rfl
        · rcases i with ⟨⟩
          rcases st with _ | st
          · rfl
          · rcases st with _ | _ <;> rfl
      · rcases i with ⟨⟩
        exact rangeRec_short_long d st
  · apply Prod.ext <;> cases d <;> rfl

/-! ### Reachability and the separating continuation -/

def block (d : Proc) (state l r iat ias : Bool) :
    List (AutomatonEdgeType Bool) :=
  EdgeBlock3.toList (automatonSubstitutionTriple automaton letter
    PUnit.unit PUnit.unit (edge d state) (ownedOf d l)
      (ownedOf d.other r) (ownedOf d.other iat) (ownedOf d ias))

private theorem prependBlock (d : Proc) (state l r iat ias : Bool)
    (restOld restOut : List (AutomatonEdgeType Bool))
    (final : BoundaryLabel Bool Bool)
    (hrest :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other r) restOld restOut final) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d l) (edge d state :: restOld)
      (block d state l r iat ias ++ restOut) final := by
  refine ⟨block d state l r iat ias, restOut, boundaryOf d.other r,
    (ownedOf d l, ownedOf d.other r, ownedOf d.other iat, ownedOf d ias),
    ?_, ?_, ?_, hrest, rfl⟩
  · change (ownedOf d l).val = boundaryOf d l
    simp
  · rfl
  · change (ownedOf d.other r).val = boundaryOf d.other r
    simp

/-- Alternating-owner state word, used to compress long runs of zero
choices in the same-parity witness. -/
def alternatingPath : Proc -> List Bool -> List (AutomatonEdgeType Bool)
  | _, [] => []
  | d, state :: states => edge d state :: alternatingPath d.other states

/-- Owner after traversing an alternating path. -/
def afterProc : Proc -> List Bool -> Proc
  | d, [] => d
  | d, _ :: states => afterProc d.other states

/-- Output of choosing zero for all four local labels along an alternating
state word. -/
def zeroExpansion : Proc -> List Bool -> List (AutomatonEdgeType Bool)
  | _, [] => []
  | d, state :: states =>
      block d state false false false false ++ zeroExpansion d.other states

/-- A run of zero choices may be prepended to any compatible tail. -/
private theorem prependZeroExpansion (d : Proc) (states : List Bool)
    (restOld restOut : List (AutomatonEdgeType Bool))
    (final : BoundaryLabel Bool Bool)
    (hrest :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf (afterProc d states) false) restOld restOut final) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d false) (alternatingPath d states ++ restOld)
      (zeroExpansion d states ++ restOut) final := by
  induction states generalizing d with
  | nil => simpa [alternatingPath, zeroExpansion, afterProc] using hrest
  | cons state states ih =>
      simp only [alternatingPath, zeroExpansion, List.cons_append]
      have htail := ih d.other hrest
      simpa [List.append_assoc] using
        prependBlock d state false false false false
          (alternatingPath d.other states ++ restOld)
          (zeroExpansion d.other states ++ restOut) final htail

@[simp] theorem block_100 (d : Proc) :
    block d true true false true false =
      [edge d true, edge d.other false, edge d false] := by
  cases d <;> rfl

@[simp] theorem block_100_to_true (d : Proc) :
    block d true true true true false =
      [edge d true, edge d.other false, edge d false] := by
  cases d <;> rfl

@[simp] theorem block_111 (d : Proc) :
    block d true true true true true =
      [edge d true, edge d.other true, edge d true] := by
  cases d <;> rfl

@[simp] theorem block_false_zero (d : Proc) (l r iat ias : Bool) :
    block d false l r iat ias =
      [edge d false, edge d.other false, edge d false] := by
  cases d <;> cases l <;> cases r <;> cases iat <;> cases ias <;> rfl

@[simp] theorem block_true_zero (d : Proc) :
    block d true false false false false =
      [edge d false, edge d.other false, edge d false] := by
  cases d <;> rfl

@[simp] theorem block_true_000 (d : Proc) :
    block d true false true false false =
      [edge d false, edge d.other false, edge d false] := by
  cases d <;> rfl

@[simp] theorem block_010 (d : Proc) :
    block d true false false true true =
      [edge d false, edge d.other true, edge d false] := by
  cases d <;> rfl

@[simp] theorem block_001 (d : Proc) :
    block d true false true false true =
      [edge d false, edge d.other false, edge d true] := by
  cases d <;> rfl

def source (d : Proc) : List (AutomatonEdgeType Bool) := [edge d true]

def middle (d : Proc) : List (AutomatonEdgeType Bool) :=
  [edge d true, edge d.other true, edge d true]

def initialEdge (d : Proc) (q : AutomatonEdgeType Bool) : Prop :=
  q = edge d true

theorem short_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (source d) (short d) (boundaryOf d.other false) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other false) [] [] (boundaryOf d.other false) :=
    ⟨rfl, rfl⟩
  simpa [source, short] using
    prependBlock d true true false true false [] []
      (boundaryOf d.other false) hnil

theorem middle_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (source d) (middle d) (boundaryOf d.other true) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other true) [] [] (boundaryOf d.other true) :=
    ⟨rfl, rfl⟩
  simpa [source, middle] using
    prependBlock d true true true true true [] []
      (boundaryOf d.other true) hnil

theorem long_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (middle d) (long d) (boundaryOf d.other false) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other false) [] [] (boundaryOf d.other false) :=
    ⟨rfl, rfl⟩
  have h₃ := prependBlock d true true false true false [] []
    (boundaryOf d.other false) hnil
  have h₂ := prependBlock d.other true true true true true
    [edge d true] (block d true true false true false)
    (boundaryOf d.other false) (by simpa using h₃)
  have h₁ := prependBlock d true true true true false
    [edge d.other true, edge d true]
    (block d.other true true true true true ++
      block d true true false true false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₂)
  simpa [middle, long, List.append_assoc] using h₁

theorem source_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d (source d) := by
  exact .initial ⟨edge d true, rfl, rfl⟩

theorem short_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d.other (short d) := by
  refine .step (param := (PUnit.unit, PUnit.unit))
    (source_iterativelyReachable d) ?_
  exact ⟨boundaryOf d true, boundaryOf d.other false, short_localFrom d⟩

theorem middle_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d.other (middle d) := by
  refine .step (param := (PUnit.unit, PUnit.unit))
    (source_iterativelyReachable d) ?_
  exact ⟨boundaryOf d true, boundaryOf d.other true, middle_localFrom d⟩

theorem long_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d (long d) := by
  have h := IterativelyReachable.step (param := (PUnit.unit, PUnit.unit))
    (middle_iterativelyReachable d)
    ⟨boundaryOf d true, boundaryOf d.other false, long_localFrom d⟩
  simpa using h

/-! ### A same-parity depth-one/depth-three collision -/

/-- A genuinely depth-two predecessor.  In states it is `100000111`. -/
def deepPredecessor (d : Proc) : List (AutomatonEdgeType Bool) :=
  block d true true false true false ++
  block d.other true false true false false ++
  block d true true true true true

/-- The depth-three source-code collision.  In states it is
`100000000000000000000001100`. -/
def deep (d : Proc) : List (AutomatonEdgeType Bool) :=
  block d true true false true false ++
  zeroExpansion d.other [false, false, false, false, false, true] ++
  block d.other true false true false true ++
  block d true true false true false

theorem deepPredecessor_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (middle d) (deepPredecessor d)
      (boundaryOf d.other true) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other true) [] [] (boundaryOf d.other true) :=
    ⟨rfl, rfl⟩
  have h₃ := prependBlock d true true true true true [] []
    (boundaryOf d.other true) hnil
  have h₂ := prependBlock d.other true false true false false
    [edge d true] (block d true true true true true)
    (boundaryOf d.other true) (by simpa using h₃)
  have h₁ := prependBlock d true true false true false
    [edge d.other true, edge d true]
    (block d.other true false true false false ++
      block d true true true true true)
    (boundaryOf d.other true) (by simpa [List.append_assoc] using h₂)
  simpa [middle, deepPredecessor, List.append_assoc] using h₁

theorem deep_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (deepPredecessor d) (deep d)
      (boundaryOf d.other false) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other false) [] [] (boundaryOf d.other false) :=
    ⟨rfl, rfl⟩
  have h₉ := prependBlock d true true false true false [] []
    (boundaryOf d.other false) hnil
  have h₈ := prependBlock d.other true false true false true
    [edge d true] (block d true true false true false)
    (boundaryOf d.other false) (by simpa using h₉)
  have hzero := prependZeroExpansion d.other
    [false, false, false, false, false, true]
    [edge d.other true, edge d true]
    (block d.other true false true false true ++
      block d true true false true false)
    (boundaryOf d.other false) (by simpa [afterProc] using h₈)
  have h₁ := prependBlock d true true false true false
    (alternatingPath d.other [false, false, false, false, false, true] ++
      [edge d.other true, edge d true])
    (zeroExpansion d.other [false, false, false, false, false, true] ++
      block d.other true false true false true ++
      block d true true false true false)
    (boundaryOf d.other false) (by simpa using hzero)
  simpa [deepPredecessor, deep, alternatingPath, List.append_assoc] using h₁

theorem deepPredecessor_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d (deepPredecessor d) := by
  have h := IterativelyReachable.step (param := (PUnit.unit, PUnit.unit))
    (middle_iterativelyReachable d)
    ⟨boundaryOf d true, boundaryOf d.other true,
      deepPredecessor_localFrom d⟩
  simpa using h

theorem deep_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d.other (deep d) := by
  refine .step (param := (PUnit.unit, PUnit.unit))
    (deepPredecessor_iterativelyReachable d) ?_
  exact ⟨boundaryOf d true, boundaryOf d.other false, deep_localFrom d⟩

/-- Full range-recognizer transition equality for the same-parity collision. -/
theorem rangeRec_short_deep (d : Proc) :
    ∀ st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool,
      (short d).foldl (rangeRecStep automaton letter) st =
        (deep d).foldl (rangeRecStep automaton letter) st := by
  intro st
  rw [rangeRec_fold_eq_computable, rangeRec_fold_eq_computable]
  cases d <;> native_decide +revert

/-- The depth-one and depth-three words have equal full concrete codes,
including both endpoint windows and the complete recognizer transition
functions. -/
theorem concreteCode_short_deep (d : Proc) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (short d) =
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (deep d) := by
  classical
  unfold finiteSummaryWindowAbstraction
  apply Prod.ext
  · rw [show concreteBase automaton letter xorSummary trivialEntryMonitors d =
        xorSummary.prod (monitorTransitionSemigroup
          (concreteMonitorFamily automaton letter trivialEntryMonitors d)) from rfl,
      PathSummarySemigroup.pathSummaryValue_prod,
      PathSummarySemigroup.pathSummaryValue_prod]
    apply Prod.ext
    · cases d <;> rfl
    · funext i st
      change pathSummaryValue
          (monitorTransitionSemigroup
            (concreteMonitorFamily automaton letter trivialEntryMonitors d))
          (short d) i st =
        pathSummaryValue
          (monitorTransitionSemigroup
            (concreteMonitorFamily automaton letter trivialEntryMonitors d))
          (deep d) i st
      rw [monitorTransition_value, monitorTransition_value]
      rcases i with i | i
      · rcases i with i | i
        · rcases i with ⟨⟩
          rfl
        · rcases i with ⟨⟩
          rcases st with _ | st
          · rfl
          · rcases st with _ | _ <;> rfl
      · rcases i with ⟨⟩
        exact rangeRec_short_deep d st
  · apply Prod.ext <;> cases d <;> rfl

/-- The depth-three continuation available only from the long collision
representative at the tested code.  In block notation its states are
`100 (000)^5 010 (000)^2`. -/
def witness (d : Proc) : List (AutomatonEdgeType Bool) :=
  block d true true false true false ++
  block d.other false false false false false ++
  block d false false false false false ++
  block d.other true false false false false ++
  block d true false false false false ++
  block d.other true false false false false ++
  block d true false false true true ++
  block d.other false false false false false ++
  block d false false false false false

theorem witness_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (long d) (witness d) (boundaryOf d.other false) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other false) [] [] (boundaryOf d.other false) :=
    ⟨rfl, rfl⟩
  have h₉ := prependBlock d false false false false false [] []
    (boundaryOf d.other false) hnil
  have h₈ := prependBlock d.other false false false false false
    [edge d false] (block d false false false false false)
    (boundaryOf d.other false) (by simpa using h₉)
  have h₇ := prependBlock d true false false true true
    [edge d.other false, edge d false]
    (block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₈)
  have h₆ := prependBlock d.other true false false false false
    [edge d true, edge d.other false, edge d false]
    (block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₇)
  have h₅ := prependBlock d true false false false false
    [edge d.other true, edge d true, edge d.other false, edge d false]
    (block d.other true false false false false ++
      block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₆)
  have h₄ := prependBlock d.other true false false false false
    [edge d true, edge d.other true, edge d true, edge d.other false, edge d false]
    (block d true false false false false ++
      block d.other true false false false false ++
      block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₅)
  have h₃ := prependBlock d false false false false false
    [edge d.other true, edge d true, edge d.other true, edge d true,
      edge d.other false, edge d false]
    (block d.other true false false false false ++
      block d true false false false false ++
      block d.other true false false false false ++
      block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₄)
  have h₂ := prependBlock d.other false false false false false
    [edge d false, edge d.other true, edge d true, edge d.other true,
      edge d true, edge d.other false, edge d false]
    (block d false false false false false ++
      block d.other true false false false false ++
      block d true false false false false ++
      block d.other true false false false false ++
      block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₃)
  have h₁ := prependBlock d true true false true false
    [edge d.other false, edge d false, edge d.other true, edge d true,
      edge d.other true, edge d true, edge d.other false, edge d false]
    (block d.other false false false false false ++
      block d false false false false false ++
      block d.other true false false false false ++
      block d true false false false false ++
      block d.other true false false false false ++
      block d true false false true true ++
      block d.other false false false false false ++
      block d false false false false false)
    (boundaryOf d.other false) (by simpa [List.append_assoc] using h₂)
  simpa [long, witness, List.append_assoc] using h₁

/-- The unmatched continuation of the genuine depth-three collision.  Its
states are `100`, then 23 zero-choice blocks, then `010`, then two zero
blocks; as a bit word it has length 81 and ones exactly at positions 0 and
73. -/
def deepWitness (d : Proc) : List (AutomatonEdgeType Bool) :=
  block d true true false true false ++
  zeroExpansion d.other (List.replicate 22 false ++ [true]) ++
  block d true false false true true ++
  zeroExpansion d.other [false, false]

theorem deepWitness_localFrom (d : Proc) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d true) (deep d) (deepWitness d)
      (boundaryOf d.other false) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other false) [] [] (boundaryOf d.other false) :=
    ⟨rfl, rfl⟩
  have htail := prependZeroExpansion d.other [false, false] [] []
    (boundaryOf d.other false) (by simpa [afterProc] using hnil)
  have hspecial := prependBlock d true false false true true
    (alternatingPath d.other [false, false])
    (zeroExpansion d.other [false, false])
    (boundaryOf d.other false) (by simpa using htail)
  have hmiddle := prependZeroExpansion d.other
    (List.replicate 22 false ++ [true])
    (edge d true :: alternatingPath d.other [false, false])
    (block d true false false true true ++
      zeroExpansion d.other [false, false])
    (boundaryOf d.other false) (by simpa [afterProc] using hspecial)
  have hfirst := prependBlock d true true false true false
    (alternatingPath d.other (List.replicate 22 false ++ [true]) ++
      edge d true :: alternatingPath d.other [false, false])
    (zeroExpansion d.other (List.replicate 22 false ++ [true]) ++
      block d true false false true true ++
      zeroExpansion d.other [false, false])
    (boundaryOf d.other false) (by simpa using hmiddle)
  simpa [deep, deepWitness, alternatingPath, zeroExpansion,
    List.append_assoc] using hfirst

def codeProjection (word : List (AutomatonEdgeType Bool)) :
    Bool × List (AutomatonEdgeType Bool) :=
  (pathSummaryValue xorSummary word, (boundedPrefixAtMost 2 word).toList)

set_option maxRecDepth 10000 in
/-- The two separating continuations agree on the only two components used
by the short-word impossibility proof: raw XOR and the radius-two prefix. -/
theorem codeProjection_witness_deepWitness (d : Proc) :
    codeProjection (witness d) = codeProjection (deepWitness d) := by
  cases d <;> rfl

theorem choiceBlock_eq_block (d : Proc) (state : Bool)
    (choice : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice (edge d state)) :
    EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block (edge d state) choice) =
      block d state
        (boundaryBit choice.1.val) (boundaryBit choice.2.1.val)
        (boundaryBit choice.2.2.1.val) (boundaryBit choice.2.2.2.val) := by
  rcases choice with ⟨l, r, iat, ias⟩
  have hl : l = ownedOf d (boundaryBit l.val) := by
    apply Subtype.ext
    exact (owned_val_eq_boundaryOf d l).trans
      (ownedOf_val d (boundaryBit l.val)).symm
  have hr : r = ownedOf d.other (boundaryBit r.val) := by
    apply Subtype.ext
    exact (owned_val_eq_boundaryOf d.other r).trans
      (ownedOf_val d.other (boundaryBit r.val)).symm
  have hiat : iat = ownedOf d.other (boundaryBit iat.val) := by
    apply Subtype.ext
    exact (owned_val_eq_boundaryOf d.other iat).trans
      (ownedOf_val d.other (boundaryBit iat.val)).symm
  have hias : ias = ownedOf d (boundaryBit ias.val) := by
    apply Subtype.ext
    exact (owned_val_eq_boundaryOf d ias).trans
      (ownedOf_val d (boundaryBit ias.val)).symm
  change EdgeBlock3.toList (automatonSubstitutionTriple automaton letter
    PUnit.unit PUnit.unit (edge d state) l r iat ias) = _
  rw [hl, hr, hiat, hias]
  simp only [ownedOf_val, boundaryBit_boundaryOf]
  rfl

/-- The finite separating calculation.  Thread-compatible choices for a
continuation of `100` cannot simultaneously have the witness prefix `10` and
its even XOR summary. -/
theorem shortProjection_ne_witness (d : Proc)
    (l₁ r₁ iat₁ ias₁ l₂ r₂ iat₂ ias₂
      l₃ r₃ iat₃ ias₃ : Bool)
    (hleft : l₁ = true) (hthread₁ : r₁ = l₂)
    (hthread₂ : r₂ = l₃) (hright : r₃ = false) :
    codeProjection
        (block d true l₁ r₁ iat₁ ias₁ ++
          block d.other false l₂ r₂ iat₂ ias₂ ++
          block d false l₃ r₃ iat₃ ias₃) ≠
      codeProjection (witness d) := by
  cases d <;> decide +revert

/-- Every same-boundary continuation of the short word is already separated
from the witness by raw XOR plus the first two emitted edges. -/
theorem no_short_continuation_projection_match (d : Proc)
    (w : List (AutomatonEdgeType Bool))
    (hlocal :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d true) (short d) w (boundaryOf d.other false)) :
    codeProjection w ≠ codeProjection (witness d) := by
  intro hproj
  change (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).LocalFrom (boundaryOf d true)
      [edge d true, edge d.other false, edge d false] w
      (boundaryOf d.other false) at hlocal
  rcases hlocal with
    ⟨em₁, rest₁, mid₁, c₁, hl₁, hem₁, hr₁, hrest₁, hw₁⟩
  rcases hrest₁ with
    ⟨em₂, rest₂, mid₂, c₂, hl₂, hem₂, hr₂, hrest₂, hw₂⟩
  rcases hrest₂ with
    ⟨em₃, rest₃, mid₃, c₃, hl₃, hem₃, hr₃, hrest₃, hw₃⟩
  rcases hrest₃ with ⟨hrest₃, hright⟩
  subst rest₃
  subst em₁
  subst em₂
  subst em₃
  rcases c₁ with ⟨l₁, r₁, iat₁, ias₁⟩
  rcases c₂ with ⟨l₂, r₂, iat₂, ias₂⟩
  rcases c₃ with ⟨l₃, r₃, iat₃, ias₃⟩
  change l₁.val = boundaryOf d true at hl₁
  change r₁.val = mid₁ at hr₁
  change l₂.val = mid₁ at hl₂
  change r₂.val = mid₂ at hr₂
  change l₃.val = mid₂ at hl₃
  change r₃.val = mid₃ at hr₃
  have hleftBit : boundaryBit l₁.val = true := by
    have h := congrArg boundaryBit hl₁
    simpa using h
  have hthread₁ : boundaryBit r₁.val = boundaryBit l₂.val :=
    congrArg boundaryBit (hr₁.trans hl₂.symm)
  have hthread₂ : boundaryBit r₂.val = boundaryBit l₃.val :=
    congrArg boundaryBit (hr₂.trans hl₃.symm)
  have hrightBit : boundaryBit r₃.val = false := by
    have h := congrArg boundaryBit (hr₃.trans hright.symm)
    simpa using h
  have hw : w =
      EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).block (edge d true)
            (l₁, r₁, iat₁, ias₁)) ++
        EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).block (edge d.other false)
            (l₂, r₂, iat₂, ias₂)) ++
        EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).block (edge d false)
            (l₃, r₃, iat₃, ias₃)) := by
    simpa [List.append_assoc] using hw₁.trans (congrArg
      (EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block (edge d true)
          (l₁, r₁, iat₁, ias₁)) ++ ·)
      (hw₂.trans (by simpa using hw₃)))
  rw [hw, choiceBlock_eq_block d true,
    choiceBlock_eq_block d.other false, choiceBlock_eq_block d false] at hproj
  exact (shortProjection_ne_witness d
    (boundaryBit l₁.val) (boundaryBit r₁.val)
    (boundaryBit iat₁.val) (boundaryBit ias₁.val)
    (boundaryBit l₂.val) (boundaryBit r₂.val)
    (boundaryBit iat₂.val) (boundaryBit ias₂.val)
    (boundaryBit l₃.val) (boundaryBit r₃.val)
    (boundaryBit iat₃.val) (boundaryBit ias₃.val)
    hleftBit hthread₁ hthread₂ hrightBit) hproj

theorem codeProjection_eq_of_concreteCode_eq (d : Proc)
    {u v : List (AutomatonEdgeType Bool)}
    (hcode :
      finiteSummaryWindowAbstraction
          (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 u =
        finiteSummaryWindowAbstraction
          (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 v) :
    codeProjection u = codeProjection v := by
  apply Prod.ext
  · change pathSummaryValue xorSummary u = pathSummaryValue xorSummary v
    simpa only [finiteSummaryWindowAbstraction, concreteBase,
      enrichedBaseSemigroup, PathSummarySemigroup.pathSummaryValue_prod]
      using congrArg (fun code => code.1.1) hcode
  · change (boundedPrefixAtMost 2 u).toList =
      (boundedPrefixAtMost 2 v).toList
    exact congrArg BoundedEndpointWindow.toList
      (congrArg (fun code => code.2.1) hcode)

theorem no_short_continuation_code_match (d : Proc)
    (w : List (AutomatonEdgeType Bool))
    (hlocal :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d true) (short d) w (boundaryOf d.other false)) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 w ≠
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (witness d) := by
  intro hcode
  exact no_short_continuation_projection_match d w hlocal
    (codeProjection_eq_of_concreteCode_eq d hcode)

/-- The same separation for the length-81 continuation of the genuine
same-parity collision. -/
theorem no_short_continuation_code_match_deep (d : Proc)
    (w : List (AutomatonEdgeType Bool))
    (hlocal :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d true) (short d) w (boundaryOf d.other false)) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 w ≠
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (deepWitness d) := by
  intro hcode
  apply no_short_continuation_projection_match d w hlocal
  exact (codeProjection_eq_of_concreteCode_eq d hcode).trans
    (codeProjection_witness_deepWitness d).symm

/-! ### The exact regular-hull failure

The two source words below are both in the regular hull at the displayed
side.  The long source enters through the range half of the hull, using the
fact that `automatonSchemeFamily` has the same concrete substitution scheme
at both sides.  Its genuine iterated derivation has the opposite side parity;
therefore this certificate refutes the hull-level exchange with trivial entry
monitors, but is deliberately not advertised as a same-side iterated
reachability counterexample.
-/

/-- The non-affine depth-one/depth-two collision, packaged in the exact
failure interface consumed by the concrete restart theorem. -/
def regularHullFailure (d : Proc) :
    EntryRestartExchangeFailure automaton letter xorSummary
      trivialEntryMonitors 2 initialEdge where
  side := d
  paramU := (PUnit.unit, PUnit.unit)
  paramV := (PUnit.unit, PUnit.unit)
  sourceU := middle d
  sourceV := source d
  out := long d
  out' := short d
  reachU := by
    have hmem : middle d ∈
        (automatonSchemeFamily automaton letter d.other
          (PUnit.unit, PUnit.unit)).SuccessorWords (source d) :=
      ⟨boundaryOf d true, boundaryOf d.other true, middle_localFrom d⟩
    simpa using mem_rangeHull_of_successorWords
      (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) hmem
  reachV := by
    apply mem_rangeHull_of_init
    exact ⟨edge d true, rfl, rfl⟩
  memOut :=
    ⟨boundaryOf d true, boundaryOf d.other false, long_localFrom d⟩
  memOut' :=
    ⟨boundaryOf d true, boundaryOf d.other false, short_localFrom d⟩
  codeEq := by
    simpa [trivialEntryMonitors] using (concreteCode_short_long d).symm
  contParam := (PUnit.unit, PUnit.unit)
  left := boundaryOf d true
  right := boundaryOf d.other false
  cont := witness d
  contLocal := witness_localFrom d
  separated := no_short_continuation_code_match d

/-- Consequently, the regular-hull restart exchange is false for the raw XOR
summary and the trivial entry family. -/
theorem not_automatonEntryRestartExchange_trivial (d : Proc) :
    ¬ AutomatonEntryRestartExchange automaton letter xorSummary
      trivialEntryMonitors 2 initialEdge :=
  not_automatonEntryRestartExchange_of_failure automaton letter xorSummary
    trivialEntryMonitors (regularHullFailure d)

/-! ### The guarded same-parity failure -/

/-- The stronger certificate: both sources are genuinely iteratively
reachable at the *same* side.  Thus this failure survives the guard that
filters spurious regular-hull representatives. -/
def sameParityFailure (d : Proc) :
    EntryRestartExchangeFailure automaton letter xorSummary
      trivialEntryMonitors 2 initialEdge where
  side := d
  paramU := (PUnit.unit, PUnit.unit)
  paramV := (PUnit.unit, PUnit.unit)
  sourceU := deepPredecessor d
  sourceV := source d
  out := deep d
  out' := short d
  reachU := rangeHull_of_iterativelyReachable
    (automatonSchemeFamily automaton letter)
    (singleEdgeInit automaton initialEdge)
    (deepPredecessor_iterativelyReachable d)
  reachV := rangeHull_of_iterativelyReachable
    (automatonSchemeFamily automaton letter)
    (singleEdgeInit automaton initialEdge)
    (source_iterativelyReachable d)
  memOut :=
    ⟨boundaryOf d true, boundaryOf d.other false, deep_localFrom d⟩
  memOut' :=
    ⟨boundaryOf d true, boundaryOf d.other false, short_localFrom d⟩
  codeEq := by
    simpa [trivialEntryMonitors] using (concreteCode_short_deep d).symm
  contParam := (PUnit.unit, PUnit.unit)
  left := boundaryOf d true
  right := boundaryOf d.other false
  cont := deepWitness d
  contLocal := deepWitness_localFrom d
  separated := no_short_continuation_code_match_deep d

/-- The trivial entry abstraction fails even when the exchange is restricted
to sources generated at matching iterated-reachability parity. -/
theorem not_automatonEntryRestartExchange_trivial_sameParity (d : Proc) :
    ¬ AutomatonEntryRestartExchange automaton letter xorSummary
      trivialEntryMonitors 2 initialEdge :=
  not_automatonEntryRestartExchange_of_failure automaton letter xorSummary
    trivialEntryMonitors (sameParityFailure d)

/-! ### The first profile layer separates the collision -/

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 10000 in
/-- The same-parity collision is separated by level one of the saturation
tower.  This is the precise theorem that `E₀` is not a fixed point: the
level-zero concrete codes agree, while the profile component added at level
one records the unmatched continuation. -/
theorem saturationLevel_one_deep_ne_short (d : Proc) :
    pathSummaryValue
        (saturationLevel (automatonSchemeFamily automaton letter)
          (concreteBase automaton letter xorSummary trivialEntryMonitors)
          2 1 d.other) (deep d) ≠
      pathSummaryValue
        (saturationLevel (automatonSchemeFamily automaton letter)
          (concreteBase automaton letter xorSummary trivialEntryMonitors)
          2 1 d.other) (short d) := by
  intro heq
  have hsplit :=
    (saturationLevel_succ_value_eq_iff
      (automatonSchemeFamily automaton letter)
      (concreteBase automaton letter xorSummary trivialEntryMonitors)
      2 0 d.other (deep d) (short d)).mp heq
  have hprofile := hsplit.2 (PUnit.unit, PUnit.unit)
  let S := concreteBase automaton letter xorSummary trivialEntryMonitors d
  let value := finiteSummaryWindowAbstraction S 2 (deepWitness d)
  letI : DecidableEq S.Summary := Classical.decEq _
  letI : DecidableEq (AutomatonEdgeType automaton.State) := by
    dsimp [automaton]
    infer_instance
  have hlaw : PathSummaryLawful S := by
    exact concreteBase_lawful automaton letter xorSummary trivialEntryMonitors
      xorSummary_lawful d
  have hprofile' :
      pathSummaryValue
          (windowProfileSemigroup
            (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit)
            S 2) (deep d) =
        pathSummaryValue
          (windowProfileSemigroup
            (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit)
            S 2) (short d) := by
    simpa [S, saturationLevel] using hprofile
  unfold windowProfileSemigroup at hprofile'
  have hexchange :
      (∃ out,
        (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
          (boundaryOf d true) (deep d) out (boundaryOf d.other false) ∧
        finiteSummaryWindowAbstraction S 2 out = value) ↔
      (∃ out,
        (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
          (boundaryOf d true) (short d) out (boundaryOf d.other false) ∧
        finiteSummaryWindowAbstraction S 2 out = value) := by
    exact
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).localFrom_value_iff_of_profile_eq _ _ _
          (finiteSummaryWindowAbstraction_nil S 2)
          (finiteSummaryWindowAbstraction_append S 2 hlaw) hprofile'
          (boundaryOf d true) (boundaryOf d.other false) value
  obtain ⟨w, hlocal, hcode⟩ := hexchange.mp
    ⟨deepWitness d, deepWitness_localFrom d, rfl⟩
  exact no_short_continuation_code_match_deep d w hlocal (by
    simpa [S, value] using hcode)

/-- The trivially enriched abstraction is not merely insufficient for the
entry-restart exchange: it is not a fixed point of the saturation tower.
The counterexample uses genuine same-parity reachable paths. -/
theorem not_saturationStabilizesAt_zero :
    ¬ SaturationStabilizesAt (automatonSchemeFamily automaton letter)
      (concreteBase automaton letter xorSummary trivialEntryMonitors) 2 0 := by
  intro hstab
  have hcode := concreteCode_short_deep Proc.one
  have hsummary :
      pathSummaryValue
          (concreteBase automaton letter xorSummary trivialEntryMonitors
            Proc.one) (short Proc.one) =
        pathSummaryValue
          (concreteBase automaton letter xorSummary trivialEntryMonitors
            Proc.one) (deep Proc.one) :=
    congrArg Prod.fst hcode
  have hpref : prefixAtMost 2 (short Proc.one) =
      prefixAtMost 2 (deep Proc.one) := by
    have h := congrArg
      (fun code => code.2.1.toList) hcode
    simpa [finiteSummaryWindowAbstraction] using h
  have hsuff : suffixAtMost 2 (short Proc.one) =
      suffixAtMost 2 (deep Proc.one) := by
    have h := congrArg
      (fun code => code.2.2.toList) hcode
    simpa [finiteSummaryWindowAbstraction] using h
  have hwindow0 :
      summaryWindowAbstraction
          (saturationLevel (automatonSchemeFamily automaton letter)
            (concreteBase automaton letter xorSummary trivialEntryMonitors)
            2 0 Proc.one) 2 (short Proc.one) =
        summaryWindowAbstraction
          (saturationLevel (automatonSchemeFamily automaton letter)
            (concreteBase automaton letter xorSummary trivialEntryMonitors)
            2 0 Proc.one) 2 (deep Proc.one) := by
    apply (summaryWindowAbstraction_eq_iff _ _ _ _).2
    simpa [saturationLevel] using And.intro hsummary (And.intro hpref hsuff)
  have hwindow1 := hstab Proc.one 2 (short Proc.one) (deep Proc.one) hwindow0
  have hsummary1 := congrArg SummaryWindowValue.summary hwindow1
  exact saturationLevel_one_deep_ne_short Proc.one hsummary1.symm

end AndShortLong

end DistributedSynthesis
