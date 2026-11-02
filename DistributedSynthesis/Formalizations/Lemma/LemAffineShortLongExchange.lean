/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemConcreteEntryRestartExchange

/-!
# The affine Boolean short--long experiment

The smallest concrete experiment for `AutomatonEntryRestartExchange`.
Inputs are singletons, outputs and automaton states are Boolean, and the
automaton update is affine in the two endpoint outputs:

`s' = s xor left xor right`.

The two internal labels of a three-edge expansion cancel.  The file first
packages that cancellation and the reachable three-to-nine-edge zero words.
The final padding lemmas show how a continuation of the short word is embedded
in a continuation of the long word by six neutral interior blocks.
-/

namespace DistributedSynthesis

namespace AffineShortLong

noncomputable local instance boundaryLabelFintype :
    Fintype (BoundaryLabel Bool Bool) :=
  Fintype.ofEquiv (Bool ⊕ Bool) (Equiv.psumEquivSum Bool Bool).symm

/-- Forget the owner tag of a Boolean boundary label. -/
def boundaryBit : BoundaryLabel Bool Bool -> Bool
  | .inl b => b
  | .inr b => b

/-- The boundary label of bit `b` owned by `p`. -/
def boundaryOf (p : Proc) (b : Bool) : BoundaryLabel Bool Bool :=
  match p with
  | .one => .inl b
  | .two => .inr b

/-- The corresponding owned label. -/
def ownedOf (p : Proc) (b : Bool) : OwnedLabel Bool Bool p := by
  cases p
  · exact ⟨PSum.inl b, trivial⟩
  · exact ⟨PSum.inr b, trivial⟩

@[simp] theorem ownedOf_val (p : Proc) (b : Bool) :
    (ownedOf p b).val = boundaryOf p b := by
  cases p <;> rfl

@[simp] theorem boundaryBit_boundaryOf (p : Proc) (b : Bool) :
    boundaryBit (boundaryOf p b) = b := by
  cases p <;> rfl

/-- Every owned Boolean label is recovered from its owner and bit. -/
theorem owned_val_eq_boundaryOf (p : Proc) (l : OwnedLabel Bool Bool p) :
    l.val = boundaryOf p (boundaryBit l.val) := by
  cases p with
  | one =>
      rcases l with ⟨label, hlabel⟩
      cases label with
      | inl b => rfl
      | inr b => exact False.elim hlabel
  | two =>
      rcases l with ⟨label, hlabel⟩
      cases label with
      | inl b => exact False.elim hlabel
      | inr b => rfl

/-- The affine alphabet remembers only the two Boolean endpoint values. -/
abbrev Alphabet := Bool × Bool

/-- The concrete letter constructor; inputs and graph are deliberately
irrelevant in this micro-instance. -/
def letter : EdgeExtensionLetter Alphabet PUnit.{1} PUnit.{1} Bool Bool :=
  fun _ _ _ left right => (boundaryBit left, boundaryBit right)

/-- The two-state affine DPA.  Its priority is immaterial for this finite
experiment. -/
abbrev automaton : DetParityAutomaton Alphabet where
  State := Bool
  stateFinite := inferInstance
  initial := false
  step s a := Bool.xor (Bool.xor s a.1) a.2
  priority _ := 0

/-- An oriented Boolean-state edge. -/
def edge (src : Proc) (state : Bool) : AutomatonEdgeType Bool :=
  ⟨src, src.other, Proc.ne_other src, state⟩

@[simp] theorem edge_srcOwner (src : Proc) (state : Bool) :
    (edge src state).srcOwner = src := rfl

@[simp] theorem edge_tgtOwner (src : Proc) (state : Bool) :
    (edge src state).tgtOwner = src.other := rfl

@[simp] theorem edge_state (src : Proc) (state : Bool) :
    (edge src state).state = state := rfl

/-- XOR of edge states, the deliberately small raw summary. -/
def xorSummary : PathSummarySemigroup (AutomatonEdgeType Bool) where
  Summary := Bool
  summaryFinite := inferInstance
  empty := false
  ofEdge q := q.state
  multiply := Bool.xor

theorem xorSummary_lawful : PathSummaryLawful xorSummary where
  assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

/-- The trivial entry-monitor family used for the first run. -/
def trivialEntryMonitors (_ : Proc) :
    DeterministicMonitorFamily (AutomatonEdgeType Bool) where
  index := PUnit
  indexFinite := inferInstance
  state _ := PUnit
  stateFinite _ := inferInstance
  init _ := PUnit.unit
  step _ _ _ := PUnit.unit

/-- The initial edge predicate for the zero source. -/
def initialEdge (d : Proc) (q : AutomatonEdgeType Bool) : Prop :=
  q = edge d false

/-- The affine cancellation inside one substitution block. -/
theorem triple_state_xor
    (src : Proc) (s l r iat ias : Bool) :
    let triple := automatonSubstitutionTriple automaton letter PUnit.unit
      PUnit.unit (edge src s) (ownedOf src l) (ownedOf src.other r)
      (ownedOf src.other iat) (ownedOf src ias)
    Bool.xor (Bool.xor triple.1.state triple.2.1.state)
        triple.2.2.state = Bool.xor (Bool.xor s l) r := by
  cases src <;> cases s <;> cases l <;> cases r <;> cases iat <;>
    cases ias <;> decide

/-- For an alternating owner triple, every pair of correctly owned endpoint
labels is feasible.  The three requested states determine the old state and
the two internal bits by affine elimination. -/
theorem rangeBlockMatch_affine_iff
    (src : Proc) (a m z : Bool)
    (lab lab' : BoundaryLabel Bool Bool) :
    RangeBlockMatch automaton letter PUnit.unit PUnit.unit lab lab'
        (edge src a) (edge src.other m) (edge src z) ↔
      (∃ l r : Bool,
        lab = boundaryOf src l ∧ lab' = boundaryOf src.other r) := by
  constructor
  · rintro ⟨c, s, l, r, iat, ias, hl, hr, htriple⟩
    have hc : c = src := by
      have howner := congrArg (fun triple => triple.1.srcOwner) htriple
      simpa [automatonSubstitutionTriple, edge] using howner
    subst c
    refine ⟨boundaryBit l.val, boundaryBit r.val, ?_, ?_⟩
    · exact hl.symm.trans (owned_val_eq_boundaryOf src l)
    · exact hr.symm.trans (owned_val_eq_boundaryOf src.other r)
  · rintro ⟨l, r, rfl, rfl⟩
    let s : Bool := Bool.xor (Bool.xor (Bool.xor (Bool.xor m l) a) r) z
    let iat : Bool := Bool.xor (Bool.xor s l) a
    let ias : Bool := Bool.xor (Bool.xor s r) z
    refine ⟨src, s, ownedOf src l, ownedOf src.other r,
      ownedOf src.other iat, ownedOf src ias, ?_, ?_, ?_⟩
    · simp
    · simp
    · cases src <;> cases a <;> cases m <;> cases z <;> cases l <;>
        cases r <;> rfl

/-- Consequently a completed affine block update is insensitive to all three
automaton states. -/
theorem rangeBlockStep_state_irrelevant
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (src : Proc) (a m z a' m' z' : Bool) :
    rangeBlockStep automaton letter feas
        (edge src a) (edge src.other m) (edge src z) =
      rangeBlockStep automaton letter feas
        (edge src a') (edge src.other m') (edge src z') := by
  classical
  ext next
  simp only [mem_rangeBlockStep]
  apply exists_congr
  intro prev
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [rangeBlockMatch_affine_iff, rangeBlockMatch_affine_iff]

/-- Ownership-only form of an affine completed-block update. -/
def labelOwnedBy (p : Proc) (lab : BoundaryLabel Bool Bool) : Prop :=
  ∃ b : Bool, lab = boundaryOf p b

open Classical in
noncomputable def ownerBlockStep (src : Proc)
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool))) :
    Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)) :=
  Finset.univ.filter fun next =>
    ∃ prev ∈ feas, prev.1 = next.1 ∧
      labelOwnedBy src prev.2 ∧ labelOwnedBy src.other next.2

theorem rangeBlockStep_eq_ownerBlockStep
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (src : Proc) (a m z : Bool) :
    rangeBlockStep automaton letter feas
        (edge src a) (edge src.other m) (edge src z) =
      ownerBlockStep src feas := by
  classical
  ext next
  simp only [mem_rangeBlockStep, ownerBlockStep, Finset.mem_filter,
    Finset.mem_univ, true_and]
  apply exists_congr
  intro prev
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  rw [rangeBlockMatch_affine_iff]
  simp only [labelOwnedBy]
  constructor
  · rintro ⟨l, r, hl, hr⟩
    exact ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
  · rintro ⟨⟨l, hl⟩, ⟨r, hr⟩⟩
    exact ⟨l, r, hl, hr⟩

theorem rangeBlockStep_other_orientation
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (src : Proc) (a m z : Bool) :
    rangeBlockStep automaton letter feas
        (edge src.other a) (edge src m) (edge src.other z) =
      ownerBlockStep src.other feas := by
  simpa using rangeBlockStep_eq_ownerBlockStep feas src.other a m z

@[simp] theorem ownerBlockStep_empty (src : Proc) :
    ownerBlockStep src
      (∅ : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
        (Out₁ := Bool) (Out₂ := Bool))) = ∅ := by
  classical
  ext next
  simp [ownerBlockStep]

/-- Two alternating affine blocks already reach the ownership saturation;
repeating the same two-block cycle changes nothing. -/
theorem ownerBlockStep_pair_idempotent (src : Proc)
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool))) :
    ownerBlockStep src.other
        (ownerBlockStep src
          (ownerBlockStep src.other (ownerBlockStep src feas))) =
      ownerBlockStep src.other (ownerBlockStep src feas) := by
  classical
  ext next
  simp only [ownerBlockStep, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p₃, ⟨p₂, ⟨p₁, hp₁, hpar₁, ho₁, ho₂⟩,
        hpar₂, ho₃, ho₄⟩, hpar₃, ho₅, ho₆⟩
    refine ⟨p₁, hp₁, hpar₁.trans (hpar₂.trans hpar₃), ho₁, ?_⟩
    simpa using ho₆
  · rintro ⟨p₁, hp₁, hpar, ho₁, ho₂⟩
    refine ⟨p₁, ?_, hpar, ho₁, ho₂⟩
    refine ⟨next, ?_, hpar.symm, ?_, ho₁⟩
    · exact ⟨p₁, hp₁, hpar, ho₁, ho₂⟩
    · simpa using ho₂

/-- The equivalent one-vs-three-block absorption law. -/
theorem ownerBlockStep_triple_idempotent (src : Proc)
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool))) :
    ownerBlockStep src
        (ownerBlockStep src.other (ownerBlockStep src feas)) =
      ownerBlockStep src feas := by
  classical
  ext next
  simp only [ownerBlockStep, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p₂, ⟨p₁, ⟨p₀, hp₀, hpar₀, ho₀, ho₁⟩,
        hpar₁, ho₂, ho₃⟩, hpar₂, ho₄, ho₅⟩
    refine ⟨p₀, hp₀, hpar₀.trans (hpar₁.trans hpar₂),
      ho₀, ho₅⟩
  · rintro ⟨p₀, hp₀, hpar, ho₀, ho₁⟩
    refine ⟨p₀, ?_, hpar, ho₀, ho₁⟩
    refine ⟨next, ?_, hpar.symm, ho₁, ?_⟩
    · exact ⟨p₀, hp₀, hpar, ho₀, ho₁⟩
    · simpa using ho₀

/-- Every Boolean automaton edge has the canonical opposite-owner shape. -/
theorem edge_eta (q : AutomatonEdgeType Bool) :
    q = edge q.srcOwner q.state := by
  rcases q with ⟨src, tgt, hne, state⟩
  cases src <;> cases tgt
  · exact False.elim (hne rfl)
  · rfl
  · rfl
  · exact False.elim (hne rfl)

theorem rangeBlockStep_eq_empty_of_owner_mismatch
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (e₁ e₂ e₃ : AutomatonEdgeType Bool)
    (hbad : e₂.srcOwner ≠ e₁.srcOwner.other ∨
      e₃.srcOwner ≠ e₁.srcOwner) :
    rangeBlockStep automaton letter feas e₁ e₂ e₃ = ∅ := by
  classical
  ext next
  rw [mem_rangeBlockStep]
  constructor
  · rintro ⟨prev, -, -, c, s, l, r, iat, ias, -, -, htriple⟩
    exfalso
    have h₁ := congrArg (fun triple => triple.1.srcOwner) htriple
    have h₂ := congrArg (fun triple => triple.2.1.srcOwner) htriple
    have h₃ := congrArg (fun triple => triple.2.2.srcOwner) htriple
    simp only [automatonSubstitutionTriple] at h₁ h₂ h₃
    rcases hbad with hbad | hbad
    · apply hbad
      rw [← h₂, ← h₁]
    · exact hbad (h₃.symm.trans h₁)
  · intro h
    simp at h

/-- Exact normal form of every affine block update. -/
theorem rangeBlockStep_normalForm
    (feas : Finset (RangeFeasPair (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool)))
    (e₁ e₂ e₃ : AutomatonEdgeType Bool) :
    rangeBlockStep automaton letter feas e₁ e₂ e₃ =
      if e₂.srcOwner = e₁.srcOwner.other ∧
          e₃.srcOwner = e₁.srcOwner then
        ownerBlockStep e₁.srcOwner feas
      else ∅ := by
  classical
  split_ifs with h
  · rcases h with ⟨h₂, h₃⟩
    rw [edge_eta e₁, edge_eta e₂, edge_eta e₃]
    simp only [edge_srcOwner] at h₂ h₃ ⊢
    rw [h₂, h₃]
    exact rangeBlockStep_eq_ownerBlockStep feas e₁.srcOwner
      e₁.state e₂.state e₃.state
  · apply rangeBlockStep_eq_empty_of_owner_mismatch
    exact not_and_or.mp h

/-- Equal endpoint and internal bits emit the zero block from a zero edge. -/
@[simp] theorem zero_triple (src : Proc) (b : Bool) :
    automatonSubstitutionTriple automaton letter PUnit.unit PUnit.unit
      (edge src false) (ownedOf src b) (ownedOf src.other b)
      (ownedOf src.other b) (ownedOf src b) =
        (edge src false, edge src.other false, edge src false) := by
  cases src <;> cases b <;> rfl

/-- The reachable source of length one. -/
def source (d : Proc) : List (AutomatonEdgeType Bool) := [edge d false]

/-- Its three-edge zero expansion. -/
def short (d : Proc) : List (AutomatonEdgeType Bool) :=
  [edge d false, edge d.other false, edge d false]

/-- The next zero expansion, of length nine. -/
def long (d : Proc) : List (AutomatonEdgeType Bool) :=
  [edge d false, edge d.other false, edge d false,
   edge d.other false, edge d false, edge d.other false,
   edge d false, edge d.other false, edge d false]

@[simp] theorem short_length (d : Proc) : (short d).length = 3 := by
  simp [short]

@[simp] theorem long_length (d : Proc) : (long d).length = 9 := by
  simp [long]

/-- The range recognizer cannot distinguish the reachable three-edge word
from its nine-edge affine expansion, from any monitor state. -/
theorem rangeRec_short_long (d : Proc)
    (st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool) :
    (short d).foldl (rangeRecStep automaton letter) st =
      (long d).foldl (rangeRecStep automaton letter) st := by
  rcases st with feas | pending
  · simp only [short, long, List.foldl, rangeRecStep]
    rw [rangeBlockStep_eq_ownerBlockStep,
      rangeBlockStep_other_orientation,
      rangeBlockStep_eq_ownerBlockStep,
      ownerBlockStep_triple_idempotent]
  · rcases pending with pending | pending
    · rcases pending with ⟨e, feas⟩
      simp only [short, long, List.foldl, rangeRecStep]
      rw [rangeBlockStep_normalForm]
      split_ifs with h
      · have he : e.srcOwner = d.other := by simpa using h.2.symm
        rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation, he]
        congr 2
        symm
        simpa using ownerBlockStep_triple_idempotent d.other feas
      · rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation]
        simp
    · rcases pending with ⟨e₁, e₂, feas⟩
      simp only [short, long, List.foldl, rangeRecStep]
      rw [rangeBlockStep_normalForm]
      split_ifs with h
      · have he : e₁.srcOwner = d := by simpa using h.2.symm
        rw [rangeBlockStep_other_orientation,
          rangeBlockStep_eq_ownerBlockStep, he,
          ownerBlockStep_triple_idempotent]
      · rw [rangeBlockStep_other_orientation,
          rangeBlockStep_eq_ownerBlockStep]
        simp

theorem singleEdgeTransition_short_long (d : Proc)
    (st : Option (Option (AutomatonEdgeType Bool))) :
    (short d).foldl
        ((singleEdgeMonitor (EdgeType := AutomatonEdgeType Bool)).step
          PUnit.unit) st =
      (long d).foldl
        ((singleEdgeMonitor (EdgeType := AutomatonEdgeType Bool)).step
          PUnit.unit) st := by
  rcases st with _ | st
  · rfl
  · rcases st with _ | _ <;> rfl

theorem concreteMonitorTransition_short_long (d : Proc)
    (i : (concreteMonitorFamily automaton letter trivialEntryMonitors d).index)
    (st : (concreteMonitorFamily automaton letter trivialEntryMonitors d).state i) :
    (short d).foldl
        ((concreteMonitorFamily automaton letter trivialEntryMonitors d).step i) st =
      (long d).foldl
        ((concreteMonitorFamily automaton letter trivialEntryMonitors d).step i) st := by
  rcases i with i | i
  · rcases i with i | i
    · rcases i with ⟨⟩
      rfl
    · rcases i with ⟨⟩
      exact singleEdgeTransition_short_long d st
  · rcases i with ⟨⟩
    exact rangeRec_short_long d st

theorem concreteBaseSummary_short_long (d : Proc) :
    pathSummaryValue
        (concreteBase automaton letter xorSummary trivialEntryMonitors d)
        (short d) =
      pathSummaryValue
        (concreteBase automaton letter xorSummary trivialEntryMonitors d)
        (long d) := by
  rw [show concreteBase automaton letter xorSummary trivialEntryMonitors d =
      enrichedBaseSemigroup xorSummary
        (concreteMonitorFamily automaton letter trivialEntryMonitors d) from rfl,
    show enrichedBaseSemigroup xorSummary
        (concreteMonitorFamily automaton letter trivialEntryMonitors d) =
      xorSummary.prod (monitorTransitionSemigroup
        (concreteMonitorFamily automaton letter trivialEntryMonitors d)) from rfl]
  let M := monitorTransitionSemigroup
    (concreteMonitorFamily automaton letter trivialEntryMonitors d)
  have hshort := PathSummarySemigroup.pathSummaryValue_prod
    xorSummary M (short d)
  have hlong := PathSummarySemigroup.pathSummaryValue_prod
    xorSummary M (long d)
  change pathSummaryValue (xorSummary.prod M) (short d) =
    pathSummaryValue (xorSummary.prod M) (long d)
  rw [hshort, hlong]
  apply Prod.ext
  · rfl
  · funext i st
    dsimp only [M, Prod.snd]
    exact (monitorTransition_value
      (concreteMonitorFamily automaton letter trivialEntryMonitors d)
      (short d) i st).trans
        ((concreteMonitorTransition_short_long d i st).trans
          (monitorTransition_value
            (concreteMonitorFamily automaton letter trivialEntryMonitors d)
            (long d) i st).symm)

/-- The intended depth-1/depth-2 collision really occurs in the full
concrete base, including the range recognizer's entire transition function. -/
theorem concreteCode_short_long (d : Proc) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (short d) =
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (long d) := by
  unfold finiteSummaryWindowAbstraction
  apply Prod.ext
  · exact concreteBaseSummary_short_long d
  · apply Prod.ext <;> rfl

/-- Six neutral interior blocks are invisible to the range recognizer when
the first two and last blocks are retained. -/
theorem rangeRec_framed_padding (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool)
    (st : RangeRecState (In₁ := PUnit) (In₂ := PUnit)
      (Out₁ := Bool) (Out₂ := Bool) Bool) :
    [edge d a₁, edge d.other a₂, edge d a₃,
      edge d.other a₄, edge d a₅, edge d.other a₆,
      edge d a₇, edge d.other a₈, edge d a₉].foldl
        (rangeRecStep automaton letter) st =
    ([edge d a₁, edge d.other a₂, edge d a₃,
      edge d.other a₄, edge d a₅, edge d.other a₆] ++
      short d ++ short d.other ++ short d ++ short d.other ++
      short d ++ short d.other ++
      [edge d a₇, edge d.other a₈, edge d a₉]).foldl
        (rangeRecStep automaton letter) st := by
  rcases st with feas | pending
  · simp only [short, List.cons_append, List.nil_append, List.foldl,
      rangeRecStep, Proc.other_other]
    simp_rw [rangeBlockStep_eq_ownerBlockStep,
      rangeBlockStep_other_orientation]
    repeat' rw [ownerBlockStep_pair_idempotent]
  · rcases pending with pending | pending
    · rcases pending with ⟨e, feas⟩
      simp only [short, List.cons_append, List.nil_append, List.foldl,
        rangeRecStep, Proc.other_other]
      rw [rangeBlockStep_normalForm feas e (edge d a₁) (edge d.other a₂)]
      split_ifs with h
      · have he : e.srcOwner = d.other := h.2.symm
        simp_rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation]
        rw [he]
        repeat' rw [ownerBlockStep_pair_idempotent]
      · simp_rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation]
        simp
    · rcases pending with ⟨e₁, e₂, feas⟩
      simp only [short, List.cons_append, List.nil_append, List.foldl,
        rangeRecStep, Proc.other_other]
      rw [rangeBlockStep_normalForm feas e₁ e₂ (edge d a₁)]
      split_ifs with h
      · have he : e₁.srcOwner = d := h.2.symm
        simp_rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation]
        rw [he]
        repeat' rw [ownerBlockStep_pair_idempotent]
      · simp_rw [rangeBlockStep_eq_ownerBlockStep,
          rangeBlockStep_other_orientation]
        simp

def framedWord (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool) :
    List (AutomatonEdgeType Bool) :=
  [edge d a₁, edge d.other a₂, edge d a₃,
    edge d.other a₄, edge d a₅, edge d.other a₆,
    edge d a₇, edge d.other a₈, edge d a₉]

/-- The six zero blocks inserted between the second and final copied block. -/
def neutralPadding (d : Proc) : List (AutomatonEdgeType Bool) :=
  short d ++ short d.other ++ short d ++ short d.other ++
    short d ++ short d.other

def paddedFramedWord (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool) :
    List (AutomatonEdgeType Bool) :=
  [edge d a₁, edge d.other a₂, edge d a₃,
    edge d.other a₄, edge d a₅, edge d.other a₆] ++
    neutralPadding d ++
    [edge d a₇, edge d.other a₈, edge d a₉]

theorem xorSummary_framed_padding (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool) :
    pathSummaryValue xorSummary (framedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) =
      pathSummaryValue xorSummary
        (paddedFramedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) := by
  simp [framedWord, paddedFramedWord, neutralPadding, short,
    pathSummaryValue, xorSummary]

theorem singleEdgeTransition_framed_padding (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool)
    (st : Option (Option (AutomatonEdgeType Bool))) :
    (framedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉).foldl
        ((singleEdgeMonitor (EdgeType := AutomatonEdgeType Bool)).step
          PUnit.unit) st =
      (paddedFramedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉).foldl
        ((singleEdgeMonitor (EdgeType := AutomatonEdgeType Bool)).step
          PUnit.unit) st := by
  rcases st with _ | st
  · rfl
  · rcases st with _ | _ <;> rfl

theorem concreteMonitorTransition_framed_padding (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool)
    (i : (concreteMonitorFamily automaton letter trivialEntryMonitors d).index)
    (st : (concreteMonitorFamily automaton letter trivialEntryMonitors d).state i) :
    (framedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉).foldl
        ((concreteMonitorFamily automaton letter trivialEntryMonitors d).step i) st =
      (paddedFramedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉).foldl
        ((concreteMonitorFamily automaton letter trivialEntryMonitors d).step i) st := by
  rcases i with i | i
  · rcases i with i | i
    · rcases i with ⟨⟩
      rfl
    · rcases i with ⟨⟩
      exact singleEdgeTransition_framed_padding d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ st
  · rcases i with ⟨⟩
    simpa [framedWord, paddedFramedWord] using
      rangeRec_framed_padding d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ st

theorem concreteCode_framed_padding (d : Proc)
    (a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ : Bool) :
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (framedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) =
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (paddedFramedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) := by
  unfold finiteSummaryWindowAbstraction
  apply Prod.ext
  · rw [show concreteBase automaton letter xorSummary trivialEntryMonitors d =
        xorSummary.prod (monitorTransitionSemigroup
          (concreteMonitorFamily automaton letter trivialEntryMonitors d)) from rfl]
    rw [PathSummarySemigroup.pathSummaryValue_prod,
      PathSummarySemigroup.pathSummaryValue_prod]
    apply Prod.ext
    · exact xorSummary_framed_padding d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉
    · funext i st
      exact (monitorTransition_value
        (concreteMonitorFamily automaton letter trivialEntryMonitors d)
        (framedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) i st).trans
          ((concreteMonitorTransition_framed_padding d
            a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉ i st).trans
            (monitorTransition_value
              (concreteMonitorFamily automaton letter trivialEntryMonitors d)
              (paddedFramedWord d a₁ a₂ a₃ a₄ a₅ a₆ a₇ a₈ a₉) i st).symm)
  · apply Prod.ext <;> rfl

private theorem zero_step (d : Proc) (b : Bool)
    (restOld restOut : List (AutomatonEdgeType Bool))
    (right : BoundaryLabel Bool Bool)
    (hrest :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other b) restOld restOut right) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d b) (edge d false :: restOld)
      (short d ++ restOut) right := by
  refine ⟨short d, restOut, boundaryOf d.other b,
    (ownedOf d b, ownedOf d.other b, ownedOf d.other b, ownedOf d b),
    ?_, ?_, ?_, hrest, rfl⟩
  · change (ownedOf d b).val = boundaryOf d b
    simp
  · change short d = EdgeBlock3.toList
      (automatonSubstitutionTriple automaton letter PUnit.unit PUnit.unit
        (edge d false) (ownedOf d b) (ownedOf d.other b)
        (ownedOf d.other b) (ownedOf d b))
    rw [zero_triple]
    rfl
  · change (ownedOf d.other b).val = boundaryOf d.other b
    simp

private theorem chosen_step
    (old : AutomatonEdgeType Bool)
    (choice : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice old)
    (left mid right : BoundaryLabel Bool Bool)
    (restOld restOut : List (AutomatonEdgeType Bool))
    (hleft : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).left old choice = left)
    (hright : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).right old choice = mid)
    (hrest : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).LocalFrom mid restOld restOut right) :
    (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).LocalFrom left (old :: restOld)
      (EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block old choice) ++ restOut) right := by
  exact ⟨_, restOut, mid, choice, hleft, rfl, hright, hrest, rfl⟩

/-- Every continuation of the short source has a locally uniform continuation
of the long source obtained by inserting six boundary-preserving zero blocks.
The original three choices are exposed for the code-preservation proof. -/
theorem padded_localFrom (d : Proc)
    (left right : BoundaryLabel Bool Bool)
    (w : List (AutomatonEdgeType Bool))
    (hlocal :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        left (short d) w right) :
    ∃ (c₁ : (automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).Choice (edge d false))
      (c₂ : (automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).Choice (edge d.other false))
      (c₃ : (automatonSubstitutionScheme automaton letter
          PUnit.unit PUnit.unit).Choice (edge d false)),
      let B₁ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block (edge d false) c₁)
      let B₂ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block (edge d.other false) c₂)
      let B₃ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
        PUnit.unit PUnit.unit).block (edge d false) c₃)
      w = B₁ ++ B₂ ++ B₃ ∧
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        left (long d) (B₁ ++ B₂ ++ neutralPadding d ++ B₃) right := by
  change (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).LocalFrom left
      [edge d false, edge d.other false, edge d false] w right at hlocal
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
  let B₁ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₁)
  let B₂ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d.other false) c₂)
  let B₃ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₃)
  have hthird :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        mid₂ [edge d false] B₃ right := by
    refine ⟨B₃, [], mid₃, c₃, hl₃, rfl, hr₃, ?_, by simp⟩
    exact ⟨rfl, hright⟩
  let b := boundaryBit mid₂
  have hmid : mid₂ = boundaryOf d b := by
    calc
      mid₂ = c₃.1.val := hl₃.symm
      _ = boundaryOf d (boundaryBit c₃.1.val) :=
        owned_val_eq_boundaryOf d c₃.1
      _ = boundaryOf d b := by
        exact congrArg (boundaryOf d) (congrArg boundaryBit hl₃)
  have htail :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d b) [edge d false] B₃ right := by
    rw [← hmid]
    exact hthird
  have htail' :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other.other b) [edge d false] B₃ right := by
    simpa using htail
  have h₈ := zero_step d.other b [edge d false] B₃ right htail'
  have h₇ := zero_step d b [edge d.other false, edge d false]
    (short d.other ++ B₃) right h₈
  have h₇' :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other.other b)
        [edge d false, edge d.other false, edge d false]
        (short d ++ short d.other ++ B₃) right := by
    simpa [List.append_assoc] using h₇
  have h₆ := zero_step d.other b
    [edge d false, edge d.other false, edge d false]
    (short d ++ short d.other ++ B₃) right h₇'
  have h₅ := zero_step d b
    [edge d.other false, edge d false, edge d.other false, edge d false]
    (short d.other ++ short d ++ short d.other ++ B₃) right h₆
  have h₅' :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other.other b)
        [edge d false, edge d.other false, edge d false, edge d.other false,
          edge d false]
        (short d ++ short d.other ++ short d ++ short d.other ++ B₃) right := by
    simpa [List.append_assoc] using h₅
  have h₄ := zero_step d.other b
    [edge d false, edge d.other false, edge d false, edge d.other false,
      edge d false]
    (short d ++ short d.other ++ short d ++ short d.other ++ B₃) right h₅'
  have h₃ := zero_step d b
    [edge d.other false, edge d false, edge d.other false, edge d false,
      edge d.other false, edge d false]
    (short d.other ++ short d ++ short d.other ++ short d ++
      short d.other ++ B₃) right h₄
  have hpad :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        mid₂
        [edge d false, edge d.other false, edge d false, edge d.other false,
          edge d false, edge d.other false, edge d false]
        (neutralPadding d ++ B₃) right := by
    rw [hmid]
    simpa [neutralPadding, short, List.append_assoc] using h₃
  have hfrom₂ := chosen_step (edge d.other false) c₂ mid₁ mid₂ right
    [edge d false, edge d.other false, edge d false, edge d.other false,
      edge d false, edge d.other false, edge d false]
    (neutralPadding d ++ B₃) hl₂ hr₂ hpad
  have hfrom₁ := chosen_step (edge d false) c₁ left mid₁ right
    [edge d.other false, edge d false, edge d.other false, edge d false,
      edge d.other false, edge d false, edge d.other false, edge d false]
    (B₂ ++ neutralPadding d ++ B₃) hl₁ hr₁ (by
      simpa [B₂, List.append_assoc] using hfrom₂)
  refine ⟨c₁, c₂, c₃, ?_, ?_⟩
  · dsimp only [B₁, B₂, B₃]
    simpa [List.append_assoc] using hw₁.trans (congrArg (B₁ ++ ·)
      (hw₂.trans (by simpa using hw₃)))
  · simpa [long, B₁, B₂, B₃, List.append_assoc] using hfrom₁

theorem substitutionBlock_toList_framed (d : Proc)
    (c : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice (edge d false)) :
    let T := (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).block (edge d false) c
    EdgeBlock3.toList T =
      [edge d T.1.state, edge d.other T.2.1.state, edge d T.2.2.state] := by
  dsimp only
  let T := (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c
  change EdgeBlock3.toList T =
    [edge d T.1.state, edge d.other T.2.1.state, edge d T.2.2.state]
  calc
    EdgeBlock3.toList T =
        [edge T.1.srcOwner T.1.state, edge T.2.1.srcOwner T.2.1.state,
          edge T.2.2.srcOwner T.2.2.state] := by
      simp only [EdgeBlock3.toList, List.cons.injEq, and_true]
      exact ⟨edge_eta T.1, edge_eta T.2.1, edge_eta T.2.2⟩
    _ = [edge d T.1.state, edge d.other T.2.1.state,
          edge d T.2.2.state] := by
      simp [T, automatonSubstitutionScheme, automatonSubstitutionTriple]

/-- Code preservation for the arbitrary three choices exposed by
`padded_localFrom`. -/
theorem concreteCode_choice_padding (d : Proc)
    (c₁ : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice (edge d false))
    (c₂ : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice (edge d.other false))
    (c₃ : (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).Choice (edge d false)) :
    let T₁ := (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).block (edge d false) c₁
    let T₂ := (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).block (edge d.other false) c₂
    let T₃ := (automatonSubstitutionScheme automaton letter
      PUnit.unit PUnit.unit).block (edge d false) c₃
    finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (EdgeBlock3.toList T₁ ++ EdgeBlock3.toList T₂ ++
          EdgeBlock3.toList T₃) =
      finiteSummaryWindowAbstraction
        (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
        (EdgeBlock3.toList T₁ ++ EdgeBlock3.toList T₂ ++
          neutralPadding d ++ EdgeBlock3.toList T₃) := by
  dsimp only
  let T₁ := (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₁
  let T₂ := (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d.other false) c₂
  let T₃ := (automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₃
  have h₁ := substitutionBlock_toList_framed d c₁
  have h₂ := substitutionBlock_toList_framed d.other c₂
  have h₃ := substitutionBlock_toList_framed d c₃
  dsimp only at h₁ h₂ h₃
  change finiteSummaryWindowAbstraction
      (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2
      (EdgeBlock3.toList T₁ ++ EdgeBlock3.toList T₂ ++ EdgeBlock3.toList T₃) = _
  rw [h₁, h₂, h₃]
  simpa [framedWord, paddedFramedWord, Proc.other_other, List.append_assoc]
    using concreteCode_framed_padding d
      T₁.1.state T₁.2.1.state T₁.2.2.state
      T₂.1.state T₂.2.1.state T₂.2.2.state
      T₃.1.state T₃.2.1.state T₃.2.2.state

/-- **Outcome 2 of the micro-run.**  For the concrete reachable short-long
collision, every continuation of the three-edge word is answered by a
same-boundary continuation of the nine-edge word with exactly the same full
concrete radius-two code.  Thus the collision is profile-preserving; it is not
an `EntryRestartExchangeFailure`, even with trivial entry monitors. -/
theorem affine_shortLong_exchange (d : Proc)
    (left right : BoundaryLabel Bool Bool)
    (w : List (AutomatonEdgeType Bool))
    (hlocal :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        left (short d) w right) :
    ∃ w',
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
          left (long d) w' right ∧
        finiteSummaryWindowAbstraction
            (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 w' =
          finiteSummaryWindowAbstraction
            (concreteBase automaton letter xorSummary trivialEntryMonitors d) 2 w := by
  rcases padded_localFrom d left right w hlocal with ⟨c₁, c₂, c₃, hw, hpad⟩
  let B₁ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₁)
  let B₂ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d.other false) c₂)
  let B₃ := EdgeBlock3.toList ((automatonSubstitutionScheme automaton letter
    PUnit.unit PUnit.unit).block (edge d false) c₃)
  refine ⟨B₁ ++ B₂ ++ neutralPadding d ++ B₃, hpad, ?_⟩
  rw [hw]
  exact (concreteCode_choice_padding d c₁ c₂ c₃).symm

/-- The first expansion is a concrete locally uniform substitution. -/
theorem short_localFrom (d : Proc) (b : Bool) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d b) (source d) (short d) (boundaryOf d.other b) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other b) [] [] (boundaryOf d.other b) := by
    exact ⟨rfl, rfl⟩
  simpa [source] using zero_step d b [] [] (boundaryOf d.other b) hnil

/-- The second expansion is also a concrete locally uniform substitution. -/
theorem long_localFrom (d : Proc) (b : Bool) :
    (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
      (boundaryOf d b) (short d) (long d) (boundaryOf d.other b) := by
  have hnil :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other b) [] [] (boundaryOf d.other b) := by
    exact ⟨rfl, rfl⟩
  have h3 := zero_step d b [] [] (boundaryOf d.other b) hnil
  have h3' :
      (automatonSubstitutionScheme automaton letter PUnit.unit PUnit.unit).LocalFrom
        (boundaryOf d.other.other b) [edge d false] (short d)
        (boundaryOf d.other b) := by
    simpa using h3
  have h2 := zero_step d.other b [edge d false] (short d)
    (boundaryOf d.other b) h3'
  have h1 := zero_step d b [edge d.other false, edge d false]
    (short d.other ++ short d) (boundaryOf d.other b) h2
  simpa [short, long] using h1

/-- Both source depths are genuine iterated paths. -/
theorem source_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d (source d) := by
  exact .initial ⟨edge d false, rfl, rfl⟩

theorem short_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d.other (short d) := by
  refine .step (param := (PUnit.unit, PUnit.unit))
    (source_iterativelyReachable d) ?_
  exact ⟨boundaryOf d false, boundaryOf d.other false, short_localFrom d false⟩

theorem long_iterativelyReachable (d : Proc) :
    IterativelyReachable (automatonSchemeFamily automaton letter)
      (singleEdgeInit automaton initialEdge) d (long d) := by
  have h := IterativelyReachable.step (param := (PUnit.unit, PUnit.unit))
    (short_iterativelyReachable d)
    ⟨boundaryOf d false, boundaryOf d.other false, long_localFrom d false⟩
  simpa using h

end AffineShortLong

end DistributedSynthesis
