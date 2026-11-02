/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmMiyanoHayashiEquivalence
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-! # Executable Miyano--Hayashi breakpoint construction

A candidate table chooses one finite successor set per frontier state.
Validity checks both satisfaction of the positive Boolean transition and
containment in its syntactic atoms. The same table advances the frontier and
the pending obligations. Exhaustive finite search is proved equivalent to the
existential over certified simultaneous supports.
-/

namespace DistributedSynthesis

/-- Structural evaluation with explicit atomic decision procedures. -/
def PosBool.evalDecidable {Atom : Type*} (valuation : Atom → Prop)
    (dec : DecidablePred valuation) : ∀ formula, Decidable (PosBool.Eval valuation formula)
  | .verum => isTrue trivial
  | .falsum => isFalse (fun h => h)
  | .atom a => dec a
  | .conj φ ψ =>
      letI := evalDecidable valuation dec φ
      letI := evalDecidable valuation dec ψ
      inferInstanceAs (Decidable (PosBool.Eval valuation φ ∧ PosBool.Eval valuation ψ))
  | .disj φ ψ =>
      letI := evalDecidable valuation dec φ
      letI := evalDecidable valuation dec ψ
      inferInstanceAs (Decidable (PosBool.Eval valuation φ ∨ PosBool.Eval valuation ψ))

namespace AlternatingParityAutomaton.MiyanoHayashi.Computable

variable {Alphabet : Type*} (A : AlternatingParityAutomaton Alphabet)
variable [DecidableEq A.State]

abbrev Table (frontier : Finset A.State) := {q // q ∈ frontier} → Finset A.State

def Valid {frontier : Finset A.State} (letter : Alphabet) (table : Table A frontier) : Prop :=
  ∀ q, PosBool.Eval (fun r => r ∈ table q) (A.step q.val letter) ∧
    ∀ r ∈ table q, r ∈ (A.step q.val letter).atoms

def validDecidable {frontier : Finset A.State} (letter : Alphabet)
    (table : Table A frontier) : Decidable (Valid A letter table) := by
  letI (q : {q // q ∈ frontier}) :=
    PosBool.evalDecidable (fun r => r ∈ table q) (fun _ => inferInstance) (A.step q.val letter)
  unfold Valid
  infer_instance

/-- Union of the chosen successors of every frontier state. -/
def successors {frontier : Finset A.State} (table : Table A frontier) : Finset A.State :=
  frontier.attach.biUnion table

/-- Only frontier states still pending contribute to the obligation update. -/
def pendingSuccessors {frontier : Finset A.State} (table : Table A frontier)
    (pending : Finset A.State) : Finset A.State :=
  (frontier.attach.filter fun q => q.val ∈ pending).biUnion table

def nextPending {frontier : Finset A.State} (table : Table A frontier)
    (pending : Finset A.State) : Finset A.State :=
  (if pending = ∅ then successors A table else pendingSuccessors A table pending).filter
    (fun q => A.priority q ≠ 0)

def toSupport {frontier : Finset A.State} {letter : Alphabet}
    (table : Table A frontier) (h : Valid A letter table) : A.MacroStepSupport frontier letter where
  choice := fun q => ⟨table q, (h q).1, (h q).2⟩

def ofSupport {frontier : Finset A.State} {letter : Alphabet}
    (support : A.MacroStepSupport frontier letter) : Table A frontier :=
  fun q => (support.choice q).support

omit [DecidableEq A.State] in
theorem ofSupport_valid {frontier : Finset A.State} {letter : Alphabet}
    (support : A.MacroStepSupport frontier letter) : Valid A letter (ofSupport A support) :=
  fun q => ⟨(support.choice q).support_satisfies, (support.choice q).support_atoms⟩

theorem successors_ofSupport {frontier : Finset A.State} {letter : Alphabet}
    (support : A.MacroStepSupport frontier letter) :
    successors A (ofSupport A support) = support.support := by
  unfold successors ofSupport MacroStepSupport.support
  congr 1
  exact Subsingleton.elim _ _

theorem pendingSuccessors_ofSupport {frontier : Finset A.State} {letter : Alphabet}
    (support : A.MacroStepSupport frontier letter) (pending : Finset A.State) :
    pendingSuccessors A (ofSupport A support) pending =
      MiyanoHayashi.pendingSuccessors support pending := by
  ext r
  simp only [pendingSuccessors, ofSupport, MiyanoHayashi.pendingSuccessors,
    Finset.mem_biUnion, Finset.mem_filter, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨q, hq, hr⟩
    refine ⟨⟨q.val, hq⟩, ?_⟩
    simpa only [dif_pos q.property] using hr
  · rintro ⟨q, hr⟩
    split_ifs at hr with hq
    · exact ⟨⟨q.val, hq⟩, q.property, hr⟩
    · exact False.elim (Finset.notMem_empty r hr)

theorem nextPending_ofSupport {frontier : Finset A.State} {letter : Alphabet}
    (support : A.MacroStepSupport frontier letter) (pending : Finset A.State) :
    nextPending A (ofSupport A support) pending = MiyanoHayashi.nextPending support pending := by
  unfold nextPending MiyanoHayashi.nextPending MiyanoHayashi.rawNextPending
  rw [successors_ofSupport, pendingSuccessors_ofSupport]
  split_ifs <;> (ext q; simp [buchiAcceptingState])

/-- The finite relation searched by the transition decision procedure. -/
def TableStep (current : BuchiState A) (letter : Alphabet) (next : BuchiState A) : Prop :=
  ∃ table : Table A current.frontier, Valid A letter table ∧
    next.frontier = successors A table ∧ next.pending = nextPending A table current.pending

theorem step_iff (current : BuchiState A) (letter : Alphabet) (next : BuchiState A) :
    buchiStep A current letter next ↔ TableStep A current letter next := by
  constructor
  · rintro ⟨support, hf, hp⟩
    exact ⟨ofSupport A support, ofSupport_valid A support,
      hf.trans (successors_ofSupport A support).symm,
      hp.trans (nextPending_ofSupport A support current.pending).symm⟩
  · rintro ⟨table, hv, hf, hp⟩
    let support := toSupport A table hv
    have heq : ofSupport A support = table := rfl
    refine ⟨support, ?_, ?_⟩
    · rw [← successors_ofSupport A support, heq]
      exact hf
    · rw [← nextPending_ofSupport A support current.pending, heq]
      exact hp

def stepDecidable (current : BuchiState A) (letter : Alphabet) (next : BuchiState A) :
    Decidable (buchiStep A current letter next) := by
  letI : Fintype (Finset A.State) := Finset.fintype
  letI := validDecidable A (frontier := current.frontier) letter
  letI : Decidable (TableStep A current letter next) := by
    unfold TableStep
    infer_instance
  exact decidable_of_iff (TableStep A current letter next) (step_iff A current letter next).symm

@[reducible] def stateFintype : Fintype (BuchiState A) :=
  letI : Fintype (Finset A.State) := Finset.fintype
  letI : Fintype (Finset A.State × Finset A.State) := instFintypeProd _ _
  Fintype.ofEquiv (Finset A.State × Finset A.State)
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun q => (q.frontier, q.pending)
      left_inv := by intro p; cases p; rfl
      right_inv := by intro q; cases q; rfl }

@[reducible] def stateDecidableEq : DecidableEq (BuchiState A) := by
  intro x y
  exact decidable_of_iff (x.frontier = y.frontier ∧ x.pending = y.pending)
    (by cases x; cases y; simp only [BuchiState.mk.injEq])

def buchi : NondetBuchiAutomaton Alphabet where
  State := BuchiState A
  stateFinite := stateFintype A
  initial := ⟨{A.initial}, ∅⟩
  step := buchiStep A
  accepting := buchiAccepting

@[reducible] def acceptingDecidable : DecidablePred (buchi A).accepting :=
  fun q => inferInstanceAs (Decidable (q.pending = ∅))

omit [DecidableEq A.State] in
theorem buchi_eq : buchi A = buchiCore A := by
  unfold buchi buchiCore
  congr 1

omit [DecidableEq A.State] in
theorem accepts_iff (hshape : BuchiShaped A) (word : OmegaWord Alphabet) :
    (buchi A).Accepts word ↔ A.Accepts word := by
  rw [buchi_eq]
  exact buchiCore_accepts_iff_accepts hshape

end AlternatingParityAutomaton.MiyanoHayashi.Computable
end DistributedSynthesis
