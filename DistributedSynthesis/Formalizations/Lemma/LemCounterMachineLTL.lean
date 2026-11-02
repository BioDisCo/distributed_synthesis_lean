/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineSource

/-! # A finite LTL formula for the counter-machine monitor -/
namespace DistributedSynthesis.CounterMachine.ResidueLTL
open ScalingSafety.ResidueLTL (Residues update Oriented decode oriented_update oriented_decode)
variable {Q : Type*} [DecidableEq Q] [Fintype Q]

structure Output (Q : Type*) where
  base : Label Q
  residue : Fin 3
deriving DecidableEq, Fintype
abbrev Letter (Q : Type*) := RoundRecord Unit Unit Graph (Output Q) (Output Q)
noncomputable instance : Fintype (Letter Q) := Fintype.ofEquiv (Graph × Output Q × Output Q)
  ⟨fun r ↦ ⟨(),(),r.1,r.2.1,r.2.2⟩,
    fun r ↦ (r.graph,r.outputOne,r.outputTwo),fun _ ↦ rfl,fun _ ↦ rfl⟩
def forget (r : Letter Q) : RoundRecord Unit Unit Graph (Label Q) (Label Q) :=
  ⟨(),(),r.graph,r.outputOne.base,r.outputTwo.base⟩
def residues (r : Letter Q) : Residues := (r.outputOne.residue,r.outputTwo.residue)
def oneLeft (r : Letter Q) := decode (residues r)
def leftLabel (r : Letter Q) : Label Q := if oneLeft r then r.outputOne.base else r.outputTwo.base
def rightLabel (r : Letter Q) : Label Q := if oneLeft r then r.outputTwo.base else r.outputOne.base
def leftCheck (l : Label Q) : Prop :=
  (∀ k, (l.carry k).val = 0) ∧ (∀ k, l.zero k = false → (l.right k).weight.val = 0)
def rightCheck (l : Label Q) : Prop := ∀ k, (l.carry k).val = 0
variable (M : Machine Q)
def initialCheck (r : Letter Q) : Prop :=
  residues r = update (0,1) r.graph ∧ (leftLabel r).control = M.initial ∧
    ∀ k, (leftLabel r).zero k = true
def localCheck (r : Letter Q) : Prop :=
  let l := leftLabel r
  let q := rightLabel r
  l.control = q.control ∧ l.zero = q.zero ∧ M.code l.control ≠ none ∧
    (∀ k, (l.right k).promised + (l.carry k).val =
      (M.op l.control l.zero k).factor * (l.right k).weight.val + (q.carry k).val) ∧
    (∀ k, l.zero k = true → (l.right k).weight.val = 1)
def pairCheck (a b : Letter Q) : Prop :=
  residues b = update (residues a) b.graph ∧
    (leftLabel b).control = M.next (leftLabel a).control (leftLabel a).zero ∧
    ∀ k, ((leftLabel b).right k).weight =
      ((leftLabel a).right k).child (ScalingSafety.digit (oneLeft a) b.graph)

noncomputable def formula : LTL (Letter Q) :=
  let test := FiniteLetterLTL.test (Letter := Letter Q)
  .conj (test (initialCheck M))
    (.conj (.always (test (localCheck M)))
      (.conj (.always (FiniteLetterLTL.relation (pairCheck M)))
        (.conj (FiniteLetterLTL.boundary (fun r ↦ r.graph = .right)
            (fun r ↦ leftCheck r.outputOne.base))
          (FiniteLetterLTL.boundary (fun r ↦ r.graph = .left)
            (fun r ↦ rightCheck r.outputTwo.base)))))
def Conditions (w : OmegaWord (Letter Q)) : Prop :=
  initialCheck M (w 0) ∧ (∀ n, localCheck M (w n)) ∧
    (∀ n, pairCheck M (w n) (w (n+1))) ∧
    (∀ n, (∀ k, k ≤ n → (w k).graph = .right) → leftCheck (w n).outputOne.base) ∧
    (∀ n, (∀ k, k ≤ n → (w k).graph = .left) → rightCheck (w n).outputTwo.base)
omit [DecidableEq Q] in
theorem satisfies_iff (w : OmegaWord (Letter Q)) :
    LTL.Satisfies FiniteLetterLTL.interp w (formula M) ↔ Conditions M w := by
  simp only [formula,LTL.Satisfies,LTL.satisfies_always,
    FiniteLetterLTL.satisfies_test,FiniteLetterLTL.satisfies_relation,
    FiniteLetterLTL.satisfies_boundary,OmegaWord.drop_apply,Nat.add_zero]
  rfl
def ResidueValid (w : OmegaWord (Letter Q)) : Prop :=
  residues (w 0) = update (0,1) (w 0).graph ∧
    ∀ n, residues (w (n+1)) = update (residues (w n)) (w (n+1)).graph
abbrev monitor (w : OmegaWord (Letter Q)) := (objective M).run (fun n ↦ forget (w n))
theorem monitor_orientation (w : OmegaWord (Letter Q)) (h : ResidueValid w) (n : Nat) :
    Oriented (monitor M w (n+1)).oneLeft (residues (w n)) := by
  induction n with
  | zero => rw [h.1]; exact oriented_update true (0,1) (w 0).graph (by rfl)
  | succ n ih => rw [h.2 n]; exact oriented_update _ _ _ ih
theorem monitor_decode (w : OmegaWord (Letter Q)) (h : ResidueValid w) (n : Nat) :
    oneLeft (w n) = (monitor M w (n+1)).oneLeft :=
  oriented_decode _ _ (monitor_orientation M w h n)
theorem step_boundary (s : State Q) (r : RoundRecord Unit Unit Graph (Label Q) (Label Q))
    (h : s.leftBoundary = true ∨ s.rightBoundary = true → s.oneLeft = true) :
    ((step M s r).leftBoundary = true ↔ s.leftBoundary = true ∧ r.graph = .right) ∧
    ((step M s r).rightBoundary = true ↔ s.rightBoundary = true ∧ r.graph = .left) ∧
    ((step M s r).leftBoundary = true ∨ (step M s r).rightBoundary = true →
      (step M s r).oneLeft = true) := by
  cases ht : s.oneLeft <;> cases hl : s.leftBoundary <;> cases hr : s.rightBoundary <;>
    cases hg : r.graph <;> simp [step,ScalingSafety.digit,ScalingSafety.Source.turn,ht,hl,hr,hg] at h ⊢
theorem monitor_boundary (w : OmegaWord (Letter Q)) (n : Nat) :
    ((monitor M w n).leftBoundary = true ↔ ∀ k, k < n → (w k).graph = .right) ∧
    ((monitor M w n).rightBoundary = true ↔ ∀ k, k < n → (w k).graph = .left) ∧
    ((monitor M w n).leftBoundary = true ∨ (monitor M w n).rightBoundary = true →
      (monitor M w n).oneLeft = true) := by
  induction n with
  | zero =>
    change (true = true ↔ ∀ k, k < 0 → _) ∧ (true = true ↔ ∀ k, k < 0 → _) ∧ _
    simp [objective]
  | succ n ih =>
    have hs := step_boundary M (monitor M w n) (forget (w n)) ih.2.2
    change ((step M (monitor M w n) (forget (w n))).leftBoundary = true ↔ _) ∧ _
    refine ⟨?_,?_,hs.2.2⟩
    · rw [hs.1,ih.1]
      constructor
      · rintro ⟨hh,hn⟩ k hk
        by_cases heq : k = n
        · simpa [heq] using hn
        · exact hh k (by omega)
      · intro hh; exact ⟨fun k hk ↦ hh k (by omega),hh n (by omega)⟩
    · change (step M (monitor M w n) (forget (w n))).rightBoundary = true ↔ _
      rw [hs.2.1,ih.2.1]
      constructor
      · rintro ⟨hh,hn⟩ k hk
        by_cases heq : k = n
        · simpa [heq] using hn
        · exact hh k (by omega)
      · intro hh; exact ⟨fun k hk ↦ hh k (by omega),hh n (by omega)⟩
theorem step_valid (s : State Q) (r : Letter Q)
    (ht : oneLeft r = (step M s (forget r)).oneLeft) :
    (step M s (forget r)).good = true ↔ s.good = true ∧
      Valid M (step M s (forget r)).leftBoundary (step M s (forget r)).rightBoundary
        s.previous (ScalingSafety.digit s.oneLeft r.graph) (leftLabel r) (rightLabel r) := by
  change oneLeft r = ScalingSafety.Source.turn s.oneLeft r.graph at ht
  simp only [step,forget,leftLabel,rightLabel,ht,Bool.and_eq_true,decide_eq_true_eq]
theorem monitor_previous (w : OmegaWord (Letter Q)) (h : ResidueValid w) (n : Nat) :
    (monitor M w (n+1)).previous = some (leftLabel (w n)).snapshot := by
  unfold leftLabel
  rw [monitor_decode M w h n]
  rfl
theorem boundary_labels (w : OmegaWord (Letter Q)) (h : ResidueValid w) (n : Nat)
    (hb : (monitor M w (n+1)).leftBoundary = true ∨ (monitor M w (n+1)).rightBoundary = true) :
    leftLabel (w n) = (w n).outputOne.base ∧ rightLabel (w n) = (w n).outputTwo.base := by
  have ht := (monitor_boundary M w (n+1)).2.2 hb
  simp only [leftLabel,rightLabel,monitor_decode M w h n,ht,↓reduceIte]
  exact ⟨trivial,trivial⟩

theorem conditions_iff_accepts (w : OmegaWord (Letter Q)) :
    Conditions M w ↔ ResidueValid w ∧ (objective M).Accepts (fun n ↦ forget (w n)) := by
  constructor
  · intro h
    have hr : ResidueValid w := ⟨h.1.1,fun n ↦ (h.2.2.1 n).1⟩
    refine ⟨hr,(accepts_iff_good M _).mpr ?_⟩
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      apply (step_valid M (monitor M w n) (w n) (monitor_decode M w hr n)).mpr
      obtain ⟨hq,hz,hlive,hbal,hw⟩ := h.2.1 n
      refine ⟨ih,hq,hz,hlive,hbal,hw,?_,?_,?_,?_,?_⟩
      · intro hb
        rw [(boundary_labels M w hr n (Or.inl hb)).1]
        exact (h.2.2.2.1 n (fun k hk ↦ (monitor_boundary M w (n+1)).1.mp hb k (by omega))).1
      · intro hb
        rw [(boundary_labels M w hr n (Or.inl hb)).1]
        exact (h.2.2.2.1 n (fun k hk ↦ (monitor_boundary M w (n+1)).1.mp hb k (by omega))).2
      · intro hb
        rw [(boundary_labels M w hr n (Or.inr hb)).2]
        exact h.2.2.2.2 n (fun k hk ↦ (monitor_boundary M w (n+1)).2.1.mp hb k (by omega))
      · intro hp
        cases n with
        | zero => exact h.1.2
        | succ n => rw [monitor_previous M w hr n] at hp; cases hp
      · intro old ho
        cases n with
        | zero => cases ho
        | succ n =>
          rw [monitor_previous M w hr n] at ho
          cases Option.some.inj ho
          rw [← monitor_decode M w hr n]
          exact (h.2.2.1 n).2
  · rintro ⟨hr,ha⟩
    have hg := (accepts_iff_good M _).mp ha
    have hc (n : Nat) := ((step_valid M (monitor M w n) (w n) (monitor_decode M w hr n)).mp (hg (n+1))).2
    refine ⟨⟨hr.1,(hc 0).initial rfl⟩,?_,?_,?_,?_⟩
    · intro n
      exact ⟨(hc n).control,(hc n).zero,(hc n).live,(hc n).balance,(hc n).zeroWeight⟩
    · intro n
      refine ⟨hr.2 n,?_⟩
      rw [monitor_decode M w hr n]
      exact (hc (n+1)).next _ (monitor_previous M w hr n)
    · intro n hn
      have hb := (monitor_boundary M w (n+1)).1.mpr (fun k hk ↦ hn k (by omega))
      have hz : leftCheck (leftLabel (w n)) := ⟨(hc n).leftCarry hb,(hc n).leftWeight hb⟩
      rwa [(boundary_labels M w hr n (Or.inl hb)).1] at hz
    · intro n hn
      have hb := (monitor_boundary M w (n+1)).2.1.mpr (fun k hk ↦ hn k (by omega))
      have hz := (hc n).rightCarry hb
      rwa [(boundary_labels M w hr n (Or.inr hb)).2] at hz

theorem formula_iff_accepts (w : OmegaWord (Letter Q)) :
    LTL.Satisfies FiniteLetterLTL.interp w (formula M) ↔
      ResidueValid w ∧ (objective M).Accepts (fun n ↦ forget (w n)) :=
  (satisfies_iff M w).trans (conditions_iff_accepts M w)

open ScalingSafety.ResidueLTL (mod3 views execution_record viewResidues viewResidues_succ)
def projectStrategy (σ : StrategyPair Unit Unit (Output Q) (Output Q)) :
    StrategyPair Unit Unit (Label Q) (Label Q) where
  one := fun v ↦ (σ.one v).base
  two := fun v ↦ (σ.two v).base
def liftStrategy (σ : StrategyPair Unit Unit (Label Q) (Label Q)) :
    StrategyPair Unit Unit (Output Q) (Output Q) where
  one := fun v ↦ ⟨σ.one v,mod3 (ScalingSafety.coordinate v)⟩
  two := fun v ↦ ⟨σ.two v,mod3 (ScalingSafety.coordinate v)⟩
section
omit [DecidableEq Q] [Fintype Q]

theorem project_execution (σ : StrategyPair Unit Unit (Output Q) (Output Q)) (env) :
    execution (projectStrategy σ) env = fun n ↦ forget (execution σ env n) := by
  funext n
  simp only [execution_record,projectStrategy,forget]
theorem lift_forget (σ : StrategyPair Unit Unit (Label Q) (Label Q)) (env) :
    (fun n ↦ forget (execution (liftStrategy σ) env n)) = execution σ env := by
  funext n
  simp only [execution_record,liftStrategy,forget]
theorem lift_residues (σ : StrategyPair Unit Unit (Label Q) (Label Q)) (env) (n : Nat) :
    residues (execution (liftStrategy σ) env n) = viewResidues env (n+1) := by
  rw [execution_record]; rfl
theorem lift_residue_valid (σ : StrategyPair Unit Unit (Label Q) (Label Q)) (env) :
    ResidueValid (execution (liftStrategy σ) env) := by
  constructor
  · rw [lift_residues,viewResidues_succ]; rfl
  · intro n
    rw [lift_residues,lift_residues,viewResidues_succ,execution_record]

end

def Realizable (φ : LTL (Letter Q)) : Prop :=
  ∃ σ : StrategyPair Unit Unit (Output Q) (Output Q),
    ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) φ

/-- The reduction targets literal LTL and arbitrary perfect-recall strategies,
not finite-state realizability or a stronger row-certificate problem. -/
theorem ltl_realizable_iff_nonhalting : Realizable (formula M) ↔ M.Nonhalting := by
  constructor
  · rintro ⟨σ,hσ⟩
    apply Rows.winning_implies_nonhalting M (projectStrategy σ)
    intro env
    rw [project_execution]
    exact ((formula_iff_accepts M _).mp (hσ env)).2
  · intro h
    refine ⟨liftStrategy (Source.strategy M),?_⟩
    intro env
    apply (formula_iff_accepts M _).mpr
    refine ⟨lift_residue_valid _ env,?_⟩
    rw [lift_forget]
    exact Source.wins M h env

end DistributedSynthesis.CounterMachine.ResidueLTL
