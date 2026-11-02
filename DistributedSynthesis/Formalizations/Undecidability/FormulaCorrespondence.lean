/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.FullPrefixUndecidability

/-! The clauses of the current manuscript's formula, with both counters
checked in parallel. Outputs use only the retained right plan. The final
nonhalting conjunct is separate from the six structural conditions. -/
namespace DistributedSynthesis.CounterMachine.Paper
open ResidueLTL
open ScalingSafety.ResidueLTL (update)
variable {Q : Type*}

def Agreement (r : Letter Q) : Prop :=
  r.outputOne.base.control = r.outputTwo.base.control ∧
    r.outputOne.base.zero = r.outputTwo.base.zero

def Balance (M : Machine Q) (r : Letter Q) : Prop :=
  ∀ k, ((leftLabel r).right k).promised + ((leftLabel r).carry k).val =
    (M.op (leftLabel r).control (leftLabel r).zero k).factor *
      ((leftLabel r).right k).weight.val + ((rightLabel r).carry k).val

def ZeroWeight (r : Letter Q) : Prop :=
  ∀ k, (leftLabel r).zero k = true → ((leftLabel r).right k).weight.val = 1

def Initial (M : Machine Q) (r : Letter Q) : Prop :=
  r.outputOne.base.control = M.initial ∧ ∀ k, r.outputOne.base.zero k = true

def Transition (M : Machine Q) (a b : Letter Q) : Prop :=
  b.outputOne.base.control = M.next a.outputOne.base.control a.outputOne.base.zero ∧
    ∀ k, ((leftLabel b).right k).weight =
      ((leftLabel a).right k).child (ScalingSafety.digit (oneLeft a) b.graph)

/-- Semantic clauses of the paper's formula. `live` is not part of C0--C5. -/
structure Checks (M : Machine Q) (w : OmegaWord (Letter Q)) : Prop where
  position : ResidueValid w
  agreement : ∀ n, Agreement (w n)
  balance : ∀ n, Balance M (w n)
  zeroWeight : ∀ n, ZeroWeight (w n)
  leftBoundary : ∀ n, (∀ k, k ≤ n → (w k).graph = .right) → leftCheck (w n).outputOne.base
  rightBoundary : ∀ n, (∀ k, k ≤ n → (w k).graph = .left) → rightCheck (w n).outputTwo.base
  initial : Initial M (w 0)
  transition : ∀ n, Transition M (w n) (w (n+1))
  live : ∀ n, M.code (w n).outputOne.base.control ≠ none

theorem agreement_iff (r : Letter Q) : Agreement r ↔
    (leftLabel r).control = (rightLabel r).control ∧
      (leftLabel r).zero = (rightLabel r).zero := by
  cases h : oneLeft r <;> simp [Agreement,leftLabel,rightLabel,h,eq_comm]

theorem left_eq_one (r : Letter Q) (h : Agreement r) :
    (leftLabel r).control = r.outputOne.base.control ∧
      (leftLabel r).zero = r.outputOne.base.zero := by
  cases orientation : oneLeft r <;> simp_all [Agreement,leftLabel]

theorem localCheck_iff (M : Machine Q) (r : Letter Q) :
    localCheck M r ↔ Agreement r ∧ Balance M r ∧ ZeroWeight r ∧
      M.code r.outputOne.base.control ≠ none := by
  constructor
  · rintro ⟨control,zero,live,balance,weight⟩
    have agreement := (agreement_iff r).mpr ⟨control,zero⟩
    exact ⟨agreement,balance,weight,by simpa only [(left_eq_one r agreement).1] using live⟩
  · rintro ⟨agreement,balance,weight,live⟩
    obtain ⟨control,zero⟩ := (agreement_iff r).mp agreement
    exact ⟨control,zero,by simpa only [(left_eq_one r agreement).1] using live,balance,weight⟩

theorem initialCheck_iff (M : Machine Q) (r : Letter Q) (agreement : Agreement r) :
    initialCheck M r ↔ residues r = update (0,1) r.graph ∧ Initial M r := by
  simp only [initialCheck,Initial,(left_eq_one r agreement).1,(left_eq_one r agreement).2]

theorem pairCheck_iff (M : Machine Q) (a b : Letter Q)
    (ha : Agreement a) (hb : Agreement b) :
    pairCheck M a b ↔ residues b = update (residues a) b.graph ∧ Transition M a b := by
  simp only [pairCheck,Transition,(left_eq_one a ha).1,(left_eq_one a ha).2,(left_eq_one b hb).1]

theorem conditions_iff_checks (M : Machine Q) (w : OmegaWord (Letter Q)) :
    Conditions M w ↔ Checks M w := by
  constructor
  · intro h
    have checksAt (n : Nat) := (localCheck_iff M (w n)).mp (h.2.1 n)
    have agreement (n : Nat) := (checksAt n).1
    have initial := (initialCheck_iff M (w 0) (agreement 0)).mp h.1
    refine ⟨⟨initial.1,fun n => (h.2.2.1 n).1⟩,agreement,
      fun n => (checksAt n).2.1,fun n => (checksAt n).2.2.1,
      h.2.2.2.1,h.2.2.2.2,initial.2,?_,fun n => (checksAt n).2.2.2⟩
    intro n
    exact ((pairCheck_iff M (w n) (w (n+1)) (agreement n) (agreement (n+1))).mp (h.2.2.1 n)).2
  · intro h
    refine ⟨(initialCheck_iff M (w 0) (h.agreement 0)).mpr ⟨h.position.1,h.initial⟩,
      ?_,?_,h.leftBoundary,h.rightBoundary⟩
    · intro n
      exact (localCheck_iff M (w n)).mpr ⟨h.agreement n,h.balance n,h.zeroWeight n,h.live n⟩
    · intro n
      exact (pairCheck_iff M (w n) (w (n+1)) (h.agreement n) (h.agreement (n+1))).mpr
        ⟨h.position.2 n,h.transition n⟩

/-- Position Order determines the actual view coordinate modulo three,
for arbitrary strategies satisfying the position checks, not just the
constructed realizing strategy. Physical round `n+1` is execution index `n`. -/
theorem position_coordinates
    (σ : StrategyPair Unit Unit (Output Q) (Output Q))
    (env : EnvironmentSequence Unit Unit)
    (position : ResidueValid (execution σ env)) (n : Nat) :
    residues (execution σ env n) = ScalingSafety.ResidueLTL.viewResidues env (n+1) := by
  induction n with
  | zero =>
    rw [position.1,ScalingSafety.ResidueLTL.viewResidues_succ,ScalingSafety.ResidueLTL.execution_record]
    rfl
  | succ n ih =>
    rw [position.2 n,ih,ScalingSafety.ResidueLTL.viewResidues_succ env (n+1),ScalingSafety.ResidueLTL.execution_record]

variable [DecidableEq Q] [Fintype Q]

/-- Every execution is tested against the literal manuscript clauses. No
extra left-plan agreement, row certificate, or finite-memory assumption. -/
theorem checks_realizable_iff_nonhalting (M : Machine Q) :
    (∃ σ : StrategyPair Unit Unit (Output Q) (Output Q),
      ∀ env, Checks M (execution σ env)) ↔ M.Nonhalting := by
  rw [← ltl_realizable_iff_nonhalting M]
  unfold Realizable
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact ((satisfies_iff M _).trans (conditions_iff_checks M _)).symm

/-- The omitted safety justification for the exact clauses in main.tex. -/
theorem checks_safety (M : Machine Q) : Characterisation.IsSafety {w | Checks M w} := by
  have eq : {w | Checks M w} = {w | Conditions M w} :=
    Set.ext fun w => (conditions_iff_checks M w).symm
  rw [eq]
  exact Characterisation.counter_conditions_safety M

/-- The manuscript's explicit local algorithm, including its position
residue, satisfies all the checks for every nonhalting machine. -/
theorem source_checks (M : Machine Q) (nonhalting : M.Nonhalting)
    (env : EnvironmentSequence Unit Unit) :
    Checks M (execution (liftStrategy (Source.strategy M)) env) := by
  apply (conditions_iff_checks M _).mp
  apply (conditions_iff_accepts M _).mpr
  refine ⟨lift_residue_valid _ env,?_⟩
  rw [lift_forget]
  exact Source.wins M nonhalting env

end DistributedSynthesis.CounterMachine.Paper
