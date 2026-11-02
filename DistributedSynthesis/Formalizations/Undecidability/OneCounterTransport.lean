/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.Undecidability.GlobalRowConditions
import DistributedSynthesis.Library.Distributed.GraphAdversaries.Undecidability.InstanceEncoding

/-! The literal one-counter output tuple, transported to the existing
counter-machine implementation. Plans, operations, views and executions
are reused. `OnlyFirst` expresses that the code is a one-counter program;
it is not an invariant supplied about its run. -/
namespace DistributedSynthesis.CounterMachine.OneCounter
open Characterisation
variable {Q : Type*}

def OnlyFirst (M : Machine Q) : Prop := ∀ q,
  match M.code q with
  | none => True
  | some (.inc k _) => k = 0
  | some (.dec k _ _) => k = 0

def zeroFlags (z : Bool) : Fin 2 → Bool := fun k => if k = 0 then z else true

def next (M : Machine Q) (q : Q) (z : Bool) := M.next q (zeroFlags z)
def op (M : Machine Q) (q : Q) (z : Bool) := M.op q (zeroFlags z) 0

theorem next_first (M : Machine Q) (single : OnlyFirst M) (q : Q) (z : Fin 2 → Bool) :
    M.next q z = next M q (z 0) := by
  have only := single q
  cases code : M.code q with
  | none => simp [Machine.next,next,code]
  | some i =>
    cases i with
    | inc k t => simp [Machine.next,next,code]
    | dec k a b =>
      simp only [code] at only
      subst k
      simp [Machine.next,next,code,zeroFlags]

theorem op_first (M : Machine Q) (single : OnlyFirst M) (q : Q) (z : Fin 2 → Bool) :
    M.op q z 0 = op M q (z 0) := by
  have only := single q
  cases code : M.code q with
  | none => simp [Machine.op,op,code]
  | some i =>
    cases i with
    | inc k t => simp [Machine.op,op,code]
    | dec k a b =>
      simp only [code] at only
      subst k
      simp [Machine.op,op,code,zeroFlags]

theorem op_second (M : Machine Q) (single : OnlyFirst M) (q : Q) (z : Fin 2 → Bool) :
    M.op q z 1 = .idle := by
  have only := single q
  cases code : M.code q with
  | none => simp [Machine.op,code]
  | some i =>
    cases i with
    | inc k t =>
      simp only [code] at only
      subst k
      simp [Machine.op,code]
    | dec k a b =>
      simp only [code] at only
      subst k
      simp [Machine.op,code]

def counts (c : Nat) : Fin 2 → Nat := fun k => if k = 0 then c else 0

def advance (M : Machine Q) (s : Q × Nat) : Q × Nat :=
  (next M s.1 (decide (s.2 = 0)),(op M s.1 (decide (s.2 = 0))).applyCount s.2)
def run (M : Machine Q) : Nat → Q × Nat
  | 0 => (M.initial,0)
  | n+1 => advance M (run M n)
def Nonhalting (M : Machine Q) : Prop := ∀ n, M.code (run M n).1 ≠ none

theorem run_embed (M : Machine Q) (single : OnlyFirst M) (n : Nat) :
    M.run n = ((run M n).1,counts (run M n).2) := by
  induction n with
  | zero =>
    apply Prod.ext
    · rfl
    · funext k
      fin_cases k <;> rfl
  | succ n ih =>
    rw [Machine.run,ih]
    change M.advance _ = ((advance M (run M n)).1,counts (advance M (run M n)).2)
    apply Prod.ext
    · simp [Machine.advance,advance,next_first M single,flags,counts]
    · funext k
      fin_cases k
      · simp [Machine.advance,advance,counts,op_first M single,flags]
      · simp [Machine.advance,counts,op_second M single,TernaryCounter.Operation.applyCount]

theorem nonhalting_iff (M : Machine Q) (single : OnlyFirst M) : M.Nonhalting ↔ Nonhalting M := by
  simp only [Machine.Nonhalting,Nonhalting,run_embed M single]

/-- Exactly the five components displayed in the manuscript. -/
structure Output (Q : Type*) where
  control : Q
  zero : Bool
  right : Plan
  carry : Fin 9
  residue : Fin 3
deriving DecidableEq, Fintype

abbrev Letter (Q : Type*) := RoundRecord Unit Unit Graph (Output Q) (Output Q)

def dummyPlan : Plan := ⟨1,fun _ => 1⟩
def embed (o : Output Q) : ResidueLTL.Output Q :=
  ⟨⟨o.control,zeroFlags o.zero,fun k => if k = 0 then o.carry else 0,
    fun k => if k = 0 then o.right else dummyPlan⟩,o.residue⟩
def project (o : ResidueLTL.Output Q) : Output Q :=
  ⟨o.base.control,o.base.zero 0,o.base.right 0,o.base.carry 0,o.residue⟩

@[simp] theorem project_embed (o : Output Q) : project (embed o) = o := by
  cases o; simp [OneCounter.project,embed,zeroFlags]

def oneLeft (r : Letter Q) := ScalingSafety.ResidueLTL.decode (r.outputOne.residue,r.outputTwo.residue)
def left (r : Letter Q) : Output Q := if oneLeft r then r.outputOne else r.outputTwo
def right (r : Letter Q) : Output Q := if oneLeft r then r.outputTwo else r.outputOne

def Position (w : OmegaWord (Letter Q)) : Prop :=
  (w 0).outputOne.residue = (ScalingSafety.ResidueLTL.update (0,1) (w 0).graph).1 ∧
  (w 0).outputTwo.residue = (ScalingSafety.ResidueLTL.update (0,1) (w 0).graph).2 ∧
  ∀ n, ((w (n+1)).outputOne.residue,(w (n+1)).outputTwo.residue) =
    ScalingSafety.ResidueLTL.update ((w n).outputOne.residue,(w n).outputTwo.residue) (w (n+1)).graph

def Agreement (r : Letter Q) := r.outputOne.control = r.outputTwo.control ∧ r.outputOne.zero = r.outputTwo.zero
def Balance (M : Machine Q) (r : Letter Q) :=
  (left r).right.promised + (left r).carry.val =
    (op M (left r).control (left r).zero).factor * (left r).right.weight.val + (right r).carry.val
def ZeroWeight (r : Letter Q) := (left r).zero = true → (left r).right.weight.val = 1
def LeftBoundary (r : Letter Q) := r.outputOne.carry.val = 0 ∧
  (r.outputOne.zero = false → r.outputOne.right.weight.val = 0)
def RightBoundary (r : Letter Q) := r.outputTwo.carry.val = 0
def Initial (M : Machine Q) (r : Letter Q) := r.outputOne.control = M.initial ∧ r.outputOne.zero = true
def Transition (M : Machine Q) (a b : Letter Q) :=
  b.outputOne.control = next M a.outputOne.control a.outputOne.zero ∧
  (left b).right.weight = (left a).right.child (ScalingSafety.digit (oneLeft a) b.graph)

/-- Literal scalar versions of the formula clauses; no dummy counter appears. -/
structure Checks (M : Machine Q) (w : OmegaWord (Letter Q)) : Prop where
  position : Position w
  agreement : ∀ n, Agreement (w n)
  balance : ∀ n, Balance M (w n)
  zeroWeight : ∀ n, ZeroWeight (w n)
  leftBoundary : ∀ n, (∀ k, k ≤ n → (w k).graph = .right) → LeftBoundary (w n)
  rightBoundary : ∀ n, (∀ k, k ≤ n → (w k).graph = .left) → RightBoundary (w n)
  initial : Initial M (w 0)
  transition : ∀ n, Transition M (w n) (w (n+1))
  live : ∀ n, M.code (w n).outputOne.control ≠ none

@[simp] theorem embed_left (r : Letter Q) :
    ResidueLTL.leftLabel (mapRecord embed embed r) = (embed (left r)).base := by
  cases h : oneLeft r <;> simp [ResidueLTL.leftLabel,ResidueLTL.oneLeft,ResidueLTL.residues,
    left,oneLeft,mapRecord,OneCounter.embed] at h ⊢ <;> simp_all
@[simp] theorem embed_right (r : Letter Q) :
    ResidueLTL.rightLabel (mapRecord embed embed r) = (embed (right r)).base := by
  cases h : oneLeft r <;> simp [ResidueLTL.rightLabel,ResidueLTL.oneLeft,ResidueLTL.residues,
    right,oneLeft,mapRecord,OneCounter.embed] at h ⊢ <;> simp_all

/-- Every scalar check embeds, with a permanently zero second counter. -/
theorem Checks.embed (M : Machine Q) (single : OnlyFirst M) (w : OmegaWord (Letter Q))
    (checks : Checks M w) : Paper.Checks M (OmegaWord.map (mapRecord embed embed) w) := by
  constructor
  · exact ⟨Prod.ext checks.position.1 checks.position.2.1,checks.position.2.2⟩
  · intro n
    exact ⟨(checks.agreement n).1,by funext k; fin_cases k <;> simp [OneCounter.embed,zeroFlags,OmegaWord.map,mapRecord,(checks.agreement n).2]⟩
  · intro n k
    simp only [OmegaWord.map,embed_left,embed_right]
    fin_cases k
    · exact checks.balance n
    · simp [OneCounter.embed,dummyPlan,Plan.promised,op_second M single,TernaryCounter.Operation.factor]
  · intro n k
    simp only [OmegaWord.map,embed_left]
    fin_cases k
    · exact checks.zeroWeight n
    · simp [OneCounter.embed,dummyPlan]
  · intro n constant
    have b := checks.leftBoundary n constant
    constructor
    · intro k; fin_cases k
      · exact b.1
      · rfl
    · intro k; fin_cases k
      · exact b.2
      · simp [OneCounter.embed,zeroFlags,OmegaWord.map,mapRecord]
  · intro n constant k
    fin_cases k
    · exact checks.rightBoundary n constant
    · rfl
  · exact ⟨checks.initial.1,by intro k; fin_cases k; exact checks.initial.2; rfl⟩
  · intro n
    constructor
    · exact (checks.transition n).1
    · intro k
      simp only [OmegaWord.map,embed_left]
      fin_cases k
      · exact (checks.transition n).2
      · rfl
  · exact checks.live

@[simp] theorem project_left (r : ResidueLTL.Letter Q) :
    left (mapRecord project project r) = project ⟨ResidueLTL.leftLabel r, if ResidueLTL.oneLeft r then r.outputOne.residue else r.outputTwo.residue⟩ := by
  cases h : ResidueLTL.oneLeft r <;>
    simp [left,oneLeft,mapRecord,OneCounter.project,ResidueLTL.leftLabel,ResidueLTL.oneLeft,ResidueLTL.residues] at h ⊢ <;> simp_all

@[simp] theorem project_right (r : ResidueLTL.Letter Q) :
    right (mapRecord project project r) = project ⟨ResidueLTL.rightLabel r, if ResidueLTL.oneLeft r then r.outputTwo.residue else r.outputOne.residue⟩ := by
  cases h : ResidueLTL.oneLeft r <;>
    simp [right,oneLeft,mapRecord,OneCounter.project,ResidueLTL.rightLabel,ResidueLTL.oneLeft,ResidueLTL.residues] at h ⊢ <;> simp_all

/-- Projection applies to every solution of the two-counter checks, not
only to solutions already lying in the image of the scalar embedding. -/
theorem Checks.project (M : Machine Q) (single : OnlyFirst M) (w : OmegaWord (ResidueLTL.Letter Q))
    (checks : Paper.Checks M w) : Checks M (OmegaWord.map (mapRecord project project) w) := by
  constructor
  · exact ⟨congrArg Prod.fst checks.position.1,congrArg Prod.snd checks.position.1,checks.position.2⟩
  · intro n
    exact ⟨(checks.agreement n).1,congrFun (checks.agreement n).2 0⟩
  · intro n
    have eq := checks.balance n 0
    simpa only [Balance,OmegaWord.map,project_left,project_right,OneCounter.project,op_first M single] using eq
  · intro n
    simpa only [ZeroWeight,OmegaWord.map,project_left,OneCounter.project] using checks.zeroWeight n 0
  · intro n constant
    exact ⟨(checks.leftBoundary n constant).1 0,(checks.leftBoundary n constant).2 0⟩
  · intro n constant
    exact checks.rightBoundary n constant 0
  · exact ⟨checks.initial.1,checks.initial.2 0⟩
  · intro n
    refine ⟨?_,?_⟩
    · simpa only [OmegaWord.map,mapRecord,OneCounter.project,next_first M single] using (checks.transition n).1
    · simpa only [OmegaWord.map,project_left,OneCounter.project] using (checks.transition n).2 0
  · exact checks.live

theorem checks_embed_iff (M : Machine Q) (single : OnlyFirst M) (w : OmegaWord (Letter Q)) :
    Paper.Checks M (OmegaWord.map (mapRecord embed embed) w) ↔ Checks M w := by
  constructor
  · intro checks
    have scalar := Checks.project M single _ checks
    have back : OmegaWord.map (mapRecord project project) (OmegaWord.map (mapRecord embed embed) w) = w := by
      funext n
      cases r : w n
      simp [OmegaWord.map,mapRecord,r,project_embed]
    rwa [back] at scalar
  · exact Checks.embed M single w

theorem map_execution {O P : Type*} (f : O → P)
    (σ : StrategyPair Unit Unit O O) (env : EnvironmentSequence Unit Unit) :
    execution (mapStrategy f f σ) env = OmegaWord.map (mapRecord f f) (execution σ env) := by
  have same : env = GraphExecutions.ofGraphs (fun n => (env n).graph) := by
    funext n
    cases h : env n
    simp [GraphExecutions.ofGraphs,h]
  rw [same]
  exact mapStrategy_execution f f σ _

/-- Both directions preserve actual perfect-recall strategies and their
executions over the smaller displayed output alphabet. -/
theorem checks_realizable_iff [DecidableEq Q] [Fintype Q]
    (M : Machine Q) (single : OnlyFirst M) :
    (∃ σ : StrategyPair Unit Unit (Output Q) (Output Q), ∀ env, Checks M (execution σ env)) ↔
      Nonhalting M := by
  rw [← nonhalting_iff M single,← Paper.checks_realizable_iff_nonhalting M]
  constructor
  · rintro ⟨σ,checks⟩
    refine ⟨mapStrategy embed embed σ,fun env => ?_⟩
    rw [map_execution]
    exact Checks.embed M single _ (checks env)
  · rintro ⟨σ,checks⟩
    refine ⟨mapStrategy project project σ,fun env => ?_⟩
    rw [map_execution]
    exact Checks.project M single _ (checks env)

/-- An arbitrary scalar increment/decrement program embeds in the existing
instruction type. The right summand gives zero and positive targets. -/
def ofCode (initial : Q) (code : Q → Option (Q ⊕ (Q × Q))) : Machine Q where
  initial := initial
  code q := (code q).map fun i => match i with
    | .inl target => .inc 0 target
    | .inr targets => .dec 0 targets.1 targets.2

theorem ofCode_onlyFirst (initial : Q) (code : Q → Option (Q ⊕ (Q × Q))) :
    OnlyFirst (ofCode initial code) := by
  intro q
  cases h : code q with
  | none => simp [ofCode,h]
  | some i => cases i <;> simp [ofCode,h]

noncomputable instance [Fintype Q] : Fintype (Letter Q) :=
  Fintype.ofEquiv (Graph × Output Q × Output Q)
    ⟨fun r => ⟨(),(),r.1,r.2.1,r.2.2⟩,
      fun r => (r.graph,r.outputOne,r.outputTwo),fun _ => rfl,fun _ => rfl⟩

/-- The scalar formula uses the displayed checks on the five-component
output alphabet. It is compiled using the existing finite-letter LTL API. -/
noncomputable def formula [Fintype Q] (M : Machine Q) : LTL (Letter Q) :=
  let test := FiniteLetterLTL.test (Letter := Letter Q)
  .conj (test (fun r => ((r.outputOne.residue,r.outputTwo.residue) =
      ScalingSafety.ResidueLTL.update (0,1) r.graph) ∧ Initial M r))
    (.conj (.always (test (fun r => Agreement r ∧ Balance M r ∧ ZeroWeight r ∧ M.code r.outputOne.control ≠ none)))
      (.conj (.always (FiniteLetterLTL.relation (fun a b =>
        (b.outputOne.residue,b.outputTwo.residue) =
          ScalingSafety.ResidueLTL.update (a.outputOne.residue,a.outputTwo.residue) b.graph ∧ Transition M a b)))
        (.conj (FiniteLetterLTL.boundary (fun r => r.graph = .right) LeftBoundary)
          (FiniteLetterLTL.boundary (fun r => r.graph = .left) RightBoundary))))

theorem satisfies_iff [Fintype Q] (M : Machine Q) (w : OmegaWord (Letter Q)) :
    LTL.Satisfies FiniteLetterLTL.interp w (formula M) ↔ Checks M w := by
  simp only [formula,LTL.Satisfies,LTL.satisfies_always,
    FiniteLetterLTL.satisfies_test,FiniteLetterLTL.satisfies_relation,
    FiniteLetterLTL.satisfies_boundary,OmegaWord.drop_apply,Nat.add_zero]
  constructor
  · rintro ⟨⟨position,initial⟩,localChecks,step,left,right⟩
    exact ⟨⟨congrArg Prod.fst position,congrArg Prod.snd position,fun n => (step n).1⟩,
      fun n => (localChecks n).1,fun n => (localChecks n).2.1,fun n => (localChecks n).2.2.1,
      left,right,initial,fun n => (step n).2,fun n => (localChecks n).2.2.2⟩
  · intro checks
    exact ⟨⟨Prod.ext checks.position.1 checks.position.2.1,checks.initial⟩,
      fun n => ⟨checks.agreement n,checks.balance n,checks.zeroWeight n,checks.live n⟩,
      fun n => ⟨checks.position.2.2 n,checks.transition n⟩,checks.leftBoundary,checks.rightBoundary⟩

/-- The displayed one-counter realizability equivalence on the literal
smaller output alphabet, with arbitrary local perfect-recall strategies. -/
theorem formula_realizable_iff [DecidableEq Q] [Fintype Q]
    (M : Machine Q) (single : OnlyFirst M) :
    (∃ σ : StrategyPair Unit Unit (Output Q) (Output Q),
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula M)) ↔ Nonhalting M := by
  rw [← checks_realizable_iff M single]
  apply exists_congr
  intro σ
  exact forall_congr' (fun env => satisfies_iff M (execution σ env))

theorem position_embed_iff (w : OmegaWord (Letter Q)) :
    ResidueLTL.ResidueValid (OmegaWord.map (mapRecord embed embed) w) ↔ Position w := by
  change (_ = _ ∧ _) ↔ (_ ∧ _ ∧ _)
  rw [Prod.mk.injEq,and_assoc]
  rfl

theorem agreement_embed_iff (r : Letter Q) :
    Paper.Agreement (mapRecord embed embed r) ↔ Agreement r := by
  constructor
  · intro h
    exact ⟨h.1,congrFun h.2 0⟩
  · intro h
    exact ⟨h.1,congrArg zeroFlags h.2⟩

theorem balance_embed_iff (M : Machine Q) (single : OnlyFirst M) (r : Letter Q) :
    Paper.Balance M (mapRecord embed embed r) ↔ Balance M r := by
  unfold Paper.Balance
  simp only [embed_left,embed_right]
  constructor
  · intro all
    exact all 0
  · intro scalar k
    fin_cases k
    · exact scalar
    · simp [embed,dummyPlan,Plan.promised,op_second M single,TernaryCounter.Operation.factor]

theorem zeroWeight_embed_iff (r : Letter Q) :
    Paper.ZeroWeight (mapRecord embed embed r) ↔ ZeroWeight r := by
  unfold Paper.ZeroWeight
  simp only [embed_left]
  constructor
  · intro all
    exact all 0
  · intro scalar k
    fin_cases k
    · exact scalar
    · simp [embed,dummyPlan]

theorem leftBoundary_embed_iff (r : Letter Q) :
    ResidueLTL.leftCheck (mapRecord embed embed r).outputOne.base ↔ LeftBoundary r := by
  constructor
  · intro all
    exact ⟨all.1 0,all.2 0⟩
  · intro scalar
    constructor
    · intro k; fin_cases k; exact scalar.1; rfl
    · intro k; fin_cases k; exact scalar.2; simp [mapRecord,embed,zeroFlags]

theorem rightBoundary_embed_iff (r : Letter Q) :
    ResidueLTL.rightCheck (mapRecord embed embed r).outputTwo.base ↔ RightBoundary r := by
  constructor
  · intro all
    exact all 0
  · intro scalar k
    fin_cases k
    · exact scalar
    · rfl

theorem initial_embed_iff (M : Machine Q) (r : Letter Q) :
    Paper.Initial M (mapRecord embed embed r) ↔ Initial M r := by
  constructor
  · intro all
    exact ⟨all.1,all.2 0⟩
  · intro scalar
    exact ⟨scalar.1,by intro k; fin_cases k; exact scalar.2; rfl⟩

theorem transition_embed_iff (M : Machine Q) (a b : Letter Q) :
    Paper.Transition M (mapRecord embed embed a) (mapRecord embed embed b) ↔ Transition M a b := by
  unfold Paper.Transition
  simp only [embed_left]
  constructor
  · intro all
    exact ⟨all.1,all.2 0⟩
  · intro scalar
    refine ⟨scalar.1,?_⟩
    intro k
    fin_cases k
    · exact scalar.2
    · rfl

/-- Ordinary scalar counter-machine semantics of the embedding. -/
theorem advance_ofCode (initial : Q) (code : Q → Option (Q ⊕ (Q × Q))) (q : Q) (c : Nat) :
    advance (ofCode initial code) (q,c) =
      match code q with
      | none => (q,c)
      | some (.inl target) => (target,c+1)
      | some (.inr targets) => if c = 0 then (targets.1,0) else (targets.2,c-1) := by
  cases h : code q with
  | none => simp [advance,next,op,ofCode,Machine.next,Machine.op,h,TernaryCounter.Operation.applyCount]
  | some i =>
    cases i with
    | inl target => simp [advance,next,op,ofCode,Machine.next,Machine.op,h,TernaryCounter.Operation.applyCount]
    | inr targets =>
      by_cases zero : c = 0 <;>
        simp [advance,next,op,ofCode,Machine.next,Machine.op,h,zeroFlags,zero,TernaryCounter.Operation.applyCount]

/-- Every scalar program is covered; the unused-counter restriction is
proved from its syntax, rather than passed as a behavioral hypothesis. -/
theorem ofCode_realizable_iff [DecidableEq Q] [Fintype Q]
    (initial : Q) (code : Q → Option (Q ⊕ (Q × Q))) :
    (∃ σ : StrategyPair Unit Unit (Output Q) (Output Q),
      ∀ env, LTL.Satisfies FiniteLetterLTL.interp (execution σ env) (formula (ofCode initial code))) ↔
      Nonhalting (ofCode initial code) :=
  formula_realizable_iff (ofCode initial code) (ofCode_onlyFirst initial code)

end DistributedSynthesis.CounterMachine.OneCounter
