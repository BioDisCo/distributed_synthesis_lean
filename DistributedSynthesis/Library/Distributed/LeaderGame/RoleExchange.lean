/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderMoves

/-! Exchange physical process roles without making any claim about the
canonical leader selector. Histories keep exactly the same number of rounds.
This transport is used for the leftward phase's local strategy only; graph
states and boundary decisions remain in the original model. -/
namespace Characterisation
open DistributedSynthesis

def exchangeGraph : Graph → Graph
  | .left => .right
  | .right => .left
  | .both => .both

@[simp] theorem exchangeGraph_twice (g : Graph) : exchangeGraph (exchangeGraph g) = g := by
  cases g <;> rfl

def exchangeInput {I₁ I₂ : Type} (r : I₁ × I₂ × Graph) : I₂ × I₁ × Graph :=
  (r.2.1,r.1,exchangeGraph r.2.2)

@[simp] theorem exchangeInput_twice {I₁ I₂ : Type} (r : I₁ × I₂ × Graph) :
    exchangeInput (exchangeInput r) = r := by simp [exchangeInput]

def exchangeRound {I₁ I₂ O₁ O₂ : Type} (r : RoundRecord I₁ I₂ Graph O₁ O₂) :
    RoundRecord I₂ I₁ Graph O₂ O₁ :=
  ⟨r.inputTwo,r.inputOne,exchangeGraph r.graph,r.outputTwo,r.outputOne⟩

@[simp] theorem exchangeRound_twice {I₁ I₂ O₁ O₂ : Type} (r : RoundRecord I₁ I₂ Graph O₁ O₂) :
    exchangeRound (exchangeRound r) = r := by cases r; simp [exchangeRound]

def exchangeHistory {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) : EnvHistory I₂ I₁ :=
  h.map exchangeRound

@[simp] theorem exchangeHistory_twice {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) :
    exchangeHistory (exchangeHistory h) = h := by
  simp [exchangeHistory,List.map_map,Function.comp_def]

@[simp] theorem exchangeHistory_length {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) :
    List.length (exchangeHistory h) = List.length h := by simp [exchangeHistory]

@[simp] theorem exchangeHistory_append {I₁ I₂ : Type} (h k : EnvHistory I₁ I₂) :
    exchangeHistory (h ++ k) = exchangeHistory h ++ exchangeHistory k := List.map_append

def exchangeSum {I₁ I₂ : Type} : PSum I₁ I₂ → PSum I₂ I₁
  | .inl i => .inr i
  | .inr i => .inl i

@[simp] theorem exchangeSum_twice {I₁ I₂ : Type} (i : PSum I₁ I₂) :
    exchangeSum (exchangeSum i) = i := by cases i <;> rfl

def exchangeView {I₁ I₂ : Type} {p : Proc} : View I₁ I₂ p → View I₂ I₁ p.other
  | .empty p => .empty p.other
  | .noRecv v i => .noRecv (exchangeView v) (exchangeSum i)
  | .recv v i w j => .recv (exchangeView v) (exchangeSum i) (exchangeView w) (exchangeSum j)

theorem exchangeView_twice {I₁ I₂ : Type} {p : Proc} (v : View I₁ I₂ p) :
    HEq (exchangeView (exchangeView v)) v := by
  induction v with
  | empty p => cases p <;> rfl
  | @noRecv p v i ih => cases p <;> simp_all only [exchangeView,Proc.other,exchangeSum_twice,heq_eq_eq]
  | @recv p v i w j ih iw =>
    cases p <;> simp_all only [exchangeView,Proc.other,exchangeSum_twice,heq_eq_eq]

@[simp] theorem exchangeView_twice_one {I₁ I₂ : Type} (v : View I₁ I₂ .one) :
    exchangeView (exchangeView v) = v := eq_of_heq (exchangeView_twice v)

@[simp] theorem exchangeView_twice_two {I₁ I₂ : Type} (v : View I₁ I₂ .two) :
    exchangeView (exchangeView v) = v := eq_of_heq (exchangeView_twice v)

theorem exchangeView_injective {I₁ I₂ : Type} (p : Proc) :
    Function.Injective (@exchangeView I₁ I₂ p) := by
  intro v w equal
  cases p <;> simpa using congrArg exchangeView equal

theorem exchangeHistory_viewPair {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) :
    viewPair (exchangeHistory h) = (exchangeView (viewPair h).2,exchangeView (viewPair h).1) := by
  induction h using List.reverseRecOn with
  | nil => rfl
  | append_singleton h r ih =>
    rw [exchangeHistory_append]
    change viewPair (History.append (exchangeHistory h) (exchangeRound r)) = _
    rw [viewPair_append,ih]
    change _ = (exchangeView (viewPair (History.append h r)).2,
      exchangeView (viewPair (History.append h r)).1)
    rw [viewPair_append]
    cases r with
    | mk i j g x y => cases g <;> rfl

@[simp] theorem exchangeHistory_view_one {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) :
    currentView .one (exchangeHistory h) = exchangeView (currentView .two h) :=
  congrArg Prod.fst (exchangeHistory_viewPair h)

@[simp] theorem exchangeHistory_view_two {I₁ I₂ : Type} (h : EnvHistory I₁ I₂) :
    currentView .two (exchangeHistory h) = exchangeView (currentView .one h) :=
  congrArg Prod.snd (exchangeHistory_viewPair h)

def exchangeStrategy {I₁ I₂ O₁ O₂ : Type} (σ : StrategyPair I₁ I₂ O₁ O₂) :
    StrategyPair I₂ I₁ O₂ O₁ where
  one v := σ.two (exchangeView v)
  two v := σ.one (exchangeView v)

@[simp] theorem exchangeStrategy_one_history {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) :
    (exchangeStrategy σ).one (currentView .one (exchangeHistory h)) = σ.two (currentView .two h) := by
  change σ.two (exchangeView (currentView .one (exchangeHistory h))) = _
  rw [exchangeHistory_view_one]
  exact congrArg σ.two (exchangeView_twice_two _)

@[simp] theorem exchangeStrategy_two_history {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) :
    (exchangeStrategy σ).two (currentView .two (exchangeHistory h)) = σ.one (currentView .one h) := by
  change σ.one (exchangeView (currentView .two (exchangeHistory h))) = _
  rw [exchangeHistory_view_two]
  exact congrArg σ.one (exchangeView_twice_one _)

def exchangeShape {H : Type} (shape : InputShape H) : InputShape H :=
  fun p => shape p.other

theorem exchangeShape_exact {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (shape : InputShape H) (rep : RepresentsInputShape past shape) :
    RepresentsInputShape (exchangeHistory ∘ past) (exchangeShape shape) := by
  intro p h k
  cases p <;> simp only [exchangeShape,Proc.other,Function.comp_apply,
    exchangeHistory_view_one,exchangeHistory_view_two]
  · exact (rep .two h k).trans (exchangeView_injective .two).eq_iff.symm
  · exact (rep .one h k).trans (exchangeView_injective .one).eq_iff.symm

def exchangeScenario {H I₁ I₂ : Type} {D : Nat} (s : WindowScenario H I₁ I₂ D) :
    WindowScenario H I₂ I₁ D := (s.1,⟨s.2.1,fun i => exchangeInput (s.2.2 i)⟩)

@[simp] theorem exchangeScenario_twice {H I₁ I₂ : Type} {D : Nat} (s : WindowScenario H I₁ I₂ D) :
    exchangeScenario (exchangeScenario s) = s := by
  rcases s with ⟨h,t,word⟩
  simp [exchangeScenario]

theorem exchangeScenario_history {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (D : Nat) (s : WindowScenario H I₁ I₂ D) :
    windowHistory (exchangeHistory ∘ past) D (exchangeScenario s) =
      exchangeHistory (windowHistory past D s) := by
  simp only [windowHistory,exchangeScenario,Function.comp_apply,
    exchangeHistory,List.map_append,List.map_ofFn]
  rfl

def exchangePlan {I₁ I₂ O₁ O₂ : Type} {D : Nat} (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) :
    LeaderClosingPlan I₂ I₁ O₂ O₁ D := fun s => (plan (exchangeScenario s)).swap

@[simp] theorem exchangePlan_twice {I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (plan : LeaderClosingPlan I₁ I₂ O₁ O₂ D) : exchangePlan (exchangePlan plan) = plan := by
  funext s
  simp [exchangePlan]

theorem exchangePlan_strategy {I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (h : EnvHistory I₁ I₂) (D : Nat) :
    closingPlanOfStrategy (exchangeStrategy σ) (exchangeHistory h) D =
      exchangePlan (closingPlanOfStrategy σ h D) := by
  funext s
  have history := exchangeScenario_history (fun _ : Unit => h) D (exchangeScenario s)
  simp only [exchangeScenario_twice,Function.comp_def] at history
  simp only [closingPlanOfStrategy,exchangePlan,history,Prod.swap,
    exchangeStrategy_one_history,exchangeStrategy_two_history]

def leftInputHistory {I₁ I₂ : Type} (node : List (I₁ × I₂)) : EnvHistory I₁ I₂ :=
  node.map fun r => ⟨r.1,r.2,.left,(),()⟩

def leftSourceHistory {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (node : List (I₁ × I₂)) (h : H) := past h ++ leftInputHistory node

theorem exchange_leftSourceHistory {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (node : List (I₁ × I₂)) (h : H) :
    exchangeHistory (leftSourceHistory past node h) =
      rollingSourceHistory (exchangeHistory ∘ past) node h := by
  simp only [leftSourceHistory,rollingSourceHistory,Function.comp_apply,
    leftInputHistory,rightInputHistory,exchangeHistory,List.map_append,List.map_map]
  rfl

def exchangeLetter {I₁ I₂ O₁ O₂ : Type} (r : ContinuationLetter I₁ I₂ O₁ O₂) :
    ContinuationLetter I₂ I₁ O₂ O₁ := (exchangeInput r.1,r.2.swap)

@[simp] theorem exchangeLetter_twice {I₁ I₂ O₁ O₂ : Type} (r : ContinuationLetter I₁ I₂ O₁ O₂) :
    exchangeLetter (exchangeLetter r) = r := by simp [exchangeLetter]

theorem exchange_continuation_history {H I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (h : H) (env : Nat → I₁ × I₂ × Graph) (n : Nat) :
    closingLayerHistory (exchangeHistory ∘ past) n (continuationScenario h (exchangeInput ∘ env) n) =
      exchangeHistory (closingLayerHistory past n (continuationScenario h env n)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [continuationScenario,closingLayerHistory,scenarioHistory]
    rw [exchangeHistory_append,ih]
    rfl

/-- The equality is at each physical position, so objectives with X and
strategies which count rounds are transported without a timing quotient. -/
theorem exchange_continuation_trace {H I₁ I₂ O₁ O₂ : Type}
    (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (h : H) (env : Nat → I₁ × I₂ × Graph) :
    continuationTrace (strategyContinuationPolicy (exchangeStrategy σ) (exchangeHistory ∘ past)) h
      (exchangeInput ∘ env) =
      exchangeLetter ∘ continuationTrace (strategyContinuationPolicy σ past) h env := by
  funext n
  simp only [continuationTrace,strategyContinuationPolicy,exchange_continuation_history,
    exchangeStrategy_one_history,exchangeStrategy_two_history,Function.comp_apply,exchangeLetter,Prod.swap]

theorem exchange_continuation_wins {H I₁ I₂ O₁ O₂ : Type}
    (objective : DetParityAutomaton (ContinuationLetter I₁ I₂ O₁ O₂))
    (initial : H → objective.State) (σ : StrategyPair I₁ I₂ O₁ O₂) (past : H → EnvHistory I₁ I₂)
    (winning : ContinuationWins objective.AcceptsFrom initial (strategyContinuationPolicy σ past)) :
    ContinuationWins (objective.comap exchangeLetter).AcceptsFrom initial
      (strategyContinuationPolicy (exchangeStrategy σ) (exchangeHistory ∘ past)) := by
  intro h env
  rw [DetParityAutomaton.comap_acceptsFrom_iff]
  have trace := exchange_continuation_trace σ past h (exchangeInput ∘ env)
  simp only [Function.comp_def,exchangeInput_twice] at trace
  change continuationTrace (strategyContinuationPolicy (exchangeStrategy σ) (exchangeHistory ∘ past)) h env = _ at trace
  rw [trace]
  have mapped : OmegaWord.map exchangeLetter
      (fun n => exchangeLetter (continuationTrace (strategyContinuationPolicy σ past) h (exchangeInput ∘ env) n)) =
      continuationTrace (strategyContinuationPolicy σ past) h (exchangeInput ∘ env) := by
    funext n
    exact exchangeLetter_twice _
  change objective.AcceptsFrom (initial h) (OmegaWord.map exchangeLetter
    (fun n => exchangeLetter (continuationTrace (strategyContinuationPolicy σ past) h (exchangeInput ∘ env) n)))
  rw [mapped]
  exact winning h (exchangeInput ∘ env)

/-- Decode the existing rightward readback into a leftward physical
strategy, including one common bank for every hypothetical closing word. -/
theorem exchange_left_readback {H G I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (past : H → EnvHistory I₁ I₂) (group : H → G)
    (bank : ClosingPlanBank H I₂ I₁ O₂ O₁ D)
    (receiver : ReceiverBlockStrategy I₁ I₂ (RollingReceiverOutput H I₂ I₁ O₂ O₁ D))
    (leader : SenderBlockStrategy I₂ (G → O₂))
    (τ : StrategyPair I₂ I₁ O₂ O₁)
    (plans : ∀ node h, closingPlanOfStrategy τ
      (rollingSourceHistory (exchangeHistory ∘ past) node h) (D+1) =
        receiverClosingBank bank receiver node h)
    (outputs : ∀ node r h,
      τ.one (currentView .one (rollingSourceHistory (exchangeHistory ∘ past) (node++[r]) h)) =
        leader (senderWord node) r.2 (group h) ∧
      τ.two (currentView .two (rollingSourceHistory (exchangeHistory ∘ past) (node++[r]) h)) =
        (receiver node r).1 h) :
    (∀ node h, closingPlanOfStrategy (exchangeStrategy τ) (leftSourceHistory past node h) (D+1) =
      exchangePlan (receiverClosingBank bank receiver node h)) ∧
    ∀ node r h,
      (exchangeStrategy τ).one (currentView .one (leftSourceHistory past (node++[r]) h)) =
        (receiver node r).1 h ∧
      (exchangeStrategy τ).two (currentView .two (leftSourceHistory past (node++[r]) h)) =
        leader (senderWord node) r.2 (group h) := by
  constructor
  · intro node h
    have result := exchangePlan_strategy τ (exchangeHistory (leftSourceHistory past node h)) (D+1)
    rw [exchangeHistory_twice,exchange_leftSourceHistory,plans] at result
    exact result
  · intro node r h
    have result := outputs node r h
    rw [← exchange_leftSourceHistory,exchangeHistory_view_one,exchangeHistory_view_two] at result
    exact ⟨result.2,result.1⟩

end Characterisation
