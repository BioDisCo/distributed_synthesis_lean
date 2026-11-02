/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.ContinuationTransfer

/-! Exact semantics of winning continuation summaries. The predicate below
retains the full infinite objective; it is not a safety approximation or a
claim that membership has already been decided. -/
namespace Characterisation
open DistributedSynthesis

abbrev ContinuationLetter (I₁ I₂ O₁ O₂ : Type) :=
  (I₁ × I₂ × Graph) × (O₁ × O₂)

def continuationScenario {H I₁ I₂ : Type} (h : H)
    (env : Nat → I₁ × I₂ × Graph) : (n : Nat) → ClosingLayer H I₁ I₂ n
  | 0 => h
  | n+1 => (continuationScenario h env n,env n)

/-- A branch contains exactly its first n physical rounds, after the given
root. In particular output zero is produced after the first new reception. -/
theorem continuationScenario_history {H I₁ I₂ : Type}
    (past : H → EnvHistory I₁ I₂) (h : H) (env : Nat → I₁ × I₂ × Graph) (n : Nat) :
    closingLayerHistory past n (continuationScenario h env n) =
      past h ++ (branchNode env n).map (fun r =>
        (⟨r.1,r.2.1,r.2.2,(),()⟩ : RoundRecord I₁ I₂ Graph Unit Unit)) := by
  induction n with
  | zero => simp [continuationScenario,closingLayerHistory,branchNode]
  | succ n ih =>
    simp only [continuationScenario,closingLayerHistory,scenarioHistory,
      branchNode,List.map_append,List.map_singleton,← List.append_assoc,ih]

def continuationTrace {H I₁ I₂ O₁ O₂ : Type}
    (out : ContinuationPolicy H I₁ I₂ O₁ O₂) (h : H)
    (env : Nat → I₁ × I₂ × Graph) : Nat → ContinuationLetter I₁ I₂ O₁ O₂ :=
  fun n => (env n,out n (continuationScenario h env (n+1)))

/-- The incoming annotation specifies the residual objective, including
the omega-acceptance of the adversary when it is not closed. -/
def ContinuationWins {H I₁ I₂ O₁ O₂ Q : Type}
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    (label : H → Q) (out : ContinuationPolicy H I₁ I₂ O₁ O₂) : Prop :=
  ∀ h env, accept (label h) (continuationTrace out h env)

/-- Semantic winning on the finite observation and annotation interface.
There is one coherent policy for all roots and all infinite branches. -/
def ContinuationWinning {H I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    (shape : InputShape H) (label : H → Q) : Prop :=
  ∃ out : ContinuationPolicy H I₁ I₂ O₁ O₂,
    ContinuationCoherent shape out ∧ ContinuationWins accept label out

/-- Exact strategy correspondence, with the universal quantifiers inside
the single strategy choice. No finite bound on continuation length is used. -/
theorem continuationWinning_iff_strategy {H I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    (past : H → EnvHistory I₁ I₂) (shape : InputShape H)
    (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ h, List.length (past h) = L) (label : H → Q) :
    ContinuationWinning accept shape label ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
        ContinuationWins accept label (strategyContinuationPolicy σ past) := by
  constructor
  · rintro ⟨out,coherent,winning⟩
    obtain ⟨σ,correct⟩ := (continuation_coherent_iff_local past shape rep L depth out).mp coherent
    have eq : strategyContinuationPolicy σ past = out := by
      funext n s
      exact Prod.ext (correct n s).1 (correct n s).2
    exact ⟨σ,by rw [eq]; exact winning⟩
  · rintro ⟨σ,winning⟩
    exact ⟨strategyContinuationPolicy σ past,
      strategyContinuationPolicy_coherent σ past shape rep,winning⟩

def SwitchContinuationWinning {I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂]
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    {B : Nat} (summary : SwitchInterface Q B) : Prop :=
  ContinuationWinning accept summary.2.1 summary.2.2

/-- A summary admits a winning continuation exactly when any concrete
realization of that summary does. This discharges dependence on the
particular histories used to represent a boundary. -/
theorem switchContinuationWinning_iff_strategy {I₁ I₂ O₁ O₂ Q : Type}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (accept : Q → (Nat → ContinuationLetter I₁ I₂ O₁ O₂) → Prop)
    {B : Nat} (summary : SwitchInterface Q B)
    (past : Fin summary.1.val → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past summary.2.1)
    (L : Nat) (depth : ∀ h, List.length (past h) = L) :
    SwitchContinuationWinning accept summary ↔
      ∃ σ : StrategyPair I₁ I₂ O₁ O₂,
        ContinuationWins accept summary.2.2 (strategyContinuationPolicy σ past) :=
  continuationWinning_iff_strategy accept past summary.2.1 rep L depth summary.2.2

end Characterisation
