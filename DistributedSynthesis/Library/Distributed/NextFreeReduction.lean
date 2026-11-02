/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Library.Distributed.NextFreeClock

/-! # Binary LTL synthesis reduces to next-free four-symbol synthesis

The reduction keeps every physical round and every graph environment.
Projection discards the clock bit; lifting appends local view-depth parity.
Both directions use the original perfect-recall strategy and view types.
-/
namespace DistributedSynthesis.NextFreeReduction
open NextFreeClock

def formula (p : LTL BinaryAgreement.Atom) : LTL Atom :=
  .conj protocol (LTL.NextFreeTranslation.translate (.inr .one) Sum.inl p)

theorem formula_nextFree (p : LTL BinaryAgreement.Atom) : LTL.NextFree (formula p) :=
  ⟨protocol_nextFree, LTL.NextFreeTranslation.nextFree _ _ _⟩

def project (τ : Strategies) : StrategyPair Unit Unit Bool Bool :=
  ⟨fun v ↦ (τ.one v).1, fun v ↦ (τ.two v).1⟩

def parity (t : Nat) : Bool := decide (t % 2 = 0)

def lift (σ : StrategyPair Unit Unit Bool Bool) : Strategies :=
  ⟨fun v ↦ (σ.one v, parity (FullViewPath.depth v)),
   fun v ↦ (σ.two v, parity (FullViewPath.depth v))⟩

@[simp] theorem project_lift (σ : StrategyPair Unit Unit Bool Bool) : project (lift σ) = σ := by
  cases σ; rfl

def data (r : Letter) : BinaryAgreement.Letter :=
  ⟨(), (), r.graph, r.outputOne.1, r.outputTwo.1⟩

theorem project_execution (τ : Strategies) (env : EnvironmentSequence Unit Unit) :
    execution (project τ) env = OmegaWord.map data (execution τ env) := by
  funext t
  have h := GraphExecutions.execution_outputs τ env t
  have hp := GraphExecutions.execution_outputs (project τ) env t
  have hg := GraphExecutions.execution_graph τ env t
  have hgp := GraphExecutions.execution_graph (project τ) env t
  change execution (project τ) env t = data (execution τ env t)
  generalize execution (project τ) env t = r at hp hgp ⊢
  generalize execution τ env t = s at h hg ⊢
  cases r with
  | mk i j g o p =>
    cases s with
    | mk i' j' g' o' p' =>
      cases i; cases j; cases i'; cases j'
      congr 1
      · exact hgp.trans hg.symm
      · exact hp.1.trans (congrArg Prod.fst h.1).symm
      · exact hp.2.trans (congrArg Prod.fst h.2).symm

theorem lift_clock (σ : StrategyPair Unit Unit Bool Bool)
    (env : EnvironmentSequence Unit Unit) (t : Nat) :
    (execution (lift σ) env t).outputOne.2 = parity (t+1) ∧
    (execution (lift σ) env t).outputTwo.2 = parity (t+1) := by
  have h := GraphExecutions.execution_outputs (lift σ) env t
  rw [h.1, h.2]
  simp only [lift, FullViewPath.at_depth, BlockEmbedding.prefix_length, and_self]

theorem parity_changes (t : Nat) : parity (t+1) ≠ parity t := by
  have := Nat.mod_lt t (by omega : 0 < 2)
  by_cases ht : t % 2 = 0
  · have hs : (t+1) % 2 ≠ 0 := by omega
    simp [parity, ht, hs]
  · have hs : (t+1) % 2 = 0 := by omega
    simp [parity, ht, hs]

theorem lift_wins_protocol (σ : StrategyPair Unit Unit Bool Bool)
    (env : EnvironmentSequence Unit Unit) :
    LTL.Satisfies interp (execution (lift σ) env) protocol := by
  apply of_alternating
  · intro t; exact (lift_clock σ env t).1.trans (lift_clock σ env t).2.symm
  · intro t
    rw [(lift_clock σ env (t+1)).1, (lift_clock σ env t).1]
    exact parity_changes (t+1)

theorem translation_correct (τ : Strategies)
    (win : ∀ env, LTL.Satisfies interp (execution τ env) protocol)
    (env : EnvironmentSequence Unit Unit) (p : LTL BinaryAgreement.Atom) :
    LTL.Satisfies interp (execution τ env)
        (LTL.NextFreeTranslation.translate (.inr .one) Sum.inl p) ↔
      LTL.Satisfies BinaryAgreement.interp (execution (project τ) env) p := by
  have hc (t : Nat) : interp (.inr .one) (execution τ env (t+1)) ↔
      ¬ interp (.inr .one) (execution τ env t) := by
    have h := winning_alternates τ win env t
    cases ha : (execution τ env (t+1)).outputOne.2 <;>
      cases hb : (execution τ env t).outputOne.2 <;> simp_all [interp]
  rw [project_execution, LTL.satisfies_word_map]
  have he : (fun a l ↦ interp (Sum.inl a) l) =
      (fun a l ↦ BinaryAgreement.interp a (data l)) := by
    funext a l
    rcases a with g | p
    · rfl
    · cases p <;> rfl
  simpa only [OmegaWord.drop_zero, he] using
    LTL.NextFreeTranslation.correct (.inr .one) Sum.inl interp (execution τ env) hc p 0

def BinaryRealizable (p : LTL BinaryAgreement.Atom) : Prop :=
  ∃ σ : StrategyPair Unit Unit Bool Bool, ∀ env,
    LTL.Satisfies BinaryAgreement.interp (execution σ env) p

def Realizable (p : LTL Atom) : Prop :=
  ∃ τ : Strategies, ∀ env, LTL.Satisfies interp (execution τ env) p

/-- No clock, finite-memory, or environment hypothesis remains. -/
theorem realizable_iff (p : LTL BinaryAgreement.Atom) :
    Realizable (formula p) ↔ BinaryRealizable p := by
  constructor
  · rintro ⟨τ, hτ⟩
    have hp : ∀ env, LTL.Satisfies interp (execution τ env) protocol := fun env ↦ (hτ env).1
    exact ⟨project τ, fun env ↦ (translation_correct τ hp env p).mp (hτ env).2⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨lift σ, fun env ↦ ⟨lift_wins_protocol σ env, ?_⟩⟩
    apply (translation_correct (lift σ) (lift_wins_protocol σ) env p).mpr
    simpa only [project_lift] using hσ env

end DistributedSynthesis.NextFreeReduction
