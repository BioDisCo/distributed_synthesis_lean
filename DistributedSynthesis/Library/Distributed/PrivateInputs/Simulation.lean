/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PrivateInputs.Model
import DistributedSynthesis.Library.Distributed.PrivateInputs.Paths

/-! # Strategy correspondence on the selected private-input histories -/

namespace DistributedSynthesis.PrivateInputs
open FullViewPath BlockEmbedding GraphExecutions

def inputs (env : EnvironmentSequence Symbol Symbol) (t : Nat) : Input :=
  ((env t).inputOne, (env t).inputTwo)

def encodeEnvironment (x : Nat → Graph) : EnvironmentSequence Symbol Symbol := fun t ↦
  let a := pair (evaluate (graphPrefix x t)).oneLeft (x t)
  ⟨a.1, a.2⟩

@[simp] theorem inputs_encode (x : Nat → Graph) (t : Nat) :
    inputs (encodeEnvironment x) t = pair (evaluate (graphPrefix x t)).oneLeft (x t) := rfl

def Legal (env : EnvironmentSequence Symbol Symbol) : Prop :=
  incoming (inputs env 0) = true ∧ ∀ t,
    Valid (inputs env t) ∧ incoming (inputs env (t+1)) = outgoing (inputs env t)

theorem orientation_succ (x : Nat → Graph) (t : Nat) :
    (evaluate (graphPrefix x (t+1))).oneLeft = turn (evaluate (graphPrefix x t)).oneLeft (x t) := by
  rw [BlockEmbedding.prefix_succ, at_append]
  rfl

theorem encode_legal (x : Nat → Graph) : Legal (encodeEnvironment x) := by
  refine ⟨by simp [graphPrefix, evaluate, root], fun t ↦ ⟨by simp, ?_⟩⟩
  simp only [inputs_encode, incoming_pair, outgoing_pair, orientation_succ]

theorem legal_orientation (env : EnvironmentSequence Symbol Symbol) (h : Legal env) (t : Nat) :
    (evaluate (graphPrefix (fun k ↦ graph (inputs env k)) t)).oneLeft = incoming (inputs env t) := by
  induction t with
  | zero => exact h.1.symm
  | succ t ih => rw [orientation_succ, ih]; exact (h.2 t).2.symm

theorem legal_eq_encode (env : EnvironmentSequence Symbol Symbol) (h : Legal env) :
    env = encodeEnvironment (fun t ↦ graph (inputs env t)) := by
  funext t
  have hh := (h.2 t).1
  unfold Valid at hh
  rw [← legal_orientation env h t] at hh
  have h₁ := congrArg Prod.fst hh
  have h₂ := congrArg Prod.snd hh
  cases he : env t
  simp only [inputs, he] at h₁ h₂
  simp only [encodeEnvironment]
  congr 1
  · simpa only [inputs, he] using h₁
  · simpa only [inputs, he] using h₂

theorem encoded_prefix (x : Nat → Graph) (t : Nat) :
    inputPrefix (fun k ↦ (encodeEnvironment x k).inputOne) t = word (evaluate (graphPrefix x t)).one ∧
    inputPrefix (fun k ↦ (encodeEnvironment x k).inputTwo) t = word (evaluate (graphPrefix x t)).two := by
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    rw [BlockEmbedding.prefix_succ, (word_advance _ _).1, (word_advance _ _).2]
    change (inputPrefix _ t ++ [_] = _) ∧ (inputPrefix _ t ++ [_] = _)
    rw [ih.1, ih.2]
    exact ⟨rfl, rfl⟩

noncomputable def recoverOne (w : List Symbol) : View Unit Unit .one := by
  classical
  exact if h : ∃ h : List Graph, word (evaluate h).one = w then (evaluate h.choose).one else .empty .one

noncomputable def recoverTwo (w : List Symbol) : View Unit Unit .two := by
  classical
  exact if h : ∃ h : List Graph, word (evaluate h).two = w then (evaluate h.choose).two else .empty .two

@[simp] theorem recoverOne_word (h : List Graph) : recoverOne (word (evaluate h).one) = (evaluate h).one := by
  have hh : ∃ k : List Graph, word (evaluate k).one = word (evaluate h).one := ⟨h, rfl⟩
  simp only [recoverOne, dif_pos hh]
  exact (word_one_eq_iff _ _).mp hh.choose_spec

@[simp] theorem recoverTwo_word (h : List Graph) : recoverTwo (word (evaluate h).two) = (evaluate h).two := by
  have hh : ∃ k : List Graph, word (evaluate k).two = word (evaluate h).two := ⟨h, rfl⟩
  simp only [recoverTwo, dif_pos hh]
  exact (word_two_eq_iff _ _).mp hh.choose_spec

noncomputable def encodeStrategy {O₁ O₂ : Type*}
    (σ : DistributedSynthesis.StrategyPair Unit Unit O₁ O₂) : StrategyPair Symbol Symbol O₁ O₂ :=
  ⟨fun w ↦ σ.one (recoverOne w), fun w ↦ σ.two (recoverTwo w)⟩

def decodeStrategy {O₁ O₂ : Type*} (τ : StrategyPair Symbol Symbol O₁ O₂) :
    DistributedSynthesis.StrategyPair Unit Unit O₁ O₂ :=
  ⟨fun v ↦ τ.one (word v), fun v ↦ τ.two (word v)⟩

def sourceLetter {O₁ O₂ : Type*} (r : Letter Symbol Symbol O₁ O₂) :
    RoundRecord Unit Unit Graph O₁ O₂ :=
  ⟨(), (), graph (r.inputOne, r.inputTwo), r.outputOne, r.outputTwo⟩

theorem source_execution_record {O₁ O₂ : Type*}
    (σ : DistributedSynthesis.StrategyPair Unit Unit O₁ O₂)
    (env : DistributedSynthesis.EnvironmentSequence Unit Unit) (t : Nat) :
    DistributedSynthesis.execution σ env t =
      ⟨(), (), (env t).graph,
        σ.one (evaluate (graphPrefix (fun k ↦ (env k).graph) (t+1))).one,
        σ.two (evaluate (graphPrefix (fun k ↦ (env k).graph) (t+1))).two⟩ := by
  have ho := GraphExecutions.execution_outputs σ env t
  have hg := GraphExecutions.execution_graph σ env t
  cases he : DistributedSynthesis.execution σ env t with
  | mk a b g o p => cases a; cases b; simp only [he] at ho hg; simp_all

theorem encode_execution {O₁ O₂ : Type*}
    (σ : DistributedSynthesis.StrategyPair Unit Unit O₁ O₂) (x : Nat → Graph) :
    (fun t ↦ sourceLetter (execution (encodeStrategy σ) (encodeEnvironment x) t)) =
      DistributedSynthesis.execution σ (ofGraphs x) := by
  funext t
  rw [source_execution_record]
  simp only [execution, sourceLetter, encodeStrategy, (encoded_prefix x (t+1)).1,
    (encoded_prefix x (t+1)).2, recoverOne_word, recoverTwo_word, ofGraphs]
  simp [encodeEnvironment]

theorem decode_execution {O₁ O₂ : Type*} (τ : StrategyPair Symbol Symbol O₁ O₂)
    (env : DistributedSynthesis.EnvironmentSequence Unit Unit) :
    DistributedSynthesis.execution (decodeStrategy τ) env =
      fun t ↦ sourceLetter (execution τ (encodeEnvironment (fun k ↦ (env k).graph)) t) := by
  funext t
  rw [source_execution_record]
  simp only [execution, sourceLetter, decodeStrategy]
  rw [(encoded_prefix _ (t+1)).1, (encoded_prefix _ (t+1)).2]
  simp [encodeEnvironment]

end DistributedSynthesis.PrivateInputs
