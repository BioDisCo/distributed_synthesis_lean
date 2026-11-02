/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryReduction
import DistributedSynthesis.Library.Logic.EncodedBinarySyntax

/-! # Encoded binary realizability and an atomic-interface composition theorem

The target instance is an ordinary finite postfix LTL string over five fixed
atoms. Its semantics is the original unrestricted perfect-recall execution.
The generic theorem below separates numeric atomic encoding from strategy
serialization; clients must prove the atomic interface, not assume it.
-/
namespace DistributedSynthesis.EncodedBinaryReduction
open BinaryAgreement BinaryReduction BinaryStrategy BlockEmbedding EncodedFiniteLTL

noncomputable instance : Primcodable Atom :=
  Primcodable.ofEquiv (Fin (Fintype.card Atom)) (Fintype.equivFin Atom)

abbrev Instance := Code Atom
def Realizable (c : Instance) : Prop :=
  ∃ τ : StrategyPair Unit Unit Bool Bool, ∀ env,
    LTL.Satisfies interp (execution τ env) (EncodedFiniteLTL.decode c)

def compile {A : Type*} (K : Nat) (ids₁ ids₂ : List Nat) (a : A → Code Atom)
    (c : Code A) : Instance :=
  EncodedBinarySyntax.guard (.inr .one) (.inr .two) (.inl .both) K ids₁ ids₂
    (EncodedBlockTranslation.translate (2*K+3) (EncodedBinarySyntax.marker (.inr .one)) a c)

theorem compile_primrec {X A : Type*} [Primcodable X] [Primcodable A]
    {k : X → Nat} {i₁ i₂ : X → List Nat} {a : X → A → Code Atom} {c : X → Code A}
    (hk : Primrec k) (h₁ : Primrec i₁) (h₂ : Primrec i₂) (ha : Primrec₂ a) (hc : Primrec c) :
    Primrec (fun x ↦ compile (k x) (i₁ x) (i₂ x) (a x) (c x)) :=
  EncodedBinarySyntax.guard_primrec _ _ _ hk h₁ h₂
    (EncodedBlockTranslation.translate_primrec
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hk) (Primrec.const 3))
      (Primrec.const _) ha hc)

section Semantics
variable {A O₁ O₂ : Type*} [Nonempty O₁] [Nonempty O₂] {K : Nat}
variable (c₁ : BinaryWords.Code O₁ K) (c₂ : BinaryWords.Code O₂ K)
variable (a₁ : List O₁) (a₂ : List O₂) (ha₁ : ∀ a, a ∈ a₁) (ha₂ : ∀ a, a ∈ a₂)

def formula (atom : A → LTL Atom) (φ : LTL A) : LTL Atom :=
  EncodedBinarySyntax.guardFormula (.inr .one) (.inr .two) (.inl .both) K
    (BinaryWords.valid (.inr .two) c₁ a₁) (BinaryWords.valid (.inr .one) c₂ a₂)
    (LTL.BlockTranslation.translate (2*K+3) marker atom φ)

omit [Nonempty O₁] [Nonempty O₂] in
theorem protocol_validity {a : A → LTL Atom} {φ : LTL A}
    (τ : StrategyPair Unit Unit Bool Bool)
    (hw : ∀ env, LTL.Satisfies interp (execution τ env) (formula c₁ c₂ a₁ a₂ a φ)) :
    TargetWinning c₁ c₂ a₁ a₂ .verum τ := by
  intro env
  exact ⟨(hw env).1, (hw env).2.1, Or.inr trivial⟩

/-- The atomic interface is required only on representing words. -/
def AtomCorrect (I : A → SourceLetter O₁ O₂ → Prop) (a : A → LTL Atom) : Prop :=
  ∀ s w, BinaryReduction.Represents c₁ c₂ s w → ∀ x n,
    LTL.Satisfies interp (w.drop ((2*K+3)*n)) (a x) ↔ I x (s n)

include ha₁ ha₂ in
theorem semantic_iff (I : A → SourceLetter O₁ O₂ → Prop) (a : A → LTL Atom)
    (ha : AtomCorrect c₁ c₂ I a) (φ : LTL A) :
    (∃ σ : StrategyPair Unit Unit O₁ O₂, ∀ env, LTL.Satisfies I (execution σ env) φ) ↔
      ∃ τ : StrategyPair Unit Unit Bool Bool, ∀ env,
        LTL.Satisfies interp (execution τ env) (formula c₁ c₂ a₁ a₂ a φ) := by
  classical
  have ht (s : OmegaWord (SourceLetter O₁ O₂)) (w : OmegaWord Letter)
      (hr : BinaryReduction.Represents c₁ c₂ s w)
      (hf : LTL.Satisfies interp w (LTL.BinaryClock.frame (.inr .one) (.inr .two) K)) :
      LTL.Satisfies interp w (LTL.BlockTranslation.translate (2*K+3) marker a φ) ↔
        LTL.Satisfies I s φ := by
    simpa using LTL.BlockTranslation.correct (2*K+3) (by omega) marker a I interp s w
      (LTL.BinaryClock.clock_exact _ _ _ _ _ hf) (ha s w hr) φ 0
  constructor
  · rintro ⟨σ, hw⟩
    refine ⟨encode c₁ c₂ σ, fun env ↦ ?_⟩
    refine ⟨encode_winning c₁ c₂ σ env, encode_valid_on_core c₁ c₂ a₁ a₂ ha₁ ha₂ σ env, ?_⟩
    change ¬ LTL.Satisfies interp _ coreCondition ∨ _
    by_cases hc : LTL.Satisfies interp (execution (encode c₁ c₂ σ) env) coreCondition
    · right
      have hf := (encode_winning c₁ c₂ σ env).1
      have he := environment_as_stream (2*K+3) env (core_environment K _ env hf hc)
      rw [he]
      exact (ht _ _ (encoded_represents c₁ c₂ σ _) (encode_winning c₁ c₂ σ _).1).mpr (hw _)
    · exact Or.inl hc
  · rintro ⟨τ, hw⟩
    have hp := protocol_validity c₁ c₂ a₁ a₂ τ hw
    have hprot := target_protocol c₁ c₂ a₁ a₂ .verum τ hp
    refine ⟨BinaryReduction.decode c₁ c₂ τ, fun env ↦ ?_⟩
    let source := fun t ↦ (env t).graph
    have hc := stream_core K τ hprot source
    have hh := (hw (GraphExecutions.ofGraphs (stream (2*K+3) source))).2.2
    have hh' : LTL.Satisfies interp
        (execution τ (GraphExecutions.ofGraphs (stream (2*K+3) source)))
        (LTL.BlockTranslation.translate (2*K+3) marker a φ) := hh.resolve_left (fun hn ↦ hn hc)
    have hs := (ht _ _ (decoded_represents c₁ c₂ a₁ a₂ .verum τ hp source) (hprot _).1).mp hh'
    rw [environment_as_graphs env]
    exact hs

omit [Nonempty O₁] [Nonempty O₂] in
theorem compile_rep (ids₁ ids₂ : List Nat) (atom : A → Code Atom) (a : A → LTL Atom)
    (h₁ : Represents (EncodedBinarySyntax.valid K (.inr .two : Atom) ids₁) (BinaryWords.valid (.inr .two : Atom) c₁ a₁))
    (h₂ : Represents (EncodedBinarySyntax.valid K (.inr .one : Atom) ids₂) (BinaryWords.valid (.inr .one : Atom) c₂ a₂))
    (ha : ∀ x, Represents (atom x) (a x)) (c : Code A) :
    Represents (compile K ids₁ ids₂ atom c) (formula c₁ c₂ a₁ a₂ a (EncodedFiniteLTL.decode c)) :=
  EncodedBinarySyntax.guard_rep _ _ _ K ids₁ ids₂ _ _ _ _ h₁ h₂
    (EncodedBlockTranslation.translate_rep _ _ _ (EncodedBinarySyntax.marker_rep _) atom a ha c)

end Semantics
end DistributedSynthesis.EncodedBinaryReduction
