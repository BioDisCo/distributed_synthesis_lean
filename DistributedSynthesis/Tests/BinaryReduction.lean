/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.BinaryReduction

/-! Public clients of the complete semantic binary serialization theorem. -/
open DistributedSynthesis BinaryReduction

private def code := BinaryWords.finCode 2 2 (by omega)

example (φ : LTL (SourceLetter (Fin 2) (Fin 2))) :
    (∃ σ, SourceWinning φ σ) ↔ ∃ τ, TargetWinning code code [0,1] [0,1] φ τ := by
  apply realizable_iff
  all_goals intro a; fin_cases a <;> simp

-- Both directions are transformations of actual local strategies.
example (φ : LTL (SourceLetter (Fin 2) (Fin 2)))
    (τ : StrategyPair Unit Unit Bool Bool) (hw : TargetWinning code code [0,1] [0,1] φ τ) :
    SourceWinning φ (decode code code τ) :=
  decode_wins code code [0,1] [0,1] φ τ hw

private def mixed : LTL (SourceLetter (Fin 2) (Fin 3)) :=
  .release (.atom ⟨(), (), .left, 0, 2⟩)
    (.until (.neg (.atom ⟨(), (), .right, 1, 0⟩)) (.next .verum))

example : (∃ σ, SourceWinning mixed σ) ↔
    ∃ τ : StrategyPair Unit Unit Bool Bool, ∀ env,
      LTL.Satisfies BinaryAgreement.interp (execution τ env) (finCompile 2 3 mixed) :=
  fin_realizable_iff 2 3 mixed

-- These finite syntax transformations execute, without arbitrary-strategy choice.
#guard (translate code code (.next .verum)).size = 8
#guard (finCompile 2 3 mixed).size > mixed.size

-- Zero-width codes are also covered when both alphabets are singletons.
private def unitCode : BinaryWords.Code Unit 0 where
  bits _ j := Fin.elim0 j
  injective := by intro a b _; cases a; cases b; rfl

example (φ : LTL (SourceLetter Unit Unit)) :
    (∃ σ, SourceWinning φ σ) ↔ ∃ τ, TargetWinning unitCode unitCode [()] [()] φ τ := by
  apply realizable_iff
  all_goals intro a; cases a; simp
