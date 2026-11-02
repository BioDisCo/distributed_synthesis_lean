/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

/-! Invert the bank's complete round and output decoding tables. These
lookups connect physical leader outputs to the original memory numbering
without imposing a particular product enumeration or graph-code order. -/
namespace Characterisation.EncodedClosingBanks
open DistributedSynthesis
local instance bankIndexRoundBEq : BEq EncodedClosingObservations.Round := instBEqOfDecidableEq
local instance bankIndexOutputBEq : BEq (Nat × Nat) := instBEqOfDecidableEq

private theorem ofFn_index {A Code : Type} {N : Nat} [DecidableEq Code]
    (e : A ≃ Fin N) (f : A → Code) (injective : Function.Injective f) (a : A) :
    @List.idxOf Code instBEqOfDecidableEq (f a) (List.ofFn (fun i => f (e.symm i))) = (e a).val := by
  letI : BEq Code := instBEqOfDecidableEq
  have nodup : (List.ofFn (fun i => f (e.symm i))).Nodup :=
    List.nodup_ofFn.mpr (injective.comp e.symm.injective)
  simpa using nodup.idxOf_getElem (e a)

variable {H I₁ I₂ O₁ O₂ : Type} {R E V N₁ N₂ P₁ P₂ D : Nat}
  (root : H ≃ Fin R) (env : (I₁ × I₂ × Graph) ≃ Fin E)
  (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
  (output : (O₁ × O₂) ≃ Fin V) (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
  (shape : InputShape H)

theorem roundTable_index (r : I₁ × I₂ × Graph) :
    (roundTable (dataEncode root env one two output outOne outTwo shape D)).idxOf
      (EncodedClosingObservations.roundEncode one two r) = (env r).val := by
  apply ofFn_index env (EncodedClosingObservations.roundEncode one two) _ r
  intro a b same
  apply Prod.ext
  · apply one.injective
    exact Fin.ext (congrArg Prod.fst same)
  · apply Prod.ext
    · apply two.injective
      exact Fin.ext (congrArg (fun x : EncodedClosingObservations.Round => x.2.1) same)
    · have graphs := congrArg (fun x : EncodedClosingObservations.Round => x.2.2) same
      cases ha : a.2.2 <;> cases hb : b.2.2 <;>
        simp_all [EncodedClosingObservations.roundEncode,graphCode]

theorem outputTable_index (o : O₁ × O₂) :
    (outputTable (dataEncode root env one two output outOne outTwo shape D)).idxOf
      ((outOne o.1).val,(outTwo o.2).val) = (output o).val := by
  apply ofFn_index output (fun o => ((outOne o.1).val,(outTwo o.2).val)) _ o
  intro a b same
  exact Prod.ext (outOne.injective (Fin.ext (congrArg Prod.fst same)))
    (outTwo.injective (Fin.ext (congrArg Prod.snd same)))

end Characterisation.EncodedClosingBanks
