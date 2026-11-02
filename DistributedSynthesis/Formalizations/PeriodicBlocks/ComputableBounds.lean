/- Project authors: see AUTHORS.md at the repository root. -/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import DistributedSynthesis.Formalizations.PeriodicBlocks.Compression
import DistributedSynthesis.Formalizations.PeriodicBlocks.PrimitiveRecursive
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockCompression

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
set_option maxHeartbeats 1200000

/-- An arithmetic upper bound, uniform in all finite alphabets and states. -/
def numericCompressionBound (g q e o d : Nat) : Nat :=
  g * (q * (o ^ ((e+1)^d) * (2^(e^d)))) * e^d

@[fun_prop] theorem nat_pow_primrec : Primrec (fun x : Nat × Nat => x.1^x.2) :=
  Primrec₂.unpaired'.mp Nat.Primrec.pow

@[fun_prop] theorem numericCompressionBound_primrec :
    Primrec (fun x : Nat × Nat × Nat × Nat × Nat =>
      numericCompressionBound x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  unfold numericCompressionBound
  fun_prop

theorem blockPrefix_card_le {E : Type} [Finite E] (D : Nat) :
    Nat.card (BlockPrefix E D) ≤ (Nat.card E+1)^D := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let code (u : BlockPrefix E D) : Fin D → Option E := fun i => u.val[i.val]?
  have inj : Function.Injective code := by
    intro u v eq
    apply Subtype.ext
    apply List.ext_getElem?
    intro i
    by_cases hi : i<D
    · exact congrFun eq ⟨i,hi⟩
    · have hu := u.property.2
      have hv := v.property.2
      rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
  simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_option] using Nat.card_le_card_of_injective code inj

theorem blockWord_card {E : Type} [Fintype E] (D : Nat) :
    Nat.card (BlockWord E D) = (Nat.card E)^D := by
  change Nat.card (List.Vector E D) = _
  simp only [Nat.card_eq_fintype_card,card_vector]

/-- The finite compression width needed by completeness has a uniform
primitive-recursive upper bound. -/
theorem compressionBound_le_numeric
    (I₁ I₂ O₁ O₂ G Q : Type) [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂]
    [Fintype G] [Fintype Q] [Nonempty O₁] [Nonempty O₂] (D : Nat) :
    compressionBound I₁ I₂ O₁ O₂ G Q D ≤
      numericCompressionBound (Nat.card G) (Nat.card Q)
        (Nat.card (I₁ × I₂ × Graph)) (Nat.card (O₁ × O₂)) D := by
  classical
  let E := RoundRecord I₁ I₂ Graph Unit Unit
  let W := BlockPrefix E D
  let Z := BlockWord E D
  let equivalence : StrategyBlockType I₁ I₂ O₁ O₂ G Q D ≃
      G × Q × (W → O₁ × O₂) × (Z → Bool) :=
    { toFun := fun t => (t.graphState,t.objectiveState,t.rule,t.suffixes)
      invFun := fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2⟩
      left_inv := by intro t; cases t; rfl
      right_inv := by intro t; rfl }
  have eventCard : Nat.card E = Nat.card (I₁ × I₂ × Graph) := Nat.card_congr (envRecordEquiv I₁ I₂).symm
  have prefixBound := blockPrefix_card_le (E:=E) D
  have suffixBound := blockWord_card (E:=E) D
  rw [eventCard] at prefixBound suffixBound
  have types : Nat.card (StrategyBlockType I₁ I₂ O₁ O₂ G Q D) =
      Nat.card G * (Nat.card Q * ((Nat.card (O₁ × O₂))^Nat.card W * 2^Nat.card Z)) := by
    rw [Nat.card_congr equivalence,Nat.card_prod,Nat.card_prod,Nat.card_prod]
    simp only [Nat.card_fun]
    rw [show Nat.card Bool=2 by simp [Nat.card_eq_fintype_card]]
  unfold compressionBound numericCompressionBound
  rw [types]
  change Nat.card G * (Nat.card Q * ((Nat.card (O₁ × O₂))^Nat.card W * 2^Nat.card Z)) * Nat.card Z ≤ _
  rw [show Nat.card Z = Nat.card (I₁ × I₂ × Graph)^D from suffixBound]
  apply Nat.mul_le_mul_right
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_left
  apply Nat.mul_le_mul_right
  exact Nat.pow_le_pow_right (Nat.card_pos (α:=O₁ × O₂)) prefixBound

/-- One block length works for every pair of private-input alphabets. -/
theorem holes_uniform_block_length (A : Set (Nat → Graph)) (regular : OmegaRegular A)
    (holes : GeometricHoles A) :
    ∃ D, 0 < D ∧ ∀ (I₁ I₂ : Type), CommonBlockRoots (I₁:=I₁) (I₂:=I₂) (LivePrefix A) D := by
  obtain ⟨d,recent⟩ := holes_component_recent_receiver A regular holes
  refine ⟨d+1,by omega,?_⟩
  intro I₁ I₂ R anchor live root suffix lengths connected
  obtain ⟨p,hp⟩ := recent _ live
  refine ⟨p,common_roots_of_common_lag root suffix (d+1) lengths p ?_⟩
  intro i j
  rw [lagView_succ_outer d,lagView_succ_outer d]
  apply congrArg (lagView 1)
  exact (selected_lag_component _ d p hp (connected i)).symm.trans
    (selected_lag_component _ d p hp (connected j))

end Characterisation.PeriodicBlocks
