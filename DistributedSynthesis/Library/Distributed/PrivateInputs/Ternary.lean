/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PrivateInputs.Simulation
import DistributedSynthesis.Library.Distributed.EncodedBinaryReduction

/-! # Effective LTL selection of the paths in the private-input model

Atoms test ordinary finite round letters. The source is the existing fixed
Boolean-output communication model. Both the assumption and the compiler
are finite postfix LTL syntax; the target predicate contains no source code.
-/

namespace DistributedSynthesis.PrivateInputs.Ternary
open EncodedFiniteLTL
noncomputable section
open Classical

abbrev Atom := Input × Bool × Bool
abbrev Instance := Code Atom
def raw (r : Letter Symbol Symbol Bool Bool) : Atom :=
  ((r.inputOne, r.inputTwo), r.outputOne, r.outputTwo)
def source (a : Atom) : BinaryAgreement.Letter := ⟨(), (), graph a.1, a.2.1, a.2.2⟩

def Realizable (c : Instance) : Prop :=
  ∃ τ : StrategyPair Symbol Symbol Bool Bool, ∀ env,
    LTL.Satisfies FiniteLetterLTL.interp (fun t ↦ raw (execution τ env t)) (decode c)

def letters : List Atom := Finset.univ.toList
@[simp] theorem mem_letters (a : Atom) : a ∈ letters := Finset.mem_toList.mpr (Finset.mem_univ _)

def initial : Code Atom := test (letters.filter fun a ↦ decide (incoming a.1 = true))
def valid : Code Atom := test (letters.filter fun a ↦ decide (Valid a.1))
def adjacent : Code Atom := relation ((letters.product letters).filter fun ab ↦
  decide (incoming ab.2.1 = outgoing ab.1.1))
def assumptionCode : Code Atom := binary 3 initial (binary 3 (always valid) (always adjacent))

theorem self_rep {A : Type*} {c : Code A} {φ : LTL A} (h : Represents c φ) :
    Represents c (decode c) := by rw [h.decode]; exact h

theorem assumption_rep : Represents assumptionCode
    (.conj (decode initial) (.conj (.always (decode valid)) (.always (decode adjacent)))) := by
  exact conj_rep (self_rep (test_rep _))
    (conj_rep (always_rep (self_rep (test_rep _)))
      (always_rep (self_rep (relation_rep _))))

theorem assumption_iff (τ : StrategyPair Symbol Symbol Bool Bool)
    (env : EnvironmentSequence Symbol Symbol) :
    LTL.Satisfies FiniteLetterLTL.interp (fun t ↦ raw (execution τ env t))
      (decode assumptionCode) ↔ Legal env := by
  rw [assumption_rep.decode]
  simp only [LTL.Satisfies, LTL.satisfies_always]
  simp [initial, valid, adjacent, satisfies_test, satisfies_relation,
    List.mem_filter, Legal, inputs, raw, execution, and_assoc, forall_and]

def atomCode (a : BinaryAgreement.Atom) : Code Atom :=
  test (letters.filter fun r ↦ decide (BinaryAgreement.interp a (source r)))

def translated (c : EncodedBinaryReduction.Instance) : Code Atom :=
  EncodedBlockTranslation.translate 1 truth atomCode c

def compile (c : EncodedBinaryReduction.Instance) : Instance :=
  binary 4 (unary 2 assumptionCode) (translated c)

theorem translated_correct (c : EncodedBinaryReduction.Instance) (w : OmegaWord Atom) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (translated c)) ↔
      LTL.Satisfies BinaryAgreement.interp (fun t ↦ source (w t)) (decode c) := by
  have hr := EncodedBlockTranslation.translate_rep 1 truth (.verum : LTL Atom) truth_rep
    atomCode (fun a ↦ decode (atomCode a))
    (fun _ ↦ self_rep (test_rep _)) c
  unfold translated
  rw [hr.decode]
  simpa using LTL.BlockTranslation.correct 1 (by omega) .verum (fun a ↦ decode (atomCode a))
    BinaryAgreement.interp FiniteLetterLTL.interp (fun t ↦ source (w t)) w
    (fun t ↦ by simp [LTL.Satisfies])
    (fun a n ↦ by simp [atomCode, satisfies_test]) (decode c) 0

theorem compile_correct (c : EncodedBinaryReduction.Instance) (w : OmegaWord Atom) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (compile c)) ↔
      (LTL.Satisfies FiniteLetterLTL.interp w (decode assumptionCode) →
        LTL.Satisfies BinaryAgreement.interp (fun t ↦ source (w t)) (decode c)) := by
  have ht := EncodedBlockTranslation.translate_rep 1 truth (.verum : LTL Atom) truth_rep
    atomCode (fun a ↦ decode (atomCode a))
    (fun _ ↦ self_rep (test_rep _)) c
  have hc := disj_rep (EncodedBinarySyntax.neg_rep assumption_rep) ht
  change LTL.Satisfies _ _ (decode (binary 4 (unary 2 assumptionCode) (translated c))) ↔ _
  unfold translated
  rw [hc.decode]
  change (¬ LTL.Satisfies _ w _ ∨ _) ↔ _
  rw [← assumption_rep.decode, ← ht.decode]
  change (¬ LTL.Satisfies _ w (decode assumptionCode) ∨
    LTL.Satisfies _ w (decode (translated c))) ↔ _
  rw [translated_correct]
  exact or_iff_not_imp_left.trans (by simp)

theorem realizable_iff (c : EncodedBinaryReduction.Instance) :
    Realizable (compile c) ↔ EncodedBinaryReduction.Realizable c := by
  constructor
  · rintro ⟨τ, hw⟩
    refine ⟨decodeStrategy τ, fun env ↦ ?_⟩
    have hh := (compile_correct c _).mp (hw (encodeEnvironment (fun t ↦ (env t).graph)))
      ((assumption_iff τ _).mpr (encode_legal _))
    rw [decode_execution]
    exact hh
  · rintro ⟨σ, hw⟩
    refine ⟨encodeStrategy σ, fun env ↦ (compile_correct c _).mpr ?_⟩
    intro ha
    have he := legal_eq_encode env ((assumption_iff _ _).mp ha)
    rw [he]
    change LTL.Satisfies _ (fun t ↦ sourceLetter (execution _ _ t)) _
    rw [encode_execution]
    exact hw _

theorem compile_primrec : Primrec compile :=
  (binary_primrec 4).comp (Primrec.const _)
    (EncodedBlockTranslation.translate_primrec (Primrec.const 1) (Primrec.const truth)
      ((Primrec.dom_finite atomCode).comp Primrec.snd).to₂ Primrec.id)

end
end DistributedSynthesis.PrivateInputs.Ternary
