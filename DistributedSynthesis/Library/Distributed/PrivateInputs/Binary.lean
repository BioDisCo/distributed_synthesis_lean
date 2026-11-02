/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.PrivateInputs.Ternary
import DistributedSynthesis.Library.Distributed.PrivateInputs.BinaryBlocks

/-! # Effective two-round LTL compilation for private binary inputs

The target has two independent Boolean inputs, an always-empty graph, two
Boolean output components at process 1, and one at process 2. All atoms are
finite current-letter tests. The clock is an ordinary strategy output.
-/

namespace DistributedSynthesis.PrivateInputs.Binary
open EncodedFiniteLTL
noncomputable section
open Classical

abbrev Instance := Code Atom

def Realizable (c : Instance) : Prop :=
  ∃ τ : StrategyPair Bool Bool (Bool × Bool) Bool, ∀ env,
    LTL.Satisfies FiniteLetterLTL.interp (fun t ↦ raw (execution τ env t)) (decode c)

def letters : List Atom := Finset.univ.toList
@[simp] theorem mem_letters (a : Atom) : a ∈ letters := Finset.mem_toList.mpr (Finset.mem_univ _)

def marker : Code Atom := test (letters.filter fun a ↦ a.2.1.2)
def clockNext : Code Atom := relation ((letters.product letters).filter fun ab ↦
  decide (ab.2.2.1.2 = !ab.1.2.1.2))
def clockCode : Code Atom := binary 3 marker (always clockNext)

theorem clock_rep : Represents clockCode (.conj (decode marker) (.always (decode clockNext))) :=
  conj_rep (Ternary.self_rep (test_rep _)) (always_rep (Ternary.self_rep (relation_rep _)))

theorem clock_spec (w : OmegaWord Atom) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode clockCode) ↔
      (w 0).2.1.2 = true ∧ ∀ t, (w (t+1)).2.1.2 = !(w t).2.1.2 := by
  rw [clock_rep.decode]
  simp [LTL.Satisfies, LTL.satisfies_always, marker, clockNext, satisfies_test, satisfies_relation]

def phase (t : Nat) : Bool := decide (t % 2 = 0)

theorem phase_succ (t : Nat) : phase (t+1) = !phase t := by
  have ht := Nat.mod_lt t (by omega : 0 < 2)
  by_cases h : t % 2 = 0
  · have hn : (t+1) % 2 ≠ 0 := by omega
    simp [phase, h, hn]
  · have hn : (t+1) % 2 = 0 := by omega
    simp [phase, h, hn]

theorem clock_value (w : OmegaWord Atom)
    (h : LTL.Satisfies FiniteLetterLTL.interp w (decode clockCode)) (t : Nat) :
    (w t).2.1.2 = phase t := by
  have hh := (clock_spec w).mp h
  induction t with
  | zero => exact hh.1
  | succ t ih => rw [hh.2 t, ih, phase_succ]

theorem clock_exact (w : OmegaWord Atom)
    (h : LTL.Satisfies FiniteLetterLTL.interp w (decode clockCode)) (t : Nat) :
    LTL.Satisfies FiniteLetterLTL.interp (w.drop t) (decode marker) ↔ ∃ n, t = 2*n := by
  simp only [marker, satisfies_test, List.mem_filter, mem_letters, true_and,
    OmegaWord.drop_apply, Nat.add_zero, clock_value w h t, phase, decide_eq_true_eq]
  constructor
  · intro ht; exact ⟨t/2, by omega⟩
  · rintro ⟨n, rfl⟩; omega

theorem encode_clock_value (σ : StrategyPair Symbol Symbol Bool Bool)
    (env : EnvironmentSequence Bool Bool) (t : Nat) :
    (raw (execution (encodeStrategy σ) env t)).2.1.2 = phase t := by
  simp only [raw, execution, encodeStrategy, prefix_length, phase]
  simp only [show (t+1) % 2 = 1 ↔ t % 2 = 0 by omega]

theorem encode_clock (σ : StrategyPair Symbol Symbol Bool Bool)
    (env : EnvironmentSequence Bool Bool) :
    LTL.Satisfies FiniteLetterLTL.interp (fun t ↦ raw (execution (encodeStrategy σ) env t))
      (decode clockCode) := by
  apply (clock_spec _).mpr
  simp only [encode_clock_value]
  exact ⟨rfl, phase_succ⟩

def atomCode (a : Ternary.Atom) : Code Atom :=
  relation ((letters.product letters).filter fun ab ↦ decide (blockLetter ab.1 ab.2 = a))

def translated (c : Ternary.Instance) : Code Atom :=
  EncodedBlockTranslation.translate 2 marker atomCode c

def compile (c : Ternary.Instance) : Instance := binary 3 clockCode (translated c)

theorem translated_rep (c : Ternary.Instance) : Represents (translated c)
    (LTL.BlockTranslation.translate 2 (decode marker) (fun a ↦ decode (atomCode a)) (decode c)) :=
  EncodedBlockTranslation.translate_rep 2 marker (decode marker) (Ternary.self_rep (test_rep _))
    atomCode (fun a ↦ decode (atomCode a)) (fun _ ↦ Ternary.self_rep (relation_rep _)) c

theorem translated_correct (c : Ternary.Instance) (w : OmegaWord Atom)
    (h : LTL.Satisfies FiniteLetterLTL.interp w (decode clockCode)) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (translated c)) ↔
      LTL.Satisfies FiniteLetterLTL.interp (sample w) (decode c) := by
  rw [(translated_rep c).decode]
  simpa using LTL.BlockTranslation.correct 2 (by omega) (decode marker)
    (fun a ↦ decode (atomCode a)) FiniteLetterLTL.interp FiniteLetterLTL.interp (sample w) w
    (clock_exact w h)
    (fun a n ↦ by simp [atomCode, satisfies_relation, sample, FiniteLetterLTL.interp]) (decode c) 0

theorem compile_correct (c : Ternary.Instance) (w : OmegaWord Atom) :
    LTL.Satisfies FiniteLetterLTL.interp w (decode (compile c)) ↔
      LTL.Satisfies FiniteLetterLTL.interp w (decode clockCode) ∧
      LTL.Satisfies FiniteLetterLTL.interp (sample w) (decode c) := by
  have hc := conj_rep (Ternary.self_rep clock_rep) (Ternary.self_rep (translated_rep c))
  change LTL.Satisfies _ _ (decode (binary 3 clockCode (translated c))) ↔ _
  rw [hc.decode]
  change (_ ∧ _) ↔ _
  exact and_congr_right (fun h ↦ translated_correct c w h)

theorem realizable_iff (c : Ternary.Instance) : Realizable (compile c) ↔ Ternary.Realizable c := by
  constructor
  · rintro ⟨τ, hw⟩
    refine ⟨decodeStrategy τ, fun env ↦ ?_⟩
    have hh := ((compile_correct c _).mp (hw (encodeEnvironment env))).2
    rw [decode_sample] at hh
    exact hh
  · rintro ⟨σ, hw⟩
    refine ⟨encodeStrategy σ, fun env ↦ (compile_correct c _).mpr ⟨encode_clock σ env, ?_⟩⟩
    rw [encode_sample]
    exact hw _

theorem compile_primrec : Primrec compile :=
  (binary_primrec 3).comp (Primrec.const _)
    (EncodedBlockTranslation.translate_primrec (Primrec.const 2) (Primrec.const marker)
      ((Primrec.dom_finite atomCode).comp Primrec.snd).to₂ Primrec.id)

end
end DistributedSynthesis.PrivateInputs.Binary
