/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedBinaryReduction
import DistributedSynthesis.Formalizations.Theorem.ThmCounterMachineEncodedUndecidability

/-! # Binary-output LTL synthesis is undecidable relative to the MM2 source

This is a separate extension of the existing finite-output result. The finite
payload enumeration is fixed once and for all. Only the control bound varies,
and all such dependence is included in the primitive-recursive compiler proof.
-/
namespace DistributedSynthesis.CounterMachine.BinaryCompiler
open Compiler ResidueLTL EncodedFiniteLTL
set_option maxRecDepth 4000
set_option maxHeartbeats 800000

def outputEquiv (n : Nat) : Output (Fin (n+1)) ≃ Payload × Fin (n+1) where
  toFun o := (eraseOutput o, o.base.control)
  invFun x := ⟨⟨x.2, x.1.base.zero, x.1.base.carry, x.1.base.right⟩, x.1.residue⟩
  left_inv := by rintro ⟨⟨q,z,c,r⟩,s⟩; rfl
  right_inv := by rintro ⟨⟨⟨⟨⟩,z,c,r⟩,s⟩,q⟩; rfl

noncomputable def payloadFin := Fintype.equivFin Payload
def width (n : Nat) : Nat := Fintype.card Payload * (n+1)
noncomputable def outputFin (n : Nat) : Output (Fin (n+1)) ≃ Fin (width n) :=
  (outputEquiv n).trans ((Equiv.prodCongr payloadFin (Equiv.refl _)).trans finProdFinEquiv)
noncomputable def code (n : Nat) : BinaryWords.Code (Output (Fin (n+1))) (width n) :=
  BinaryWords.ofEmbedding (outputFin n).toEmbedding
noncomputable def alphabet (n : Nat) : List (Output (Fin (n+1))) := List.ofFn (outputFin n).symm

theorem mem_alphabet (n : Nat) (o : Output (Fin (n+1))) : o ∈ alphabet n := by
  exact List.mem_ofFn.mpr ⟨outputFin n o, (outputFin n).symm_apply_apply o⟩

instance (n : Nat) : Nonempty (Output (Fin (n+1))) := by
  exact ⟨⟨⟨0, fun _ ↦ false, fun _ ↦ 0,
    fun _ ↦ ⟨0, fun _ ↦ 0⟩⟩, 0⟩⟩

noncomputable def key₁ (n : Nat) (r : RawLetter) : Nat :=
  r.2.1 + (n+1) * (payloadFin r.1.2.1).val
noncomputable def key₂ (n : Nat) (r : RawLetter) : Nat :=
  r.2.2 + (n+1) * (payloadFin r.1.2.2).val

noncomputable def atomCode (n : Nat) (r : RawLetter) : Code BinaryAgreement.Atom :=
  if r.2.1 ≤ n ∧ r.2.2 ≤ n then
    binary 3 (atom (.inl r.1.1)) (binary 3
      (EncodedBinarySyntax.word (width n) (.inr .two) (key₁ n r))
      (EncodedBinarySyntax.word (width n) (.inr .one) (key₂ n r)))
  else falsity

noncomputable def compileInstance (I : Compiler.Instance) : EncodedBinaryReduction.Instance :=
  EncodedBinaryReduction.compile (width I.1) (List.range (width I.1)) (List.range (width I.1))
    (atomCode I.1) I.2

theorem width_primrec : Primrec width :=
  Primrec.nat_mul.comp (Primrec.const _) Primrec.succ
theorem key₁_primrec : Primrec₂ key₁ :=
  Primrec.nat_add.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst)
      ((Primrec.dom_finite (fun s : Shape ↦ (payloadFin s.2.1).val)).comp (Primrec.fst.comp Primrec.snd)))
theorem key₂_primrec : Primrec₂ key₂ :=
  Primrec.nat_add.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_mul.comp (Primrec.succ.comp Primrec.fst)
      ((Primrec.dom_finite (fun s : Shape ↦ (payloadFin s.2.2).val)).comp (Primrec.fst.comp Primrec.snd)))

theorem atomCode_primrec : Primrec₂ atomCode :=
  Primrec.ite
    ((Primrec.nat_le.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst).and
      (Primrec.nat_le.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))
    ((binary_primrec 3).comp
      ((Primrec.dom_finite (fun s : Shape ↦ atom (Sum.inl s.1 : BinaryAgreement.Atom))).comp
        (Primrec.fst.comp Primrec.snd))
      ((binary_primrec 3).comp
        ((EncodedBinarySyntax.word_primrec (.inr .two : BinaryAgreement.Atom)).comp (width_primrec.comp Primrec.fst) key₁_primrec)
        ((EncodedBinarySyntax.word_primrec (.inr .one : BinaryAgreement.Atom)).comp (width_primrec.comp Primrec.fst) key₂_primrec)))
    (Primrec.const falsity)

theorem compileInstance_primrec : Primrec compileInstance :=
  EncodedBinaryReduction.compile_primrec (width_primrec.comp Primrec.fst)
    (Primrec.list_range.comp (width_primrec.comp Primrec.fst))
    (Primrec.list_range.comp (width_primrec.comp Primrec.fst))
    (atomCode_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂ Primrec.snd

def rebuild (n : Nat) (r : RawLetter) (h : r.2.1 ≤ n ∧ r.2.2 ≤ n) : Letter (Fin (n+1)) :=
  ⟨(), (), r.1.1, (outputEquiv n).symm (r.1.2.1, ⟨r.2.1, by omega⟩),
    (outputEquiv n).symm (r.1.2.2, ⟨r.2.2, by omega⟩)⟩

theorem raw_rebuild (n : Nat) (r : RawLetter) (h : r.2.1 ≤ n ∧ r.2.2 ≤ n) :
    raw (rebuild n r h) = r := by
  obtain ⟨⟨g, ⟨⟨⟨⟩,z,c,r⟩,s⟩, ⟨⟨⟨⟩,z',c',r'⟩,s'⟩⟩, i,j⟩ := r
  rfl

theorem raw_injective (n : Nat) : Function.Injective (raw (n := n)) := by
  intro x y h
  obtain ⟨⟨⟩,⟨⟩,g,⟨⟨q,z,c,r⟩,s⟩,⟨⟨q',z',c',r'⟩,s'⟩⟩ := x
  obtain ⟨⟨⟩,⟨⟩,g₂,⟨⟨q₂,z₂,c₂,r₂⟩,s₂⟩,⟨⟨q₂',z₂',c₂',r₂'⟩,s₂'⟩⟩ := y
  simp_all [raw, eraseOutput, eraseLabel, Fin.val_inj]

noncomputable def atomFormula (n : Nat) (r : RawLetter) : LTL BinaryAgreement.Atom :=
  if h : r.2.1 ≤ n ∧ r.2.2 ≤ n then BinaryReduction.letterTest (code n) (code n) (rebuild n r h)
  else .falsum

theorem code_rebuild_one (n : Nat) (r : RawLetter) (h : r.2.1 ≤ n ∧ r.2.2 ≤ n) :
    (code n).bits (rebuild n r h).outputOne = fun j ↦ decide (key₁ n r = j.val) := by
  obtain ⟨⟨g, ⟨⟨⟨⟩,z,c,r⟩,s⟩, ⟨⟨⟨⟩,z',c',r'⟩,s'⟩⟩, i,j⟩ := r
  funext k
  change decide ((outputFin n) _ = k) = decide (_ = k.val)
  simp only [Fin.ext_iff]
  rfl

theorem code_rebuild_two (n : Nat) (r : RawLetter) (h : r.2.1 ≤ n ∧ r.2.2 ≤ n) :
    (code n).bits (rebuild n r h).outputTwo = fun j ↦ decide (key₂ n r = j.val) := by
  obtain ⟨⟨g, ⟨⟨⟨⟩,z,c,r⟩,s⟩, ⟨⟨⟨⟩,z',c',r'⟩,s'⟩⟩, i,j⟩ := r
  funext k
  change decide ((outputFin n) _ = k) = decide (_ = k.val)
  simp only [Fin.ext_iff]
  rfl

theorem atomCode_rep (n : Nat) (r : RawLetter) : Represents (atomCode n r) (atomFormula n r) := by
  by_cases h : r.2.1 ≤ n ∧ r.2.2 ≤ n
  · rw [atomCode, if_pos h, atomFormula, dif_pos h, BinaryReduction.letterTest,
      code_rebuild_one, code_rebuild_two]
    exact conj_rep (atom_rep _) (conj_rep (EncodedBinarySyntax.word_rep _ _ _)
      (EncodedBinarySyntax.word_rep _ _ _))
  · simp only [atomCode, atomFormula, h, ↓reduceIte]
    exact falsity_rep

theorem atom_correct (n : Nat) : EncodedBinaryReduction.AtomCorrect (code n) (code n)
    (fun r s ↦ raw s = r) (atomFormula n) := by
  intro s w hr r t
  by_cases h : r.2.1 ≤ n ∧ r.2.2 ≤ n
  · rw [atomFormula, dif_pos h, BinaryReduction.letterTest_correct (code n) (code n) s w hr]
    change s t = rebuild n r h ↔ raw (s t) = r
    exact (raw_injective n).eq_iff.symm.trans (by rw [raw_rebuild])
  · rw [atomFormula, dif_neg h]
    change False ↔ raw (s t) = r
    constructor
    · exact False.elim
    · intro he
      have hb := (mem_letters n (raw (s t))).mp (raw_mem (s t))
      rw [he] at hb
      exact h hb

theorem valid_rep (n : Nat) (p : BinaryAgreement.Atom) :
    Represents (EncodedBinarySyntax.valid (width n) p (List.range (width n)))
      (BinaryWords.valid p (code n) (alphabet n)) := by
  have hb (i : Fin (width n)) : (code n).bits ((outputFin n).symm i) =
      fun j ↦ decide (i.val = j.val) := by
    funext j
    change decide (outputFin n ((outputFin n).symm i) = j) = decide (i.val = j.val)
    simp only [Equiv.apply_symm_apply, Fin.ext_iff]
  have he : (List.ofFn fun i : Fin (width n) ↦
      BinaryWords.wordTest p (fun j : Fin (width n) ↦ decide (i.val = j.val))) =
      (List.range (width n)).map (fun i ↦ BinaryWords.wordTest p
        (fun j : Fin (width n) ↦ decide (i = j.val))) := by
    exact EncodedBinarySyntax.ofFn_range_map (width n)
      (fun i ↦ BinaryWords.wordTest p (fun j : Fin (width n) ↦ decide (i = j.val)))
  rw [BinaryWords.valid, alphabet, List.map_ofFn]
  simp only [Function.comp_def, hb]
  rw [he]
  exact EncodedBinarySyntax.valid_rep _ _ _

/-- Every emitted string represents an ordinary LTL formula, even if the
supplied source string is malformed or contains out-of-alphabet atoms. -/
theorem compileInstance_rep (I : Compiler.Instance) :
    Represents (compileInstance I)
      (EncodedBinaryReduction.formula (code I.1) (code I.1) (alphabet I.1) (alphabet I.1)
        (atomFormula I.1) (EncodedFiniteLTL.decode I.2)) :=
  EncodedBinaryReduction.compile_rep (code I.1) (code I.1) (alphabet I.1) (alphabet I.1)
    (List.range (width I.1)) (List.range (width I.1)) (atomCode I.1) (atomFormula I.1)
    (valid_rep I.1 (.inr .two)) (valid_rep I.1 (.inr .one)) (atomCode_rep I.1) I.2

theorem compiled_realizable_iff (I : Compiler.Instance) :
    EncodedBinaryReduction.Realizable (compileInstance I) ↔ Compiler.EncodedRealizable I := by
  unfold EncodedBinaryReduction.Realizable
  rw [(compileInstance_rep I).decode]
  refine (EncodedBinaryReduction.semantic_iff (code I.1) (code I.1) (alphabet I.1) (alphabet I.1)
    (mem_alphabet I.1) (mem_alphabet I.1) (fun r s ↦ raw s = r) (atomFormula I.1)
    (atom_correct I.1) (EncodedFiniteLTL.decode I.2)).symm.trans ?_
  apply exists_congr
  intro σ
  apply forall_congr'
  intro env
  exact (LTL.satisfies_word_map FiniteLetterLTL.interp raw (execution σ env) (EncodedFiniteLTL.decode I.2)).symm

/-- The output alphabet and atomic vocabulary of the target are fixed. -/
theorem finiteOutput_manyOneReducible : Compiler.EncodedRealizable ≤₀ EncodedBinaryReduction.Realizable :=
  ⟨compileInstance, compileInstance_primrec.to_comp, fun I ↦ (compiled_realizable_iff I).symm⟩

noncomputable def compileProgram (P : MM2.Program) : EncodedBinaryReduction.Instance :=
  compileInstance (Compiler.compileInstance P)

theorem compileProgram_primrec : Primrec compileProgram :=
  compileInstance_primrec.comp Compiler.compileInstance_primrec

theorem compileProgram_realizable_iff (P : MM2.Program) :
    EncodedBinaryReduction.Realizable (compileProgram P) ↔ ¬ MM2.ZeroHalts P :=
  (compiled_realizable_iff (Compiler.compileInstance P)).trans (Compiler.compiled_realizable_iff P)

theorem nonhalting_manyOneReducible :
    (fun P : MM2.Program ↦ ¬ MM2.ZeroHalts P) ≤₀ EncodedBinaryReduction.Realizable :=
  Compiler.nonhalting_manyOneReducible.trans finiteOutput_manyOneReducible

/-- Assuming the explicit two-counter-machine source theorem, LTL synthesis
is undecidable even with one Boolean output per process and singleton inputs.
The compiler and its correctness are proved; the unconditional result supplies
the source theorem from `CounterMachine.SourcePort`. -/
theorem binary_ltl_synthesis_undecidable (source : MM2.SourceUndecidability) :
    ¬ ComputablePred EncodedBinaryReduction.Realizable :=
  source.transfer EncodedBinaryReduction.Realizable nonhalting_manyOneReducible

end DistributedSynthesis.CounterMachine.BinaryCompiler
