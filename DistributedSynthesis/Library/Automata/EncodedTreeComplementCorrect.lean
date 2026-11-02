/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeComplement
import DistributedSynthesis.Library.Automata.EncodedUniversalThreads
import DistributedSynthesis.Library.Automata.TreeComplement
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Correctness of numeric rejecting-policy tables -/
namespace DistributedSynthesis.EncodedTreeComplement
open EncodedProjectedTree

variable (d : Data)

abbrev Direction := Fin (branches d)
abbrev State := Fin (states d)
abbrev Label := Fin (alphabetSize d)
abbrev Successors := Direction d → State d
abbrev Policy := TreeComplement.Policy (automaton d)

noncomputable def vectorEquiv : Successors d ≃ Fin (vectors d).length :=
  FiniteFunctionCoding.equiv (branches d) (states d)

noncomputable def policyFunctionEquiv : Policy d ≃
    (Fin (states d * (vectors d).length) → Direction d) where
  toFun p i := let qv := finProdFinEquiv.symm i; p qv.1 ((vectorEquiv d).symm qv.2)
  invFun f q v := f (finProdFinEquiv (q, vectorEquiv d v))
  left_inv p := by funext q v; simp
  right_inv f := by
    funext i
    simp only [Equiv.apply_symm_apply]
    exact congrArg f (finProdFinEquiv.apply_symm_apply i)

noncomputable def policyEquiv : Policy d ≃ Fin (policies d).length :=
  (policyFunctionEquiv d).trans (FiniteFunctionCoding.equiv _ _)

theorem policy_lookup (p : Policy d) (q : State d) (v : Successors d) :
    ((policies d).getD (policyEquiv d p).val []).getD
      (q.val * (vectors d).length +
        FiniteFunctionCoding.name (branches d) (states d) (FiniteFunctionCoding.encode v)) 0 =
      (p q v).val := by
  change ((FiniteFunctionCoding.codes _ _).getD
    (FiniteFunctionCoding.equiv _ _ (policyFunctionEquiv d p)).val []).getD _ _ = _
  rw [FiniteFunctionCoding.get_equiv]
  let i := finProdFinEquiv (q, vectorEquiv d v)
  have hi : i.val = q.val * (vectors d).length +
      FiniteFunctionCoding.name (branches d) (states d) (FiniteFunctionCoding.encode v) := by
    change (vectorEquiv d v).val + (vectors d).length * q.val = _
    rw [show (vectorEquiv d v).val = FiniteFunctionCoding.name (branches d) (states d)
      (FiniteFunctionCoding.encode v) from rfl]
    ac_rfl
  rw [← hi, FiniteFunctionCoding.lookup_encode]
  simp only [policyFunctionEquiv, Equiv.coe_fn_mk, i, Equiv.symm_apply_apply]

theorem legal_correct (q : State d) (a : Label d) (v : Successors d) :
    legal d q.val a.val (FiniteFunctionCoding.encode v) ↔ (automaton d).delta q a v := by
  change (∃ l < choices d, output d l = a.val ∧
      (List.range (branches d)).map (fun b => next d q.val l b) = _) ↔
    ∃ l : Fin (choices d), letter d l = a ∧
      ∀ b, v b = (EncodedTreeNonemptiness.monitor (monitorData d)).step q l b
  constructor
  · rintro ⟨l, hl, ha, hv⟩
    refine ⟨⟨l, hl⟩, Fin.ext ha, fun b => Fin.ext ?_⟩
    have h := congrArg (fun xs : List Nat => xs.getD b.val 0) hv
    have lookup : ((List.range (branches d)).map (fun b => next d q.val l b)).getD b.val 0 =
        next d q.val l b.val := by
      rw [List.getD_eq_getElem _ _ (by simpa using b.isLt)]
      simp only [List.getElem_map, List.getElem_range]
    dsimp only at h
    rw [lookup, FiniteFunctionCoding.lookup_encode] at h
    exact h.symm
  · rintro ⟨l, ha, hv⟩
    refine ⟨l.val, l.isLt, congrArg Fin.val ha, ?_⟩
    apply FiniteSearch.tabulate_eq_ofFn
    intro b
    exact congrArg Fin.val (hv b).symm

def stateEquiv : Option (State d) ≃ Fin (states d + 1) := (finSuccEquiv _).symm

@[simp] theorem stateEquiv_none : stateEquiv d none = 0 := finSuccEquiv_symm_none
@[simp] theorem stateEquiv_some (q : State d) : stateEquiv d (some q) = q.succ :=
  finSuccEquiv_symm_some q


theorem resolve_correct (q : Option (State d)) (a : Label d) (p : Policy d)
    (b : Direction d) (v : Successors d) :
    resolve d (stateEquiv d q).val a.val ((policies d).getD (policyEquiv d p).val [])
      b.val (FiniteFunctionCoding.encode v) =
    (stateEquiv d ((TreeComplement.threads (automaton d)).step q ((a, p), b) v)).val := by
  classical
  cases q with
  | none =>
    simp only [stateEquiv_none, Fin.val_zero, resolve, ↓reduceIte]
    exact congrArg Fin.val (stateEquiv_none d).symm
  | some q =>
    simp only [stateEquiv_some, Fin.val_succ, resolve, Nat.add_sub_cancel,
      Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte,
      legal_correct, policy_lookup, Fin.val_inj, FiniteFunctionCoding.lookup_encode]
    by_cases h : (automaton d).delta q a v ∧ p q v = b
    · simp only [if_pos h, TreeComplement.threads]
      exact congrArg Fin.val (stateEquiv_some d (v b)).symm
    · simp only [if_neg h, TreeComplement.threads]
      exact congrArg Fin.val (stateEquiv_none d).symm

noncomputable def letterEquiv : ((Label d × Policy d) × Direction d) ≃
    Fin (alphabetSize d * (policies d).length * branches d) :=
  (Equiv.prodCongr
    ((Equiv.prodCongr (Equiv.refl _) (policyEquiv d)).trans finProdFinEquiv)
    (Equiv.refl _)).trans finProdFinEquiv

theorem edges_letter (a : Label d) (p : Policy d) (b : Direction d) :
    edges d (letterEquiv d ((a, p), b)).val =
      (List.range (states d + 1)).flatMap fun q => (vectors d).map fun v =>
        (q, resolve d q a.val ((policies d).getD (policyEquiv d p).val []) b.val v) := by
  have hb : 0 < branches d := Nat.zero_lt_of_lt b.isLt
  have hp : 0 < (policies d).length := Nat.zero_lt_of_lt (policyEquiv d p).isLt
  unfold edges letterEquiv
  simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply]
  change (List.range (states d + 1)).flatMap (fun q => (vectors d).map (fun v =>
    (q, resolve d q
      ((b.val + branches d * ((policyEquiv d p).val + (policies d).length * a.val)) /
        branches d / (policies d).length)
      ((policies d).getD
        ((b.val + branches d * ((policyEquiv d p).val + (policies d).length * a.val)) /
          branches d % (policies d).length) [])
      ((b.val + branches d * ((policyEquiv d p).val + (policies d).length * a.val)) % branches d) v))) = _
  rw [Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt b.isLt, Nat.zero_add,
    Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (policyEquiv d p).isLt, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (policyEquiv d p).isLt,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

theorem encode_mem_vectors (v : Successors d) : FiniteFunctionCoding.encode v ∈ vectors d :=
  (FiniteCodeNumbering.mem_unique _ _).mpr (FiniteSearch.ofFn_mem_tables v)

theorem vectors_complete (v : List Nat) (hv : v ∈ vectors d) :
    ∃ f : Successors d, FiniteFunctionCoding.encode f = v :=
  (FiniteSearch.mem_tables_iff_policy _).mp ((FiniteCodeNumbering.mem_unique _ _).mp hv)

theorem edges_correct (q r : Option (State d)) (a : Label d) (p : Policy d) (b : Direction d) :
    ((stateEquiv d q).val, (stateEquiv d r).val) ∈ edges d (letterEquiv d ((a, p), b)).val ↔
      ∃ v : Successors d, r = (TreeComplement.threads (automaton d)).step q ((a, p), b) v := by
  rw [edges_letter]
  simp only [List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨qn, _, v, hv, hq, hr⟩
    subst qn
    obtain ⟨f, rfl⟩ := vectors_complete d v hv
    refine ⟨f, (stateEquiv d).injective (Fin.ext ?_)⟩
    exact hr.symm.trans (resolve_correct d q a p b f)
  · rintro ⟨v, rfl⟩
    exact ⟨(stateEquiv d q).val, (stateEquiv d q).isLt,
      FiniteFunctionCoding.encode v, encode_mem_vectors d v, rfl, resolve_correct d q a p b v⟩

noncomputable def threadNumber : (TreeComplement.threads (automaton d)).State ≃
    Fin (Fintype.card (TreeComplement.threads (automaton d)).State) :=
  (stateEquiv d).trans (finCongr (by
    change states d + 1 = Fintype.card (Option (State d))
    simp [State]))

theorem threadNumber_val (q : Option (State d)) :
    (threadNumber d q).val = (stateEquiv d q).val := rfl

theorem priority_correct (q : Option (State d)) :
    (priorities d).getD (threadNumber d q).val 0 =
      (TreeComplement.threads (automaton d)).priority q := by
  cases q with
  | none => rfl
  | some q =>
    change (0 :: (List.range (states d)).map _).getD (q.val + 1) 0 = _
    rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by simpa using q.isLt)]
    simp only [List.getElem_map, List.getElem_range]
    rfl

theorem priority_range (p : Nat) :
    p ∈ priorities d ↔
      p ∈ FiniteThreadSystem.Computable.priorityRange (TreeComplement.threads (automaton d)) := by
  simp only [FiniteThreadSystem.Computable.priorityRange, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    rcases List.mem_cons.mp h with h | h
    · exact ⟨none, h.symm⟩
    · obtain ⟨q, hq, heq⟩ := List.mem_map.mp h
      exact ⟨some ⟨q, List.mem_range.mp hq⟩, heq⟩
  · rintro ⟨q, rfl⟩
    cases q with
    | none => exact List.mem_cons_self
    | some q =>
      exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q.val, List.mem_range.mpr q.isLt, rfl⟩)

theorem alphabet_length : (threadData d).2.2.2.length =
    alphabetSize d * (policies d).length * branches d := by
  simp only [threadData, List.length_map, List.length_range]

noncomputable def decodeLetter (a : Fin (threadData d).2.2.2.length) :
    (Label d × Policy d) × Direction d :=
  (letterEquiv d).symm (Fin.cast (alphabet_length d) a)

theorem encode_decode_val (a : Fin (threadData d).2.2.2.length) :
    (letterEquiv d (decodeLetter d a)).val = a.val := by
  simp only [decodeLetter, Equiv.apply_symm_apply, Fin.val_cast]

theorem lookup_edges (a : Fin (threadData d).2.2.2.length) :
    (threadData d).2.2.2[a.val]?.getD [] = edges d a.val := by
  rw [List.getElem?_eq_getElem a.isLt]
  change ((List.range _).map (edges d))[a.val] = _
  simp only [List.getElem_map, List.getElem_range]

theorem transition_correct (q r : (TreeComplement.threads (automaton d)).State)
    (a : Fin (threadData d).2.2.2.length) :
    ((threadNumber d q).val, (threadNumber d r).val) ∈ (threadData d).2.2.2[a.val]?.getD [] ↔
      ∃ v, r = (TreeComplement.threads (automaton d)).step q (decodeLetter d a) v := by
  rw [lookup_edges, ← encode_decode_val d a]
  exact edges_correct d q r (decodeLetter d a).1.1 (decodeLetter d a).1.2 (decodeLetter d a).2

theorem sourceData_eq :
    EncodedUniversalThreads.sourceData (TreeComplement.threads (automaton d))
      (threadNumber d) (priorities d) (threadData d).2.2.2 = threadData d := by
  change (Fintype.card (Option (State d)), _, _, _) = (states d + 1, _, _, _)
  congr 1
  simp [State]

/-- The numeric word automaton checks the same rejecting threads as the
semantic tree-complement construction. -/
theorem word_accepts_iff (word : OmegaWord (Fin (threadData d).2.2.2.length)) :
    (EncodedThreadCompiler.automaton (threadData d)).Accepts word ↔
      ∀ q, (TreeComplement.threads (automaton d)).IsRun (OmegaWord.map (decodeLetter d) word) q →
        NatSeqMinEvenParity (fun n => (TreeComplement.threads (automaton d)).priority (q n)) := by
  classical
  letI : Fintype (TreeComplement.threads (automaton d)).Resolution :=
    inferInstanceAs (Fintype (Successors d))
  have h := EncodedUniversalThreads.accepts_iff (TreeComplement.threads (automaton d))
    (threadNumber d) (priorities d) (priority_correct d) (priority_range d)
    (threadData d).2.2.2 (decodeLetter d) (fun q a r => transition_correct d q r a) word
  have align := EncodedThreadCompiler.config_accepts_congr (priorities d) (threadData d).2.2.2
    (congrArg Prod.fst (sourceData_eq d)) (congrArg (fun x => x.2.1) (sourceData_eq d)) word
  exact align.symm.trans h

noncomputable def labelEquiv : (Label d × Policy d) ≃ Fin (alphabetSize d * (policies d).length) :=
  (Equiv.prodCongr (Equiv.refl _) (policyEquiv d)).trans finProdFinEquiv

def pairLetter (a : Fin (alphabetSize d * (policies d).length) × Direction d) :
    Fin (threadData d).2.2.2.length :=
  Fin.cast (alphabet_length d).symm (finProdFinEquiv a)

theorem numericWord_eq :
    EncodedWordTree.wordAutomaton (branches d) (alphabetSize d * (policies d).length) (wordAutomaton d) =
      (EncodedThreadCompiler.automaton (threadData d)).comap (pairLetter d) := by
  rw [EncodedThreadCompiler.automaton_eq]
  unfold EncodedWordTree.wordAutomaton EncodedParityTables.automaton DetParityAutomaton.comap
  congr 1
  funext q a
  apply Fin.ext
  change EncodedParityTables.next _ q.val (a.1.val * branches d + a.2.val) =
    EncodedParityTables.next _ q.val (a.2.val + branches d * a.1.val)
  congr 1
  ac_rfl

theorem decode_pair (a : Label d × Policy d) (b : Direction d) :
    decodeLetter d (pairLetter d (labelEquiv d a, b)) = (a, b) := by
  apply (letterEquiv d).injective
  change letterEquiv d ((letterEquiv d).symm _) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem projection_label (a : Label d × Policy d) :
    letter (compile d) (labelEquiv d a) = a.1 := by
  apply Fin.ext
  change ((List.range _).map (fun i => i / (policies d).length)).getD (labelEquiv d a).val 0 %
    alphabetSize d = _
  rw [List.getD_eq_getElem _ _ (by simpa using (labelEquiv d a).isLt)]
  simp only [List.getElem_map, List.getElem_range]
  change ((policyEquiv d a.2).val + (policies d).length * a.1.val) /
    (policies d).length % alphabetSize d = a.1.val
  rw [Nat.add_mul_div_left _ _ (Nat.zero_lt_of_lt (policyEquiv d a.2).isLt),
    Nat.div_eq_of_lt (policyEquiv d a.2).isLt, Nat.zero_add, Nat.mod_eq_of_lt a.1.isLt]

/-- The compiled monitor has exactly the intended policy semantics. -/
theorem annotated_accepts_iff (tree : LabeledTree (Direction d) (Label d))
    (p : TreeNode (Direction d) → Policy d) :
    (EncodedTreeNonemptiness.monitor (monitorData (compile d))).toRunAutomaton.acceptsTree
        (fun node => labelEquiv d (tree node, p node)) ↔
      TreeComplement.Rejects (automaton d) tree p := by
  change (EncodedTreeNonemptiness.monitor (EncodedWordTree.compile _)).toRunAutomaton.acceptsTree _ ↔ _
  rw [EncodedWordTree.accepts_iff, numericWord_eq]
  have words (branch : Nat → Direction d) :
      OmegaWord.map (decodeLetter d) (OmegaWord.map (pairLetter d)
        (WordTreeMonitor.word (fun node => labelEquiv d (tree node, p node)) branch)) =
      WordTreeMonitor.word (fun node => (tree node, p node)) branch := by
    funext n
    exact decode_pair d _ _
  refine (forall_congr' (fun branch => ?_)).trans
    (TreeComplement.universal_threads_iff (automaton d) tree p)
  have h := word_accepts_iff d (OmegaWord.map (pairLetter d)
    (WordTreeMonitor.word (fun node => labelEquiv d (tree node, p node)) branch))
  have hw := Iff.of_eq (congrArg (fun w =>
    ∀ q, (TreeComplement.threads (automaton d)).IsRun w q →
      NatSeqMinEvenParity (fun n => (TreeComplement.threads (automaton d)).priority (q n)))
    (words branch))
  exact (DetParityAutomaton.comap_accepts_iff _ _ _).trans (h.trans hw)

variable [Nonempty (Direction d)]

/-- Numeric complementation recognizes the complement of the complete source
language, with arbitrary infinite trees and runs. -/
theorem compile_correct (tree : LabeledTree (Direction d) (Label d)) :
    (automaton (compile d)).acceptsTree tree ↔ ¬ (automaton d).acceptsTree tree := by
  classical
  letI : Nonempty (Fin (EncodedTreeNonemptiness.branches (monitorData d))) :=
    inferInstanceAs (Nonempty (Direction d))
  rw [EncodedProjectedTree.accepts_iff, TreeComplement.rejects_iff_exists_policy]
  constructor
  · rintro ⟨annotated, projected, accepts⟩
    let decoded := fun node => (labelEquiv d).symm (annotated node)
    have hlabel (node) : (decoded node).1 = tree node := by
      have h := projection_label d (decoded node)
      rw [show labelEquiv d (decoded node) = annotated node from (labelEquiv d).apply_symm_apply _] at h
      exact h.symm.trans (congrFun projected node)
    let p := fun node => (decoded node).2
    refine ⟨p, (annotated_accepts_iff d tree p).mp ?_⟩
    have heq : (fun node => labelEquiv d (tree node, p node)) = annotated := by
      funext node
      rw [← hlabel node]
      exact (labelEquiv d).apply_symm_apply _
    exact heq.symm ▸ accepts
  · rintro ⟨p, rejects⟩
    refine ⟨fun node => labelEquiv d (tree node, p node), ?_,
      (annotated_accepts_iff d tree p).mpr rejects⟩
    funext node
    exact projection_label d (tree node, p node)

end DistributedSynthesis.EncodedTreeComplement
