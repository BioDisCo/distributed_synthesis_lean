/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedTreeIntersection

/-! # Correctness of numeric parity-tree conjunction -/
namespace DistributedSynthesis.EncodedTreeIntersection
open EncodedProjectedTree
open Characterisation

variable (x : Input)

abbrev LeftChoice := Fin (EncodedTreeNonemptiness.labels (monitorData (left x)))
abbrev RightChoice := Fin (EncodedTreeNonemptiness.labels (monitorData (right x)))
abbrev Choice := Fin (pairs x).length
abbrev Direction := Fin x.1

theorem mem_pairs (p : Nat × Nat) : p ∈ pairs x ↔
    p.1 < EncodedTreeNonemptiness.labels (monitorData (left x)) ∧
    p.2 < EncodedTreeNonemptiness.labels (monitorData (right x)) ∧
    output (left x) p.1 = output (right x) p.2 := by
  rcases p with ⟨l, r⟩
  have hp : (l, r) ∈
      (List.range (EncodedTreeNonemptiness.labels (monitorData (left x)))).product
        (List.range (EncodedTreeNonemptiness.labels (monitorData (right x)))) ↔
      l ∈ List.range (EncodedTreeNonemptiness.labels (monitorData (left x))) ∧
        r ∈ List.range (EncodedTreeNonemptiness.labels (monitorData (right x))) := List.mem_product
  simp only [pairs, List.mem_filter, hp, List.mem_range, decide_eq_true_eq, and_assoc]

def leftChoice (i : Choice x) : LeftChoice x :=
  ⟨((pairs x)[i.val]).1, ((mem_pairs x _).mp (List.getElem_mem i.isLt)).1⟩
def rightChoice (i : Choice x) : RightChoice x :=
  ⟨((pairs x)[i.val]).2, ((mem_pairs x _).mp (List.getElem_mem i.isLt)).2.1⟩

theorem compatible (i : Choice x) : letter (left x) (leftChoice x i) =
    letter (right x) (rightChoice x i) :=
  Fin.ext (((mem_pairs x _).mp (List.getElem_mem i.isLt)).2.2)

theorem projection_left (i : Choice x) :
    letter (compile x) i = letter (left x) (leftChoice x i) := by
  apply Fin.ext
  change ((pairs x).map _).getD i.val 0 % (x.2.1 + 1) = _
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp only [List.getElem_map]
  exact Nat.mod_mod _ _

theorem exists_choice (l : LeftChoice x) (r : RightChoice x)
    (h : letter (left x) l = letter (right x) r) :
    ∃ i : Choice x, leftChoice x i = l ∧ rightChoice x i = r := by
  have hp : (l.val, r.val) ∈ pairs x :=
    (mem_pairs x _).mpr ⟨l.isLt, r.isLt, congrArg Fin.val h⟩
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp hp
  exact ⟨⟨i, hi⟩, Fin.ext (congrArg Prod.fst heq), Fin.ext (congrArg Prod.snd heq)⟩

theorem product_alphabet :
    (EncodedParityTables.rows (EncodedParityProduct.transition (productData x))).length =
      (pairs x).length * x.1 := by
  rw [EncodedParityProduct.alphabet_transition]
  simp only [productData, EncodedParityProduct.letters, List.length_map, List.length_range]

def splitLetter (a : EncodedParityProduct.Alphabet (productData x)) : Choice x × Direction x :=
  finProdFinEquiv.symm (Fin.cast (product_alphabet x) a)

def leftLetter (a : EncodedParityProduct.Alphabet (productData x)) :
    Fin (EncodedParityTables.rows (EncodedTreeWord.compile (monitorData (left x)))).length :=
  EncodedTreeWord.letter _ (leftChoice x (splitLetter x a).1, (splitLetter x a).2)

def rightLetter (a : EncodedParityProduct.Alphabet (productData x)) :
    Fin (EncodedParityTables.rows (EncodedTreeWord.compile (monitorData (right x)))).length :=
  EncodedTreeWord.letter _ (rightChoice x (splitLetter x a).1, (splitLetter x a).2)

theorem product_letter (a : EncodedParityProduct.Alphabet (productData x)) :
    EncodedParityProduct.letter (productData x) a.val = ((leftLetter x a).val, (rightLetter x a).val) := by
  change ((List.range ((pairs x).length * x.1)).map _).getD a.val (0,0) = _
  rw [List.getD_eq_getElem _ _ (by
    simpa only [List.length_map, List.length_range, ← product_alphabet x] using a.isLt)]
  simp only [List.getElem_map, List.getElem_range]
  have hi : a.val / x.1 < (pairs x).length := (splitLetter x a).1.isLt
  rw [List.getD_eq_getElem _ _ hi]
  rfl

def pairLetter (a : Choice x × Direction x) : EncodedParityProduct.Alphabet (productData x) :=
  Fin.cast (product_alphabet x).symm (finProdFinEquiv a)

theorem split_pair (a : Choice x × Direction x) : splitLetter x (pairLetter x a) = a := by
  simp only [splitLetter, pairLetter, Fin.cast_cast, Fin.cast_eq_self, Equiv.symm_apply_apply]

theorem numericWord_eq :
    EncodedWordTree.wordAutomaton x.1 (pairs x).length
        (EncodedParityProduct.conjunction (productData x)) =
      (EncodedParityFamilies.automaton (EncodedParityProduct.conjunctionData (productData x))).comap
        (pairLetter x) := by
  unfold EncodedParityFamilies.automaton EncodedMuller.automaton
  unfold EncodedWordTree.wordAutomaton EncodedParityTables.automaton DetParityAutomaton.comap
  congr 1
  funext q a
  apply Fin.ext
  change EncodedParityTables.next _ q.val (a.1.val * x.1 + a.2.val) =
    EncodedParityTables.next _ q.val (a.2.val + x.1 * a.1.val)
  congr 1
  ac_rfl

/-- A compatible annotated tree is accepted exactly when both monitors accept
its two projections. -/
theorem monitor_accepts_iff (tree : LabeledTree (Direction x) (Choice x)) :
    (EncodedTreeNonemptiness.monitor (monitorData (compile x))).toRunAutomaton.acceptsTree tree ↔
      (EncodedTreeNonemptiness.monitor (monitorData (left x))).toRunAutomaton.acceptsTree
        (leftChoice x ∘ tree) ∧
      (EncodedTreeNonemptiness.monitor (monitorData (right x))).toRunAutomaton.acceptsTree
        (rightChoice x ∘ tree) := by
  change (EncodedTreeNonemptiness.monitor (EncodedWordTree.compile _)).toRunAutomaton.acceptsTree _ ↔ _
  rw [EncodedWordTree.accepts_iff, numericWord_eq,
    EncodedTreeWord.accepts_iff, EncodedTreeWord.accepts_iff]
  have pointwise (branch : Nat → Direction x) :
      ((EncodedParityFamilies.automaton (EncodedParityProduct.conjunctionData (productData x))).comap
          (pairLetter x)).Accepts (WordTreeMonitor.word tree branch) ↔
        (EncodedParityTables.automaton (EncodedTreeWord.compile (monitorData (left x)))).Accepts
          (OmegaWord.map (EncodedTreeWord.letter _) (WordTreeMonitor.word (leftChoice x ∘ tree) branch)) ∧
        (EncodedParityTables.automaton (EncodedTreeWord.compile (monitorData (right x)))).Accepts
          (OmegaWord.map (EncodedTreeWord.letter _) (WordTreeMonitor.word (rightChoice x ∘ tree) branch)) := by
    rw [DetParityAutomaton.comap_accepts_iff]
    have h := EncodedParityProduct.accepts_conjunction_iff (productData x)
      (leftLetter x) (rightLetter x) (fun a => congrArg Prod.fst (product_letter x a))
      (fun a => congrArg Prod.snd (product_letter x a))
      (OmegaWord.map (pairLetter x) (WordTreeMonitor.word tree branch))
    have hl : (fun n => leftLetter x (OmegaWord.map (pairLetter x)
        (WordTreeMonitor.word tree branch) n)) =
        OmegaWord.map (EncodedTreeWord.letter _) (WordTreeMonitor.word (leftChoice x ∘ tree) branch) := by
      funext n
      simp only [OmegaWord.map, WordTreeMonitor.word, leftLetter, split_pair, Function.comp_apply]
      rfl
    have hr : (fun n => rightLetter x (OmegaWord.map (pairLetter x)
        (WordTreeMonitor.word tree branch) n)) =
        OmegaWord.map (EncodedTreeWord.letter _) (WordTreeMonitor.word (rightChoice x ∘ tree) branch) := by
      funext n
      simp only [OmegaWord.map, WordTreeMonitor.word, rightLetter, split_pair, Function.comp_apply]
      rfl
    exact h.trans (and_congr (Iff.of_eq (congrArg _ hl)) (Iff.of_eq (congrArg _ hr)))
  exact (forall_congr' pointwise).trans forall_and

/-- Conjunction at a shared direction and public-letter alphabet. -/
theorem compile_correct (tree : LabeledTree (Fin x.1) (Fin (x.2.1 + 1))) :
    (automaton (compile x)).acceptsTree tree ↔
      EncodedTreeShape.Accepts x.1 x.2.1 x.2.2.1 tree ∧
      EncodedTreeShape.Accepts x.1 x.2.1 x.2.2.2 tree := by
  change (automaton (compile x)).acceptsTree tree ↔
    (automaton (left x)).acceptsTree tree ∧ (automaton (right x)).acceptsTree tree
  rw [EncodedProjectedTree.accepts_iff]
  constructor
  · rintro ⟨annotated, hpublic, accepts⟩
    obtain ⟨hl, hr⟩ := (monitor_accepts_iff x annotated).mp accepts
    constructor
    · apply (EncodedProjectedTree.accepts_iff (left x) tree).mpr
      refine ⟨leftChoice x ∘ annotated, ?_, hl⟩
      funext node
      exact (projection_left x (annotated node)).symm.trans (congrFun hpublic node)
    · apply (EncodedProjectedTree.accepts_iff (right x) tree).mpr
      refine ⟨rightChoice x ∘ annotated, ?_, hr⟩
      funext node
      exact (compatible x (annotated node)).symm.trans
        ((projection_left x (annotated node)).symm.trans (congrFun hpublic node))
  · rintro ⟨hl, hr⟩
    obtain ⟨tl, htl, hl⟩ := (EncodedProjectedTree.accepts_iff (left x) tree).mp hl
    obtain ⟨tr, htr, hr⟩ := (EncodedProjectedTree.accepts_iff (right x) tree).mp hr
    have compatible (node) : letter (left x) (tl node) = letter (right x) (tr node) :=
      (congrFun htl node).trans (congrFun htr node).symm
    choose paired pl pr using fun node => exists_choice x (tl node) (tr node) (compatible node)
    refine ⟨paired, ?_, (monitor_accepts_iff x paired).mpr ?_⟩
    · funext node
      exact (projection_left x (paired node)).trans
        ((congrArg (letter (left x)) (pl node)).trans (congrFun htl node))
    · have left_eq : leftChoice x ∘ paired = tl := funext pl
      have right_eq : rightChoice x ∘ paired = tr := funext pr
      exact ⟨left_eq.symm ▸ hl, right_eq.symm ▸ hr⟩

end DistributedSynthesis.EncodedTreeIntersection
