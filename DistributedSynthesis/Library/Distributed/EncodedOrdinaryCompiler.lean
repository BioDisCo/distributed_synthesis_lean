/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedOrdinaryThreadsCorrect

/-! # Complete finite tables for ordinary journal bad threads

Both orientations use the same numeric constructor. The boundary selects the
initial monitor state; each input letter is a complete journal response table
and a sender input. These are Büchi tables, before numbering and determinization.
-/
namespace DistributedSynthesis.EncodedOrdinaryCompiler
open EncodedRoundObjectives EncodedOrdinaryThreads
abbrev Input := Data × Bool × Nat

def shape (d : Data) : EncodedJournalLabels.Shape :=
  (stateCount d, inputOne d, inputTwo d, outputOne d, outputTwo d)
def labels (d : Data) := EncodedJournalLabels.allCodes (shape d)
@[irreducible] def alphabet (x : Input) :=
  (labels x.1).product (List.range (senderCount (x.1,x.2.1,[])))
def baseRows (x : Input) :=
  (alphabet x).map (fun a => edges (x.1,x.2.1,a.1) a.2)
def threadInput (x : Input) : EncodedThreadBuchi.Input :=
  (stateCount x.1 * stateCount x.1, initial x.1 x.2.2, priorities x.1, baseRows x)
def compile (x : Input) := EncodedThreadBuchi.compile (threadInput x)

theorem shape_primrec : Primrec shape :=
  stateCount_primrec.pair (inputOne_primrec.pair (inputTwo_primrec.pair
    (outputOne_primrec.pair outputTwo_primrec)))
theorem labels_primrec : Primrec labels := EncodedJournalLabels.allCodes_primrec.comp shape_primrec
theorem alphabet_primrec : Primrec alphabet := by
  unfold alphabet
  exact FiniteSearch.product_primrec.comp (labels_primrec.comp Primrec.fst)
    (Primrec.list_range.comp (senderCount_primrec.comp
      (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (Primrec.const [])))))
theorem baseRows_primrec : Primrec baseRows := by
  unfold baseRows
  have hd : Primrec (fun y : Input × (EncodedJournalLabels.Code × Nat) => y.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hb : Primrec (fun y : Input × (EncodedJournalLabels.Code × Nat) => y.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_map alphabet_primrec
    (edges_primrec.comp (hd.pair (hb.pair (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
theorem threadInput_primrec : Primrec threadInput :=
  (Primrec.nat_mul.comp (stateCount_primrec.comp Primrec.fst) (stateCount_primrec.comp Primrec.fst)).pair
    ((initial_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).pair
      ((priorities_primrec.comp Primrec.fst).pair baseRows_primrec))
theorem compile_primrec : Primrec compile := EncodedThreadBuchi.compile_primrec.comp threadInput_primrec

theorem labels_complete (d : Data) (l : DetParityAutomaton.GlobalJournalLabel (automaton d)) :
    ∃ c ∈ labels d, label d c = l := by
  simpa only [labels, shape, stateCount_card, inputOne, inputTwo, outputOne, outputTwo, label]
    using EncodedJournalLabels.complete (automaton d) (stateNumber d) l

theorem mem_alphabet (x : Input) (a : EncodedJournalLabels.Code × Nat) :
    a ∈ alphabet x ↔ a.1 ∈ labels x.1 ∧ a.2 < senderCount (x.1,x.2.1,[]) := by
  rcases a with ⟨c,i⟩
  unfold alphabet
  exact List.mem_product.trans (and_congr Iff.rfl List.mem_range)

theorem left_alphabet_complete (d : Data) (boundary : Nat)
    (l : DetParityAutomaton.GlobalJournalLabel (automaton d)) (j : Fin (inputTwo d)) :
    ∃ c, (c,j.val) ∈ alphabet (d,false,boundary) ∧ label d c = l := by
  obtain ⟨c,hc,he⟩ := labels_complete d l
  refine ⟨c, ?_, he⟩
  unfold alphabet
  exact List.mem_product.mpr ⟨hc, List.mem_range.mpr j.isLt⟩

theorem right_alphabet_complete (d : Data) (boundary : Nat)
    (l : DetParityAutomaton.GlobalJournalLabel (automaton d)) (i : Fin (inputOne d)) :
    ∃ c, (c,i.val) ∈ alphabet (d,true,boundary) ∧ label d c = l := by
  obtain ⟨c,hc,he⟩ := labels_complete d l
  refine ⟨c, ?_, he⟩
  unfold alphabet
  exact List.mem_product.mpr ⟨hc, List.mem_range.mpr i.isLt⟩

theorem row_get (x : Input) (k : Fin (alphabet x).length) :
    (baseRows x).getD k.val [] =
      edges (x.1,x.2.1,(alphabet x)[k].1) (alphabet x)[k].2 := by
  have hk : k.val < (baseRows x).length := by simpa only [baseRows, List.length_map] using k.isLt
  rw [List.getD_eq_getElem _ _ hk]
  unfold baseRows
  exact List.getElem_map _

end DistributedSynthesis.EncodedOrdinaryCompiler
