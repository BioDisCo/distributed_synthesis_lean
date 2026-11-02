/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanMinima

/-! # Numeric deletion and name compaction

Deleted nodes lose their labels and active flags, but retain names and parents.
The complete removed-node set is retained separately for the final compaction.
-/

namespace DistributedSynthesis.EncodedPitermanDeletion
open EncodedPitermanStates EncodedPitermanPruning EncodedPitermanMinima

abbrev MaskInput := Input × List Nat × Nat × Nat
def maskedActive (y : MaskInput) (q : Nat) : Nat :=
  if q ∈ y.2.1 then 0 else read y.1.2.1 q
def maskedLabel (y : MaskInput) (q : Nat) : List Nat :=
  if q ∈ y.2.1 then [] else readLabel y.1.2 q
def erase (y : MaskInput) : Code :=
  ((List.range (bound y.1)).map (maskedActive y), y.1.2.2.1, y.1.2.2.2.1,
    (List.range (bound y.1)).map (maskedLabel y), y.2.2.1, y.2.2.2)

private theorem mem_primrec : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
  Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)

theorem maskedActive_primrec : Primrec₂ maskedActive :=
  Primrec.ite (mem_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (Primrec.const 0)
    (read_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
theorem maskedLabel_primrec : Primrec₂ maskedLabel :=
  Primrec.ite (mem_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (Primrec.const [])
    (readLabel_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
theorem erase_primrec : Primrec erase :=
  (Primrec.list_map (Primrec.list_range.comp (bound_primrec.comp Primrec.fst)) maskedActive_primrec).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
        ((Primrec.list_map (Primrec.list_range.comp (bound_primrec.comp Primrec.fst)) maskedLabel_primrec).pair
          ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))

def emptyNodes (x : Input) : List Nat :=
  (List.range (bound x)).filter
    (fun q => decide (isActive x q ∧ FiniteSubsets.normalize x.1 (readLabel x.2 q) = []))
def removed (x : Input) (previous : List Nat) : List Nat :=
  FiniteSubsets.normalize (bound x) (previous ++ emptyNodes x)
def stage5 (x : Input) (previous : List Nat) : Code :=
  erase (x, removed x previous, minName x (removed x previous), x.2.2.2.2.2.2)

theorem emptyNodes_primrec : Primrec emptyNodes := by
  have hp : PrimrecRel (fun (x : Input) q =>
      isActive x q ∧ FiniteSubsets.normalize x.1 (readLabel x.2 q) = []) :=
    isActive_primrec.and (Primrec.eq.comp
      (FiniteSubsets.normalize_primrec.comp (Primrec.fst.comp Primrec.fst)
        (readLabel_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)) (Primrec.const []))
  exact hp.swap.listFilter.comp (Primrec.list_range.comp bound_primrec) Primrec.id
theorem removed_primrec : Primrec₂ removed :=
  FiniteSubsets.normalize_primrec.comp (bound_primrec.comp Primrec.fst)
    (Primrec.list_append.comp Primrec.snd (emptyNodes_primrec.comp Primrec.fst))
theorem stage5_primrec : Primrec₂ stage5 := by
  have hr : Primrec (fun y : Input × List Nat => removed y.1 y.2) := removed_primrec
  exact erase_primrec.comp (Primrec.fst.pair (hr.pair
    ((minName_primrec.comp Primrec.fst removed_primrec).pair
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))))))))

def smaller (x : Input) (previous : List Nat) (q : Nat) : List Nat :=
  (List.range (bound x)).filter (fun old => decide (old ∈ previous ∧ name x old < name x q))
def compacted (x : Input) (previous : List Nat) (q : Nat) : Nat :=
  if FiniteSubsets.normalize x.1 (readLabel x.2 q) = [] then name x q
  else name x q - (smaller x previous q).length
def stage6 (x : Input) (previous : List Nat) : Code :=
  (x.2.1, (List.range (bound x)).map (compacted x previous), x.2.2.2.1,
    x.2.2.2.2.1, x.2.2.2.2.2.1, x.2.2.2.2.2.2)

theorem smaller_primrec : Primrec (fun y : Input × List Nat × Nat => smaller y.1 y.2.1 y.2.2) := by
  have hp : PrimrecRel (fun (y : Input × List Nat × Nat) old => old ∈ y.2.1 ∧ name y.1 old < name y.1 y.2.2) :=
    (mem_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).and
      (Primrec.nat_lt.comp (name_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (name_primrec.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  exact hp.swap.listFilter.comp (Primrec.list_range.comp (bound_primrec.comp Primrec.fst)) Primrec.id
theorem compacted_primrec : Primrec (fun y : Input × List Nat × Nat => compacted y.1 y.2.1 y.2.2) :=
  Primrec.ite (Primrec.eq.comp (FiniteSubsets.normalize_primrec.comp (Primrec.fst.comp Primrec.fst)
    (readLabel_primrec.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))) (Primrec.const []))
    (name_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (Primrec.nat_sub.comp (name_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
      (Primrec.list_length.comp smaller_primrec))
theorem stage6_primrec : Primrec₂ stage6 :=
  (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
    ((Primrec.list_map (Primrec.list_range.comp (bound_primrec.comp Primrec.fst))
      (compacted_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).pair
          ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
            (Primrec.snd.comp Primrec.fst)))))).pair
            (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
              (Primrec.snd.comp Primrec.fst))))))))))

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State)) (tree : CompactTreeData A)
local notation "x" => input A number tree

def masked (nodes : Finset (Node A)) (e f : Name A) : CompactTreeData A where
  active q := if q ∈ nodes then false else tree.active q
  name := tree.name
  parent := tree.parent
  label q := if q ∈ nodes then ∅ else tree.label q
  e := e
  f := f

omit [DecidableEq A.State] in
theorem erase_encode (nodes : Finset (Node A)) (e f : Name A) :
    erase (x, FiniteSubsets.encode nodes, e.val, f.val) = encode A number (masked A tree nodes e f) := by
  have hm (q : Node A) : q.val ∈ FiniteSubsets.encode nodes ↔ q ∈ nodes := by
    rw [← FiniteSubsets.mem_decode _ _ q, FiniteSubsets.decode_encode]
  unfold erase encode
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))))
  · apply FiniteSearch.tabulate_eq_ofFn (n := 2 * Fintype.card A.State)
    intro q
    simp only [maskedActive, masked, hm]
    split_ifs <;> simp [input, encode, EncodedPitermanStates.read, q.isLt]
  · apply FiniteSearch.tabulate_eq_ofFn (n := 2 * Fintype.card A.State)
    intro q
    simp only [maskedLabel, masked, hm]
    split_ifs <;> simp [input, encode, readLabel, encodeLabel, FiniteSubsets.encode, q.isLt]

theorem emptyNodes_correct : emptyNodes x = FiniteSubsets.encode (tree.emptyActiveNodes A) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  simp only [decide_eq_true_eq]
  rw [isActive_correct]
  simp only [input, readLabel_encode, encodeLabel,
    FiniteSubsets.normalize_encode]
  rw [← encodeLabel, encodeLabel_eq_nil]
  exact (CompactTreeData.mem_emptyActiveNodes A tree).symm

theorem removed_correct (previous : Finset (Node A)) :
    removed x (FiniteSubsets.encode previous) =
      FiniteSubsets.encode (previous ∪ tree.emptyActiveNodes A) := by
  unfold removed
  rw [emptyNodes_correct]
  change FiniteSubsets.normalize (2 * Fintype.card A.State) _ = _
  rw [← FiniteSubsets.normalize_encode (previous ∪ tree.emptyActiveNodes A), FiniteSubsets.normalize_eq_iff]
  rw [FiniteSubsets.decode_encode]
  ext q
  simp only [FiniteSubsets.mem_decode, List.mem_append, Finset.mem_union]
  have hm (s : Finset (Node A)) : q.val ∈ FiniteSubsets.encode s ↔ q ∈ s := by
    rw [← FiniteSubsets.mem_decode _ _ q, FiniteSubsets.decode_encode]
  rw [hm, hm]

theorem stage5_encode (previous : Finset (Node A)) :
    stage5 x (FiniteSubsets.encode previous) = encode A number (Computable.stage5 A tree previous) := by
  unfold stage5
  rw [removed_correct, minName_correct]
  change erase (x, FiniteSubsets.encode (previous ∪ tree.emptyActiveNodes A),
    (tree.minBoundedNameOf A (previous ∪ tree.emptyActiveNodes A)).val, tree.f.val) = _
  rw [erase_encode]
  congr 1
  unfold masked Computable.stage5
  congr 1 <;> funext q <;> simp [CompactTreeData.RemovedByStage5]

omit [DecidableEq A.State] in
theorem smaller_correct (previous : Finset (Node A)) (q : Node A) :
    smaller x (FiniteSubsets.encode previous) q.val =
      FiniteSubsets.encode (tree.removedBeforeName A previous q) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro old
  simp only [decide_eq_true_eq, name_correct, CompactTreeData.mem_removedBeforeName]
  have hm : old.val ∈ FiniteSubsets.encode previous ↔ old ∈ previous := by
    rw [← FiniteSubsets.mem_decode _ _ old, FiniteSubsets.decode_encode]
  rw [hm]

theorem compacted_correct (previous : Finset (Node A)) (q : Node A) :
    compacted x (FiniteSubsets.encode previous) q.val =
      ((Computable.stage6 A tree previous).name q).val := by
  have hempty : FiniteSubsets.normalize x.1 (readLabel x.2 q.val) = [] ↔ tree.label q = ∅ := by
    simp only [input, readLabel_encode, encodeLabel, FiniteSubsets.normalize_encode]
    exact encodeLabel_eq_nil A number _
  simp only [compacted, hempty, name_correct, smaller_correct, FiniteSubsets.encode_length,
    Computable.stage6, CompactTreeData.compactedName]
  split_ifs <;> rfl

theorem stage6_encode (previous : Finset (Node A)) :
    stage6 x (FiniteSubsets.encode previous) = encode A number (Computable.stage6 A tree previous) := by
  unfold stage6 encode
  refine Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl rfl))))
  exact FiniteSearch.tabulate_eq_ofFn _ _ (compacted_correct A number tree previous)

end DistributedSynthesis.EncodedPitermanDeletion
