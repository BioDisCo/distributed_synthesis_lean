/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanDeletion

/-! # Numeric green-node deletion

A node is green when the union of its active children's labels equals its own
label. The removal predicate follows the existing definition through a child
of a green node; it is not replaced by a proper-ancestor approximation.
-/

namespace DistributedSynthesis.EncodedPitermanGreen
open EncodedPitermanStates EncodedPitermanPruning EncodedPitermanMinima EncodedPitermanDeletion

def child (x : Input) (p q : Nat) : Prop := isActive x q ∧ q ≠ 0 ∧ parent x q = p
instance (x : Input) (p q : Nat) : Decidable (child x p q) := by unfold child; infer_instance
def covered (x : Input) (q r : Nat) : Prop :=
  ∃ c < bound x, child x q c ∧ r ∈ readLabel x.2 c
instance (x : Input) (q r : Nat) : Decidable (covered x q r) := by unfold covered; infer_instance
def childUnion (x : Input) (q : Nat) : List Nat := (List.range x.1).filter (fun r => decide (covered x q r))
def green (x : Input) (q : Nat) : Prop :=
  isActive x q ∧ FiniteSubsets.normalize x.1 (readLabel x.2 q) = childUnion x q
instance (x : Input) (q : Nat) : Decidable (green x q) := by unfold green; infer_instance
def greenNodes (x : Input) : List Nat := (List.range (bound x)).filter (fun q => decide (green x q))
def removedByGreen (x : Input) (q : Nat) : Prop :=
  isActive x q ∧ ∃ g < bound x, green x g ∧ ∃ c < bound x, child x g c ∧ ancestor x c q
instance (x : Input) (q : Nat) : Decidable (removedByGreen x q) := by unfold removedByGreen; infer_instance
def removedNodes (x : Input) : List Nat := (List.range (bound x)).filter (fun q => decide (removedByGreen x q))
def stage4 (x : Input) : Code := erase (x, removedNodes x, x.1, minName x (greenNodes x))

private theorem mem_primrec : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
  Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)

theorem child_primrec : PrimrecPred (fun y : Args => child y.1 y.2.1 y.2.2) :=
  (isActive_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).and
    ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0)).not.and
      (Primrec.eq.comp (parent_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
        (Primrec.fst.comp Primrec.snd)))
theorem covered_primrec : PrimrecPred (fun y : Args => covered y.1 y.2.1 y.2.2) :=
  FiniteSearch.exists_lt (bound_primrec.comp Primrec.fst)
    ((child_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).and
      (mem_primrec.comp (readLabel_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
theorem childUnion_primrec : Primrec₂ childUnion := by
  have hp : PrimrecRel (fun (y : Input × Nat) r => covered y.1 y.2 r) :=
    covered_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  exact hp.swap.listFilter.comp (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) Primrec.id
theorem green_primrec : PrimrecRel green :=
  isActive_primrec.and (Primrec.eq.comp
    (FiniteSubsets.normalize_primrec.comp (Primrec.fst.comp Primrec.fst)
      (readLabel_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)) childUnion_primrec)
theorem greenNodes_primrec : Primrec greenNodes :=
  green_primrec.swap.listFilter.comp (Primrec.list_range.comp bound_primrec) Primrec.id
theorem removedByGreen_primrec : PrimrecRel removedByGreen := by
  have hctx : Primrec (fun y : ((Input × Nat) × Nat) × Nat => y.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun y : ((Input × Nat) × Nat) × Nat => y.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
  have hg : Primrec (fun y : ((Input × Nat) × Nat) × Nat => y.1.2) := Primrec.snd.comp Primrec.fst
  exact isActive_primrec.and
    (FiniteSearch.exists_lt (bound_primrec.comp Primrec.fst)
      ((green_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).and
        (FiniteSearch.exists_lt (bound_primrec.comp (Primrec.fst.comp Primrec.fst))
          ((child_primrec.comp (hctx.pair (hg.pair Primrec.snd))).and
            (ancestor_primrec.comp (hctx.pair (Primrec.snd.pair hq)))))))
theorem removedNodes_primrec : Primrec removedNodes :=
  removedByGreen_primrec.swap.listFilter.comp (Primrec.list_range.comp bound_primrec) Primrec.id
theorem stage4_primrec : Primrec stage4 :=
  erase_primrec.comp (Primrec.id.pair (removedNodes_primrec.pair
    (Primrec.fst.pair (minName_primrec.comp Primrec.id greenNodes_primrec))))

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State)) (tree : CompactTreeData A)
local notation "x" => input A number tree

omit [DecidableEq A.State] in
theorem child_correct (p q : Node A) : child x p.val q.val ↔ q ∈ tree.children A p := by
  have hroot : q = root A ↔ q.val = 0 := by exact Fin.ext_iff
  have hparent : tree.parent q = p ↔ (tree.parent q).val = p.val := Fin.ext_iff
  simp only [child, isActive_correct, parent_correct, CompactTreeData.children,
    Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, hroot, hparent]

theorem covered_correct (q : Node A) (r : A.State) :
    covered x q.val (number r).val ↔ r ∈ tree.childLabelUnion A q := by
  have hm (c : Node A) : (number r).val ∈ readLabel x.2 c.val ↔ r ∈ tree.label c := by
    change _ ∈ readLabel (encode A number tree) c.val ↔ _
    rw [readLabel_encode]
    exact (mem_decodeLabel A number _ r).symm.trans (by rw [decode_encodeLabel])
  simp only [covered, CompactTreeData.childLabelUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, hchild, hmem⟩
    exact ⟨⟨c, hc⟩, (child_correct A number tree q _).mp hchild, (hm ⟨c, hc⟩).mp hmem⟩
  · rintro ⟨c, hchild, hmem⟩
    exact ⟨c.val, c.isLt, (child_correct A number tree q c).mpr hchild, (hm c).mpr hmem⟩

theorem childUnion_correct (q : Node A) :
    childUnion x q.val = encodeLabel A number (tree.childLabelUnion A q) := by
  apply filter_range_eq_encodeLabel
  intro r
  exact (decide_eq_true_iff).trans (covered_correct A number tree q r)

theorem green_correct (q : Node A) : green x q.val ↔ q ∈ tree.greenNodes A := by
  unfold green
  rw [isActive_correct, childUnion_correct]
  change tree.active q = true ∧
    FiniteSubsets.normalize (Fintype.card A.State) (readLabel (encode A number tree) q.val) = _ ↔ _
  rw [readLabel_encode]
  have hn : FiniteSubsets.normalize (Fintype.card A.State) (encodeLabel A number (tree.label q)) =
      encodeLabel A number (tree.label q) := FiniteSubsets.normalize_encode _
  rw [hn, (encodeLabel_injective A number).eq_iff]
  exact (CompactTreeData.mem_greenNodes A tree).symm

theorem greenNodes_correct : greenNodes x = FiniteSubsets.encode (tree.greenNodes A) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  exact (decide_eq_true_iff).trans (green_correct A number tree q)

theorem removedByGreen_correct (q : Node A) : removedByGreen x q.val ↔ tree.RemovedByGreen A q := by
  simp only [removedByGreen, isActive_correct, CompactTreeData.RemovedByGreen]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨g, hg, hgreen, c, hc, hchild, hanc⟩
    exact ⟨⟨g, hg⟩, (green_correct A number tree _).mp hgreen, ⟨c, hc⟩,
      (child_correct A number tree _ _).mp hchild, (ancestor_correct A number tree _ q).mp hanc⟩
  · rintro ⟨g, hgreen, c, hchild, hanc⟩
    exact ⟨g.val, g.isLt, (green_correct A number tree g).mpr hgreen, c.val, c.isLt,
      (child_correct A number tree g c).mpr hchild, (ancestor_correct A number tree c q).mpr hanc⟩

theorem removedNodes_correct : removedNodes x = FiniteSubsets.encode (Computable.greenRemovedNodes A tree) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  simp only [decide_eq_true_eq, Computable.greenRemovedNodes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact removedByGreen_correct A number tree q

theorem stage4_encode : stage4 x = encode A number (Computable.stage4 A tree) := by
  letI := Computable.removedByGreenDecidable A tree
  have hm (q : Node A) : q ∈ Computable.greenRemovedNodes A tree ↔ tree.RemovedByGreen A q := by
    constructor
    · intro h; exact (Finset.mem_filter.mp h).2
    · intro h; exact Finset.mem_filter.mpr ⟨Finset.mem_univ q, h⟩
  unfold stage4
  rw [removedNodes_correct, greenNodes_correct, minName_correct]
  change erase (x, FiniteSubsets.encode (Computable.greenRemovedNodes A tree),
    (sentinel A).val, (tree.minBoundedNameOf A (tree.greenNodes A)).val) = _
  rw [erase_encode]
  congr 1
  unfold masked Computable.stage4
  congr 1 <;> funext q <;> simp only [hm]

end DistributedSynthesis.EncodedPitermanGreen
