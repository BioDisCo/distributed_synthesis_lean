/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanStates

/-! # Numeric ancestor search and Piterman's sibling pruning

Reachability follows parent pointers for fewer than `2*n` steps. The bound is
complete on the finite node carrier, including cyclic raw records. Blocking
checks older siblings of every ancestor, not just immediate siblings.
-/

namespace DistributedSynthesis.EncodedPitermanPruning
open EncodedPitermanStates

abbrev Input := Nat × Code
def bound (x : Input) : Nat := 2 * x.1
def isActive (x : Input) (q : Nat) : Prop := read x.2.1 q = 1
instance (x : Input) (q : Nat) : Decidable (isActive x q) := inferInstanceAs (Decidable (read x.2.1 q = 1))
def parent (x : Input) (q : Nat) : Nat := read x.2.2.2.1 q % bound x
def name (x : Input) (q : Nat) : Nat := read x.2.2.1 q % bound x
def orbit (x : Input × Nat) : Nat → Nat
  | 0 => x.2
  | k + 1 => parent x.1 (orbit x k)
def ancestor (x : Input) (a q : Nat) : Prop := ∃ k < bound x, orbit (x, q) k = a
instance (x : Input) (a q : Nat) : Decidable (ancestor x a q) := by unfold ancestor; infer_instance
def older (x : Input) (a b : Nat) : Prop :=
  isActive x a ∧ isActive x b ∧ parent x a ≠ a ∧ a ≠ b ∧ parent x a = parent x b ∧ name x a < name x b
instance (x : Input) (a b : Nat) : Decidable (older x a b) := by unfold older; infer_instance
def blocked (x : Input) (q r : Nat) : Prop :=
  ∃ a < bound x, ∃ o < bound x, ancestor x a q ∧ older x o a ∧ r ∈ readLabel x.2 o
instance (x : Input) (q r : Nat) : Decidable (blocked x q r) := by unfold blocked; infer_instance

def label (x : Input) (q : Nat) : List Nat :=
  (List.range x.1).filter (fun r => decide (r ∈ readLabel x.2 q ∧ ¬ blocked x q r))
def stage3 (x : Input) : Code :=
  (x.2.1, x.2.2.1, x.2.2.2.1, (List.range (bound x)).map (label x), x.1, x.1)

theorem bound_primrec : Primrec bound := Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst
theorem isActive_primrec : PrimrecRel isActive :=
  Primrec.eq.comp (read_primrec.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (Primrec.const 1)
theorem parent_primrec : Primrec₂ parent :=
  Primrec.nat_mod.comp
    (read_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      Primrec.snd) (bound_primrec.comp Primrec.fst)
theorem name_primrec : Primrec₂ name :=
  Primrec.nat_mod.comp
    (read_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
      Primrec.snd) (bound_primrec.comp Primrec.fst)

theorem orbit_primrec : Primrec₂ orbit := by
  have h := Primrec.nat_rec Primrec.snd
    (parent_primrec.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd)).to₂
  exact h.of_eq (fun x k => by induction k <;> simp_all [orbit])

abbrev Args := Input × Nat × Nat
private theorem ctx_primrec : Primrec (fun x : Args => x.1) := Primrec.fst
private theorem left_primrec : Primrec (fun x : Args => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem right_primrec : Primrec (fun x : Args => x.2.2) := Primrec.snd.comp Primrec.snd

theorem ancestor_primrec : PrimrecPred (fun x : Args => ancestor x.1 x.2.1 x.2.2) :=
  FiniteSearch.exists_lt (bound_primrec.comp ctx_primrec)
    (Primrec.eq.comp (orbit_primrec.comp
      (((ctx_primrec.pair right_primrec).comp Primrec.fst)) Primrec.snd)
      (left_primrec.comp Primrec.fst))

theorem older_primrec : PrimrecPred (fun x : Args => older x.1 x.2.1 x.2.2) :=
  (isActive_primrec.comp ctx_primrec left_primrec).and
    ((isActive_primrec.comp ctx_primrec right_primrec).and
      ((Primrec.eq.comp (parent_primrec.comp ctx_primrec left_primrec) left_primrec).not.and
        ((Primrec.eq.comp left_primrec right_primrec).not.and
          ((Primrec.eq.comp (parent_primrec.comp ctx_primrec left_primrec)
            (parent_primrec.comp ctx_primrec right_primrec)).and
            (Primrec.nat_lt.comp (name_primrec.comp ctx_primrec left_primrec)
              (name_primrec.comp ctx_primrec right_primrec))))))

theorem blocked_primrec : PrimrecPred (fun x : Args => blocked x.1 x.2.1 x.2.2) := by
  have hctx : Primrec (fun x : (Args × Nat) × Nat => x.1.1.1) :=
    ctx_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hq : Primrec (fun x : (Args × Nat) × Nat => x.1.1.2.1) :=
    left_primrec.comp (Primrec.fst.comp Primrec.fst)
  have hr : Primrec (fun x : (Args × Nat) × Nat => x.1.1.2.2) :=
    right_primrec.comp (Primrec.fst.comp Primrec.fst)
  have ha : Primrec (fun x : (Args × Nat) × Nat => x.1.2) := Primrec.snd.comp Primrec.fst
  have ho : Primrec (fun x : (Args × Nat) × Nat => x.2) := Primrec.snd
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  exact FiniteSearch.exists_lt (bound_primrec.comp ctx_primrec)
    (FiniteSearch.exists_lt (bound_primrec.comp (ctx_primrec.comp Primrec.fst))
      ((ancestor_primrec.comp (hctx.pair (ha.pair hq))).and
        ((older_primrec.comp (hctx.pair (ho.pair ha))).and
          (hm.comp (readLabel_primrec.comp (Primrec.snd.comp hctx) ho) hr))))

theorem label_primrec : Primrec₂ label := by
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  have hp : PrimrecRel (fun (x : Input × Nat) r => r ∈ readLabel x.1.2 x.2 ∧ ¬ blocked x.1 x.2 r) :=
    (hm.comp (readLabel_primrec.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)) Primrec.snd).and
      (blocked_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).not
  exact hp.swap.listFilter.comp (Primrec.list_range.comp (Primrec.fst.comp Primrec.fst)) Primrec.id

theorem stage3_primrec : Primrec stage3 :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
        ((Primrec.list_map (Primrec.list_range.comp bound_primrec) label_primrec).pair
          (Primrec.fst.pair Primrec.fst))))

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State)) (tree : CompactTreeData A)
@[reducible] def input : Input := (Fintype.card A.State, encode A number tree)
local notation "x" => input A number tree

section
omit [DecidableEq A.State]

theorem isActive_correct (q : Node A) : isActive x q.val ↔ tree.active q = true := by
  simp [isActive, input, encode, EncodedPitermanStates.read, q.isLt]
theorem parent_correct (q : Node A) : parent x q.val = (tree.parent q).val := by
  simp [parent, input, encode, EncodedPitermanStates.read, q.isLt, bound,
    Nat.mod_eq_of_lt (tree.parent q).isLt]
theorem name_correct (q : Node A) : name x q.val = (tree.name q).val := by
  simp [name, input, encode, EncodedPitermanStates.read, q.isLt, bound,
    Nat.mod_eq_of_lt (tree.name q).isLt]

theorem orbit_correct (q : Node A) (k : Nat) : orbit (x, q.val) k = ((tree.parent^[k]) q).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [orbit, ih, parent_correct, Function.iterate_succ_apply']

end

omit [DecidableEq A.State] in
theorem ancestor_correct (a q : Node A) : ancestor x a.val q.val ↔ tree.IsAncestorOrSelf A a q := by
  rw [CompactTreeData.IsAncestorOrSelf, FiniteOrbits.reachable_iff_bounded]
  simp only [ancestor, input, bound, Fintype.card_fin]
  constructor
  · rintro ⟨k, hk, he⟩
    exact ⟨⟨k, by simpa only [Node, Fintype.card_fin] using hk⟩,
      Fin.ext ((orbit_correct A number tree q k).symm.trans he)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k.val, by simpa only [Node, Fintype.card_fin] using k.isLt,
      (orbit_correct A number tree q k.val).trans (congrArg Fin.val hk)⟩

omit [DecidableEq A.State] in
theorem older_correct (a b : Node A) : older x a.val b.val ↔ tree.OlderSibling A a b := by
  have hpa : tree.parent a = a ↔ (tree.parent a).val = a.val := Fin.ext_iff
  have hab : a = b ↔ a.val = b.val := Fin.ext_iff
  simp only [older, isActive_correct, parent_correct, name_correct,
    CompactTreeData.OlderSibling, ne_eq, hpa, hab, Fin.ext_iff]

theorem blocked_correct (q : Node A) (r : A.State) :
    blocked x q.val (number r).val ↔ tree.BlockedByOlderSibling A q r := by
  have hm (o : Node A) : (number r).val ∈ readLabel x.2 o.val ↔ r ∈ tree.label o := by
    simp only [input, encode, readLabel, List.getElem?_ofFn, dif_pos o.isLt, Fin.eta, Option.getD_some]
    exact (mem_decodeLabel A number _ r).symm.trans
      (by rw [decode_encodeLabel])
  constructor
  · rintro ⟨a, ha, o, ho, hac, hol, hmem⟩
    exact ⟨⟨a, ha⟩, ⟨o, ho⟩, (ancestor_correct A number tree _ q).mp hac,
      (older_correct A number tree _ _).mp hol, (hm ⟨o, ho⟩).mp hmem⟩
  · rintro ⟨a, o, hac, hol, hmem⟩
    exact ⟨a.val, a.isLt, o.val, o.isLt, (ancestor_correct A number tree a q).mpr hac,
      (older_correct A number tree o a).mpr hol, (hm o).mpr hmem⟩

theorem label_correct (q : Node A) :
    label x q.val = encodeLabel A number ((Computable.stage3 A tree).label q) := by
  apply filter_range_eq_encodeLabel
  intro r
  simp only [decide_eq_true_eq, Computable.stage3, Finset.mem_filter, blocked_correct]
  have hm : (number r).val ∈ readLabel x.2 q.val ↔ r ∈ tree.label q := by
    simp only [input, encode, readLabel, List.getElem?_ofFn, dif_pos q.isLt, Fin.eta, Option.getD_some]
    exact (mem_decodeLabel A number _ r).symm.trans (by rw [decode_encodeLabel])
  exact and_congr hm Iff.rfl

theorem stage3_encode : stage3 x = encode A number (Computable.stage3 A tree) := by
  unfold stage3 encode
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext rfl rfl))))
  exact FiniteSearch.tabulate_eq_ofFn _ _ (label_correct A number tree)

theorem stage3_correct : decode A number (stage3 x) = Computable.stage3 A tree := by
  rw [stage3_encode, decode_encode]

end DistributedSynthesis.EncodedPitermanPruning
