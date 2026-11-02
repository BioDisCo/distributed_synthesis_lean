/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanAllocation

/-! # Numeric Piterman child creation

All triggering nodes are determined before any fresh child is created. Each
new child's parent, name, and accepting-state label use the same allocation.
The first part of the interface computes the finite lists used by that update.
-/

namespace DistributedSynthesis.EncodedPitermanCreation
open EncodedPitermanStates

abbrev Input := Nat × List Nat × Code

def active (x : Input) : List Nat :=
  (List.range (2 * x.1)).filter (fun q => decide (read x.2.2.1 q = 1))

def inactive (x : Input) : List Nat :=
  (List.range (2 * x.1)).filter (fun q => decide (read x.2.2.1 q ≠ 1))

def acceptingPart (x : Input) (q : Nat) : List Nat :=
  (List.range x.1).filter (fun r => decide (r ∈ readLabel x.2.2 q ∧ r ∈ x.2.1))

def triggers (x : Input) : List Nat :=
  (List.range (2 * x.1)).filter
    (fun q => decide (read x.2.2.1 q = 1 ∧ acceptingPart x q ≠ []))

def freshChild (x : Input) (q : Nat) : Nat :=
  EncodedPitermanAllocation.child (2 * x.1) (triggers x) (inactive x) q

def freshName (x : Input) (q : Nat) : Nat :=
  EncodedPitermanAllocation.name (2 * x.1) (active x) (triggers x) q

/-- Search by the same increasing source-node order as the semantic allocation. -/
def owner (x : Input) (q : Nat) : Option Nat :=
  ((triggers x).filter (fun p => decide (freshChild x p = q))).head?

def nextActive (x : Input) (q : Nat) : Nat :=
  if (owner x q).isSome then 1 else read x.2.2.1 q
def nextName (x : Input) (q : Nat) : Nat :=
  ((owner x q).map (freshName x)).getD (read x.2.2.2.1 q)
def nextParent (x : Input) (q : Nat) : Nat :=
  (owner x q).getD (read x.2.2.2.2.1 q)
def nextLabel (x : Input) (q : Nat) : List Nat :=
  ((owner x q).map (acceptingPart x)).getD (readLabel x.2.2 q)

def stage2 (x : Input) : Code :=
  ((List.range (2 * x.1)).map (nextActive x),
    (List.range (2 * x.1)).map (nextName x),
    (List.range (2 * x.1)).map (nextParent x),
    (List.range (2 * x.1)).map (nextLabel x), x.1, x.1)

private theorem n_primrec : Primrec (fun x : Input => x.1) := Primrec.fst
private theorem acc_primrec : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
private theorem code_primrec : Primrec (fun x : Input => x.2.2) := Primrec.snd.comp Primrec.snd
private theorem nodes_primrec : Primrec (fun x : Input => 2 * x.1) :=
  Primrec.nat_mul.comp (Primrec.const 2) n_primrec
private theorem bit_primrec : Primrec₂ (fun (x : Input) q => read x.2.2.1 q) :=
  read_primrec.comp (Primrec.fst.comp (code_primrec.comp Primrec.fst)) Primrec.snd

theorem active_primrec : Primrec active := by
  have h : PrimrecRel (fun (x : Input) q => read x.2.2.1 q = 1) :=
    Primrec.eq.comp bit_primrec (Primrec.const 1)
  exact h.swap.listFilter.comp
    (Primrec.list_range.comp nodes_primrec) Primrec.id

theorem inactive_primrec : Primrec inactive := by
  have h : PrimrecRel (fun (x : Input) q => read x.2.2.1 q ≠ 1) :=
    (Primrec.eq.comp bit_primrec (Primrec.const 1)).not
  exact h.swap.listFilter.comp
    (Primrec.list_range.comp nodes_primrec) Primrec.id

theorem acceptingPart_primrec : Primrec₂ acceptingPart := by
  have hm : PrimrecRel (fun (xs : List Nat) q => q ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  have hp : PrimrecRel (fun (y : Input × Nat) r => r ∈ readLabel y.1.2.2 y.2 ∧ r ∈ y.1.2.1) :=
    (hm.comp (readLabel_primrec.comp (code_primrec.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)) Primrec.snd).and
      (hm.comp (acc_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  exact hp.swap.listFilter.comp (Primrec.list_range.comp (n_primrec.comp Primrec.fst)) Primrec.id

theorem triggers_primrec : Primrec triggers := by
  have h : PrimrecRel (fun (x : Input) q => read x.2.2.1 q = 1 ∧ acceptingPart x q ≠ []) :=
    (Primrec.eq.comp bit_primrec (Primrec.const 1)).and
      (Primrec.eq.comp acceptingPart_primrec (Primrec.const [])).not
  exact h.swap.listFilter.comp
      (Primrec.list_range.comp nodes_primrec) Primrec.id

theorem freshChild_primrec : Primrec₂ freshChild :=
  EncodedPitermanAllocation.child_primrec.comp ((nodes_primrec.comp Primrec.fst).pair
    ((triggers_primrec.comp Primrec.fst).pair ((inactive_primrec.comp Primrec.fst).pair Primrec.snd)))

theorem freshName_primrec : Primrec₂ freshName :=
  EncodedPitermanAllocation.name_primrec.comp ((nodes_primrec.comp Primrec.fst).pair
    ((active_primrec.comp Primrec.fst).pair ((triggers_primrec.comp Primrec.fst).pair Primrec.snd)))

theorem owner_primrec : Primrec₂ owner := by
  have h : PrimrecRel (fun (y : Input × Nat) p => freshChild y.1 p = y.2) :=
    Primrec.eq.comp (freshChild_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.snd.comp Primrec.fst)
  exact Primrec.list_head?.comp
    (h.swap.listFilter.comp
        (triggers_primrec.comp Primrec.fst) Primrec.id)

theorem nextActive_primrec : Primrec₂ nextActive :=
  Primrec.ite (Primrec.eq.comp (Primrec.option_isSome.comp owner_primrec) (Primrec.const true))
    (Primrec.const 1) bit_primrec

theorem nextName_primrec : Primrec₂ nextName :=
  Primrec.option_getD.comp
    (Primrec.option_map owner_primrec
      (freshName_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
    (read_primrec.comp (Primrec.fst.comp (Primrec.snd.comp (code_primrec.comp Primrec.fst))) Primrec.snd)

theorem nextParent_primrec : Primrec₂ nextParent :=
  Primrec.option_getD.comp owner_primrec
    (read_primrec.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (code_primrec.comp Primrec.fst)))) Primrec.snd)

theorem nextLabel_primrec : Primrec₂ nextLabel :=
  Primrec.option_getD.comp
    (Primrec.option_map owner_primrec
      (acceptingPart_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)
    (readLabel_primrec.comp (code_primrec.comp Primrec.fst) Primrec.snd)

theorem stage2_primrec : Primrec stage2 :=
  (Primrec.list_map (Primrec.list_range.comp nodes_primrec) nextActive_primrec).pair
    ((Primrec.list_map (Primrec.list_range.comp nodes_primrec) nextName_primrec).pair
      ((Primrec.list_map (Primrec.list_range.comp nodes_primrec) nextParent_primrec).pair
        ((Primrec.list_map (Primrec.list_range.comp nodes_primrec) nextLabel_primrec).pair
          (n_primrec.pair n_primrec))))

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State)) (acc : List Nat)
  (decAccept : DecidablePred A.accepting)

@[reducible] def input (tree : CompactTreeData A) : Input := (Fintype.card A.State, acc, encode A number tree)

omit [DecidableEq A.State] in
theorem active_correct (tree : CompactTreeData A) :
    active (input A number acc tree) = FiniteSubsets.encode (tree.activeNodes A) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  simp [input, encode, EncodedPitermanStates.read, CompactTreeData.activeNodes, q.isLt]

omit [DecidableEq A.State] in
theorem inactive_correct (tree : CompactTreeData A) :
    inactive (input A number acc tree) = FiniteSubsets.encode (tree.inactiveNodes A) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  simp [input, encode, EncodedPitermanStates.read, CompactTreeData.inactiveNodes,
    CompactTreeData.activeNodes, q.isLt]

variable (ha : ∀ q, (number q).val ∈ acc ↔ A.accepting q)
include ha in
theorem acceptingPart_correct (tree : CompactTreeData A) (q : Node A) :
    acceptingPart (input A number acc tree) q.val =
      encodeLabel A number (Computable.acceptingPart A decAccept tree q) := by
  apply filter_range_eq_encodeLabel
  intro r
  simp only [input, encode, readLabel, List.getElem?_ofFn, Option.getD_some,
    dif_pos q.isLt, Fin.eta, decide_eq_true_eq, Computable.acceptingPart, Finset.mem_filter]
  have hm := mem_decodeLabel A number (encodeLabel A number (tree.label q)) r
  rw [decode_encodeLabel] at hm
  exact and_congr hm.symm (ha r)

include ha in
theorem triggers_correct (tree : CompactTreeData A) :
    triggers (input A number acc tree) =
      FiniteSubsets.encode (Computable.stage2Triggers A decAccept tree) := by
  apply FiniteSubsets.filter_range_eq_encode (n := 2 * Fintype.card A.State)
  intro q
  simp only [decide_eq_true_eq, Computable.stage2Triggers, Finset.mem_filter]
  have hb : read (input A number acc tree).2.2.1 q.val = 1 ↔ tree.active q = true := by
    simp [input, encode, EncodedPitermanStates.read, q.isLt]
  rw [hb, acceptingPart_correct A number acc decAccept ha]
  have hn (s : Finset A.State) : encodeLabel A number s = [] ↔ s = ∅ := by
    constructor
    · intro h
      have hd := decode_encodeLabel A number s
      rw [h] at hd
      simpa [decodeLabel, FiniteSubsets.decode] using hd.symm
    · rintro rfl; simp [encodeLabel, FiniteSubsets.encode]
  simp [CompactTreeData.activeNodes, hn, Finset.nonempty_iff_ne_empty]

variable (tree : CompactTreeData A)
  (hbound : ∀ node, tree.active node = true → (tree.name node).val < Fintype.card A.State)
  (hinjective : ∀ left right, tree.active left = true → tree.active right = true →
    tree.name left = tree.name right → left = right)
  (hconsecutive : ∀ k : Nat, k < Fintype.card A.State →
    (∃ node, tree.active node ∧ (tree.name node).val = k) →
    ∀ j : Nat, j < k → ∃ node, tree.active node ∧ (tree.name node).val = j)

local notation "P" => Computable.stage2PlanOfBounds A decAccept tree hbound hinjective hconsecutive
local notation "x" => input A number acc tree

include ha in
theorem freshChild_correct (q : Node A) : freshChild x q.val = ((P).freshChild q).val := by
  unfold freshChild
  rw [triggers_correct A number acc decAccept ha, inactive_correct]
  exact EncodedPitermanAllocation.child_eq_plan A decAccept tree hbound hinjective hconsecutive q

include ha in
theorem freshName_correct (q : Node A) : freshName x q.val = ((P).freshName q).val := by
  unfold freshName
  rw [triggers_correct A number acc decAccept ha, active_correct]
  exact EncodedPitermanAllocation.name_eq_plan A decAccept tree hbound hinjective hconsecutive q

private theorem head_filter_eq_find {S : Type*} (xs : List S) (p : S → Bool) :
    (xs.filter p).head? = xs.find? p := by
  induction xs with
  | nil => rfl
  | cons a xs ih => cases h : p a <;> simp [h, ih]

private theorem head_filter_map {S T : Type*} (xs : List S) (f : S → T) (p : T → Bool) :
    ((xs.map f).filter p).head? = (xs.find? (fun a => p (f a))).map f := by
  rw [List.filter_map, List.head?_map, head_filter_eq_find]
  rfl

include ha in
theorem owner_correct (q : Node A) :
    owner x q.val = (Computable.ownerOf A decAccept P q).map Fin.val := by
  unfold owner
  rw [triggers_correct A number acc decAccept ha]
  rw [← FiniteSubsets.normalize_encode, FiniteSubsets.normalize_encode_eq_sort, head_filter_map]
  unfold Computable.ownerOf
  congr 1
  apply congrArg (fun pred => ((Computable.stage2Triggers A decAccept tree).sort (· ≤ ·)).find? pred)
  funext p
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Fin.ext_iff]
  rw [freshChild_correct A number acc decAccept ha tree hbound hinjective hconsecutive]

include ha in
/-- Exact code identity, so this stage can be composed without a new
canonicalization or a choice of representations between stages. -/
theorem stage2_encode :
    stage2 x = encode A number (Computable.stage2 A decAccept tree P) := by
  unfold stage2 encode
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
  · apply FiniteSearch.tabulate_eq_ofFn
    intro q
    have ho := owner_correct A number acc decAccept ha tree hbound hinjective hconsecutive q
    simp only [nextActive, ho, Computable.stage2]
    cases h : Computable.ownerOf A decAccept P q <;>
      simp [h, input, encode, EncodedPitermanStates.read, q.isLt]
  · apply FiniteSearch.tabulate_eq_ofFn
    intro q
    have ho := owner_correct A number acc decAccept ha tree hbound hinjective hconsecutive q
    simp only [nextName, ho, Computable.stage2]
    cases h : Computable.ownerOf A decAccept P q with
    | none => simp [h, input, encode, EncodedPitermanStates.read, q.isLt]
    | some p =>
      simpa only [h, Option.map_some, Option.getD_some] using
        freshName_correct A number acc decAccept ha tree hbound hinjective hconsecutive p
  · apply FiniteSearch.tabulate_eq_ofFn
    intro q
    have ho := owner_correct A number acc decAccept ha tree hbound hinjective hconsecutive q
    simp only [nextParent, ho, Computable.stage2]
    cases h : Computable.ownerOf A decAccept P q <;>
      simp [h, input, encode, EncodedPitermanStates.read, q.isLt]
  · apply FiniteSearch.tabulate_eq_ofFn
    intro q
    have ho := owner_correct A number acc decAccept ha tree hbound hinjective hconsecutive q
    simp only [nextLabel, ho, Computable.stage2]
    cases h : Computable.ownerOf A decAccept P q with
    | none => simp [h, input, encode, readLabel, q.isLt]
    | some p =>
      simpa only [h, Option.map_some, Option.getD_some] using
        acceptingPart_correct A number acc decAccept ha tree p

include ha in
theorem stage2_correct :
    decode A number (stage2 x) = Computable.stage2 A decAccept tree P := by
  rw [stage2_encode A number acc decAccept ha tree hbound hinjective hconsecutive, decode_encode]

end DistributedSynthesis.EncodedPitermanCreation
