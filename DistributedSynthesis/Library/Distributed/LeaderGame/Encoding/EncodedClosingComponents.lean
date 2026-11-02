/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingReachability
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservations

/-! Compute live closing components from their two observation matrices.
Numbering checks reject duplicated slots, omitted component members, and
out-of-range indices. -/
namespace Characterisation.EncodedClosingComponents
open DistributedSynthesis
open EncodedClosingObservations (Views)
attribute [local irreducible] Primrec

abbrev Data := Nat × List Views × List Bool
def size (d : Data) := d.1
def views (d : Data) (i j : Nat) := d.2.1.getD (i*d.1+j) (false,false)
def live (d : Data) (i : Nat) := d.2.2.getD i false
def Adjacent (d : Data) (i j : Nat) : Prop :=
  i ≠ j ∧ live d i = true ∧ live d j = true ∧
    ((views d i j).1 = true ∨ (views d i j).2 = true ∨
     (views d j i).1 = true ∨ (views d j i).2 = true)
instance (d : Data) (i j : Nat) : Decidable (Adjacent d i j) := by
  unfold Adjacent
  infer_instance
def graphData (d : Data) : EncodedClosingReachability.Data :=
  (d.1,EncodedClosingReachability.tabulate d.1 (fun i j => decide (Adjacent d i j)))
def mask (d : Data) (root i : Nat) := live d i && EncodedClosingReachability.reachable (graphData d) root i

def Enumerates (d : Data) (root : Nat) (keep : List Nat) : Prop :=
  (∀ i ∈ keep, i < d.1) ∧
  (∀ i < keep.length, ∀ j < keep.length, keep.getD i 0 = keep.getD j 0 → i=j) ∧
  (∀ i < d.1, mask d root i = true ↔ i ∈ keep)
instance (d : Data) (root : Nat) (keep : List Nat) : Decidable (Enumerates d root keep) := by
  unfold Enumerates
  infer_instance
@[irreducible] def enumeration (d : Data) (root : Nat) (keep : List Nat) := decide (Enumerates d root keep)

theorem views_primrec : Primrec (fun x : Data × Nat × Nat => views x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD (false,false)).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd))
theorem live_primrec : Primrec₂ live :=
  (Primrec.list_getD false).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
theorem adjacent_primrec : PrimrecPred (fun x : Data × Nat × Nat => Adjacent x.1 x.2.1 x.2.2) := by
  have hd : Primrec (fun x : Data × Nat × Nat => x.1) := Primrec.fst
  have hi : Primrec (fun x : Data × Nat × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun x : Data × Nat × Nat => x.2.2) := Primrec.snd.comp Primrec.snd
  have hf := views_primrec
  have hb := views_primrec.comp (hd.pair (hj.pair hi))
  exact (Primrec.eq.comp hi hj).not.and
    ((Primrec.eq.comp (live_primrec.comp hd hi) (Primrec.const true)).and
    ((Primrec.eq.comp (live_primrec.comp hd hj) (Primrec.const true)).and
      ((Primrec.eq.comp (Primrec.fst.comp hf) (Primrec.const true)).or
       ((Primrec.eq.comp (Primrec.snd.comp hf) (Primrec.const true)).or
       ((Primrec.eq.comp (Primrec.fst.comp hb) (Primrec.const true)).or
        (Primrec.eq.comp (Primrec.snd.comp hb) (Primrec.const true)))))))
theorem graphData_primrec : Primrec graphData := Primrec.fst.pair
  (EncodedClosingReachability.tabulate_primrec Primrec.fst adjacent_primrec.decide)
theorem mask_primrec : Primrec (fun x : Data × Nat × Nat => mask x.1 x.2.1 x.2.2) :=
  (Primrec.dom_finite (fun x : Bool × Bool => x.1 && x.2)).comp
    ((live_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).pair
      (EncodedClosingReachability.reachable_primrec.comp ((graphData_primrec.comp Primrec.fst).pair Primrec.snd)))

theorem enumeration_primrec : Primrec (fun x : Data × Nat × List Nat => enumeration x.1 x.2.1 x.2.2) := by
  unfold enumeration Enumerates
  apply PrimrecPred.decide
  have hd : Primrec (fun x : Data × Nat × List Nat => x.1) := Primrec.fst
  have hr : Primrec (fun x : Data × Nat × List Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hk : Primrec (fun x : Data × Nat × List Nat => x.2.2) := Primrec.snd.comp Primrec.snd
  have mem : PrimrecRel (fun (xs : List Nat) i => i ∈ xs) := Primrec.eq.exists_mem_list.of_eq (by simp)
  have himp {X : Type} [Primcodable X] {p q : X → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
      PrimrecPred (fun x => p x → q x) := (hp.not.or hq).of_eq (fun _ => by tauto)
  apply PrimrecPred.and
  · exact FiniteSearch.forall_mem hk (Primrec.nat_lt.comp Primrec.snd ((Primrec.fst.comp hd).comp Primrec.fst)).primrecRel
  apply PrimrecPred.and
  · apply FiniteSearch.forall_lt (Primrec.list_length.comp hk)
    apply FiniteSearch.forall_lt (Primrec.list_length.comp (hk.comp Primrec.fst))
    exact himp (Primrec.eq.comp
      ((Primrec.list_getD 0).comp (hk.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (hk.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd))
      (Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  · apply FiniteSearch.forall_lt (Primrec.fst.comp hd)
    have hp := Primrec.eq.comp (mask_primrec.comp ((hd.comp Primrec.fst).pair
      ((hr.comp Primrec.fst).pair Primrec.snd))) (Primrec.const true)
    have hq := mem.comp (hk.comp Primrec.fst) Primrec.snd
    exact ((himp hp hq).and (himp hq hp)).of_eq (fun _ => by tauto)

end Characterisation.EncodedClosingComponents
