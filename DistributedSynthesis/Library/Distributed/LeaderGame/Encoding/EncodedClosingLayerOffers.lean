/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingComponents
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderAlphabet

/-! Generate all complete target numberings at a closing depth. Observation
matrices, annotations, parent slots, and minima are read from the same
selected descendants; incompatible pieces cannot be assembled separately. -/
namespace Characterisation.EncodedClosingLayerOffers
open DistributedSynthesis
attribute [local irreducible] Primrec

abbrev Data := EncodedClosingComponents.Data × Nat × List Bool × List Nat × List Nat × List Nat
def components (d : Data) := d.1
def width (d : Data) := d.2.1
def eligible (d : Data) := d.2.2.1
def labels (d : Data) := d.2.2.2.1
def parents (d : Data) := d.2.2.2.2.1
def minima (d : Data) := d.2.2.2.2.2
def select (xs keep : List Nat) := keep.map (fun i => xs.getD i 0)
def selectedMatrix (d : Data) (keep : List Nat) (receiver : Bool) : List Nat :=
  (List.range (keep.length*keep.length)).map (fun index =>
    let i := keep.getD (index / keep.length) 0
    let j := keep.getD (index % keep.length) 0
    (if receiver then (EncodedClosingComponents.views d.1 i j).2 else
      (EncodedClosingComponents.views d.1 i j).1).toNat)
def candidate (d : Data) (keep : List Nat) : EncodedLeaderAlphabet.Outcome :=
  ((keep.length,selectedMatrix d keep false,selectedMatrix d keep true,select (labels d) keep),
    select (parents d) keep,select (minima d) keep)
def Accepted (d : Data) (keep : List Nat) : Prop :=
  ∃ root < d.1.1, (eligible d).getD root false = true ∧
    EncodedClosingComponents.enumeration d.1 root keep = true
instance (d : Data) (keep : List Nat) : Decidable (Accepted d keep) := by
  unfold Accepted
  infer_instance
def targets (d : Data) (n : Nat) :=
  (FiniteSearch.tables d.1.1 n).filter (fun keep => decide (Accepted d keep))
def offers (d : Data) :=
  ((List.range (width d+1)).flatMap (targets d)).map (candidate d)

/-- Collect every eligible depth of one fixed, locally coherent policy. -/
def collect (input : Bool × List Data) :=
  if input.1 then input.2.flatMap offers else []

theorem components_primrec : Primrec components := Primrec.fst
theorem width_primrec : Primrec width := Primrec.fst.comp Primrec.snd
theorem eligible_primrec : Primrec eligible := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem labels_primrec : Primrec labels := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem parents_primrec : Primrec parents := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem minima_primrec : Primrec minima := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem select_primrec : Primrec₂ select := Primrec.list_map Primrec.snd
  ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

theorem selectedMatrix_primrec : Primrec (fun x : Data × List Nat × Bool => selectedMatrix x.1 x.2.1 x.2.2) := by
  have hk : Primrec (fun x : Data × List Nat × Bool => x.2.1) := Primrec.fst.comp Primrec.snd
  have hn := Primrec.list_length.comp hk
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp hn hn))
  have hv : Primrec (fun x : (Data × List Nat × Bool) × Nat =>
      EncodedClosingComponents.views x.1.1.1
        (x.1.2.1.getD (x.2 / x.1.2.1.length) 0) (x.1.2.1.getD (x.2 % x.1.2.1.length) 0)) :=
    EncodedClosingComponents.views_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (((Primrec.list_getD 0).comp (hk.comp Primrec.fst)
          (Primrec.nat_div.comp Primrec.snd (hn.comp Primrec.fst))).pair
         ((Primrec.list_getD 0).comp (hk.comp Primrec.fst)
          (Primrec.nat_mod.comp Primrec.snd (hn.comp Primrec.fst)))))
  exact (Primrec.dom_finite (fun x : Bool × (Bool × Bool) => (if x.1 then x.2.2 else x.2.1).toNat)).comp
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair hv)

theorem candidate_primrec : Primrec₂ candidate :=
  ((Primrec.list_length.comp Primrec.snd).pair
    ((selectedMatrix_primrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const false)))).pair
      ((selectedMatrix_primrec.comp (Primrec.fst.pair (Primrec.snd.pair (Primrec.const true)))).pair
        (select_primrec.comp (labels_primrec.comp Primrec.fst) Primrec.snd)))).pair
    ((select_primrec.comp (parents_primrec.comp Primrec.fst) Primrec.snd).pair
      (select_primrec.comp (minima_primrec.comp Primrec.fst) Primrec.snd))

theorem accepted_primrec : PrimrecRel Accepted := by
  apply FiniteSearch.exists_lt (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  exact (Primrec.eq.comp ((Primrec.list_getD false).comp
    (eligible_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd) (Primrec.const true)).and
    (Primrec.eq.comp (EncodedClosingComponents.enumeration_primrec.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))) (Primrec.const true))

theorem targets_primrec : Primrec₂ targets := accepted_primrec.swap.listFilter.comp
  (FiniteSearch.tables_primrec.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  Primrec.fst
theorem offers_primrec : Primrec offers := Primrec.list_map
  (Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp width_primrec)) targets_primrec) candidate_primrec
theorem collect_primrec : Primrec collect := Primrec.ite
  (Primrec.eq.comp Primrec.fst (Primrec.const true))
  (Primrec.list_flatMap Primrec.snd (offers_primrec.comp Primrec.snd).to₂) (Primrec.const [])

end Characterisation.EncodedClosingLayerOffers
