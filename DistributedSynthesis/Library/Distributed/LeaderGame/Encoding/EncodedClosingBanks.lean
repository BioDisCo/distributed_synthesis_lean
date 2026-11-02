/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingPlans
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingObservations

/-! Numeric local-consistency checks for a complete bank of leader tables.
The finite data specify numbered roots, round and output decoding tables,
and the two observation matrices. Every pair at the same physical depth is
checked, including pairs belonging to different hidden roots. -/
namespace Characterisation.EncodedClosingBanks
open DistributedSynthesis
open EncodedClosingPlans EncodedClosingObservations

abbrev Bank := List Plan
abbrev Slot := Nat × List Nat
abbrev Data := Nat × Context × List Round × List (Nat × Nat) × List Views
def roots (d : Data) := d.1
def context (d : Data) := d.2.1
def roundTable (d : Data) := d.2.2.1
def outputTable (d : Data) := d.2.2.2.1
def matrix (d : Data) := d.2.2.2.2
def slots (d : Data) := (List.range (roots d)).product (scenarios (context d))
def banks (d : Data) (outputs : Nat) := FiniteSearch.words (plans (context d) outputs) (roots d)
def word (d : Data) (xs : List Nat) := xs.map (fun i => (roundTable d).getD i (0,0,0))
@[irreducible] def observed (d : Data) (left right : Slot) :=
  compareWords ((matrix d).getD (right.1+roots d*left.1) (false,false))
    (word d left.2) (word d right.2)
@[irreducible] def response (d : Data) (bank : Bank) (s : Slot) :=
  (outputTable d).getD (entry (context d) (bank.getD s.1 []) s.2) (0,0)
def PairCoherent (d : Data) (bank : Bank) (left right : Slot) : Prop :=
  left.2.length = right.2.length →
    ((observed d left right).1 = true → (response d bank left).1 = (response d bank right).1) ∧
    ((observed d left right).2 = true → (response d bank left).2 = (response d bank right).2)
instance (d : Data) (bank : Bank) (left right : Slot) : Decidable (PairCoherent d bank left right) := by
  unfold PairCoherent
  infer_instance
def Coherent (d : Data) (bank : Bank) : Prop :=
  ∀ left ∈ slots d, ∀ right ∈ slots d, PairCoherent d bank left right
instance (d : Data) (bank : Bank) : Decidable (Coherent d bank) := by
  unfold Coherent
  infer_instance
@[irreducible] def coherent (d : Data) (bank : Bank) := decide (Coherent d bank)

theorem roots_primrec : Primrec roots := Primrec.fst
theorem context_primrec : Primrec context := Primrec.fst.comp Primrec.snd
theorem roundTable_primrec : Primrec roundTable := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem outputTable_primrec : Primrec outputTable := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem matrix_primrec : Primrec matrix := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem slots_primrec : Primrec slots := FiniteSearch.product_primrec.comp
  (Primrec.list_range.comp roots_primrec) (scenarios_primrec.comp context_primrec)
theorem banks_primrec : Primrec₂ banks := FiniteSearch.words_primrec.comp
  (plans_primrec.comp (context_primrec.comp Primrec.fst) Primrec.snd) (roots_primrec.comp Primrec.fst)
theorem word_primrec : Primrec₂ word := Primrec.list_map Primrec.snd
  ((Primrec.list_getD (0,0,0)).comp (roundTable_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd).to₂

set_option maxHeartbeats 800000 in
theorem observed_primrec : Primrec (fun x : Data × Slot × Slot => observed x.1 x.2.1 x.2.2) := by
  unfold observed
  have hd : Primrec (fun x : Data × Slot × Slot => x.1) := Primrec.fst
  have hl : Primrec (fun x : Data × Slot × Slot => x.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun x : Data × Slot × Slot => x.2.2) := Primrec.snd.comp Primrec.snd
  exact compareWords_primrec.comp
    (((Primrec.list_getD (false,false)).comp (matrix_primrec.comp hd)
      (Primrec.nat_add.comp (Primrec.fst.comp hr)
        (Primrec.nat_mul.comp (roots_primrec.comp hd) (Primrec.fst.comp hl)))).pair
      ((word_primrec.comp hd (Primrec.snd.comp hl)).pair
        (word_primrec.comp hd (Primrec.snd.comp hr))))

set_option maxHeartbeats 800000 in
theorem response_primrec : Primrec (fun x : Data × Bank × Slot => response x.1 x.2.1 x.2.2) := by
  unfold response
  exact (Primrec.list_getD (0,0)).comp (outputTable_primrec.comp Primrec.fst)
    (entry_primrec.comp ((context_primrec.comp Primrec.fst).pair
      (((Primrec.list_getD []).comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem pairCoherent_primrec : PrimrecPred (fun x : Data × Bank × Slot × Slot => PairCoherent x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have himp {X : Type} [Primcodable X] {p q : X → Prop} (hp : PrimrecPred p) (hq : PrimrecPred q) :
      PrimrecPred (fun x => p x → q x) := (hp.not.or hq).of_eq (fun _ => by tauto)
  have hd : Primrec (fun x : Data × Bank × Slot × Slot => x.1) := Primrec.fst
  have hb : Primrec (fun x : Data × Bank × Slot × Slot => x.2.1) := Primrec.fst.comp Primrec.snd
  have hl : Primrec (fun x : Data × Bank × Slot × Slot => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun x : Data × Bank × Slot × Slot => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hv := observed_primrec.comp (hd.pair (hl.pair hr))
  have hol := response_primrec.comp (hd.pair (hb.pair hl))
  have hor := response_primrec.comp (hd.pair (hb.pair hr))
  exact himp (Primrec.eq.comp (Primrec.list_length.comp (Primrec.snd.comp hl))
    (Primrec.list_length.comp (Primrec.snd.comp hr)))
    ((himp (Primrec.eq.comp (Primrec.fst.comp hv) (Primrec.const true))
      (Primrec.eq.comp (Primrec.fst.comp hol) (Primrec.fst.comp hor))).and
     (himp (Primrec.eq.comp (Primrec.snd.comp hv) (Primrec.const true))
      (Primrec.eq.comp (Primrec.snd.comp hol) (Primrec.snd.comp hor))))

theorem coherent_primrec : Primrec₂ coherent := by
  unfold coherent
  apply PrimrecPred.decide
  apply FiniteSearch.forall_mem (slots_primrec.comp Primrec.fst)
  apply FiniteSearch.forall_mem (slots_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact pairCoherent_primrec.comp
    ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))

end Characterisation.EncodedClosingBanks
