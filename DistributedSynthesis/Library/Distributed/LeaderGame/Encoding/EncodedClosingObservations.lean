/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Data.Fintype.Prod

/-! Finite observation comparison along physical closing words. Graph codes
use the characterisation instance convention: right = 0, both = 1, left = 2.
Receiving along a one-way graph and along the both-way graph is deliberately
indistinguishable when the received views and inputs agree. -/
namespace Characterisation.EncodedClosingObservations
open DistributedSynthesis

abbrev Round := Nat × Nat × Nat
abbrev Views := Bool × Bool

def reception (x : Bool × Bool × Nat × Nat × Nat) : Bool :=
  if x.2.2.1 = x.2.2.2.2 ∧ x.2.2.2.1 = x.2.2.2.2 then x.1
  else if x.2.2.1 ≠ x.2.2.2.2 ∧ x.2.2.2.1 ≠ x.2.2.2.2 then x.1 && x.2.1
  else false

def advance (same : Views) (rounds : Round × Round) : Views :=
  let one := same.1 && decide (rounds.1.1 = rounds.2.1)
  let two := same.2 && decide (rounds.1.2.1 = rounds.2.2.1)
  (reception (one,two,rounds.1.2.2,rounds.2.2.2,0),
   reception (two,one,rounds.1.2.2,rounds.2.2.2,2))

def compare (same : Views) (rounds : List (Round × Round)) : Views := rounds.foldl advance same

/-- Pair corresponding positions using their actual list indices. -/
def paired (left right : List Round) : List (Round × Round) :=
  (List.range (min left.length right.length)).map
    (fun n => (left.getD n (0,0,0),right.getD n (0,0,0)))

def compareWords (same : Views) (left right : List Round) : Views := compare same (paired left right)

theorem reception_primrec : Primrec reception := by
  have ha : Primrec (fun x : Bool × Bool × Nat × Nat × Nat => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun x : Bool × Bool × Nat × Nat × Nat => x.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hn : Primrec (fun x : Bool × Bool × Nat × Nat × Nat => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite ((Primrec.eq.comp ha hn).and (Primrec.eq.comp hb hn)) Primrec.fst
    (Primrec.ite ((Primrec.eq.comp ha hn).not.and (Primrec.eq.comp hb hn).not)
      ((Primrec.dom_finite (fun p : Bool × Bool => p.1 && p.2)).comp
        (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))) (Primrec.const false))

theorem advance_primrec : Primrec₂ advance := by
  have hand := Primrec.dom_finite (fun p : Bool × Bool => p.1 && p.2)
  have ho : Primrec (fun x : Views × Round × Round => x.1.1 && decide (x.2.1.1 = x.2.2.1)) :=
    hand.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.eq.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).decide))
  have ht : Primrec (fun x : Views × Round × Round => x.1.2 && decide (x.2.1.2.1 = x.2.2.2.1)) :=
    hand.comp ((Primrec.snd.comp Primrec.fst).pair
      ((Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).decide))
  have hg : Primrec (fun x : Views × Round × Round => x.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hz : Primrec (fun x : Views × Round × Round => x.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (reception_primrec.comp (ho.pair (ht.pair (hg.pair (hz.pair (Primrec.const 0)))))).pair
    (reception_primrec.comp (ht.pair (ho.pair (hg.pair (hz.pair (Primrec.const 2))))))

theorem compare_primrec : Primrec₂ compare :=
  Primrec.list_foldl Primrec.snd Primrec.fst (advance_primrec.comp
    (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

theorem paired_primrec : Primrec₂ paired :=
  Primrec.list_map (Primrec.list_range.comp
    (Primrec.nat_min.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)))
    (((Primrec.list_getD (0,0,0)).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
      ((Primrec.list_getD (0,0,0)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂

theorem compareWords_primrec : Primrec (fun x : Views × List Round × List Round => compareWords x.1 x.2.1 x.2.2) :=
  compare_primrec.comp Primrec.fst (paired_primrec.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))

end Characterisation.EncodedClosingObservations
