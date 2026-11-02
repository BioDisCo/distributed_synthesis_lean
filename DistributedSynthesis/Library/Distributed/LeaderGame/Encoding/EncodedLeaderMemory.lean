/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanks

/-! The generated rolling leader-memory check combines whole-bank local
consistency, overlap of promised prefixes, and the current physical outputs.
The two data arguments carry the initial and refined observation matrices. -/
namespace Characterisation.EncodedLeaderMemory
open DistributedSynthesis
open EncodedClosingBanks EncodedClosingPlans

-- Keep composition proofs at the function level rather than reducing the
-- nested numeric decoder in the definition of primitive recursiveness.
attribute [local irreducible] Primrec

abbrev Transition := Bank × Bank × Nat × List (Nat × Nat)
def oldBank (x : Transition) := x.1
def newBank (x : Transition) := x.2.1
def round (x : Transition) := x.2.2.1
def expected (x : Transition) := x.2.2.2

def RootChecked (d : Data) (x : Transition) (h : Nat) : Prop :=
  overlap (((context d).1,(context d).2-1),
    (oldBank x).getD h [],(newBank x).getD h [],round x) = true ∧
    response d (oldBank x) (h,[round x]) = (expected x).getD h (0,0)
instance (d : Data) (x : Transition) (h : Nat) : Decidable (RootChecked d x h) := by
  unfold RootChecked
  infer_instance
def RollingChecked (d : Data) (x : Transition) : Prop := ∀ h < roots d, RootChecked d x h
instance (d : Data) (x : Transition) : Decidable (RollingChecked d x) := by
  unfold RollingChecked
  infer_instance
@[irreducible] def rollingCheck (d : Data) (x : Transition) := decide (RollingChecked d x)
def check (data : Data × Data) (x : Transition) : Bool :=
  coherent data.1 (oldBank x) && coherent data.2 (newBank x) && rollingCheck data.1 x

theorem oldBank_primrec : Primrec oldBank := Primrec.fst
theorem newBank_primrec : Primrec newBank := Primrec.fst.comp Primrec.snd
theorem round_primrec : Primrec round := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem expected_primrec : Primrec expected := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem rootChecked_primrec : PrimrecPred (fun x : Data × Transition × Nat => RootChecked x.1 x.2.1 x.2.2) := by
  unfold RootChecked
  have hd : Primrec (fun x : Data × Transition × Nat => x.1) := Primrec.fst
  have ht : Primrec (fun x : Data × Transition × Nat => x.2.1) := Primrec.fst.comp Primrec.snd
  have hh : Primrec (fun x : Data × Transition × Nat => x.2.2) := Primrec.snd.comp Primrec.snd
  have hc := context_primrec.comp hd
  have ho := (Primrec.list_getD []).comp (oldBank_primrec.comp ht) hh
  have hn := (Primrec.list_getD []).comp (newBank_primrec.comp ht) hh
  have hr := round_primrec.comp ht
  apply PrimrecPred.and
  · exact Primrec.eq.comp (overlap_primrec.comp
      (((Primrec.fst.comp hc).pair (Primrec.nat_sub.comp (Primrec.snd.comp hc) (Primrec.const 1))).pair
        (ho.pair (hn.pair hr)))) (Primrec.const true)
  · exact Primrec.eq.comp
      (response_primrec.comp (hd.pair ((oldBank_primrec.comp ht).pair
        (hh.pair (Primrec.list_cons.comp hr (Primrec.const []))))))
      ((Primrec.list_getD (0,0)).comp (expected_primrec.comp ht) hh)

theorem rollingCheck_primrec : Primrec₂ rollingCheck := by
  unfold rollingCheck
  apply PrimrecPred.decide
  apply FiniteSearch.forall_lt (roots_primrec.comp Primrec.fst)
  exact rootChecked_primrec.comp
    ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))

theorem check_primrec : Primrec₂ check := by
  have ha : Primrec (fun x : (Data × Data) × Transition => coherent x.1.1 (oldBank x.2)) :=
    coherent_primrec.comp (Primrec.fst.comp Primrec.fst) (oldBank_primrec.comp Primrec.snd)
  have hb : Primrec (fun x : (Data × Data) × Transition => coherent x.1.2 (newBank x.2)) :=
    coherent_primrec.comp (Primrec.snd.comp Primrec.fst) (newBank_primrec.comp Primrec.snd)
  have hc : Primrec (fun x : (Data × Data) × Transition => rollingCheck x.1.1 x.2) :=
    rollingCheck_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact (Primrec.dom_finite (fun x : Bool × Bool × Bool => x.1 && x.2.1 && x.2.2)).comp
    (ha.pair (hb.pair hc))

end Characterisation.EncodedLeaderMemory
