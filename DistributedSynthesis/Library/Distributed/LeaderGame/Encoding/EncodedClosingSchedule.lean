/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingScans

/-! First-exit and window flags computed from the same finite graph scan.
An exit includes its own output and excludes every later output in that scan. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis
open EncodedClosingLayers (Slot)
attribute [local irreducible] Primrec

def takePrefix (s : Slot) (n : Nat) : Slot := (s.1,s.2.take n)
def Active (d : Data) (table : List Nat) (s : Slot) : Prop :=
  ∀ n < s.2.length, 0 < n → boundary d table (takePrefix s n) = false
instance (d : Data) (table : List Nat) (s : Slot) : Decidable (Active d table s) := by
  unfold Active
  infer_instance
@[irreducible] def active (d : Data) (table : List Nat) (s : Slot) := decide (Active d table s)
def firstExit (d : Data) (table : List Nat) (s : Slot) := active d table s && boundary d table s
def scheduled (initial : Bool) (horizon depth : Nat) := initial || decide (depth = horizon)
def eligible (d : Data) (table : List Nat) (initial : Bool) (s : Slot) :=
  scheduled initial d.1.2.2 s.2.length && live d table s && firstExit d table s

theorem takePrefix_primrec : Primrec₂ takePrefix := (Primrec.fst.comp Primrec.fst).pair
  (Primrec.list_take.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
theorem active_primrec : Primrec (fun x : Data × List Nat × Slot => active x.1 x.2.1 x.2.2) := by
  unfold active Active
  apply PrimrecPred.decide
  apply FiniteSearch.forall_lt (Primrec.list_length.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hp : PrimrecPred (fun x : (Data × List Nat × Slot) × Nat => 0 < x.2) :=
    Primrec.nat_lt.comp (Primrec.const 0) Primrec.snd
  have hb : PrimrecPred (fun x : (Data × List Nat × Slot) × Nat =>
      boundary x.1.1 x.1.2.1 (takePrefix x.1.2.2 x.2) = false) :=
    Primrec.eq.comp (boundary_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        (takePrefix_primrec.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd))))
      (Primrec.const false)
  exact (hp.not.or hb).of_eq (fun _ => by tauto)
theorem firstExit_primrec : Primrec (fun x : Data × List Nat × Slot => firstExit x.1 x.2.1 x.2.2) :=
  (Primrec.dom_bool₂ Bool.and).comp active_primrec boundary_primrec
theorem scheduled_primrec : Primrec (fun x : Bool × Nat × Nat => scheduled x.1 x.2.1 x.2.2) :=
  (Primrec.dom_bool₂ Bool.or).comp Primrec.fst
    ((Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).decide)
theorem eligible_primrec : Primrec (fun x : Data × List Nat × Bool × Slot => eligible x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hd : Primrec (fun x : Data × List Nat × Bool × Slot => x.1) := Primrec.fst
  have ht : Primrec (fun x : Data × List Nat × Bool × Slot => x.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun x : Data × List Nat × Bool × Slot => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hs : Primrec (fun x : Data × List Nat × Bool × Slot => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.dom_bool₂ Bool.and).comp
    ((Primrec.dom_bool₂ Bool.and).comp (scheduled_primrec.comp (hi.pair
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp hd))).pair
        (Primrec.list_length.comp (Primrec.snd.comp hs))))) (live_primrec.comp (hd.pair (ht.pair hs))))
    (firstExit_primrec.comp (hd.pair (ht.pair hs)))

theorem active_short (d : Data) (table : List Nat) (s : Slot) (short : s.2.length ≤ 1) :
    active d table s = true := by
  rw [active,decide_eq_true_eq]
  intro n hn positive
  omega

theorem active_parent (d : Data) (table : List Nat) (s : Slot) (long : 2 ≤ s.2.length) :
    active d table s = (active d table (parent s) && !boundary d table (parent s)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [active,decide_eq_true_eq,Bool.and_eq_true,Bool.not_eq_true',Active]
  have length : (parent s).2.length = s.2.length-1 := by simp [parent]
  have before (n : Nat) (hn : n ≤ s.2.length-1) : takePrefix (parent s) n = takePrefix s n := by
    simp [takePrefix,parent,List.take_take,Nat.min_eq_left hn]
  constructor
  · intro all
    refine ⟨?_,all (s.2.length-1) (by omega) (by omega)⟩
    intro n hn positive
    rw [length] at hn
    rw [before n (by omega)]
    exact all n (by omega) positive
  · rintro ⟨all,last⟩ n hn positive
    by_cases early : n < s.2.length-1
    · have value := all n (by simpa only [length] using early) positive
      rwa [before n (by omega)] at value
    · have equal : n = s.2.length-1 := by omega
      subst n
      exact last

end Characterisation.EncodedClosingScans
