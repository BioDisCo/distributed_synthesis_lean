/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.FiniteOrbitParity
import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Computability.RE
import Mathlib.Data.List.GetD

/-! # Primitive-recursive parity checking for numeric transition tables

Data are `(maximumState, successors, priorities, initialState)`. The state set
is `Fin (maximumState + 1)`. Missing table entries are zero; successor and
initial indices are reduced modulo the state count. Thus every input has a
specified finite-state semantics. Valid tables are unchanged by normalization.
-/

namespace DistributedSynthesis.EncodedOrbitParity

abbrev Data := Nat × List Nat × List Nat × Nat

def bound (d : Data) : Nat := d.1 + 1
def next (d : Data) (q : Nat) : Nat := d.2.1.getD q 0 % bound d
def priority (d : Data) (q : Nat) : Nat := d.2.2.1.getD q 0
def initial (d : Data) : Nat := d.2.2.2 % bound d
def orbit (d : Data) (q n : Nat) : Nat := (next d)^[n] q

def Recurrent (d : Data) (q : Nat) : Prop :=
  (∃ i < bound d, orbit d (initial d) i = q) ∧
  (∃ j < bound d, orbit d q (j + 1) = q)

def Passes (d : Data) : Prop :=
  ∃ q < bound d, Recurrent d q ∧ priority d q % 2 = 0 ∧
    ∀ r < bound d, Recurrent d r → priority d q ≤ priority d r

instance recurrentDecidable (d : Data) (q : Nat) : Decidable (Recurrent d q) := by
  unfold Recurrent
  infer_instance

instance passesDecidable (d : Data) : Decidable (Passes d) := by
  unfold Passes
  infer_instance

def solve (d : Data) : Bool := decide (Passes d)

theorem bound_primrec : Primrec bound := Primrec.succ.comp Primrec.fst

theorem next_primrec : Primrec₂ next :=
  Primrec.nat_mod.comp
    ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
    (bound_primrec.comp Primrec.fst)

theorem priority_primrec : Primrec₂ priority :=
  (Primrec.list_getD 0).comp
    (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd

theorem initial_primrec : Primrec initial :=
  Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) bound_primrec

theorem orbit_primrec : Primrec (fun x : Data × Nat × Nat => orbit x.1 x.2.1 x.2.2) :=
  Primrec.nat_iterate (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
    ((next_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂)

theorem recurrent_primrec : PrimrecRel Recurrent := by
  apply PrimrecPred.and
  · apply FiniteSearch.exists_lt (bound_primrec.comp Primrec.fst)
    exact (Primrec.eq.comp
      (orbit_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        (((initial_primrec.comp (Primrec.fst.comp Primrec.fst))).pair Primrec.snd)))
      (Primrec.snd.comp Primrec.fst)).primrecRel
  · apply FiniteSearch.exists_lt (bound_primrec.comp Primrec.fst)
    exact (Primrec.eq.comp
      (orbit_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.succ.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.fst)).primrecRel

theorem passes_primrec : PrimrecPred Passes := by
  apply FiniteSearch.exists_lt bound_primrec
  apply PrimrecPred.and recurrent_primrec
  apply PrimrecPred.and
  · exact Primrec.eq.comp
      (Primrec.nat_mod.comp priority_primrec (Primrec.const 2)) (Primrec.const 0)
  · apply FiniteSearch.forall_lt (bound_primrec.comp Primrec.fst)
    exact ((recurrent_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).not.or
      (Primrec.nat_le.comp (priority_primrec.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.snd.comp Primrec.fst))
        (priority_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd))).of_eq
          (fun _ => imp_iff_not_or.symm)

theorem solve_primrec : Primrec solve := passes_primrec.decide

abbrev State (d : Data) := Fin (bound d)

def stateNext (d : Data) (q : State d) : State d :=
  ⟨next d q.val, Nat.mod_lt _ (Nat.succ_pos _)⟩

def stateInitial (d : Data) : State d :=
  ⟨initial d, Nat.mod_lt _ (Nat.succ_pos _)⟩

def Accepts (d : Data) : Prop :=
  NatSeqMinEvenParity (fun n => priority d (((stateNext d)^[n]) (stateInitial d)).val)

theorem orbit_val (d : Data) (q : State d) (n : Nat) :
    (((stateNext d)^[n]) q).val = orbit d q.val n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply', stateNext, orbit] at ih ⊢
    rw [ih]

theorem recurrent_iff (d : Data) (q : State d) :
    Recurrent d q.val ↔ FiniteOrbitParity.Recurring (stateNext d) (stateInitial d) q := by
  rw [FiniteOrbitParity.recurring_iff]
  simp only [Fintype.card_fin, Fin.ext_iff, orbit_val]
  simp only [Recurrent, stateInitial, State, Fintype.card_fin, Fin.exists_iff, exists_prop]

theorem passes_iff (d : Data) : Passes d ↔ Accepts d := by
  unfold Accepts
  rw [FiniteOrbitParity.parity_iff (stateNext d) (stateInitial d) (fun q => priority d q.val)]
  constructor
  · rintro ⟨q, hq, hr, hp, hmin⟩
    exact ⟨⟨q, hq⟩, (recurrent_iff d _).mp hr, hp,
      fun r h => hmin r.val r.isLt ((recurrent_iff d r).mpr h)⟩
  · rintro ⟨q, hr, hp, hmin⟩
    exact ⟨q.val, q.isLt, (recurrent_iff d q).mpr hr, hp,
      fun r hbound h => hmin ⟨r, hbound⟩ ((recurrent_iff d _).mp h)⟩

theorem solve_correct (d : Data) : solve d = true ↔ Accepts d :=
  decide_eq_true_iff.trans (passes_iff d)

theorem accepts_computable : ComputablePred Accepts :=
  passes_primrec.computablePred.of_eq passes_iff

/-- Serialize any map on an explicitly numbered nonempty finite state set. -/
def ofFin {n : Nat} (f : Fin (n + 1) → Fin (n + 1))
    (p : Fin (n + 1) → Nat) (x : Fin (n + 1)) : Data :=
  (n, List.ofFn (fun q => (f q).val), List.ofFn p, x.val)

private theorem lookup_ofFn {n : Nat} (f : Fin n → Nat) (q : Fin n) :
    (List.ofFn f).getD q.val 0 = f q := by
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp

theorem next_ofFin {n : Nat} (f : Fin (n + 1) → Fin (n + 1))
    (p : Fin (n + 1) → Nat) (x q : Fin (n + 1)) :
    stateNext (ofFin f p x) q = f q := by
  apply Fin.ext
  change (List.ofFn (fun q => (f q).val)).getD q.val 0 % (n + 1) = (f q).val
  rw [lookup_ofFn, Nat.mod_eq_of_lt (f q).isLt]

theorem ofFin_correct {n : Nat} (f : Fin (n + 1) → Fin (n + 1))
    (p : Fin (n + 1) → Nat) (x : Fin (n + 1)) :
    solve (ofFin f p x) = true ↔ NatSeqMinEvenParity (fun k => p ((f^[k]) x)) := by
  rw [solve_correct]
  have hs : stateNext (ofFin f p x) = f := funext (next_ofFin f p x)
  have hi : stateInitial (ofFin f p x) = x := by
    apply Fin.ext
    exact Nat.mod_eq_of_lt x.isLt
  change NatSeqMinEvenParity (fun k => priority (ofFin f p x)
    (((stateNext (ofFin f p x))^[k]) (stateInitial (ofFin f p x))).val) ↔ _
  rw [hs, hi]
  simp only [priority, ofFin, lookup_ofFn]
  rfl

section NumberedState

variable {Q : Type*} {n : Nat} (e : Q ≃ Fin (n + 1)) (f : Q → Q) (p : Q → Nat) (x : Q)

/-- The numbering is supplied explicitly; no state enumeration is chosen from a winner. -/
def encode : Data := ofFin (fun q => e (f (e.symm q))) (fun q => p (e.symm q)) (e x)

theorem encode_correct : solve (encode e f p x) = true ↔
    NatSeqMinEvenParity (fun k => p ((f^[k]) x)) := by
  rw [encode, ofFin_correct]
  have h (k : Nat) : ((fun q => e (f (e.symm q)))^[k]) (e x) = e ((f^[k]) x) := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply', ih, Equiv.symm_apply_apply]
  simp only [h, Equiv.symm_apply_apply]

end NumberedState

end DistributedSynthesis.EncodedOrbitParity
