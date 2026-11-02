/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedMullerCorrect

/-! Compile a Boolean condition on finitely many parity tests on a common
finite transition system. Both the priority tables and the accepted Boolean
profiles are numeric input, so this covers conjunction and implication
without an acceptance oracle. -/
namespace Characterisation.EncodedParityFamilies
open DistributedSynthesis

abbrev Data := EncodedParityTables.Data × List (List Nat) × List (List Bool)
def base (d : Data) := d.1
def priorities (d : Data) := d.2.1
def profiles (d : Data) := d.2.2

def Passes (ps xs : List Nat) : Prop :=
  ∃ q ∈ xs, ps.getD q 0 % 2 = 0 ∧ ∀ r ∈ xs, ps.getD q 0 ≤ ps.getD r 0
instance (ps xs : List Nat) : Decidable (Passes ps xs) := by unfold Passes; infer_instance

def passes (ps xs : List Nat) := decide (Passes ps xs)
def profile (d : Data) (xs : List Nat) := (priorities d).map (fun ps => passes ps xs)
def family (d : Data) := (FiniteSubsets.codes (EncodedParityTables.size (base d))).filter
  (fun xs => decide (profile d xs ∈ profiles d))
def muller (d : Data) : EncodedMuller.Data :=
  ((base d).1,EncodedParityTables.initial (base d),EncodedParityTables.rows (base d),family d)
def compile (d : Data) := EncodedMuller.compile (muller d)

theorem base_primrec : Primrec base := Primrec.fst
theorem priorities_primrec : Primrec priorities := Primrec.fst.comp Primrec.snd
theorem profiles_primrec : Primrec profiles := Primrec.snd.comp Primrec.snd
theorem passes_pred_primrec : PrimrecRel Passes := by
  apply FiniteSearch.exists_mem Primrec.snd
  apply PrimrecPred.and
  · exact Primrec.eq.comp
      (Primrec.nat_mod.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
        (Primrec.const 2)) (Primrec.const 0)
  · apply FiniteSearch.forall_mem (Primrec.snd.comp Primrec.fst)
    exact (Primrec.nat_le.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.snd.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)).primrecRel

theorem passes_primrec : Primrec₂ passes := passes_pred_primrec.decide
theorem profile_primrec : Primrec₂ profile := Primrec.list_map (priorities_primrec.comp Primrec.fst)
  (passes_primrec.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
theorem profile_allowed_primrec : PrimrecRel (fun d xs => profile d xs ∈ profiles d) := by
  have mem : PrimrecRel (fun xs (ys : List (List Bool)) => xs ∈ ys) :=
    (Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)).swap
  exact mem.comp profile_primrec (profiles_primrec.comp Primrec.fst)
theorem family_primrec : Primrec family :=
  profile_allowed_primrec.swap.listFilter.comp
    (FiniteSubsets.codes_primrec.comp (EncodedParityTables.size_primrec.comp base_primrec)) Primrec.id

theorem muller_primrec : Primrec muller :=
  (Primrec.fst.comp base_primrec).pair ((EncodedParityTables.initial_primrec.comp base_primrec).pair
    ((EncodedParityTables.rows_primrec.comp base_primrec).pair family_primrec))
theorem compile_primrec : Primrec compile := EncodedMuller.compile_primrec.comp muller_primrec

/-- One parity condition on the common finite transition system. -/
def condition (d : Data) (ps : List Nat) : DetParityAutomaton (Fin (EncodedParityTables.rows (base d)).length) where
  State := Fin (EncodedParityTables.size (base d))
  stateFinite := inferInstance
  initial := (EncodedParityTables.automaton (base d)).initial
  step := (EncodedParityTables.automaton (base d)).step
  priority q := ps.getD q.val 0

def automaton (d : Data) := EncodedMuller.automaton (muller d)

theorem passes_encode (d : Data) (ps : List Nat)
    (s : Finset (Fin (EncodedParityTables.size (base d)))) :
    passes ps (FiniteSubsets.encode s) = true ↔
      (s : Set (Fin (EncodedParityTables.size (base d)))) ∈ (condition d ps).toMuller.accepting := by
  have member (q : Nat) : q ∈ FiniteSubsets.encode s ↔ ∃ r ∈ s, r.val = q := by
    simp only [FiniteSubsets.encode,List.mem_filter,List.mem_range,decide_eq_true_eq]
    constructor
    · rintro ⟨hq,hr⟩
      exact ⟨⟨q,hq⟩,hr.choose_spec,rfl⟩
    · rintro ⟨r,hr,rfl⟩
      exact ⟨r.isLt,⟨r.isLt,hr⟩⟩
  change decide (Passes ps (FiniteSubsets.encode s)) = true ↔ _
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨q,hq,even,least⟩
    obtain ⟨r,hr,rfl⟩ := (member q).mp hq
    refine ⟨ps.getD r.val 0,Nat.dvd_of_mod_eq_zero even,⟨r,hr,rfl⟩,?_⟩
    intro t ht
    exact least t.val ((member t.val).mpr ⟨t,ht,rfl⟩)
  · rintro ⟨p,even,⟨r,hr,hp⟩,least⟩
    refine ⟨r.val,(member r.val).mpr ⟨r,hr,rfl⟩,?_,?_⟩
    · change ps.getD r.val 0 = p at hp
      rw [hp]
      exact Nat.mod_eq_zero_of_dvd even
    · intro t ht
      obtain ⟨r',hr',rfl⟩ := (member t).mp ht
      change ps.getD r.val 0 = p at hp
      rw [hp]
      exact least r' hr'

theorem family_encode (d : Data) (s : Finset (Fin (EncodedParityTables.size (base d)))) :
    FiniteSubsets.encode s ∈ family d ↔ profile d (FiniteSubsets.encode s) ∈ profiles d := by
  simp only [family,List.mem_filter,decide_eq_true_eq]
  exact and_iff_right (FiniteSubsets.encode_mem_codes s)

end Characterisation.EncodedParityFamilies
