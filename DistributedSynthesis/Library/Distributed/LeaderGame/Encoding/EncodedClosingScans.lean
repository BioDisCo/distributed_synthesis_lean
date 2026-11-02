/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayers

/-! Enumerate and check all bounded graph scans. Graph rules are fixed finite
tables; the source family, input alphabet, and horizon are numeric parameters.
Both live and boundary flags are computed from the same checked scan. -/
namespace Characterisation.EncodedClosingScans
open DistributedSynthesis
open EncodedClosingLayers (Context Slot)
attribute [local irreducible] Primrec

/-- Graph-state count, allowed steps, boundary flags, and live-state flags. -/
abbrev Rules := Nat × List Bool × List Bool × List Bool
abbrev Data := Context × Rules × List Nat × List Nat
def context (d : Data) := d.1
def rules (d : Data) := d.2.1
def graphs (d : Data) := d.2.2.1
def source (d : Data) := d.2.2.2
def raw (c : Context) := (List.range (c.2.2+1)).flatMap (fun n => EncodedClosingLayers.slots (c.1,c.2.1,n))
@[irreducible] def domain (c : Context) := FiniteCodeNumbering.unique (raw c)
def name (c : Context) (s : Slot) := FiniteCodeNumbering.name (raw c) s
def entry (c : Context) (table : List Nat) (s : Slot) := table.getD (name c s) 0
def parent (s : Slot) : Slot := (s.1,s.2.take (s.2.length-1))
def lastGraph (d : Data) (s : Slot) := (graphs d).getD (s.2.getD (s.2.length-1) 0) 0
def allowed (r : Rules) (q g next : Nat) := r.2.1.getD ((q*3+g)*r.1+next) false
def boundaryRule (r : Rules) (q g : Nat) := r.2.2.1.getD (q*3+g) false
def liveRule (r : Rules) (q : Nat) := r.2.2.2.getD q false
def StepChecked (d : Data) (table : List Nat) (s : Slot) : Prop :=
  0 < s.2.length → allowed (rules d) (entry d.1 table (parent s)) (lastGraph d s) (entry d.1 table s) = true
instance (d : Data) (table : List Nat) (s : Slot) : Decidable (StepChecked d table s) := by
  unfold StepChecked
  infer_instance
def Checked (d : Data) (table : List Nat) : Prop :=
  (∀ h < d.1.1, entry d.1 table (h,[]) = (source d).getD h 0) ∧
  (∀ s ∈ domain d.1, StepChecked d table s)
instance (d : Data) (table : List Nat) : Decidable (Checked d table) := by
  unfold Checked
  infer_instance
@[irreducible] def check (d : Data) (table : List Nat) := decide (Checked d table)
def candidates (d : Data) := FiniteSearch.tables (rules d).1 (domain d.1).length
def scans (d : Data) := (candidates d).filter (fun table => check d table)
def live (d : Data) (table : List Nat) (s : Slot) := liveRule (rules d) (entry d.1 table s)
def boundary (d : Data) (table : List Nat) (s : Slot) :=
  if s.2 = [] then false else boundaryRule (rules d) (entry d.1 table (parent s)) (lastGraph d s)

theorem context_primrec : Primrec context := Primrec.fst
theorem rules_primrec : Primrec rules := Primrec.fst.comp Primrec.snd
theorem graphs_primrec : Primrec graphs := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem source_primrec : Primrec source := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
theorem raw_primrec : Primrec raw := Primrec.list_flatMap
  (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.id))))
  (EncodedClosingLayers.slots_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))).to₂
theorem domain_primrec : Primrec domain := by
  unfold domain
  exact FiniteCodeNumbering.unique_primrec.comp raw_primrec
theorem name_primrec : Primrec₂ name := FiniteCodeNumbering.name_primrec.comp (raw_primrec.comp Primrec.fst) Primrec.snd
theorem entry_primrec : Primrec (fun x : Context × List Nat × Slot => entry x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd)
    (name_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
theorem parent_primrec : Primrec parent := Primrec.fst.pair
  (Primrec.list_take.comp (Primrec.nat_sub.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 1)) Primrec.snd)
theorem lastGraph_primrec : Primrec₂ lastGraph := (Primrec.list_getD 0).comp (graphs_primrec.comp Primrec.fst)
  ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.snd)
    (Primrec.nat_sub.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)))
theorem allowed_primrec : Primrec (fun x : Rules × Nat × Nat × Nat => allowed x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 3))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))) (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem boundaryRule_primrec : Primrec (fun x : Rules × Nat × Nat => boundaryRule x.1 x.2.1 x.2.2) :=
  (Primrec.list_getD false).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 3))
      (Primrec.snd.comp Primrec.snd))
theorem liveRule_primrec : Primrec₂ liveRule := (Primrec.list_getD false).comp
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd

theorem stepChecked_primrec : PrimrecPred (fun x : Data × List Nat × Slot => StepChecked x.1 x.2.1 x.2.2) := by
  have hd : Primrec (fun x : Data × List Nat × Slot => x.1) := Primrec.fst
  have ht : Primrec (fun x : Data × List Nat × Slot => x.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun x : Data × List Nat × Slot => x.2.2) := Primrec.snd.comp Primrec.snd
  have h := Primrec.eq.comp (allowed_primrec.comp ((rules_primrec.comp hd).pair
    ((entry_primrec.comp ((Primrec.fst.comp hd).pair (ht.pair (parent_primrec.comp hs)))).pair
      ((lastGraph_primrec.comp hd hs).pair (entry_primrec.comp ((Primrec.fst.comp hd).pair (ht.pair hs)))))))
    (Primrec.const true)
  exact ((Primrec.nat_lt.comp (Primrec.const 0) (Primrec.list_length.comp (Primrec.snd.comp hs))).not.or h).of_eq
    (fun _ => by tauto)

theorem check_primrec : Primrec₂ check := by
  unfold check Checked
  apply PrimrecPred.decide
  apply PrimrecPred.and
  · apply FiniteSearch.forall_lt (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
    exact Primrec.eq.comp
      (entry_primrec.comp ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.pair (Primrec.const [])))))
      ((Primrec.list_getD 0).comp (source_primrec.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
  · apply FiniteSearch.forall_mem (domain_primrec.comp (Primrec.fst.comp Primrec.fst))
    exact stepChecked_primrec.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
theorem candidates_primrec : Primrec candidates := FiniteSearch.tables_primrec.comp
  (Primrec.fst.comp rules_primrec) (Primrec.list_length.comp (domain_primrec.comp Primrec.fst))
theorem scans_primrec : Primrec scans := by
  have h : PrimrecRel (fun d table => check d table = true) := Primrec.eq.comp check_primrec (Primrec.const true)
  exact (h.swap.listFilter.comp candidates_primrec Primrec.id).of_eq (fun d => by simp [scans,Function.swap])
theorem live_primrec : Primrec (fun x : Data × List Nat × Slot => live x.1 x.2.1 x.2.2) :=
  liveRule_primrec.comp (rules_primrec.comp Primrec.fst)
    (entry_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd))
theorem boundary_primrec : Primrec (fun x : Data × List Nat × Slot => boundary x.1 x.2.1 x.2.2) :=
  Primrec.ite (Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const []))
    (Primrec.const false)
    (boundaryRule_primrec.comp ((rules_primrec.comp Primrec.fst).pair
      ((entry_primrec.comp ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (parent_primrec.comp (Primrec.snd.comp Primrec.snd))))).pair
        (lastGraph_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)))))

end Characterisation.EncodedClosingScans
