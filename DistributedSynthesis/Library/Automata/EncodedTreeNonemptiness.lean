/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedOrbitParity
import DistributedSynthesis.Library.Automata.TreeNonemptiness

/-! # Primitive-recursive nonemptiness for numeric deterministic parity trees

Input fields are maximum state index, label count, branch count, flattened
transition table, priority table, and initial index. The transition-table index
is `(state * labelCount + label) * branchCount + branch`. Missing entries are
zero; successor and initial indices are reduced modulo the positive state count.
Label and branch alphabets may be empty. No strategy or solver is input data.
-/

namespace DistributedSynthesis.EncodedTreeNonemptiness

abbrev Data := Nat × Nat × Nat × List Nat × List Nat × Nat

def bound (d : Data) : Nat := d.1 + 1
def labels (d : Data) : Nat := d.2.1
def branches (d : Data) : Nat := d.2.2.1
def transitions (d : Data) : List Nat := d.2.2.2.1
def priorities (d : Data) : List Nat := d.2.2.2.2.1
def initial (d : Data) : Nat := d.2.2.2.2.2

def rawNext (d : Data) (q l b : Nat) : Nat :=
  (transitions d).getD ((q * labels d + l) * branches d + b) 0

def orbitData (d : Data) (ls bs : List Nat) : EncodedOrbitParity.Data :=
  (d.1, (List.range (bound d)).map (fun q => rawNext d q (ls.getD q 0) (bs.getD q 0)),
    priorities d, initial d)

def Passes (d : Data) : Prop :=
  ∃ ls ∈ FiniteSearch.tables (labels d) (bound d),
    ∀ bs ∈ FiniteSearch.tables (branches d) (bound d),
      EncodedOrbitParity.Passes (orbitData d ls bs)

instance passesDecidable (d : Data) : Decidable (Passes d) := by
  unfold Passes
  infer_instance

def solve (d : Data) : Bool := decide (Passes d)

theorem bound_primrec : Primrec bound := Primrec.succ.comp Primrec.fst
theorem labels_primrec : Primrec labels := Primrec.fst.comp Primrec.snd
theorem branches_primrec : Primrec branches := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
theorem transitions_primrec : Primrec transitions :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
theorem priorities_primrec : Primrec priorities :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
theorem initial_primrec : Primrec initial :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem rawNext_primrec {X : Type*} [Primcodable X] {d : X → Data} {q l b : X → Nat}
    (hd : Primrec d) (hq : Primrec q) (hl : Primrec l) (hb : Primrec b) :
    Primrec (fun x => rawNext (d x) (q x) (l x) (b x)) :=
  (Primrec.list_getD 0).comp (transitions_primrec.comp hd)
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp hq (labels_primrec.comp hd)) hl)
        (branches_primrec.comp hd)) hb)

theorem orbitData_primrec :
    Primrec (fun x : (Data × List Nat) × List Nat => orbitData x.1.1 x.1.2 x.2) := by
  apply Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  apply Primrec.pair
  · apply Primrec.list_map
      (Primrec.list_range.comp (bound_primrec.comp (Primrec.fst.comp Primrec.fst)))
    exact (rawNext_primrec (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)).to₂
  · exact (priorities_primrec.comp (Primrec.fst.comp Primrec.fst)).pair
      (initial_primrec.comp (Primrec.fst.comp Primrec.fst))

private theorem policyTest_primrec : PrimrecPred (fun x : (Data × List Nat) × List Nat =>
    EncodedOrbitParity.Passes (orbitData x.1.1 x.1.2 x.2)) :=
  PrimrecPred.comp EncodedOrbitParity.passes_primrec orbitData_primrec

theorem passes_primrec : PrimrecPred Passes := by
  apply FiniteSearch.exists_mem (FiniteSearch.tables_primrec.comp labels_primrec bound_primrec)
  apply FiniteSearch.forall_mem
    (FiniteSearch.tables_primrec.comp (branches_primrec.comp Primrec.fst)
      (bound_primrec.comp Primrec.fst))
  exact policyTest_primrec

theorem solve_primrec : Primrec solve := passes_primrec.decide

def monitor (d : Data) : DeterministicBlockMonitor (Fin (branches d)) (Fin (labels d)) where
  branchFinite := inferInstance
  alphabetFinite := inferInstance
  State := Fin (bound d)
  stateFinite := inferInstance
  initial := ⟨initial d % bound d, Nat.mod_lt _ (Nat.succ_pos _)⟩
  step := fun q l b => ⟨rawNext d q.val l.val b.val % bound d,
    Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority := fun q => (priorities d).getD q.val 0

def Nonempty (d : Data) : Prop := ∃ tree, (monitor d).toRunAutomaton.acceptsTree tree

private theorem lookup_map_range (n : Nat) (f : Nat → Nat) (q : Fin n) :
    ((List.range n).map f).getD q.val 0 = f q.val := by
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp

private theorem lookup_ofFn {n : Nat} (f : Fin n → Nat) (q : Fin n) :
    (List.ofFn f).getD q.val 0 = f q := by
  rw [List.getD_eq_getElem _ _ (by simpa using q.isLt)]
  simp

theorem orbitData_correct (d : Data)
    (ls : Fin (bound d) → Fin (labels d)) (bs : Fin (bound d) → Fin (branches d)) :
    EncodedOrbitParity.Passes
        (orbitData d (List.ofFn (fun q => (ls q).val)) (List.ofFn (fun q => (bs q).val))) ↔
      NatSeqMinEvenParity (fun n => (monitor d).priority
        ((TreeNonemptiness.policyStep (monitor d) ls bs)^[n] (monitor d).initial)) := by
  rw [EncodedOrbitParity.passes_iff]
  have hs : EncodedOrbitParity.stateNext
      (orbitData d (List.ofFn (fun q => (ls q).val)) (List.ofFn (fun q => (bs q).val))) =
      TreeNonemptiness.policyStep (monitor d) ls bs := by
    funext q
    apply Fin.ext
    change ((List.range (bound d)).map
      (fun q => rawNext d q ((List.ofFn (fun q => (ls q).val)).getD q 0)
        ((List.ofFn (fun q => (bs q).val)).getD q 0))).getD q.val 0 % bound d = _
    rw [lookup_map_range, lookup_ofFn, lookup_ofFn]
    rfl
  change NatSeqMinEvenParity (fun n => (priorities d).getD
    (((EncodedOrbitParity.stateNext
      (orbitData d (List.ofFn (fun q => (ls q).val)) (List.ofFn (fun q => (bs q).val))))^[n])
        (monitor d).initial).val 0) ↔ _
  rw [hs]
  rfl

theorem passes_iff (d : Data) : Passes d ↔ Nonempty d := by
  rw [Nonempty, TreeNonemptiness.nonempty_iff]
  constructor
  · rintro ⟨ls, hls, h⟩
    obtain ⟨lp, rfl⟩ := FiniteSearch.mem_tables_iff_policy ls |>.mp hls
    refine ⟨lp, fun bp => (orbitData_correct d lp bp).mp ?_⟩
    exact h _ (FiniteSearch.ofFn_mem_tables bp)
  · rintro ⟨lp, h⟩
    refine ⟨List.ofFn (fun q => (lp q).val), FiniteSearch.ofFn_mem_tables lp, ?_⟩
    intro bs hbs
    obtain ⟨bp, rfl⟩ := FiniteSearch.mem_tables_iff_policy bs |>.mp hbs
    exact (orbitData_correct d lp bp).mpr (h bp)

theorem solve_correct (d : Data) : solve d = true ↔ Nonempty d :=
  decide_eq_true_iff.trans (passes_iff d)

theorem nonempty_computable : ComputablePred Nonempty :=
  passes_primrec.computablePred.of_eq passes_iff

end DistributedSynthesis.EncodedTreeNonemptiness
