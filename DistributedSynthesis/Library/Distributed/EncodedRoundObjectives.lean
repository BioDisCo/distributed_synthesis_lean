/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedNoDirectParity

/-! # Numeric objectives over the original round-record alphabets
The instance supplies alphabet sizes only; the parity tables are independent
data. Thus this interface can also carry a reversal-forgiving companion.
-/
namespace DistributedSynthesis.EncodedRoundObjectives
open EncodedNoDirect
set_option synthInstance.maxSize 2048
abbrev Data := Instance × EncodedParityTables.Data
abbrev Letter (d : Data) := EncodedNoDirect.Letter d.1

def stateCount (d : Data) : Nat := EncodedParityTables.size d.2
def objectivePriority (d : Data) (q : Nat) : Nat :=
  EncodedParityTables.priority d.2 q
def objectiveStep (d : Data) (q : Nat) (a : LetterCode) : Nat :=
  EncodedParityTables.next d.2 q ((letters d.1).idxOf a)

theorem stateCount_primrec : Primrec stateCount :=
  EncodedParityTables.size_primrec.comp Primrec.snd
theorem objectivePriority_primrec : Primrec₂ objectivePriority :=
  EncodedParityTables.priority_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd

-- List.idxOf's executable BEq and its decidable-equality version agree.
private theorem index_primrec : Primrec₂ (fun (d : Data) (a : LetterCode) => (letters d.1).idxOf a) := by
  have h := Primrec.list_idxOf.comp (Primrec.snd : Primrec (fun x : Data × LetterCode => x.2))
    (letters_primrec.comp (Primrec.fst.comp Primrec.fst))
  exact h.of_eq (fun y => by
    unfold List.idxOf
    congr 1
    funext x
    apply Bool.eq_iff_iff.mpr
    simp)

theorem objectiveStep_comp {X : Type*} [Primcodable X]
    {d : X → Data} {q : X → Nat} {a : X → LetterCode}
    (hd : Primrec d) (hq : Primrec q) (ha : Primrec a) :
    Primrec (fun x => objectiveStep (d x) (q x) (a x)) := by
  have hi : Primrec (fun x => (letters (d x).1).idxOf (a x)) := index_primrec.comp hd ha
  have ht := Primrec.snd.comp hd
  exact Primrec.nat_mod.comp ((Primrec.list_getD 0).comp
    ((Primrec.list_getD []).comp (EncodedParityTables.rows_primrec.comp ht) hi) hq)
    (EncodedParityTables.size_primrec.comp ht)

theorem objectiveStep_primrec : Primrec (fun x : Data × Nat × LetterCode => objectiveStep x.1 x.2.1 x.2.2) :=
  objectiveStep_comp Primrec.fst (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)

def inputOne (d : Data) := d.1.inputOneSizeMinusOne + 1
def inputTwo (d : Data) := d.1.inputTwoSizeMinusOne + 1
def outputOne (d : Data) := d.1.outputOneSizeMinusOne + 1
def outputTwo (d : Data) := d.1.outputTwoSizeMinusOne + 1
theorem inputOne_primrec : Primrec inputOne := by
  have hf : Primrec (fun x : InstanceFields => x.1 + 1) := Primrec.succ.comp Primrec.fst
  have h : Primrec (fun d : Instance => d.inputOneSizeMinusOne + 1) := (Primrec.comp (α:=Instance) (β:=InstanceFields) (σ:=Nat)
    (f:=fun x => x.1+1) (g:=instanceEquiv) hf instanceEquiv_primrec).of_eq (fun _ => rfl)
  exact h.comp Primrec.fst

theorem inputTwo_primrec : Primrec inputTwo := by
  have hf : Primrec (fun x : InstanceFields => x.2.1 + 1) := Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have h : Primrec (fun d : Instance => d.inputTwoSizeMinusOne + 1) := (Primrec.comp (α:=Instance) (β:=InstanceFields) (σ:=Nat)
    (f:=fun x => x.2.1+1) (g:=instanceEquiv) hf instanceEquiv_primrec).of_eq (fun _ => rfl)
  exact h.comp Primrec.fst

theorem outputOne_primrec : Primrec outputOne := by
  have hf : Primrec (fun x : InstanceFields => x.2.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have h : Primrec (fun d : Instance => d.outputOneSizeMinusOne + 1) := (Primrec.comp (α:=Instance) (β:=InstanceFields) (σ:=Nat)
    (f:=fun x => x.2.2.1+1) (g:=instanceEquiv) hf instanceEquiv_primrec).of_eq (fun _ => rfl)
  exact h.comp Primrec.fst

theorem outputTwo_primrec : Primrec outputTwo := by
  have hf : Primrec (fun x : InstanceFields => x.2.2.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h : Primrec (fun d : Instance => d.outputTwoSizeMinusOne + 1) := (Primrec.comp (α:=Instance) (β:=InstanceFields) (σ:=Nat)
    (f:=fun x => x.2.2.2.1+1) (g:=instanceEquiv) hf instanceEquiv_primrec).of_eq (fun _ => rfl)
  exact h.comp Primrec.fst

def automaton (d : Data) : DetParityAutomaton (Letter d) where
  State := Fin (stateCount d)
  stateFinite := inferInstance
  initial := ⟨EncodedParityTables.initial d.2 % stateCount d, Nat.mod_lt _ (Nat.succ_pos _)⟩
  step q a := ⟨objectiveStep d q.val (letterCode a), Nat.mod_lt _ (Nat.succ_pos _)⟩
  priority q := objectivePriority d q.val

def fromInstance (d : Instance) : Data := (d, EncodedNoDirectParity.compile d)
theorem fromInstance_primrec : Primrec fromInstance :=
  Primrec.id.pair EncodedNoDirectParity.compile_primrec
theorem automaton_fromInstance (d : Instance) :
    automaton (fromInstance d) = EncodedNoDirectParity.automaton d := by
  unfold automaton fromInstance EncodedNoDirectParity.automaton EncodedLTLParity.automaton
  dsimp only [EncodedParityTables.automaton, DetParityAutomaton.comap,
    stateCount, objectiveStep, objectivePriority, EncodedNoDirectParity.compile,
    EncodedNoDirectParity.letterIndex, Fin.cast]

end DistributedSynthesis.EncodedRoundObjectives
