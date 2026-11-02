/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.JournalCompilation
import DistributedSynthesis.Library.Computability.FiniteFunctionCodes

/-! # The sixteen finite response tables of a global journal label

Shapes list the objective-state, two input, and two output cardinalities.
Fields 0--3 and 4--7 are the ordinary left/right tables. Fields 8--11 and
12--15 are the reversed-left/right tables. The domain numbering is explicit;
in particular, reversal fields indexed by two atoms have four state indices.
-/

namespace DistributedSynthesis.EncodedJournalLabels
abbrev Shape := Nat × Nat × Nat × Nat × Nat
abbrev Code := List (List Nat)

/-- Each pair is (domain cardinality, output cardinality). -/
def specs (x : Shape) : List (Nat × Nat) :=
  let q := x.1*x.1
  let qq := q*q
  let r := x.2.1
  let s := x.2.2.1
  let a := x.2.2.2.1
  let b := x.2.2.2.2
  [(s,b), (q*(r*s),a), (q*(r*s),b), (q*r,a),
   (r,a), (q*(s*r),b), (q*(s*r),a), (q*s,b),
   (qq*(r*s),a), (qq*r,a), (q*s,b), (qq*(r*s),b),
   (qq*(r*s),a), (q*r,a), (qq*s,b), (qq*(r*s),b)]

def allCodes (x : Shape) : List Code :=
  ((specs x).map (fun s => FiniteSearch.tables s.2 s.1)).sections

theorem specs_primrec : Primrec specs := by
  have hn : Primrec (fun x : Shape => x.1) := Primrec.fst
  have hr : Primrec (fun x : Shape => x.2.1) := Primrec.fst.comp Primrec.snd
  have hs : Primrec (fun x : Shape => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ha : Primrec (fun x : Shape => x.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hb : Primrec (fun x : Shape => x.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hq := Primrec.nat_mul.comp hn hn
  have hqq := Primrec.nat_mul.comp hq hq
  have hrs := Primrec.nat_mul.comp hr hs
  have hsr := Primrec.nat_mul.comp hs hr
  have hqrs := Primrec.nat_mul.comp hq hrs
  have hqsr := Primrec.nat_mul.comp hq hsr
  have hqr := Primrec.nat_mul.comp hq hr
  have hqs := Primrec.nat_mul.comp hq hs
  have hqqrs := Primrec.nat_mul.comp hqq hrs
  have hqqr := Primrec.nat_mul.comp hqq hr
  have hqqs := Primrec.nat_mul.comp hqq hs
  exact Primrec.list_cons.comp (hs.pair hb) (Primrec.list_cons.comp (hqrs.pair ha)
    (Primrec.list_cons.comp (hqrs.pair hb) (Primrec.list_cons.comp (hqr.pair ha)
    (Primrec.list_cons.comp (hr.pair ha) (Primrec.list_cons.comp (hqsr.pair hb)
    (Primrec.list_cons.comp (hqsr.pair ha) (Primrec.list_cons.comp (hqs.pair hb)
    (Primrec.list_cons.comp (hqqrs.pair ha) (Primrec.list_cons.comp (hqqr.pair ha)
    (Primrec.list_cons.comp (hqs.pair hb) (Primrec.list_cons.comp (hqqrs.pair hb)
    (Primrec.list_cons.comp (hqqrs.pair ha) (Primrec.list_cons.comp (hqr.pair ha)
    (Primrec.list_cons.comp (hqqs.pair hb) (Primrec.list_cons.comp (hqqrs.pair hb) (Primrec.const []))))))))))))))))

theorem allCodes_primrec : Primrec allCodes :=
  FiniteSearch.sections_primrec.comp (Primrec.list_map specs_primrec
    (FiniteSearch.tables_primrec.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)).to₂)

open DetParityAutomaton
variable {r s a b : Nat}
  (A : DetParityAutomaton (RoundRecord (Fin r) (Fin s) Graph (Fin (a+1)) (Fin (b+1))))
  (number : A.State ≃ Fin (Fintype.card A.State))

private abbrev atom := FiniteFunctionCodes.prod number number
private abbrev twoAtoms := FiniteFunctionCodes.prod (atom A number) (atom A number)
private abbrev inputs := FiniteFunctionCodes.prod (Equiv.refl (Fin r)) (Equiv.refl (Fin s))
private abbrev swappedInputs := FiniteFunctionCodes.prod (Equiv.refl (Fin s)) (Equiv.refl (Fin r))
private abbrev atomInputs := FiniteFunctionCodes.prod (atom A number) (inputs (r:=r) (s:=s))
private abbrev atomSwapped := FiniteFunctionCodes.prod (atom A number) (swappedInputs (r:=r) (s:=s))
private abbrev atomR := FiniteFunctionCodes.prod (atom A number) (Equiv.refl (Fin r))
private abbrev atomS := FiniteFunctionCodes.prod (atom A number) (Equiv.refl (Fin s))
private abbrev twoInputs := FiniteFunctionCodes.prod (twoAtoms A number) (inputs (r:=r) (s:=s))
private abbrev twoR := FiniteFunctionCodes.prod (twoAtoms A number) (Equiv.refl (Fin r))
private abbrev twoS := FiniteFunctionCodes.prod (twoAtoms A number) (Equiv.refl (Fin s))

def encode (l : GlobalJournalLabel A) : Code :=
  [FiniteFunctionCodes.encode (Equiv.refl _) l.1.1,
   FiniteFunctionCodes.encode (atomInputs A number) (Function.uncurry l.1.2),
   FiniteFunctionCodes.encode (atomInputs A number) (Function.uncurry l.2.1),
   FiniteFunctionCodes.encode (atomR A number) (Function.uncurry l.2.2.1),
   FiniteFunctionCodes.encode (Equiv.refl _) l.2.2.2.1.1,
   FiniteFunctionCodes.encode (atomSwapped A number) (Function.uncurry l.2.2.2.1.2),
   FiniteFunctionCodes.encode (atomSwapped A number) (Function.uncurry l.2.2.2.2.1),
   FiniteFunctionCodes.encode (atomS A number) (Function.uncurry l.2.2.2.2.2.1),
   FiniteFunctionCodes.encode (twoInputs A number) (Function.uncurry l.2.2.2.2.2.2.1.1),
   FiniteFunctionCodes.encode (twoR A number) (Function.uncurry l.2.2.2.2.2.2.1.2.1),
   FiniteFunctionCodes.encode (atomS A number) (Function.uncurry l.2.2.2.2.2.2.1.2.2.1),
   FiniteFunctionCodes.encode (twoInputs A number) (Function.uncurry l.2.2.2.2.2.2.1.2.2.2),
   FiniteFunctionCodes.encode (twoInputs A number) (Function.uncurry l.2.2.2.2.2.2.2.1),
   FiniteFunctionCodes.encode (atomR A number) (Function.uncurry l.2.2.2.2.2.2.2.2.1),
   FiniteFunctionCodes.encode (twoS A number) (Function.uncurry l.2.2.2.2.2.2.2.2.2.1),
   FiniteFunctionCodes.encode (twoInputs A number) (Function.uncurry l.2.2.2.2.2.2.2.2.2.2)]

def decode (c : Code) : GlobalJournalLabel A :=
  ((FiniteFunctionCodes.decode (Equiv.refl _) (c.getD 0 []),
      Function.curry (FiniteFunctionCodes.decode (atomInputs A number) (c.getD 1 []))),
    Function.curry (FiniteFunctionCodes.decode (atomInputs A number) (c.getD 2 [])),
    Function.curry (FiniteFunctionCodes.decode (atomR A number) (c.getD 3 [])),
    (FiniteFunctionCodes.decode (Equiv.refl _) (c.getD 4 []),
      Function.curry (FiniteFunctionCodes.decode (atomSwapped A number) (c.getD 5 []))),
    Function.curry (FiniteFunctionCodes.decode (atomSwapped A number) (c.getD 6 [])),
    Function.curry (FiniteFunctionCodes.decode (atomS A number) (c.getD 7 [])),
    (Function.curry (FiniteFunctionCodes.decode (twoInputs A number) (c.getD 8 [])),
      Function.curry (FiniteFunctionCodes.decode (twoR A number) (c.getD 9 [])),
      Function.curry (FiniteFunctionCodes.decode (atomS A number) (c.getD 10 [])),
      Function.curry (FiniteFunctionCodes.decode (twoInputs A number) (c.getD 11 []))),
    (Function.curry (FiniteFunctionCodes.decode (twoInputs A number) (c.getD 12 [])),
      Function.curry (FiniteFunctionCodes.decode (atomR A number) (c.getD 13 [])),
      Function.curry (FiniteFunctionCodes.decode (twoS A number) (c.getD 14 [])),
      Function.curry (FiniteFunctionCodes.decode (twoInputs A number) (c.getD 15 []))))

theorem decode_encode (l : GlobalJournalLabel A) : decode A number (encode A number l) = l := by
  simp [decode, encode, FiniteFunctionCodes.decode_encode]

theorem left_close (c : Code) (q m : A.State) (i : Fin r) (j : Fin s) :
    ((decode A number c).leftClose (q,m) (i,j)).val =
      (c.getD 2 []).getD (j.val+s*i.val+(r*s)*((number m).val+Fintype.card A.State*(number q).val)) 0 % (b+1) := rfl
theorem left_reverse (c : Code) (q m : A.State) (i : Fin r) :
    ((decode A number c).leftRev (q,m) i).val =
      (c.getD 3 []).getD (i.val+r*((number m).val+Fintype.card A.State*(number q).val)) 0 % (a+1) := rfl
theorem right_close (c : Code) (q m : A.State) (j : Fin s) (i : Fin r) :
    ((decode A number c).rightClose (q,m) (j,i)).val =
      (c.getD 6 []).getD (i.val+r*j.val+(s*r)*((number m).val+Fintype.card A.State*(number q).val)) 0 % (a+1) := rfl
theorem right_reverse (c : Code) (q m : A.State) (j : Fin s) :
    ((decode A number c).rightRev (q,m) j).val =
      (c.getD 7 []).getD (j.val+s*((number m).val+Fintype.card A.State*(number q).val)) 0 % (b+1) := rfl

theorem left_sender (c : Code) (j : Fin s) :
    ((decode A number c).1.1 j).val = (c.getD 0 []).getD j.val 0 % (b+1) := rfl
theorem left_receiver (c : Code) (q m : A.State) (i : Fin r) (j : Fin s) :
    ((decode A number c).1.2 (q,m) (i,j)).val =
      (c.getD 1 []).getD (j.val+s*i.val+(r*s)*((number m).val+Fintype.card A.State*(number q).val)) 0 % (a+1) := rfl
theorem right_sender (c : Code) (i : Fin r) :
    ((decode A number c).2.2.2.1.1 i).val = (c.getD 4 []).getD i.val 0 % (a+1) := rfl
theorem right_receiver (c : Code) (q m : A.State) (j : Fin s) (i : Fin r) :
    ((decode A number c).2.2.2.1.2 (q,m) (j,i)).val =
      (c.getD 5 []).getD (i.val+r*j.val+(s*r)*((number m).val+Fintype.card A.State*(number q).val)) 0 % (b+1) := rfl

def atomCode (qm : A.State × A.State) := (number qm.2).val + Fintype.card A.State*(number qm.1).val
def chainCode (th : ChainThread A) := atomCode A number th.2 +
  (Fintype.card A.State*Fintype.card A.State)*atomCode A number th.1

theorem revLeft_oneRecv (c : Code) (th : ChainThread A) (i : Fin r) (j : Fin s) :
    ((decode A number c).revLeft.oneRecv th (i,j)).val =
      (c.getD 8 []).getD (j.val+s*i.val+(r*s)*chainCode A number th) 0 % (a+1) := rfl
theorem revLeft_oneSend (c : Code) (th : ChainThread A) (i : Fin r) :
    ((decode A number c).revLeft.oneSend th i).val =
      (c.getD 9 []).getD (i.val+r*chainCode A number th) 0 % (a+1) := rfl
theorem revLeft_twoSend (c : Code) (qm : A.State × A.State) (j : Fin s) :
    ((decode A number c).revLeft.twoSend qm j).val =
      (c.getD 10 []).getD (j.val+s*atomCode A number qm) 0 % (b+1) := rfl
theorem revLeft_twoRecv (c : Code) (th : ChainThread A) (i : Fin r) (j : Fin s) :
    ((decode A number c).revLeft.twoRecv th (i,j)).val =
      (c.getD 11 []).getD (j.val+s*i.val+(r*s)*chainCode A number th) 0 % (b+1) := rfl
theorem revRight_oneRecv (c : Code) (th : ChainThread A) (i : Fin r) (j : Fin s) :
    ((decode A number c).revRight.oneRecv th (i,j)).val =
      (c.getD 12 []).getD (j.val+s*i.val+(r*s)*chainCode A number th) 0 % (a+1) := rfl
theorem revRight_oneSend (c : Code) (qm : A.State × A.State) (i : Fin r) :
    ((decode A number c).revRight.oneSend qm i).val =
      (c.getD 13 []).getD (i.val+r*atomCode A number qm) 0 % (a+1) := rfl
theorem revRight_twoSend (c : Code) (th : ChainThread A) (j : Fin s) :
    ((decode A number c).revRight.twoSend th j).val =
      (c.getD 14 []).getD (j.val+s*chainCode A number th) 0 % (b+1) := rfl
theorem revRight_twoRecv (c : Code) (th : ChainThread A) (i : Fin r) (j : Fin s) :
    ((decode A number c).revRight.twoRecv th (i,j)).val =
      (c.getD 15 []).getD (j.val+s*i.val+(r*s)*chainCode A number th) 0 % (b+1) := rfl

theorem encode_mem (l : GlobalJournalLabel A) :
    encode A number l ∈ allCodes (Fintype.card A.State, r, s, a+1, b+1) := by
  simp only [allCodes, specs, encode, List.map_cons, List.map_nil, List.mem_sections,
    List.forall₂_cons]
  repeat' apply And.intro
  all_goals first | exact FiniteFunctionCodes.encode_mem _ _ | exact List.Forall₂.nil

theorem complete (l : GlobalJournalLabel A) :
    ∃ c ∈ allCodes (Fintype.card A.State, r, s, a+1, b+1), decode A number c = l :=
  ⟨encode A number l, encode_mem A number l, decode_encode A number l⟩

end DistributedSynthesis.EncodedJournalLabels
