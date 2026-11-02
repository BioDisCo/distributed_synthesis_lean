/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/
import DistributedSynthesis.Formalizations.Lemma.LemCounterMachineMM2
import DistributedSynthesis.Formalizations.Lemma.LemEncodedFiniteLTL

/-! # Primitive-recursive finite tables for the machine-dependent LTL checks

Only control numbers vary with the source program. All other label data
belong to one fixed finite type; functions on that type are primitive
recursive finite lookup tables. This separates fixed constants from every
input-dependent computation.
-/
namespace DistributedSynthesis.CounterMachine.Compiler
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
open MM2 ResidueLTL
abbrev Payload := Output Unit
abbrev Shape := Graph × Payload × Payload
abbrev RawLetter := Shape × Nat × Nat
abbrev Kind := Bool × Bool
noncomputable instance : Primcodable Shape :=
  Primcodable.ofEquiv (Fin (Fintype.card Shape)) (Fintype.equivFin Shape)

def unitLetter (s : Shape) : Letter Unit := ⟨(),(),s.1,s.2.1,s.2.2⟩
def orientation (s : Shape) := oneLeft (unitLetter s)
def leftPayload (s : Shape) := if orientation s then s.2.1 else s.2.2
def leftControl (r : RawLetter) := if orientation r.1 then r.2.1 else r.2.2
def rightControl (r : RawLetter) := if orientation r.1 then r.2.2 else r.2.1
def kind (ρ : MM2.Instr) : Kind := (ρ.equivCode.1,ρ.equivCode.2.isSome)
def unitMachine (k : Option Kind) : Machine Unit where
  initial := ()
  code := fun _ ↦ k.map fun ab ↦
    if ab.2 then .dec (if ab.1 then 1 else 0) () () else .inc (if ab.1 then 1 else 0) ()

instance {Q : Type*} [DecidableEq Q] (M : Machine Q) (r : Letter Q) :
    Decidable (initialCheck M r) := by unfold initialCheck; infer_instance
instance {Q : Type*} [DecidableEq Q] (M : Machine Q) (r : Letter Q) :
    Decidable (localCheck M r) := by unfold localCheck; infer_instance
instance {Q : Type*} [DecidableEq Q] (M : Machine Q) (a b : Letter Q) :
    Decidable (pairCheck M a b) := by unfold pairCheck; infer_instance
instance {Q : Type*} (l : Label Q) : Decidable (leftCheck l) := by unfold leftCheck; infer_instance
instance {Q : Type*} (l : Label Q) : Decidable (rightCheck l) := by unfold rightCheck; infer_instance

def initialStatic (s : Shape) := decide (initialCheck (unitMachine none) (unitLetter s))
def localStatic (k : Option Kind) (s : Shape) := decide (localCheck (unitMachine k) (unitLetter s))
def pairStatic (s t : Shape) := decide (pairCheck (unitMachine none) (unitLetter s) (unitLetter t))
def positive (k : Kind) (s : Shape) := k.2 && ! (leftPayload s).base.zero (if k.1 then 1 else 0)
def clamp (P : Program) (i : Nat) := if i ≤ P.length then i else 0
def nextControl (P : Program) (i : Nat) (s : Shape) : Nat :=
  match lookup P i with
  | none => i
  | some ρ => clamp P (if positive (kind ρ) s then ρ.equivCode.2.getD 0 else i+1)

def initialTest (P : Program) (r : RawLetter) : Bool :=
  decide (leftControl r = clamp P 1) && initialStatic r.1
def localTest (P : Program) (r : RawLetter) : Bool :=
  decide (leftControl r = rightControl r) && localStatic ((lookup P (leftControl r)).map kind) r.1
def pairTest (P : Program) (ab : RawLetter × RawLetter) : Bool :=
  decide (leftControl ab.2 = nextControl P (leftControl ab.1) ab.1.1) && pairStatic ab.1.1 ab.2.1
def leaveRight (s : Shape) := decide (s.1 ≠ .right)
def guardLeft (s : Shape) := decide (s.1 ≠ .right ∨ leftCheck s.2.1.base)
def leaveLeft (s : Shape) := decide (s.1 ≠ .left)
def guardRight (s : Shape) := decide (s.1 ≠ .left ∨ rightCheck s.2.2.base)

theorem lookup_primrec : Primrec₂ lookup :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
theorem clamp_primrec : Primrec₂ clamp :=
  Primrec.ite (Primrec.nat_le.comp Primrec.snd (Primrec.list_length.comp Primrec.fst))
    Primrec.snd (Primrec.const 0)
theorem kind_primrec : Primrec kind :=
  Primrec.pair (Primrec.fst.comp (Primrec.of_equiv (e := MM2.Instr.equivCode)))
    (Primrec.option_isSome.comp (Primrec.snd.comp (Primrec.of_equiv (e := MM2.Instr.equivCode))))
theorem leftControl_primrec : Primrec leftControl := by
  have h : Primrec (fun r : RawLetter ↦ cond (orientation r.1) r.2.1 r.2.2) :=
    Primrec.cond ((Primrec.dom_finite orientation).comp Primrec.fst)
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact h.of_eq fun r ↦ by cases ht : orientation r.1 <;> simp [leftControl,ht]
theorem rightControl_primrec : Primrec rightControl := by
  have h : Primrec (fun r : RawLetter ↦ cond (orientation r.1) r.2.2 r.2.1) :=
    Primrec.cond ((Primrec.dom_finite orientation).comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact h.of_eq fun r ↦ by cases ht : orientation r.1 <;> simp [rightControl,ht]

theorem nextControl_primrec : Primrec (fun x : Program × Nat × Shape ↦ nextControl x.1 x.2.1 x.2.2) := by
  have hb : Primrec (fun x : (Program × Nat × Shape) × MM2.Instr ↦
      clamp x.1.1 (cond (positive (kind x.2) x.1.2.2) (x.2.equivCode.2.getD 0) (x.1.2.1+1))) :=
    clamp_primrec.comp (Primrec.fst.comp Primrec.fst)
    (Primrec.cond
      ((Primrec.dom_finite (fun x : Kind × Shape ↦ positive x.1 x.2)).comp
        (Primrec.pair (kind_primrec.comp Primrec.snd)
          (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
      (Primrec.option_getD.comp (Primrec.snd.comp ((Primrec.of_equiv (e := MM2.Instr.equivCode)).comp Primrec.snd))
        (Primrec.const 0))
      (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))
  have hh := Primrec.option_casesOn (lookup_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd) hb.to₂
  exact hh.of_eq fun x ↦ by
    cases h : lookup x.1 x.2.1 with
    | none => simp [nextControl,h]
    | some ρ => cases ht : positive (kind ρ) x.2.2 <;> simp [nextControl,h,ht]

theorem initialTest_primrec : Primrec₂ initialTest :=
  Primrec.and.comp
    (Primrec.eq.decide.comp (leftControl_primrec.comp Primrec.snd)
      (clamp_primrec.comp Primrec.fst (Primrec.const 1)))
    ((Primrec.dom_finite initialStatic).comp (Primrec.fst.comp Primrec.snd))
theorem localTest_primrec : Primrec₂ localTest :=
  Primrec.and.comp
    (Primrec.eq.decide.comp (leftControl_primrec.comp Primrec.snd) (rightControl_primrec.comp Primrec.snd))
    ((Primrec.dom_finite (fun x : Option Kind × Shape ↦ localStatic x.1 x.2)).comp
      (Primrec.pair
        (Primrec.option_map (lookup_primrec.comp Primrec.fst (leftControl_primrec.comp Primrec.snd))
          (kind_primrec.comp Primrec.snd).to₂)
        (Primrec.fst.comp Primrec.snd)))
theorem pairTest_primrec : Primrec₂ pairTest :=
  Primrec.and.comp
    (Primrec.eq.decide.comp (leftControl_primrec.comp (Primrec.snd.comp Primrec.snd))
      (nextControl_primrec.comp (Primrec.pair Primrec.fst
        (Primrec.pair (leftControl_primrec.comp (Primrec.fst.comp Primrec.snd))
          (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))))))
    ((Primrec.dom_finite (fun x : Shape × Shape ↦ pairStatic x.1 x.2)).comp
      (Primrec.pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))

noncomputable def shapes : List Shape := Finset.univ.toList
theorem mem_shapes (s : Shape) : s ∈ shapes := by simp [shapes]
noncomputable def letters (n : Nat) : List RawLetter :=
  shapes.flatMap fun s ↦ (List.range (n+1)).flatMap fun i ↦ (List.range (n+1)).map fun j ↦ (s,i,j)
theorem mem_letters (n : Nat) (r : RawLetter) : r ∈ letters n ↔ r.2.1 ≤ n ∧ r.2.2 ≤ n := by
  rcases r with ⟨s,i,j⟩
  simp [letters,mem_shapes]
theorem letters_primrec : Primrec letters := by
  apply Primrec.list_flatMap (Primrec.const shapes)
  unfold Primrec₂
  apply Primrec.list_flatMap (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  unfold Primrec₂
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
  unfold Primrec₂
  exact Primrec.pair (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
    (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd)
def pairs {A : Type*} (xs : List A) := xs.flatMap fun a ↦ xs.map fun b ↦ (a,b)
theorem mem_pairs {A : Type*} (xs : List A) (a b : A) : (a,b) ∈ pairs xs ↔ a ∈ xs ∧ b ∈ xs := by
  simp [pairs]
theorem pairs_primrec {A : Type*} [Primcodable A] : Primrec (pairs : List A → List (A × A)) := by
  apply Primrec.list_flatMap Primrec.id
  unfold Primrec₂
  apply Primrec.list_map Primrec.fst
  exact (Primrec.pair (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

noncomputable def tables (P : Program) : EncodedFiniteLTL.Tables RawLetter :=
  let xs := letters P.length
  (xs.filter (initialTest P),xs.filter (localTest P),(pairs xs).filter (pairTest P),
    xs.filter (fun r ↦ leaveRight r.1),xs.filter (fun r ↦ guardLeft r.1),
    xs.filter (fun r ↦ leaveLeft r.1),xs.filter (fun r ↦ guardRight r.1))
theorem tables_primrec : Primrec tables := by
  have hx : Primrec (fun P : Program ↦ letters P.length) := letters_primrec.comp Primrec.list_length
  have hf (f : Shape → Bool) : Primrec (fun P : Program ↦ (letters P.length).filter (fun r ↦ f r.1)) :=
    EncodedFiniteLTL.filter_primrec hx ((Primrec.dom_finite f).comp (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.pair (EncodedFiniteLTL.filter_primrec hx initialTest_primrec)
    (Primrec.pair (EncodedFiniteLTL.filter_primrec hx localTest_primrec)
      (Primrec.pair (EncodedFiniteLTL.filter_primrec (pairs_primrec.comp hx) pairTest_primrec)
        (Primrec.pair (hf leaveRight) (Primrec.pair (hf guardLeft) (Primrec.pair (hf leaveLeft) (hf guardRight))))))

abbrev Instance := Nat × EncodedFiniteLTL.Code RawLetter
noncomputable def compileInstance (P : Program) : Instance :=
  (P.length,EncodedFiniteLTL.assemble (tables P))
theorem compileInstance_primrec : Primrec compileInstance :=
  Primrec.pair Primrec.list_length (EncodedFiniteLTL.assemble_primrec.comp tables_primrec)
theorem compileInstance_computable : Computable compileInstance := compileInstance_primrec.to_comp

end DistributedSynthesis.CounterMachine.Compiler
