/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedLTLStates
import DistributedSynthesis.Library.Logic.EncodedPositiveBoolean

/-! # Numeric alternating transition tables for LTL

A letter is supplied as a finite list of its true atoms. Successor atoms are
the first-occurrence indices in the source formula's subformula list. The
compiler folds each positive subformula while retaining its syntax, so the
until/release continuation names the current state and next names its operand.
No determinization or synthesis construction is imported here.
-/

namespace DistributedSynthesis.EncodedLTLTransitions
open EncodedFiniteLTL EncodedPositiveLTL
variable {A : Type*} [DecidableEq A]

abbrev Context (A : Type*) := EncodedFiniteLTL.Code A × List A
abbrev Acc (A : Type*) := EncodedPositiveLTL.Code A × EncodedFiniteLTL.Code Nat

def literal (v : List A) (a : Bool × A) : Bool := decide (a.2 ∈ v) == a.1

def binary (k : Fin 8) (p q : Acc A) : Acc A :=
  (EncodedFiniteLTL.binary k p.1 q.1, EncodedFiniteLTL.binary k p.2 q.2)

def temporal (ctx : Context A) (k outer inner : Fin 8) (p q : Acc A) : Acc A :=
  let c := EncodedFiniteLTL.binary k p.1 q.1
  (c, EncodedFiniteLTL.binary outer q.2
    (EncodedFiniteLTL.binary inner p.2 (atom (index ctx.1 c))))

def algebra (ctx : Context A) : PostfixFold.Algebra (Bool × A) (Acc A) where
  truth := (truth, truth)
  falsity := (falsity, falsity)
  atom := fun a => (atom a, if literal ctx.2 a then truth else falsity)
  neg := fun _ => (falsity, falsity)
  conj := binary 3
  disj := binary 4
  next := fun p => (unary 5 p.1, atom (index ctx.1 p.1))
  «until» := temporal ctx 6 4 3
  «release» := temporal ctx 7 3 4

/-- A transition code. The caller supplies a positive subformula code. -/
def transition (ctx : Context A) (state : EncodedPositiveLTL.Code A) :
    EncodedFiniteLTL.Code Nat := (PostfixFold.run (algebra ctx) state).2

def interp (v : List A) (a : A) (_ : Unit) : Prop := a ∈ v

instance (v : List A) : ∀ a l, Decidable (interp v a l) :=
  fun a _ => inferInstanceAs (Decidable (a ∈ v))

def name (source : EncodedFiniteLTL.Code A) (p : PositiveLTL A) : Nat :=
  index source (quote p)

theorem name_root (source : EncodedFiniteLTL.Code A) :
    name source (PositiveLTL.ofLTL (EncodedFiniteLTL.decode source)) = 0 := by
  unfold name index
  rw [states_eq]
  cases PositiveLTL.ofLTL (EncodedFiniteLTL.decode source) <;>
    simp [PositiveLTL.subformulas]

theorem formula_correct (ctx : Context A) (p : PositiveLTL A) :
    PostfixFold.formula (algebra ctx) (embed p) =
      (quote p, EncodedPositiveBoolean.quote
        ((PositiveLTL.alternatingStep (interp ctx.2) () p).map (name ctx.1))) := by
  induction p with
  | lit l =>
    rcases l with ⟨b, a⟩
    cases b <;> by_cases h : a ∈ ctx.2 <;>
      simp [PostfixFold.formula, algebra, embed, quote, literal, interp,
        PositiveLTL.alternatingStep, PositiveLTL.literalHolds, PosBool.map,
        EncodedPositiveBoolean.quote, h]
  | _ =>
    simp_all [PostfixFold.formula, algebra, embed, quote, binary, temporal, name,
      PositiveLTL.alternatingStep, PosBool.map, EncodedPositiveBoolean.quote]

theorem transition_quote (ctx : Context A) (p : PositiveLTL A) :
    transition ctx (quote p) = EncodedPositiveBoolean.quote
      ((PositiveLTL.alternatingStep (interp ctx.2) () p).map (name ctx.1)) := by
  rw [transition, PostfixFold.run_correct, (quote_rep p).decode, formula_correct]

/-- Exact equality with the canonical alternating transition, after numbering. -/
theorem transition_correct (ctx : Context A) (p : PositiveLTL A) :
    EncodedPositiveBoolean.decode (transition ctx (quote p)) =
      (PositiveLTL.alternatingStep (interp ctx.2) () p).map (name ctx.1) := by
  rw [transition_quote, EncodedPositiveBoolean.decode_quote]

theorem transition_correct_of_interp {Letter : Type*} (ctx : Context A)
    (meaning : A → Letter → Prop) [∀ a l, Decidable (meaning a l)]
    (letter : Letter) (h : ∀ a, meaning a letter ↔ a ∈ ctx.2) (p : PositiveLTL A) :
    EncodedPositiveBoolean.decode (transition ctx (quote p)) =
      (PositiveLTL.alternatingStep meaning letter p).map (name ctx.1) := by
  rw [transition_correct]
  have he : PositiveLTL.alternatingStep (interp ctx.2) () p =
      PositiveLTL.alternatingStep meaning letter p := by
    induction p with
    | lit l =>
      rcases l with ⟨b, a⟩
      cases b <;> simp [PositiveLTL.alternatingStep, PositiveLTL.literalHolds, interp, h]
    | _ => simp_all [PositiveLTL.alternatingStep]
  rw [he]

/-- Every referenced successor is in range; absent-query defaults are never used. -/
theorem transition_bounded (ctx : Context A)
    (p : (PositiveLTL.ofLTL (EncodedFiniteLTL.decode ctx.1)).Subformula)
    (n : Nat) (hn : .inl n ∈ transition ctx (quote p.val)) : n < (states ctx.1).length := by
  rw [transition_quote, EncodedPositiveBoolean.atom_mem_quote] at hn
  have hm (b : PosBool (PositiveLTL A)) :
      (b.map (name ctx.1)).atoms = b.atoms.map (name ctx.1) := by
    induction b <;> simp_all [PosBool.map, PosBool.atoms]
  rw [hm, List.mem_map] at hn
  obtain ⟨q, hq, rfl⟩ := hn
  have hq' := PositiveLTL.subformulas_trans
    (PositiveLTL.alternatingStep_atoms_subformulas (interp ctx.2) () p.val q hq) p.property
  exact (number ctx.1 ⟨q, hq'⟩).isLt

/-- One transition per state occurrence, in the same order as the priority table. -/
def row (ctx : Context A) : List (EncodedFiniteLTL.Code Nat) :=
  (states ctx.1).map (transition ctx)

theorem row_correct (ctx : Context A) :
    (row ctx).map EncodedPositiveBoolean.decode =
      (PositiveLTL.ofLTL (EncodedFiniteLTL.decode ctx.1)).subformulas.map
        (fun p => (PositiveLTL.alternatingStep (interp ctx.2) () p).map (name ctx.1)) := by
  simp only [row, states_eq, List.map_map, Function.comp_def, transition_correct]

theorem row_length (ctx : Context A) : (row ctx).length = (states ctx.1).length :=
  List.length_map _

/-- Letter-major table for a supplied finite list of atom valuations. -/
def table (source : EncodedFiniteLTL.Code A) (valuations : List (List A)) :=
  valuations.map (fun v => row (source, v))

theorem table_correct (source : EncodedFiniteLTL.Code A) (valuations : List (List A)) :
    (table source valuations).map (List.map EncodedPositiveBoolean.decode) =
      valuations.map (fun v =>
        (PositiveLTL.ofLTL (EncodedFiniteLTL.decode source)).subformulas.map
          (fun p => (PositiveLTL.alternatingStep (interp v) () p).map (name source))) := by
  simp only [table, List.map_map, Function.comp_def, row_correct]

section TruthTable
variable {Letter : Type*} [DecidableEq Letter]

/-- Duplicate entries are harmless; missing atom/letter pairs are false. -/
def trueAtoms (truthTable : List (A × Letter)) (letter : Letter) : List A :=
  (truthTable.filter (fun entry => decide (entry.2 = letter))).map Prod.fst

omit [DecidableEq A] in
theorem mem_trueAtoms (truthTable : List (A × Letter)) (letter : Letter) (a : A) :
    a ∈ trueAtoms truthTable letter ↔ (a, letter) ∈ truthTable := by
  simp only [trueAtoms, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨b, l⟩, ⟨hm, rfl⟩, rfl⟩
    exact hm
  · intro hm
    exact ⟨(a, letter), ⟨hm, rfl⟩, rfl⟩

omit [DecidableEq A] in
theorem trueAtoms_primrec [Primcodable A] [Primcodable Letter] :
    Primrec₂ (trueAtoms (A := A) (Letter := Letter)) := by
  have hr : PrimrecRel (fun (entry : A × Letter) (l : Letter) => entry.2 = l) :=
    Primrec.eq.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hf : Primrec₂ (fun (xs : List (A × Letter)) l =>
      xs.filter (fun entry => decide (entry.2 = l))) :=
    hr.listFilter
  exact Primrec.list_map hf (Primrec.fst.comp Primrec.snd).to₂

end TruthTable

section Computability
variable [Primcodable A]

theorem literal_primrec : Primrec₂ (literal (A := A)) := by
  have hm : PrimrecRel (fun (v : List A) a => a ∈ v) :=
    (Primrec.eq.exists_mem_list).of_eq (fun v a => by simp)
  exact Primrec.beq.comp (hm.decide.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
    (Primrec.fst.comp Primrec.snd)

omit [DecidableEq A] in
theorem binary_primrec (k : Fin 8) : Primrec₂ (binary (A := A) k) :=
  ((EncodedFiniteLTL.binary_primrec k).comp
    (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
  ((EncodedFiniteLTL.binary_primrec k).comp
    (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem temporal_primrec (k outer inner : Fin 8) :
    Primrec (fun x : Context A × Acc A × Acc A => temporal x.1 k outer inner x.2.1 x.2.2) := by
  have hc : Primrec (fun x : Context A × Acc A × Acc A =>
      EncodedFiniteLTL.binary k x.2.1.1 x.2.2.1) :=
    (EncodedFiniteLTL.binary_primrec k).comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  exact hc.pair ((EncodedFiniteLTL.binary_primrec outer).comp
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
    ((EncodedFiniteLTL.binary_primrec inner).comp
      (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
      (atom_primrec.comp (index_primrec.comp (Primrec.fst.comp Primrec.fst) hc))))

theorem algebra_effective : PostfixFold.EffectiveFamily (algebra (A := A)) := by
  constructor
  · exact Primrec.const _
  · exact Primrec.const _
  · exact (atom_primrec.comp Primrec.snd).pair
      (Primrec.ite (Primrec.eq.comp
        (literal_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd) (Primrec.const true))
        (Primrec.const truth) (Primrec.const falsity))
  · exact Primrec.const _
  · exact (binary_primrec 3).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  · exact (binary_primrec 4).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  · exact ((unary_primrec 5).comp (Primrec.fst.comp Primrec.snd)).pair
      (atom_primrec.comp (index_primrec.comp
        (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)))
  · exact temporal_primrec 6 4 3
  · exact temporal_primrec 7 3 4

theorem transition_primrec : Primrec₂ (transition (A := A)) :=
  Primrec.snd.comp (PostfixFold.run_family_primrec algebra algebra_effective)

theorem row_primrec : Primrec (row (A := A)) :=
  Primrec.list_map (states_primrec.comp Primrec.fst) transition_primrec

theorem table_primrec : Primrec₂ (table (A := A)) :=
  Primrec.list_map Primrec.snd
    (row_primrec.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

end Computability

end DistributedSynthesis.EncodedLTLTransitions
