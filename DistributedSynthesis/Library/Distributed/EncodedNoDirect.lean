/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.NoDirectLTLDecision
import DistributedSynthesis.Library.Logic.FiniteEncoding
import DistributedSynthesis.Library.Automata.EncodedLTLTransitions
import DistributedSynthesis.Library.Computability.FiniteSearch
import DistributedSynthesis.Library.Automata.EncodedSupportTables
import DistributedSynthesis.Library.Automata.EncodedLTLBreakpoints

/-! # Finite-data input for no-direct-reversal LTL synthesis

Each alphabet is `Fin (n + 1)`: the four size fields encode positive cardinalities.
The atom interpretation is a finite list of true atom/letter pairs. Missing pairs
are false; pairs outside the alphabet bounds are never inspected. Graph codes
0, 1, 2 denote left, right, both. Formulas use the existing total postfix decoder,
including its specified stack-underflow behavior.

`solve` is executable and its semantic correctness is proved. This module does
not itself prove mathlib `Computable solve` or `ComputablePred Realizable`.
The separate `EncodedNoDirectComputable` module now closes these obligations
through a primitive-recursive numeric journal compiler and verified solver.
-/

namespace DistributedSynthesis.EncodedNoDirect

abbrev LetterCode := Nat × Nat × Fin 3 × Nat × Nat

structure Instance where
  inputOneSizeMinusOne : Nat
  inputTwoSizeMinusOne : Nat
  outputOneSizeMinusOne : Nat
  outputTwoSizeMinusOne : Nat
  truthTable : List (Nat × LetterCode)
  formula : EncodedFiniteLTL.Code Nat
  deriving Repr, DecidableEq

/-- A fixed numeric representation, independent of the synthesis answer. -/
abbrev InstanceFields := Nat × Nat × Nat × Nat × List (Nat × LetterCode) × EncodedFiniteLTL.Code Nat

def instanceEquiv : Instance ≃ InstanceFields where
  toFun := fun data => (data.inputOneSizeMinusOne, data.inputTwoSizeMinusOne,
    data.outputOneSizeMinusOne, data.outputTwoSizeMinusOne, data.truthTable, data.formula)
  invFun := fun fields => ⟨fields.1, fields.2.1, fields.2.2.1, fields.2.2.2.1,
    fields.2.2.2.2.1, fields.2.2.2.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

instance : Primcodable Instance := Primcodable.ofEquiv InstanceFields instanceEquiv

theorem instanceEquiv_primrec : Primrec (instanceEquiv : Instance → InstanceFields) :=
  Primrec.of_equiv

private theorem formulaFields_primrec :
    Primrec (fun x : InstanceFields => x.2.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

theorem formula_primrec : Primrec Instance.formula := by
  have h : Primrec (fun x : Instance => (instanceEquiv x).2.2.2.2.2) :=
    Primrec.comp (α := Instance) (β := InstanceFields) (σ := EncodedFiniteLTL.Code Nat)
      (f := fun x => x.2.2.2.2.2) (g := instanceEquiv)
      formulaFields_primrec instanceEquiv_primrec
  exact h.of_eq (fun _ => rfl)

theorem truthTable_primrec : Primrec Instance.truthTable := by
  have hf : Primrec (fun x : InstanceFields => x.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have h := Primrec.comp (α := Instance) (β := InstanceFields) (σ := List (Nat × LetterCode))
    (f := fun x => x.2.2.2.2.1) (g := instanceEquiv) hf instanceEquiv_primrec
  exact h.of_eq (fun _ => rfl)

/-- The proved numeric frontend stage; this is not yet the complete tree compiler. -/
def stateTables (data : Instance) := EncodedLTLStates.compile data.formula

theorem stateTables_primrec : Primrec stateTables :=
  EncodedLTLStates.compile_primrec.comp formula_primrec

theorem stateTables_correct (data : Instance) :
    stateTables data =
      ((PositiveLTL.ofLTL (EncodedFiniteLTL.decode data.formula)).subformulas.map EncodedPositiveLTL.quote,
       (PositiveLTL.ofLTL (EncodedFiniteLTL.decode data.formula)).subformulas.map
         (PositiveLTL.alternatingPriority (PositiveLTL.ofLTL (EncodedFiniteLTL.decode data.formula)))) :=
  EncodedLTLStates.compile_correct data.formula

abbrev Letter (data : Instance) :=
  RoundRecord (Fin (data.inputOneSizeMinusOne + 1)) (Fin (data.inputTwoSizeMinusOne + 1))
    Graph (Fin (data.outputOneSizeMinusOne + 1)) (Fin (data.outputTwoSizeMinusOne + 1))

def graphCode : Graph → Fin 3
  | .left => 0
  | .right => 1
  | .both => 2

def letterCode {data : Instance} (letter : Letter data) : LetterCode :=
  (letter.inputOne.val, letter.inputTwo.val, graphCode letter.graph,
    letter.outputOne.val, letter.outputTwo.val)

def interp (data : Instance) (atom : Nat) (letter : Letter data) : Prop :=
  (atom, letterCode letter) ∈ data.truthTable

def interpDecidable (data : Instance) (atom : Nat) (letter : Letter data) :
    Decidable (interp data atom letter) :=
  inferInstanceAs (Decidable ((atom, letterCode letter) ∈ data.truthTable))

/-- Numeric alternating transitions for one coded round record. -/
def transitionRow (data : Instance) (letter : LetterCode) :=
  EncodedLTLTransitions.row
    (data.formula, EncodedLTLTransitions.trueAtoms data.truthTable letter)

theorem transitionRow_primrec : Primrec₂ transitionRow :=
  EncodedLTLTransitions.row_primrec.comp ((formula_primrec.comp Primrec.fst).pair
    (EncodedLTLTransitions.trueAtoms_primrec.comp (truthTable_primrec.comp Primrec.fst) Primrec.snd))

/-- A letter-major table; the caller supplies the list of coded letters. -/
def transitionTable (data : Instance) (letters : List LetterCode) :=
  letters.map (transitionRow data)

theorem transitionTable_primrec : Primrec₂ transitionTable :=
  Primrec.list_map Primrec.snd
    (transitionRow_primrec.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

/-- Simultaneous successor-support choices for a coded frontier and round record. -/
def supportTables (data : Instance) (letter : LetterCode) (frontier : List Nat) :=
  EncodedSupportTables.enumerateTables (transitionRow data letter) frontier

theorem supportTables_primrec :
    Primrec (fun x : Instance × LetterCode × List Nat => supportTables x.1 x.2.1 x.2.2) :=
  EncodedSupportTables.enumerateTables_primrec.comp
    (transitionRow_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd)

theorem transitionRow_correct (data : Instance) (letter : Letter data) :
    (transitionRow data (letterCode letter)).map EncodedPositiveBoolean.decode =
      (PositiveLTL.ofLTL (EncodedFiniteLTL.decode data.formula)).subformulas.map
        (fun p => (@PositiveLTL.alternatingStep Nat (Letter data)
          (interp data) (interpDecidable data) letter p).map
            (EncodedLTLTransitions.name data.formula)) := by
  unfold transitionRow EncodedLTLTransitions.row
  simp only [EncodedPositiveLTL.states_eq, List.map_map]
  apply List.map_congr_left
  intro p _
  exact @EncodedLTLTransitions.transition_correct_of_interp Nat _ (Letter data)
    (data.formula, EncodedLTLTransitions.trueAtoms data.truthTable (letterCode letter))
    (interp data) (interpDecidable data) letter
    (fun a => (EncodedLTLTransitions.mem_trueAtoms _ _ a).symm) p

private def lettersFields (x : InstanceFields) : List LetterCode :=
  (List.range (x.1 + 1)).product ((List.range (x.2.1 + 1)).product
    (([0, 1, 2] : List (Fin 3)).product
      ((List.range (x.2.2.1 + 1)).product (List.range (x.2.2.2.1 + 1)))))

/-- All valid round records, independent of the truth table and formula. -/
def letters (data : Instance) : List LetterCode := lettersFields (instanceEquiv data)

theorem letters_primrec : Primrec letters := by
  have hf : Primrec lettersFields :=
    FiniteSearch.product_primrec.comp (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
      (FiniteSearch.product_primrec.comp
        (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
        (FiniteSearch.product_primrec.comp (Primrec.const [0, 1, 2])
          (FiniteSearch.product_primrec.comp
            (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
            (Primrec.list_range.comp (Primrec.succ.comp
              (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))))
  exact Primrec.comp (α := Instance) (β := InstanceFields) (σ := List LetterCode)
    (f := lettersFields) (g := instanceEquiv) hf instanceEquiv_primrec

theorem mem_letters_iff (data : Instance) (code : LetterCode) :
    code ∈ letters data ↔ ∃ letter : Letter data, letterCode letter = code := by
  have hg (g : Fin 3) : g ∈ ([0, 1, 2] : List (Fin 3)) := by fin_cases g <;> simp
  have hge (g : Fin 3) : ∃ graph, graphCode graph = g := by
    fin_cases g
    · exact ⟨.left, rfl⟩
    · exact ⟨.right, rfl⟩
    · exact ⟨.both, rfl⟩
  rcases code with ⟨i₁, i₂, g, o₁, o₂⟩
  have hp {B C : Type} (xs : List B) (ys : List C) (b : B) (c : C) :
      (b, c) ∈ xs.product ys ↔ b ∈ xs ∧ c ∈ ys := List.mem_product
  simp only [letters, lettersFields, instanceEquiv, Equiv.coe_fn_mk,
    hp, List.mem_range, hg, true_and]
  constructor
  · rintro ⟨hi₁, hi₂, ho₁, ho₂⟩
    obtain ⟨graph, hgraph⟩ := hge g
    exact ⟨⟨⟨i₁, hi₁⟩, ⟨i₂, hi₂⟩, graph, ⟨o₁, ho₁⟩, ⟨o₂, ho₂⟩⟩,
      by simp [letterCode, hgraph]⟩
  · rintro ⟨letter, hletter⟩
    cases hletter
    exact ⟨letter.inputOne.isLt, letter.inputTwo.isLt, letter.outputOne.isLt, letter.outputTwo.isLt⟩

/-- Numeric state/priority tables, alphabet, and letter-major transition table.
The initial state is always zero (`EncodedLTLTransitions.name_root`).
This is the alternating frontend, not the complete parity-tree compiler. -/
def alternatingTables (data : Instance) :=
  (stateTables data, letters data, transitionTable data (letters data))

theorem alternatingTables_primrec : Primrec alternatingTables :=
  stateTables_primrec.pair (letters_primrec.pair
    (transitionTable_primrec.comp Primrec.id letters_primrec))

/-- Complete numeric Büchi edges for a round record. -/
def buchiEdges (data : Instance) (letter : LetterCode) :=
  EncodedLTLBreakpoints.edges
    (data.formula, EncodedLTLTransitions.trueAtoms data.truthTable letter)

theorem buchiEdges_primrec : Primrec₂ buchiEdges :=
  EncodedLTLBreakpoints.edges_primrec.comp ((formula_primrec.comp Primrec.fst).pair
    (EncodedLTLTransitions.trueAtoms_primrec.comp (truthTable_primrec.comp Primrec.fst) Primrec.snd))

/-- Uniform numeric Büchi tables over the complete round-record alphabet.
This closes alternation removal, not determinization or journal compilation. -/
def buchiTables (data : Instance) :=
  (EncodedLTLBreakpoints.stateCodes data.formula, EncodedLTLBreakpoints.initial,
    EncodedLTLBreakpoints.acceptingCodes data.formula,
    (letters data).map (fun letter => (letter, buchiEdges data letter)))

theorem buchiTables_primrec : Primrec buchiTables :=
  (EncodedLTLBreakpoints.stateCodes_primrec.comp formula_primrec).pair
    ((Primrec.const EncodedLTLBreakpoints.initial).pair
      ((EncodedLTLBreakpoints.acceptingCodes_primrec.comp formula_primrec).pair
        (Primrec.list_map letters_primrec
          (Primrec.snd.pair (buchiEdges_primrec.comp Primrec.fst Primrec.snd)).to₂)))

theorem mem_buchiEdges (data : Instance) (letter : LetterCode) (s t : FiniteSubsets.Pair) :
    (s, t) ∈ buchiEdges data letter ↔
      s ∈ EncodedLTLBreakpoints.stateCodes data.formula ∧
      t ∈ EncodedLTLBreakpoints.stateCodes data.formula ∧
      (AlternatingParityAutomaton.WeakComputable.buchi (EncodedLTLAutomaton.automaton data.formula)).step
        (EncodedLTLBreakpoints.decodeState data.formula s)
        (EncodedLTLTransitions.trueAtoms data.truthTable letter)
        (EncodedLTLBreakpoints.decodeState data.formula t) := by
  rw [buchiEdges, EncodedLTLBreakpoints.mem_edges, EncodedLTLBreakpoints.transition_correct]

def Realizable (data : Instance) : Prop :=
  NoDirectLTLDecision.Realizable (interp data) (EncodedFiniteLTL.decode data.formula)

def solve (data : Instance) : Bool :=
  NoDirectLTLDecision.solve (interp data) (interpDecidable data)
    (EncodedFiniteLTL.decode data.formula)

theorem solve_correct (data : Instance) : solve data = true ↔ Realizable data :=
  NoDirectLTLDecision.solve_correct (interp data) (interpDecidable data)
    (EncodedFiniteLTL.decode data.formula)

end DistributedSynthesis.EncodedNoDirect
