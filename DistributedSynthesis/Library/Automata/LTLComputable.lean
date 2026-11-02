/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.WeakComputable
import DistributedSynthesis.Library.Automata.LTLTranslation

/-! # Executable LTL-to-parity compilation

The compiler enumerates subformulas, computes the alternating transition,
removes weak alternation, and determinizes. It reuses the existing semantic
bridge. This is executable Lean data, not yet an encoded `Computable` theorem.
-/

namespace DistributedSynthesis.LTLComputable
open PositiveLTL

private theorem restrict_eq {α : Type*} {P : α → Prop}
    {f g : PosBool α} (h : f = g)
    (hf : ∀ a, a ∈ f.atoms → P a) (hg : ∀ a, a ∈ g.atoms → P a) :
    f.pmap (fun a ha => (⟨a, hf a ha⟩ : {a // P a})) =
      g.pmap (fun a ha => (⟨a, hg a ha⟩ : {a // P a})) := by
  subst g
  rfl

variable {AP Letter : Type*} [DecidableEq AP]
variable (interp : AP → Letter → Prop) (dec : ∀ ap letter, Decidable (interp ap letter))

def literalDecidable (letter : Letter) (literal : LTLLiteral AP) :
    Decidable (literalHolds interp letter literal) := by
  letI := dec
  rcases literal with ⟨positive, atom⟩
  cases positive
  · exact inferInstanceAs (Decidable (¬ interp atom letter))
  · exact inferInstanceAs (Decidable (interp atom letter))

def step (letter : Letter) : PositiveLTL AP → PosBool (PositiveLTL AP)
  | .verum => .verum
  | .falsum => .falsum
  | .lit literal =>
      if @decide (literalHolds interp letter literal) (literalDecidable interp dec letter literal)
      then .verum else .falsum
  | .conj φ ψ => .conj (step letter φ) (step letter ψ)
  | .disj φ ψ => .disj (step letter φ) (step letter ψ)
  | .next φ => .atom φ
  | .until φ ψ => .disj (step letter ψ) (.conj (step letter φ) (.atom (.until φ ψ)))
  | .release φ ψ => .conj (step letter ψ) (.disj (step letter φ) (.atom (.release φ ψ)))

omit [DecidableEq AP] in
theorem step_eq (letter : Letter) (φ : PositiveLTL AP) :
    step interp dec letter φ = @alternatingStep AP Letter interp dec letter φ := by
  induction φ <;> simp_all only [step, alternatingStep, decide_eq_true_eq]

@[reducible] def subformulaFintype (root : PositiveLTL AP) : Fintype root.Subformula :=
  Fintype.subtype root.subformulas.toFinset (fun _ => List.mem_toFinset)

def transition (root : PositiveLTL AP) (state : root.Subformula) (letter : Letter) :
    PosBool root.Subformula :=
  (step interp dec letter state.val).pmap fun ψ h =>
    ⟨ψ, subformulas_trans
      (alternatingStep_atoms_subformulas interp letter state.val ψ
        (by rw [← step_eq interp dec] ; exact h)) state.property⟩

omit [DecidableEq AP] in
theorem transition_eq (root : PositiveLTL AP) (state : root.Subformula) (letter : Letter) :
    transition interp dec root state letter =
      @subformulaTransition AP Letter root interp dec state letter := by
  unfold transition subformulaTransition
  exact restrict_eq (step_eq interp dec letter state.val) _ _

def apa (root : PositiveLTL AP) : AlternatingParityAutomaton Letter where
  State := root.Subformula
  stateFinite := subformulaFintype root
  initial := rootSubformula root
  step := transition interp dec root
  priority := fun q => alternatingPriority root q.val

local instance (root : PositiveLTL AP) : DecidableEq (apa interp dec root).State :=
  inferInstanceAs (DecidableEq root.Subformula)

theorem apa_eq (root : PositiveLTL AP) :
    apa interp dec root = closureAPA root interp dec := by
  unfold apa closureAPA PositiveLTL.subformulaClosure FiniteLTLAlternatingClosure.toAPA
  congr 1
  funext state letter
  exact transition_eq interp dec root state letter

theorem weak (root : PositiveLTL AP) :
    AlternatingParityAutomaton.SelfOrDecreasing (apa interp dec root) (fun q => q.val.size) := by
  have h := subformulaClosure_selfOrDecreasing root interp dec
  intro q letter q' hmem
  apply h q letter q'
  change q' ∈ (transition interp dec root q letter).atoms at hmem
  rw [transition_eq] at hmem
  exact hmem

def positiveDPA (root : PositiveLTL AP) : DetParityAutomaton Letter :=
  AlternatingParityAutomaton.WeakComputable.dpa (apa interp dec root)

theorem positive_correct (root : PositiveLTL AP) (word : OmegaWord Letter) :
    (positiveDPA interp dec root).Accepts word ↔ PositiveLTL.Satisfies interp word root := by
  have h := AlternatingParityAutomaton.WeakComputable.accepts_iff
    (apa interp dec root) (fun q => q.val.size) (weak interp dec root) word
  apply h.trans
  rw [apa_eq]
  exact subformulaClosure_accepts_iff_satisfies root interp dec word

def compile (φ : LTL AP) : DetParityAutomaton Letter :=
  positiveDPA interp dec (PositiveLTL.ofLTL φ)

@[reducible] def stateDecidableEq (φ : LTL AP) : DecidableEq (compile interp dec φ).State :=
  AlternatingParityAutomaton.WeakComputable.stateDecidableEq (apa interp dec (PositiveLTL.ofLTL φ))

theorem correct (φ : LTL AP) (word : OmegaWord Letter) :
    (compile interp dec φ).Accepts word ↔ LTL.Satisfies interp word φ :=
  (positive_correct interp dec (PositiveLTL.ofLTL φ) word).trans
    (PositiveLTL.satisfies_ofLTL interp word φ)

def compiler : LTLToDPACompiler AP Letter where
  interp := interp
  compile := compile interp dec
  correct := correct interp dec

end DistributedSynthesis.LTLComputable
