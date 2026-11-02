/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.Theorem.ThmWeakAlternationRemoval

/-! # Alternating automata with redundant state names

The decoding map may identify several target states. Encoding picks one
representative of each source state. Transitions only mention representatives;
priorities depend on the decoded state. This preserves run-tree acceptance and
weakness, even when the larger carrier contains redundant occurrences.
-/

namespace DistributedSynthesis.AlternatingParityAutomaton.Retraction
variable {Letter Q : Type*} [Fintype Q]
variable (A : AlternatingParityAutomaton Letter)
variable (encode : A.State → Q) (decode : Q → A.State)

@[reducible] def automaton : AlternatingParityAutomaton Letter where
  State := Q
  stateFinite := inferInstance
  initial := encode A.initial
  step := fun q a => (A.step (decode q) a).map encode
  priority := fun q => A.priority (decode q)

variable (hleft : Function.LeftInverse decode encode)

def liftRun {word : OmegaWord Letter} (run : A.Run word) :
    (automaton A encode decode).Run word where
  active := run.active
  stateAt := fun node => encode (run.stateAt node)
  root_active := run.root_active
  root_state := congrArg encode run.root_state
  step_satisfied := by
    intro node hnode
    change PosBool.Eval _ ((A.step (decode (encode (run.stateAt node))) _).map encode)
    rw [hleft, PosBool.eval_map]
    apply PosBool.eval_mono _ _ (run.step_satisfied node hnode)
    intro q hq
    obtain ⟨child, hc, he⟩ := hq
    exact ⟨child, hc, congrArg encode he⟩

def projectRun {word : OmegaWord Letter} (run : (automaton A encode decode).Run word) :
    A.Run word where
  active := run.active
  stateAt := fun node => decode (run.stateAt node)
  root_active := run.root_active
  root_state := (congrArg decode run.root_state).trans (hleft A.initial)
  step_satisfied := by
    intro node hnode
    have h := run.step_satisfied node hnode
    change PosBool.Eval _ ((A.step (decode (run.stateAt node)) _).map encode) at h
    rw [PosBool.eval_map] at h
    apply PosBool.eval_mono _ _ h
    intro q hq
    obtain ⟨child, hc, he⟩ := hq
    exact ⟨child, hc, (congrArg decode he).trans (hleft q)⟩

theorem liftRun_accepting {word : OmegaWord Letter} (run : A.Run word) :
    (liftRun A encode decode hleft run).Accepting ↔ run.Accepting := by
  have he (q : A.State) : decode (encode q) = q := hleft q
  simp only [Run.Accepting, Run.ActiveBranch, Run.BranchAccepts,
    Run.PrioritySeenInfinitelyOften, liftRun, automaton, he]

theorem projectRun_accepting {word : OmegaWord Letter}
    (run : (automaton A encode decode).Run word) :
    (projectRun A encode decode hleft run).Accepting ↔ run.Accepting := by
  rfl

include hleft in
theorem accepts_iff (word : OmegaWord Letter) :
    (automaton A encode decode).Accepts word ↔ A.Accepts word := by
  constructor
  · rintro ⟨run, hrun⟩
    exact ⟨projectRun A encode decode hleft run,
      (projectRun_accepting A encode decode hleft run).mpr hrun⟩
  · rintro ⟨run, hrun⟩
    exact ⟨liftRun A encode decode hleft run,
      (liftRun_accepting A encode decode hleft run).mpr hrun⟩

section Weakness
variable [DecidableEq Q]

/-- Redundant occurrences have one extra unit of rank over their representative. -/
def measure (μ : A.State → Nat) (q : Q) : Nat :=
  2 * μ (decode q) + if encode (decode q) = q then 0 else 1

include hleft in
theorem selfOrDecreasing (μ : A.State → Nat) (hweak : SelfOrDecreasing A μ) :
    SelfOrDecreasing (automaton A encode decode) (measure A encode decode μ) := by
  have hm (p : PosBool A.State) : (p.map encode).atoms = p.atoms.map encode := by
    induction p <;> simp_all [PosBool.map, PosBool.atoms]
  have hecode (s : A.State) : decode (encode s) = s := hleft s
  intro q a q' hq'
  change q' ∈ ((A.step (decode q) a).map encode).atoms at hq'
  rw [hm, List.mem_map] at hq'
  obtain ⟨s, hs, rfl⟩ := hq'
  rcases hweak (decode q) a s hs with he | hlt
  · subst s
    by_cases hq : encode (decode q) = q
    · exact Or.inl hq
    · right
      simp [measure, hecode, hq]
  · right
    simp only [measure, hecode, ↓reduceIte]
    split_ifs <;> omega

end Weakness
end DistributedSynthesis.AlternatingParityAutomaton.Retraction
