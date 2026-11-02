/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteLetterLTL
import DistributedSynthesis.Formalizations.Lemma.LemScalingNoFiniteWinner

/-! # A literal LTL encoding of the scaling checks using coordinate residues

Coordinates are reduced modulo three. Adjacent vertices still determine a
unique orientation, since +1 and -1 are distinct modulo three.
-/

namespace DistributedSynthesis.ScalingSafety.ResidueLTL

structure Output where
  base : Label
  residue : Fin 3
deriving DecidableEq, Fintype

abbrev Letter := RoundRecord Unit Unit Graph Output Output

noncomputable instance : Fintype Letter := Fintype.ofEquiv (Graph × Output × Output)
  ⟨fun r ↦ ⟨(),(),r.1,r.2.1,r.2.2⟩,
    fun r ↦ (r.graph,r.outputOne,r.outputTwo),fun _ ↦ rfl,fun _ ↦ rfl⟩

def forget (r : Letter) : RoundRecord Unit Unit Graph Label Label :=
  ⟨(),(),r.graph,r.outputOne.base,r.outputTwo.base⟩

abbrev Residues := Fin 3 × Fin 3
def residues (r : Letter) : Residues := (r.outputOne.residue,r.outputTwo.residue)
def mod3 (n : Nat) : Fin 3 := ⟨n % 3,Nat.mod_lt _ (by decide)⟩
def update (xy : Residues) (g : Graph) : Residues :=
  match g with
  | .right => (mod3 (3*xy.1.val),mod3 (xy.2.val+2*xy.1.val))
  | .left => (mod3 (xy.1.val+2*xy.2.val),mod3 (3*xy.2.val))
  | .both => (mod3 (xy.1.val+2*xy.2.val),mod3 (xy.2.val+2*xy.1.val))

def Oriented (t : Bool) (xy : Residues) : Prop :=
  if t then xy.2.val = (xy.1.val+1)%3 else xy.1.val = (xy.2.val+1)%3
def decode (xy : Residues) : Bool := decide (xy.2.val = (xy.1.val+1)%3)

theorem oriented_update (t : Bool) (xy : Residues) (g : Graph) :
    Oriented t xy → Oriented (Source.turn t g) (update xy g) := by
  revert t xy g
  unfold Oriented
  decide

theorem oriented_decode (t : Bool) (xy : Residues) :
    Oriented t xy → decode xy = t := by
  revert t xy
  unfold Oriented
  decide

def oneLeft (r : Letter) : Bool := decode (residues r)
def leftLabel (r : Letter) : Label := if oneLeft r then r.outputOne.base else r.outputTwo.base
def rightLabel (r : Letter) : Label := if oneLeft r then r.outputTwo.base else r.outputOne.base
def edgePlan (r : Letter) : Plan := (leftLabel r).right

def initialCheck (r : Letter) : Prop := residues r = update (0,1) r.graph
def localCheck (r : Letter) : Prop :=
  let l := leftLabel r
  let q := rightLabel r
  l.up = q.up ∧ l.right = q.left ∧
    l.right.childValue 0 + l.right.childValue 1 + l.right.childValue 2 + l.carry.val =
      l.multiplier * l.right.value + q.carry.val
def pairCheck (a b : Letter) : Prop :=
  residues b = update (residues a) b.graph ∧
    (edgePlan b).value = (edgePlan a).childValue (digit (oneLeft a) b.graph)

noncomputable def formula : LTL Letter :=
  let test := FiniteLetterLTL.test (Letter := Letter)
  .conj (test initialCheck)
    (.conj (.always (test localCheck))
      (.conj (.always (FiniteLetterLTL.relation pairCheck))
        (.conj (FiniteLetterLTL.boundary (fun r ↦ r.graph = .right)
            (fun r ↦ r.outputOne.base.carry.val = 0))
          (FiniteLetterLTL.boundary (fun r ↦ r.graph = .left)
            (fun r ↦ r.outputTwo.base.carry.val = 0)))))

def Conditions (w : OmegaWord Letter) : Prop :=
  initialCheck (w 0) ∧ (∀ n, localCheck (w n)) ∧
    (∀ n, pairCheck (w n) (w (n+1))) ∧
    (∀ n, (∀ k, k ≤ n → (w k).graph = .right) → (w n).outputOne.base.carry.val = 0) ∧
    (∀ n, (∀ k, k ≤ n → (w k).graph = .left) → (w n).outputTwo.base.carry.val = 0)

theorem satisfies_iff (w : OmegaWord Letter) :
    LTL.Satisfies FiniteLetterLTL.interp w formula ↔ Conditions w := by
  simp only [formula,LTL.Satisfies, LTL.satisfies_always,
    FiniteLetterLTL.satisfies_test,FiniteLetterLTL.satisfies_relation,
    FiniteLetterLTL.satisfies_boundary,OmegaWord.drop_apply,Nat.add_zero]
  rfl

def ResidueValid (w : OmegaWord Letter) : Prop :=
  initialCheck (w 0) ∧ ∀ n, residues (w (n+1)) = update (residues (w n)) (w (n+1)).graph

abbrev monitor (w : OmegaWord Letter) := objective.run (fun n ↦ forget (w n))

theorem monitor_orientation (w : OmegaWord Letter) (h : ResidueValid w) (n : Nat) :
    Oriented (monitor w (n+1)).oneLeft (residues (w n)) := by
  induction n with
  | zero =>
    rw [show residues (w 0) = update (0,1) (w 0).graph from h.1]
    exact oriented_update true (0,1) (w 0).graph (by rfl)
  | succ n ih =>
    rw [h.2 n]
    exact oriented_update _ _ _ ih

theorem monitor_decode (w : OmegaWord Letter) (h : ResidueValid w) (n : Nat) :
    oneLeft (w n) = (monitor w (n+1)).oneLeft :=
  oriented_decode _ _ (monitor_orientation w h n)

theorem step_boundary (s : State) (r : RoundRecord Unit Unit Graph Label Label)
    (h : s.leftBoundary = true ∨ s.rightBoundary = true → s.oneLeft = true) :
    ((step s r).leftBoundary = true ↔ s.leftBoundary = true ∧ r.graph = .right) ∧
    ((step s r).rightBoundary = true ↔ s.rightBoundary = true ∧ r.graph = .left) ∧
    ((step s r).leftBoundary = true ∨ (step s r).rightBoundary = true →
      (step s r).oneLeft = true) := by
  cases ht : s.oneLeft <;> cases hl : s.leftBoundary <;> cases hr : s.rightBoundary <;>
    cases hg : r.graph <;> simp [step,digit,ht,hl,hr,hg] at h ⊢

theorem monitor_boundary (w : OmegaWord Letter) (n : Nat) :
    ((monitor w n).leftBoundary = true ↔ ∀ k, k < n → (w k).graph = .right) ∧
    ((monitor w n).rightBoundary = true ↔ ∀ k, k < n → (w k).graph = .left) ∧
    ((monitor w n).leftBoundary = true ∨ (monitor w n).rightBoundary = true →
      (monitor w n).oneLeft = true) := by
  induction n with
  | zero =>
    change (true = true ↔ ∀ k, k < 0 → _) ∧ (true = true ↔ ∀ k, k < 0 → _) ∧ _
    simp [objective]
  | succ n ih =>
    have hs := step_boundary (monitor w n) (forget (w n)) ih.2.2
    change ((step (monitor w n) (forget (w n))).leftBoundary = true ↔ _) ∧ _
    refine ⟨?_,?_,hs.2.2⟩
    · rw [hs.1,ih.1]
      constructor
      · rintro ⟨hh,hn⟩ k hk
        by_cases heq : k = n
        · simpa [heq] using hn
        · exact hh k (by omega)
      · intro hh
        exact ⟨fun k hk ↦ hh k (by omega),hh n (by omega)⟩
    · change (step (monitor w n) (forget (w n))).rightBoundary = true ↔ _
      rw [hs.2.1,ih.2.1]
      constructor
      · rintro ⟨hh,hn⟩ k hk
        by_cases heq : k = n
        · simpa [heq] using hn
        · exact hh k (by omega)
      · intro hh
        exact ⟨fun k hk ↦ hh k (by omega),hh n (by omega)⟩

theorem step_checks (s : State) (r : Letter)
    (ht : oneLeft r = (step s (forget r)).oneLeft) :
    (step s (forget r)).good = true ↔ s.good = true ∧ localCheck r ∧
      ((step s (forget r)).leftBoundary = true → (leftLabel r).carry.val = 0) ∧
      ((step s (forget r)).rightBoundary = true → (rightLabel r).carry.val = 0) ∧
      (∀ old, s.previous = some old →
        (edgePlan r).value = old.childValue (digit s.oneLeft r.graph)) := by
  change oneLeft r = (if r.graph = .both then !s.oneLeft else s.oneLeft) at ht
  simp only [step,forget,localCheck,leftLabel,rightLabel,edgePlan,ht,
    Bool.and_eq_true,decide_eq_true_eq]
  tauto

theorem monitor_previous (w : OmegaWord Letter) (h : ResidueValid w) (n : Nat) :
    (monitor w (n+1)).previous = some (edgePlan (w n)) := by
  unfold edgePlan leftLabel
  rw [monitor_decode w h n]
  rfl

theorem boundary_labels (w : OmegaWord Letter) (h : ResidueValid w) (n : Nat)
    (hb : (monitor w (n+1)).leftBoundary = true ∨ (monitor w (n+1)).rightBoundary = true) :
    leftLabel (w n) = (w n).outputOne.base ∧
      rightLabel (w n) = (w n).outputTwo.base := by
  have ht := (monitor_boundary w (n+1)).2.2 hb
  simp only [leftLabel,rightLabel,monitor_decode w h n,ht,↓reduceIte]
  exact ⟨trivial,trivial⟩

theorem conditions_iff_accepts (w : OmegaWord Letter) :
    Conditions w ↔ ResidueValid w ∧ objective.Accepts (fun n ↦ forget (w n)) := by
  constructor
  · intro h
    have hr : ResidueValid w := ⟨h.1, fun n ↦ (h.2.2.1 n).1⟩
    refine ⟨hr, (accepts_iff_good _).mpr ?_⟩
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      apply (step_checks (monitor w n) (w n) (monitor_decode w hr n)).mpr
      refine ⟨ih,h.2.1 n,?_,?_,?_⟩
      · intro hb
        rw [(boundary_labels w hr n (Or.inl hb)).1]
        exact h.2.2.2.1 n (fun k hk ↦ (monitor_boundary w (n+1)).1.mp hb k (by omega))
      · intro hb
        rw [(boundary_labels w hr n (Or.inr hb)).2]
        exact h.2.2.2.2 n (fun k hk ↦ (monitor_boundary w (n+1)).2.1.mp hb k (by omega))
      · intro old ho
        cases n with
        | zero => cases ho
        | succ n =>
          rw [monitor_previous w hr n] at ho
          cases Option.some.inj ho
          rw [← monitor_decode w hr n]
          exact (h.2.2.1 n).2
  · rintro ⟨hr,ha⟩
    have hg := (accepts_iff_good _).mp ha
    have hc (n : Nat) := (step_checks (monitor w n) (w n) (monitor_decode w hr n)).mp (hg (n+1))
    refine ⟨hr.1,fun n ↦ (hc n).2.1,?_,?_,?_⟩
    · intro n
      refine ⟨hr.2 n,?_⟩
      rw [monitor_decode w hr n]
      exact (hc (n+1)).2.2.2.2 _ (monitor_previous w hr n)
    · intro n hn
      have hb := (monitor_boundary w (n+1)).1.mpr (fun k hk ↦ hn k (by omega))
      have hz := (hc n).2.2.1 hb
      rwa [(boundary_labels w hr n (Or.inl hb)).1] at hz
    · intro n hn
      have hb := (monitor_boundary w (n+1)).2.1.mpr (fun k hk ↦ hn k (by omega))
      have hz := (hc n).2.2.2.1 hb
      rwa [(boundary_labels w hr n (Or.inr hb)).2] at hz

/-- Exact language equivalence, not an appeal to arbitrary safety-DPA
expressibility in LTL. The residue update is part of the formula. -/
theorem formula_iff_accepts (w : OmegaWord Letter) :
    LTL.Satisfies FiniteLetterLTL.interp w formula ↔
      ResidueValid w ∧ objective.Accepts (fun n ↦ forget (w n)) :=
  (satisfies_iff w).trans (conditions_iff_accepts w)

end DistributedSynthesis.ScalingSafety.ResidueLTL
