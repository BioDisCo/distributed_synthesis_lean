/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusHoles
import DistributedSynthesis.Formalizations.ComponentGames.LiveStates

/- Executable version of the manuscript's finite test: enumerate complete
joint tables, check local-view consistency, and check every live R-round
graph word and every binary proposal pair. -/
namespace Characterisation.ComponentGames.Consensus
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1800000

abbrev TestCase (R : Nat) := (Proc → Bool) × BlockWord Graph R

def caseHistory {R : Nat} (c : TestCase R) : EnvHistory Bool Bool := proposalHistory c.1 c.2.val

def caseScenario {R : Nat} (c : TestCase R) : ClosingLayer Unit Bool Bool R :=
  wordScenario () ⟨caseHistory c,by simp [caseHistory,proposalHistory,c.2.property]⟩

def caseShape (R : Nat) : InputShape (TestCase R) :=
  fun p c d => closingLayerShape (fun (_ : Proc) (_ _ : Unit) => true) R p (caseScenario c) (caseScenario d)

theorem caseShape_exact (R : Nat) : RepresentsInputShape (caseHistory (R:=R)) (caseShape R) := by
  have empty : RepresentsInputShape (fun _ : Unit => ([] : EnvHistory Bool Bool)) (fun _ _ _ => true) := by
    intro p c d; simp
  intro p c d
  have exactShape := closingLayerShape_exact (fun _ : Unit => ([] : EnvHistory Bool Bool))
    (fun _ _ _ => true) empty R p (caseScenario c) (caseScenario d)
  simpa only [caseShape,caseScenario,wordScenario_history,List.nil_append] using exactShape

def caseValid {R : Nat} (c : TestCase R) (o : Bool × Bool) : Prop :=
  o.1 = o.2 ∧ (o.1 = c.1 .one ∨ o.1 = c.1 .two)

instance {R : Nat} (c : TestCase R) (o : Bool × Bool) : Decidable (caseValid c o) :=
  inferInstanceAs (Decidable (o.1 = o.2 ∧ (o.1 = c.1 .one ∨ o.1 = c.1 .two)))

variable (M : DetParityAutomaton Graph) [DecidableEq M.State]

def checkState (q : M.State) (R : Nat) : Bool :=
  decide (∃ out : TestCase R → Bool × Bool,
    ShapeCoherent (caseShape R) out ∧ ∀ c : TestCase R,
      liveState M ((prefixRecognizer M).evalFrom q c.2.val) = true → caseValid c (out c))

/-- Exact finite-round meaning of the test. This includes consistency
between ALL occurrences of the same local view, not independent choices. -/
theorem checkState_exact (q : M.State) (R : Nat) : checkState M q R = true ↔
    ∃ σ : StrategyPair Bool Bool Bool Bool, ∀ c : TestCase R,
      liveState M ((prefixRecognizer M).evalFrom q c.2.val) = true →
      caseValid c (σ.one (currentView .one (caseHistory c)),σ.two (currentView .two (caseHistory c))) := by
  rw [checkState,decide_eq_true_eq]
  constructor
  · rintro ⟨out,coherent,valid⟩
    obtain ⟨σ,implements⟩ := (shapeCoherent_iff_local caseHistory (caseShape R) (caseShape_exact R) out).mp coherent
    refine ⟨σ,fun c live => ?_⟩
    rw [(implements c).1,(implements c).2]
    exact valid c live
  · rintro ⟨σ,valid⟩
    let out (c : TestCase R) := (σ.one (currentView .one (caseHistory c)),σ.two (currentView .two (caseHistory c)))
    refine ⟨out,?_,valid⟩
    exact (shapeCoherent_iff_local caseHistory (caseShape R) (caseShape_exact R) out).mpr
      ⟨σ,fun _ => ⟨rfl,rfl⟩⟩

/-- Reachability is checked by a finite enumeration of words shorter than
|State|. The existing loop-deletion theorem proves that this is exact. -/
def reachableState (q : M.State) : Bool :=
  decide (∃ n : Fin (Fintype.card M.State), ∃ w : BlockWord Graph n.val,
    (prefixRecognizer M).eval w.val = q)

theorem reachableState_exact (q : M.State) : reachableState M q = true ↔
    ∃ w : List Graph, (prefixRecognizer M).eval w = q := by
  rw [reachableState,decide_eq_true_eq]
  constructor
  · rintro ⟨n,w,eq⟩; exact ⟨w.val,eq⟩
  · rintro ⟨w,eq⟩
    obtain ⟨v,len,same⟩ := short_word_same_state (prefixRecognizer M) M.initial w
    exact ⟨⟨v.length,len⟩,⟨v,rfl⟩,same.trans eq⟩

/-- Each reachable live state gets its own complete algorithm. Requiring
one common table for all states would be a stronger, incorrect test. -/
def checkAll (R : Nat) : Bool :=
  decide (∀ q : M.State, reachableState M q = true → liveState M q = true → checkState M q R = true)

/-- Unbounded increasing search, justified by a successful-round witness.
The witness is erased from the compiled code; the search discovers the bound. -/
def searchBound (terminates : ∃ n, checkAll M (n+1) = true) : Nat :=
  Nat.find terminates + 1

theorem searchBound_positive (terminates : ∃ n, checkAll M (n+1) = true) :
    0 < searchBound M terminates := by unfold searchBound; omega

theorem searchBound_correct (terminates : ∃ n, checkAll M (n+1) = true) :
    ∀ q : M.State, (∃ w : List Graph, (prefixRecognizer M).eval w = q) →
      (∃ word, M.AcceptsFrom q word) →
      ∃ σ : StrategyPair Bool Bool Bool Bool, ∀ c : TestCase (searchBound M terminates),
        liveState M ((prefixRecognizer M).evalFrom q c.2.val) = true →
        caseValid c (σ.one (currentView .one (caseHistory c)),σ.two (currentView .two (caseHistory c))) := by
  intro q reachable live
  have found := Nat.find_spec terminates
  have all : ∀ q : M.State, reachableState M q = true → liveState M q = true →
      checkState M q (searchBound M terminates) = true := by
    simpa only [checkAll,decide_eq_true_eq,searchBound] using found
  exact (checkState_exact M q _).mp
    (all q ((reachableState_exact M q).mpr reachable) ((liveState_correct M q).mpr live))

end Characterisation.ComponentGames.Consensus
