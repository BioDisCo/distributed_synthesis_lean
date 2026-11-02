/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteReceptionMemory
import DistributedSynthesis.Library.Distributed.LeaderPhases.GraphComponentMasks

/-! Compute the agreed leader and boundary bit from a complete finite graph
component and bounded reception annotations. Private inputs do not enter the
test. Exactness does not license revealing scenario graphs to processes. -/
namespace Characterisation
open DistributedSynthesis FullViewPath

private def vertexSilentAge : Vertex → Nat
  | .inl v => silentAge v
  | .inr v => silentAge v

private theorem vertexSilentAge_blind (v : Vertex) : vertexSilentAge (blind v) = vertexSilentAge v + 1 := by
  cases v <;> rfl

private theorem vertexSilentAge_iterate (d : Nat) (v : Vertex) :
    vertexSilentAge (blind^[d] v) = vertexSilentAge v + d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply',vertexSilentAge_blind,ih]; omega

theorem blindFor_iff_silentAge (d : Nat) (p : Proc) (g : List Graph) :
    BlindFor d (tagView (graphView p g)) ↔ d ≤ silentAge (graphView p g) := by
  constructor
  · rintro ⟨v,eq⟩
    have age := vertexSilentAge_iterate d v
    rw [eq] at age
    cases p <;> simp only [tagView,vertexSilentAge] at age <;> omega
  · exact silentAge_implies_blindFor d p g

theorem recentOther_one_iff (P : List Graph → Prop) (d : Nat) (g : List Graph) :
    RecentOther P d g .one ↔ ∀ k, Connected P g k → silentAge (graphView .two k) < d := by
  constructor
  · intro recent k conn
    have no := recent k (tagView (graphView .two k)) conn (Or.inr rfl) (by simp [tagView,viewOwner])
    rw [blindFor_iff_silentAge] at no
    omega
  · intro all k v conn incident different
    rcases incident with rfl | rfl
    · exact False.elim (different rfl)
    · change ¬ BlindFor d (tagView (graphView .two k))
      rw [blindFor_iff_silentAge]
      have lt := all k conn
      omega

def finiteGraphLeader {S : Type} [Fintype S] {d : Nat}
    (mask : S → Bool) (age : S → CappedReceptionAge d) : Proc :=
  if ∀ s, mask s = true → (age s .two).val < d then .one else .two

/-- Complete graph-component coverage makes the finite universal age test
exactly the existing agreed leader selection. Repeated labels remain distinct slots. -/
theorem finiteGraphLeader_exact {S : Type} [Fintype S]
    (P : List Graph → Prop) (d : Nat) (g : List Graph) (past : S → List Graph)
    (mask : S → Bool) (maskExact : ∀ s, mask s = true ↔ Connected P g (past s))
    (covers : ∀ k, Connected P g k → ∃ s, past s = k)
    (age : S → CappedReceptionAge d)
    (ageExact : ∀ s p, (age s p).val = min d (silentAge (graphView p (past s)))) :
    finiteGraphLeader mask age = componentLeader P d g := by
  have test : (∀ s, mask s = true → (age s .two).val < d) ↔ RecentOther P d g .one := by
    rw [recentOther_one_iff]
    constructor
    · intro all k conn
      obtain ⟨s,eq⟩ := covers k conn
      have small := all s ((maskExact s).mpr (by rwa [eq]))
      rw [ageExact,eq] at small
      omega
    · intro all s marked
      have small := all (past s) ((maskExact s).mp marked)
      rw [ageExact]
      omega
  unfold finiteGraphLeader componentLeader
  by_cases yes : ∀ s, mask s = true → (age s .two).val < d
  · rw [if_pos yes,if_pos (test.mp yes)]
  · rw [if_neg yes,if_neg (fun h => yes (test.mpr h))]

/-- The boundary bit combines the delayed reception checkpoint with a
change of the agreed leader. All arguments are finite interface data. -/
def finiteGraphBoundary {S : Type} [Fintype S] {d : Nat}
    (mask : S → Bool) (age : S → CappedReceptionAge d)
    (memory : S → ReceptionMemory d) (root : S) (previousLeader : Proc) : Bool :=
  receptionCheckpoint (memory root) (finiteGraphLeader mask age) ||
    decide (previousLeader ≠ finiteGraphLeader mask age)

theorem finiteGraphBoundary_exact {S I₁ I₂ : Type} [Fintype S]
    (P : List Graph → Prop) (d : Nat) (h : EnvHistory I₁ I₂) (past : S → List Graph)
    (mask : S → Bool)
    (maskExact : ∀ s, mask s = true ↔ Connected P (History.graphSequence h) (past s))
    (covers : ∀ k, Connected P (History.graphSequence h) k → ∃ s, past s = k)
    (age : S → CappedReceptionAge d)
    (ageExact : ∀ s p, (age s p).val = min d (silentAge (graphView p (past s))))
    (memory : S → ReceptionMemory d) (root : S)
    (memoryExact : memory root = receptionMemoryRun d (History.graphSequence h))
    (previousLeader : Proc)
    (previousExact : previousLeader = componentLeader P d (History.graphSequence h.dropLast)) :
    finiteGraphBoundary mask age memory root previousLeader = leaderBoundary P d h := by
  rw [finiteGraphBoundary,finiteGraphLeader_exact P d (History.graphSequence h) past mask maskExact covers age ageExact,
    memoryExact,receptionCheckpoint_exact,previousExact]
  rfl

end Characterisation
