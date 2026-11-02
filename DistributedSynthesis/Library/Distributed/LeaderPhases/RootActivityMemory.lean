/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FirstExitBundleSoundness

/-! One persistent bit per original phase root records whether that root
has handed over. The bit is updated after the boundary output and is carried
into later scans. Truthful boundary flags remain explicit source data. -/
namespace Characterisation
open DistributedSynthesis

def rootActivityNext {H : Type} (active boundary : H → Bool) : H → Bool :=
  fun h => active h && !boundary h

def rootActivityRun {H : Type} (boundary : Nat → H → Bool) : Nat → H → Bool
  | 0 => fun _ => true
  | n+1 => rootActivityNext (rootActivityRun boundary n) (boundary n)

/-- The carried bit is true exactly until the first positive-depth boundary
of this phase root, including that boundary in the updates already made. -/
theorem rootActivityRun_exact {H : Type} (boundary : Nat → H → Bool) (n : Nat) (h : H) :
    rootActivityRun boundary n h = true ↔ ∀ i, i < n → boundary i h = false := by
  induction n with
  | zero => simp [rootActivityRun]
  | succ n ih =>
    simp only [rootActivityRun,rootActivityNext,Bool.and_eq_true,Bool.not_eq_true',ih]
    constructor
    · rintro ⟨old,last⟩ i bound
      by_cases earlier : i < n
      · exact old i earlier
      · have eq : i = n := by omega
        simpa only [eq] using last
    · intro all
      exact ⟨fun i hi => all i (by omega),all n (by omega)⟩

theorem rootActivityRun_no_reactivation {H : Type}
    (boundary : Nat → H → Bool) (a b : Nat) (before : a ≤ b) (h : H)
    (inactive : rootActivityRun boundary a h = false) : rootActivityRun boundary b h = false := by
  apply Bool.eq_false_iff.mpr
  intro active
  have all := (rootActivityRun_exact boundary b h).mp active
  have old := (rootActivityRun_exact boundary a h).mpr (fun i hi => all i (by omega))
  rw [inactive] at old
  contradiction

/-- Carrying the bit into a later scan agrees with continuing the original
scan. Resetting it to true would violate this identity after a handover. -/
theorem rootActivityRun_restart {H : Type} (boundary : Nat → H → Bool) (a n : Nat) (h : H) :
    rootActivityRun boundary (a+n) h =
      (rootActivityRun boundary a h && rootActivityRun (fun i => boundary (a+i)) n h) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true,rootActivityRun_exact]
  constructor
  · intro all
    exact ⟨fun i hi => all i (by omega),fun i hi => all (a+i) (by omega)⟩
  · rintro ⟨old,later⟩ i hi
    by_cases early : i < a
    · exact old i early
    · have eq : a+(i-a) = i := by omega
      simpa only [eq] using later (i-a) (by omega)

/-- The update is the existing finite phase-memory mechanism specialized
to one Boolean per root. It requires no unbounded counter in its state. -/
theorem rootActivityRun_phaseMemory {H Branch : Type}
    (flag : Branch → H → Bool) (letters : Nat → Branch) (n : Nat) :
    phaseMemoryRun (fun _ : H => true) (fun old letter => rootActivityNext old (flag letter)) letters n =
      rootActivityRun (fun i => flag (letters i)) n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [phaseMemoryRun,rootActivityRun,ih]

/-- Semantic interpretation along an arbitrary physical root history. Flags
at index i concern the output after i+1 extension rounds. Absolute source
depth a is retained, and all rounds through the current cut are checked. -/
theorem rootActivityRun_history {H I₁ I₂ : Type}
    (P : List Graph → Prop) (d a : Nat)
    (history : Nat → H → EnvHistory I₁ I₂)
    (prefixes : ∀ i j, i ≤ j → ∀ h, (history j h).take (a+i) = history i h)
    (boundary : Nat → H → Bool)
    (exactFlags : ∀ i h, boundary i h = leaderBoundary P d (history (i+1) h))
    (n : Nat) (h : H) :
    rootActivityRun boundary n h = true ↔
      ∀ m, a < m → m ≤ a+n → leaderBoundary P d ((history n h).take m) = false := by
  rw [rootActivityRun_exact]
  constructor
  · intro all m lower upper
    have eq : a+(m-a-1+1) = m := by omega
    rw [← eq,prefixes (m-a-1+1) n (by omega)]
    rw [← exactFlags]
    exact all (m-a-1) (by omega)
  · intro all i hi
    rw [exactFlags]
    have no := all (a+(i+1)) (by omega) (by omega)
    rwa [prefixes (i+1) n (by omega)] at no

end Characterisation
