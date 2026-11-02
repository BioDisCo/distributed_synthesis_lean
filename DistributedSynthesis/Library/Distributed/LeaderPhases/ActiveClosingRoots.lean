/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.RootActivityMemory

/-! Reuse the first-exit checker on the carried active root subset. Scenario
maps retain every round, input and graph; source labels and policy entries
are restricted along the same map. -/
namespace Characterisation
open DistributedSynthesis

abbrev ActiveClosingRoots {H : Type} (active : H → Bool) := {h : H // active h = true}

def mapClosingLayer {H K I₁ I₂ : Type} (f : H → K) :
    (n : Nat) → ClosingLayer H I₁ I₂ n → ClosingLayer K I₁ I₂ n
  | 0 => f
  | n+1 => fun s => (mapClosingLayer f n s.1,s.2)

theorem mapClosingLayer_injective {H K I₁ I₂ : Type} (f : H → K)
    (injective : Function.Injective f) (n : Nat) :
    Function.Injective (mapClosingLayer (I₁:=I₁) (I₂:=I₂) f n) := by
  induction n with
  | zero => exact injective
  | succ n ih =>
    intro s t eq
    exact Prod.ext (ih (congrArg Prod.fst eq)) (congrArg (fun r : ClosingLayer K I₁ I₂ (n+1) => r.2) eq)

theorem closingLayerRoot_map {H K I₁ I₂ : Type} (f : H → K)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerRoot n (mapClosingLayer f n s) = f (closingLayerRoot n s) := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih s.1

theorem closingLayerHistory_map {H K I₁ I₂ : Type}
    (past : K → EnvHistory I₁ I₂) (f : H → K) (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerHistory (past ∘ f) n s = closingLayerHistory past n (mapClosingLayer f n s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [closingLayerHistory,mapClosingLayer,scenarioHistory] using
      congrArg (fun h : EnvHistory I₁ I₂ => h++[⟨s.2.1,s.2.2.1,s.2.2.2,(),()⟩]) (ih s.1)

/-- No scenario from a surviving root is lost by restricting the family. -/
theorem activeClosingLayer_preimage {H I₁ I₂ : Type} (active : H → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) (alive : active (closingLayerRoot n s) = true) :
    ∃ t : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n,
      mapClosingLayer Subtype.val n t = s := by
  induction n with
  | zero => exact ⟨⟨s,alive⟩,rfl⟩
  | succ n ih =>
    obtain ⟨t,eq⟩ := ih s.1 alive
    exact ⟨(t,s.2),Prod.ext eq rfl⟩

theorem activeClosingLayer_root_alive {H I₁ I₂ : Type} (active : H → Bool)
    (n : Nat) (s : ClosingLayer (ActiveClosingRoots active) I₁ I₂ n) :
    active (closingLayerRoot n (mapClosingLayer Subtype.val n s)) = true := by
  rw [closingLayerRoot_map]
  exact (closingLayerRoot n s).property

def restrictClosingPolicy {H K I₁ I₂ O₁ O₂ : Type} {D : Nat}
    (f : H → K) (out : ClosingPolicy K I₁ I₂ O₁ O₂ D) : ClosingPolicy H I₁ I₂ O₁ O₂ D :=
  fun n s => out n (mapClosingLayer f (n.val+1) s)

def restrictClosingFlags {H K I₁ I₂ : Type} {D : Nat}
    (f : H → K) (table : ClosingFlagTable K I₁ I₂ D) : ClosingFlagTable H I₁ I₂ D :=
  fun n s => table n (mapClosingLayer f n.val s)

theorem closingFlagAt_restrict {H K I₁ I₂ : Type} {D : Nat}
    (f : H → K) (table : ClosingFlagTable K I₁ I₂ D)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingFlagAt (restrictClosingFlags f table) n s = closingFlagAt table n (mapClosingLayer f n s) := by
  unfold closingFlagAt
  split <;> rfl

theorem closingActive_map {H K I₁ I₂ : Type} (f : H → K)
    (boundary : (n : Nat) → ClosingLayer K I₁ I₂ n → Bool)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingActive (fun m t => boundary m (mapClosingLayer f m t)) n s =
      closingActive boundary n (mapClosingLayer f n s) := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n _ ih => simp only [closingActive,mapClosingLayer,ih]

theorem closingActive_restrict {H K I₁ I₂ : Type} {D : Nat}
    (f : H → K) (table : ClosingFlagTable K I₁ I₂ D)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingActive (closingFlagAt (restrictClosingFlags f table)) n s =
      closingActive (closingFlagAt table) n (mapClosingLayer f n s) := by
  have flags : closingFlagAt (restrictClosingFlags f table) =
      fun m t => closingFlagAt table m (mapClosingLayer f m t) := by
    funext m t
    exact closingFlagAt_restrict f table m t
  rw [flags,closingActive_map]

theorem closingFirstExit_restrict {H K I₁ I₂ : Type} {D : Nat}
    (f : H → K) (table : ClosingFlagTable K I₁ I₂ D)
    (n : Nat) (s : ClosingLayer H I₁ I₂ n) :
    closingFirstExit (closingFlagAt (restrictClosingFlags f table)) n s =
      closingFirstExit (closingFlagAt table) n (mapClosingLayer f n s) := by
  have flags : closingFlagAt (restrictClosingFlags f table) =
      fun m t => closingFlagAt table m (mapClosingLayer f m t) := by
    funext m t
    exact closingFlagAt_restrict f table m t
  rw [flags]
  cases n with
  | zero => rfl
  | succ n => simp only [closingFirstExit,closingActive_map]

/-- Restriction preserves the computed monitor labels exactly; it never
restarts the monitor or changes the source from which a label is replayed. -/
theorem closingLayerLabels_restrict {H K I₁ I₂ O₁ O₂ Q : Type} {D : Nat}
    (f : H → K) (step : Q → (I₁ × I₂ × Graph) → (O₁ × O₂) → Q) (initial : K → Q)
    (out : ClosingPolicy K I₁ I₂ O₁ O₂ D)
    (n : Nat) (bound : n ≤ D) (s : ClosingLayer H I₁ I₂ n) :
    closingLayerLabels step (initial ∘ f) (restrictClosingPolicy f out) n bound s =
      closingLayerLabels step initial out n bound (mapClosingLayer f n s) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [closingLayerLabels,restrictClosingPolicy,mapClosingLayer,ih]

/-- Reuse the original local-policy equivalence for the restricted source
observation matrix, rather than introducing another coherence test. -/
theorem restrictClosingPolicy_coherent {H K I₁ I₂ O₁ O₂ : Type} {D : Nat}
    [DecidableEq I₁] [DecidableEq I₂] [Nonempty O₁] [Nonempty O₂]
    (past : K → EnvHistory I₁ I₂) (shape : InputShape K) (rep : RepresentsInputShape past shape)
    (L : Nat) (depth : ∀ k, List.length (past k) = L)
    (f : H → K) (out : ClosingPolicy K I₁ I₂ O₁ O₂ D) (coherent : ClosingPolicyCoherent shape out) :
    ClosingPolicyCoherent (restrictInputShape shape f) (restrictClosingPolicy f out) := by
  obtain ⟨σ,correct⟩ := (closingPolicyCoherent_iff_local past shape rep L depth out).mp coherent
  apply (closingPolicyCoherent_iff_local (past ∘ f) (restrictInputShape shape f)
    (restrictInputShape_exact past shape rep f) L (fun h => depth (f h)) _).mpr
  refine ⟨σ,fun n s => ?_⟩
  simpa only [closingLayerHistory_map,restrictClosingPolicy] using correct n (mapClosingLayer f (n.val+1) s)

/-- The mask and a bundle over its surviving roots still form a fixed finite
alphabet. There are no roots added when the activity mask is updated. -/
theorem activeRootBundle_finite {H I₁ I₂ O₁ O₂ Q : Type}
    [Fintype H] [Fintype I₁] [Fintype I₂] [Fintype O₁] [Fintype O₂] [Fintype Q]
    [DecidableEq H] [DecidableEq I₁] [DecidableEq I₂] (B D : Nat) :
    Finite (Σ active : H → Bool, FirstExitBundle (ActiveClosingRoots active) I₁ I₂ O₁ O₂ Q B D) := by
  infer_instance

end Characterisation
