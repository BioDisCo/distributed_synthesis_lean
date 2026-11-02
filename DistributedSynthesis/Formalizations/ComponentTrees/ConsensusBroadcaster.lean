/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.ComponentTrees.CommonView
import DistributedSynthesis.Library.Distributed.LeaderPhases.CoordinatorDelivery

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.Consensus

/-- `lem:cons:means:broadcaster`. Evaluate the two local decision functions
at round R. They agree on a process whose message was delivered to the other
process during these same R rounds. The application inputs are arbitrary
and are ignored by the simulation of two distinct consensus proposals. -/
theorem consensus_broadcaster_of_pos {V I₁ I₂ : Type} [Nontrivial V]
    (A : Set (Nat → Graph)) (R : Nat) (positive : 0 < R)
    (σ : StrategyPair V V (Option V) (Option V)) (solves : SolvesBy σ A R) :
    ∃ select : StrategyPair I₁ I₂ Proc Proc, ∀ h : EnvHistory I₁ I₂,
      h.length = R → LivePrefix A (History.graphSequence h) →
      ∃ p : Proc, select.one (currentView .one h) = p ∧ select.two (currentView .two h) = p ∧
        ∃ a : List Graph, ∃ g : Graph, ∃ b : List Graph,
          History.graphSequence h = a ++ [g] ++ b ∧ DeliversFrom p g := by
  classical
  obtain ⟨a, b, different⟩ := exists_pair_ne V
  let ids : Proc → V := fun p => match p with | .one => a | .two => b
  have injective : Function.Injective ids := by
    intro p q eq
    cases p <;> cases q <;> simp_all [ids]
  let decode (v : Option V) : Proc := if v = some a then .one else .two
  have decoded (p : Proc) : decode (some (ids p)) = p := by
    cases p <;> simp [decode, ids, different.symm]
  let select : StrategyPair I₁ I₂ Proc Proc :=
    ⟨fun v => decode (σ.one (InputAlphabetRelabeling.view (fun _ => a) (fun _ => b) v)),
     fun v => decode (σ.two (InputAlphabetRelabeling.view (fun _ => a) (fun _ => b) v))⟩
  refine ⟨select, fun h len live => ?_⟩
  let gs := History.graphSequence h
  have length : gs.length = R := by simpa [gs, History.graphSequence] using len
  obtain ⟨p, outputs⟩ := consensus_selects_process A R positive σ solves ids gs length live
  have localDecision (q : Proc) :
      strategyOutput σ q (InputAlphabetRelabeling.view (fun _ : I₁ => a) (fun _ : I₂ => b)
        (currentView q h)) = some (ids p) := by
    have eq := constant_proposal_view ids h q
    change InputAlphabetRelabeling.view (fun _ : I₁ => a) (fun _ : I₂ => b)
      (currentView q h) = currentView q (proposalHistory ids gs) at eq
    rw [eq]
    exact outputs q
  refine ⟨p, ?_, ?_, ?_⟩
  · change decode (strategyOutput σ .one _) = p
    rw [localDecision, decoded]
  · change decode (strategyOutput σ .two _) = p
    rw [localDecision, decoded]
  · have young : silentAge (currentView p.other (proposalHistory ids gs)) < R := by
      by_contra old
      have eq := consensus_selected_of_blind A R positive σ solves ids injective gs length live
        p p.other (outputs p.other) (by omega)
      cases p <;> simp [Proc.other] at eq
    have graphYoung : silentAge (graphView p.other gs) < R := by
      rw [← silentAge_erase, eraseView_current] at young
      simpa [History.graphSequence, proposalHistory, List.map_map, Function.comp_def] using young
    obtain ⟨before, g, after, eq, _, received⟩ := recent_receive_factor p.other gs R (by omega) graphYoung
    exact ⟨before,g,after,eq,received⟩

/-- The broadcaster statement also covers a zero bound: for a nontrivial
proposal alphabet that case forces the adversary to be empty. -/
theorem consensus_broadcaster {V I₁ I₂ : Type} [Nontrivial V]
    (A : Set (Nat → Graph)) (R : Nat)
    (σ : StrategyPair V V (Option V) (Option V)) (solves : SolvesBy σ A R) :
    ∃ select : StrategyPair I₁ I₂ Proc Proc, ∀ h : EnvHistory I₁ I₂,
      h.length = R → LivePrefix A (History.graphSequence h) →
      ∃ p : Proc, select.one (currentView .one h) = p ∧ select.two (currentView .two h) = p ∧
        ∃ a : List Graph, ∃ g : Graph, ∃ b : List Graph,
          History.graphSequence h = a ++ [g] ++ b ∧ DeliversFrom p g := by
  classical
  by_cases positive : 0 < R
  · exact consensus_broadcaster_of_pos A R positive σ solves
  · refine ⟨⟨fun _ => .one, fun _ => .one⟩, fun h _ live => ?_⟩
    obtain ⟨word, admitted, _⟩ := live
    let proposal : V := Classical.choice inferInstance
    obtain ⟨n, before, _⟩ := solves.bound (proposalEnvironment (fun _ => proposal) word) admitted .one
    omega

end Characterisation.ComponentTrees
