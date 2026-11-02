/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.ConsensusProposals
import DistributedSynthesis.Library.Distributed.LeaderPhases.RollingWindowSources

/-! `main.tex`, `lem:bounded-common-view`, following its broadcaster proof.
Fresh proposal values are independent of the application input alphabets.
No missing-extension property or geometric interval argument is used here.
-/

namespace Characterisation.ComponentTrees
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
open Characterisation.ComponentGames.Consensus
noncomputable section
set_option maxHeartbeats 1800000

variable {V I₁ I₂ H : Type}

/-- A bounded consensus algorithm gives valid common decisions on every
live finite graph word, by extending that word to an admitted execution. -/
theorem consensus_proposal_decisions
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (σ : StrategyPair V V (Option V) (Option V)) (solves : SolvesBy σ A D)
    (x : Proc → V) (gs : List Graph) (len : gs.length = D) (live : LivePrefix A gs) :
    ∃ o : Proc → V, (task V).allows x o ∧
      ∀ p, strategyOutput σ p (currentView p (proposalHistory x gs)) = some (o p) := by
  obtain ⟨word, admitted, pref⟩ := live
  obtain ⟨o, valid, outputs⟩ := solves.decidesAt (proposalEnvironment x word) admitted
  have inputs : proposals (proposalEnvironment x word) = x := by
    funext p
    cases p <;> rfl
  refine ⟨o, by simpa only [inputs] using valid, ?_⟩
  intro p
  have out := outputs p
  rw [outputAt_view, show D-1+1 = D by omega, proposalEnvironment_prefix,
    ← len, pref] at out
  exact out

/-- Agreement on two distinct proposals selects one process. -/
theorem consensus_selects_process
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (σ : StrategyPair V V (Option V) (Option V)) (solves : SolvesBy σ A D)
    (ids : Proc → V) (gs : List Graph) (len : gs.length = D) (live : LivePrefix A gs) :
    ∃ selected : Proc, ∀ p,
      strategyOutput σ p (currentView p (proposalHistory ids gs)) = some (ids selected) := by
  obtain ⟨o, valid, outputs⟩ := consensus_proposal_decisions A D positive σ solves ids gs len live
  obtain ⟨agree, first | second⟩ := valid
  · refine ⟨.one, fun p => ?_⟩
    cases p
    · exact (outputs .one).trans (congrArg some first)
    · exact (outputs .two).trans (congrArg some (agree.symm.trans first))
  · refine ⟨.two, fun p => ?_⟩
    cases p
    · exact (outputs .one).trans (congrArg some second)
    · exact (outputs .two).trans (congrArg some (agree.symm.trans second))

/-- The English broadcaster argument: if i received nothing, replace the
other proposal by i's. Its decision cannot change, and validity forces i. -/
theorem consensus_selected_of_blind
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (σ : StrategyPair V V (Option V) (Option V)) (solves : SolvesBy σ A D)
    (ids : Proc → V) (distinct : Function.Injective ids)
    (gs : List Graph) (len : gs.length = D) (live : LivePrefix A gs)
    (selected i : Proc)
    (decision : strategyOutput σ i (currentView i (proposalHistory ids gs)) = some (ids selected))
    (blind : D ≤ silentAge (currentView i (proposalHistory ids gs))) : selected = i := by
  let uniform : Proc → V := fun _ => ids i
  have same := blind_proposals_equal ids uniform gs i rfl (by omega)
  obtain ⟨o, valid, outputs⟩ := consensus_proposal_decisions A D positive σ solves uniform gs len live
  have first : o .one = ids i := valid.2.elim id id
  have all (p : Proc) : o p = ids i := by
    cases p
    · exact first
    · exact valid.1.symm.trans first
  apply distinct
  apply Option.some.inj
  exact decision.symm.trans ((congrArg (strategyOutput σ i) same).trans
    ((outputs i).trans (congrArg some (all i))))

/-- Simulating fixed proposals ignores the application's input values. -/
theorem constant_proposal_view (ids : Proc → V) (h : EnvHistory I₁ I₂) (p : Proc) :
    InputAlphabetRelabeling.view (fun _ : I₁ => ids .one) (fun _ : I₂ => ids .two)
      (currentView p h) = currentView p (proposalHistory ids (History.graphSequence h)) := by
  induction h using List.reverseRecOn generalizing p with
  | nil => cases p <;> rfl
  | append_singleton h r ih =>
    simp only [History.graphSequence, List.map_append, List.map_singleton, proposalHistory_append]
    change InputAlphabetRelabeling.view _ _ (currentView p (History.append h r)) =
      currentView p (History.append _ _)
    cases p
    all_goals simp only [currentView_one_append, currentView_two_append]
    all_goals cases r.graph <;>
      simp [InputAlphabetRelabeling.view, InputAlphabetRelabeling.payload, Proc.other, ih,
        History.graphSequence]

/-- Equal final views determine the local view in a fixed-input simulation
of the last D rounds, even if the earlier histories differ. -/
theorem proposal_suffix_views (ids : Proc → V)
    (h k u v : EnvHistory I₁ I₂) (len : u.length = v.length) (p : Proc)
    (same : currentView p (h ++ u) = currentView p (k ++ v)) :
    currentView p (proposalHistory ids (History.graphSequence u)) =
      currentView p (proposalHistory ids (History.graphSequence v)) := by
  have suffix := append_preserves_views h k [] [] (fun _ _ => rfl) u v len p same
  simp only [List.nil_append] at suffix
  simpa only [constant_proposal_view] using
    congrArg (InputAlphabetRelabeling.view (fun _ : I₁ => ids .one) (fun _ : I₂ => ids .two)) suffix

/-- A silent final block remains silent when simulated from empty views. -/
theorem proposal_suffix_blind (ids : Proc → V) (h u : EnvHistory I₁ I₂) (p : Proc)
    (blind : List.length u ≤ silentAge (currentView p (h ++ u))) :
    List.length u ≤ silentAge (currentView p (proposalHistory ids (History.graphSequence u))) := by
  induction u using List.reverseRecOn generalizing p with
  | nil => exact Nat.zero_le _
  | append_singleton u r ih =>
    simp only [List.length_append, List.length_singleton, ← List.append_assoc] at blind ⊢
    simp only [History.graphSequence, List.map_append, List.map_singleton, proposalHistory_append]
    change List.length u + 1 ≤ silentAge (currentView p (History.append (h ++ u) r)) at blind
    change List.length u + 1 ≤ silentAge (currentView p (History.append _ _))
    cases p
    all_goals simp only [currentView_one_append, currentView_two_append] at blind ⊢
    all_goals cases hg : r.graph <;> simp only [hg, silentAge] at blind ⊢
    all_goals first
      | omega
      | exact Nat.add_le_add_right (ih _ (by omega)) 1

/-- The core of the new proof: label each edge by its selected broadcaster
and that process's old view. Sharing either endpoint preserves this label.
The family may be any connected subgraph, not necessarily a maximal component. -/
theorem broadcaster_common_roots [Nontrivial V]
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ g, LivePrefix A g → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A g) D)
    (past suffix : H → EnvHistory I₁ I₂) (round : Nat)
    (depth : ∀ e, List.length (past e) = round) (lengths : ∀ e, List.length (suffix e) = D)
    (alive : ∀ e, LivePrefix A (History.graphSequence (past e ++ suffix e)))
    (nonempty : Nonempty H)
    (connected : ∀ e f, Relation.ReflTransGen
      (fun x y => ∃ i, currentView i (past x ++ suffix x) = currentView i (past y ++ suffix y)) e f) :
    ∃ p, ∀ e f, currentView p (past e) = currentView p (past f) := by
  classical
  obtain ⟨a, b, different⟩ := exists_pair_ne V
  let ids : Proc → V := fun p => match p with | .one => a | .two => b
  have distinct : Function.Injective ids := by
    intro p q same
    cases p <;> cases q <;> simp_all [ids]
  let alg (g : List Graph) : StrategyPair V V (Option V) (Option V) :=
    if hg : LivePrefix A g then (consensus g hg).choose else ⟨fun _ => none, fun _ => none⟩
  have solved (g) (hg : LivePrefix A g) : SolvesBy (alg g) (Residual A g) D := by
    simp only [alg, dif_pos hg]
    exact (consensus g hg).choose_spec
  have livePast e : LivePrefix A (History.graphSequence (past e)) := by
    apply livePrefix_closed A _ (History.graphSequence (suffix e))
    simpa only [History.graphSequence, List.map_append] using alive e
  have liveSuffix e : LivePrefix (Residual A (History.graphSequence (past e)))
      (History.graphSequence (suffix e)) := by
    obtain ⟨w, hw, pref⟩ := live_extension_residual A
      (History.graphSequence (past e)) (History.graphSequence (suffix e))
      (by simpa only [History.graphSequence, List.map_append] using alive e)
    exact ⟨w, hw, pref⟩
  have gslen e : (History.graphSequence (suffix e)).length = D := by
    simpa only [History.graphSequence, List.length_map] using lengths e
  have selection e := consensus_selects_process _ D positive _
    (solved _ (livePast e)) ids _ (gslen e) (liveSuffix e)
  let choose (e : H) : Proc := (selection e).choose
  have decision e i : strategyOutput (alg (History.graphSequence (past e))) i
      (currentView i (proposalHistory ids (History.graphSequence (suffix e)))) = some (ids (choose e)) :=
    (selection e).choose_spec i
  have blindChoice e i (blind : D ≤ silentAge (currentView i (past e ++ suffix e))) : choose e = i :=
    consensus_selected_of_blind _ D positive _ (solved _ (livePast e)) ids distinct _
      (gslen e) (liveSuffix e) (choose e) i (decision e i)
      (by simpa only [lengths] using proposal_suffix_blind ids (past e) (suffix e) i (by simpa only [lengths] using blind))
  let label (e : H) : (p : Proc) × View I₁ I₂ p := ⟨choose e, currentView (choose e) (past e)⟩
  have takeBoundary e : (past e ++ suffix e).take round = past e := by
    conv_lhs => rw [← depth e]
    exact List.take_left
  have adjacent e f (i : Proc)
      (same : currentView i (past e ++ suffix e) = currentView i (past f ++ suffix f)) : label e = label f := by
    by_cases recent : silentAge (currentView i (past e ++ suffix e)) < D
    · have roots : past e = past f := by
        have eq := equal_view_recent_prefix i _ _ same round
          (by simpa only [List.length_append, depth, lengths, Nat.add_sub_cancel_left] using recent)
        simpa only [takeBoundary] using eq
      have simulated := proposal_suffix_views ids (past e) (past f) (suffix e) (suffix f)
        ((lengths e).trans (lengths f).symm) i same
      have choices : choose e = choose f := distinct (Option.some.inj
        ((decision e i).symm.trans (by rw [roots, simulated]; exact decision f i)))
      change Sigma.mk (choose e) (currentView (choose e) (past e)) = _
      rw [choices, roots]
    · have ce := blindChoice e i (by omega)
      have cf := blindChoice f i (by rw [← same]; omega)
      have old := equal_currentView_take i _ _ same round (by simp only [List.length_append, depth, lengths]; omega)
      have old' : currentView i (past e) = currentView i (past f) := by
        simpa only [takeBoundary] using old
      dsimp only [label]
      rw [ce, cf, old']
  have equal e f : label e = label f := by
    have path := connected e f
    induction path with
    | refl => rfl
    | @tail b c _ edge ih =>
      obtain ⟨i, same⟩ := edge
      exact ih.trans (adjacent b c i same)
  let anchor : H := nonempty.some
  refine ⟨choose anchor, fun e f => ?_⟩
  have each (e : H) : currentView (choose anchor) (past anchor) = currentView (choose anchor) (past e) := by
    have eq := equal anchor e
    have extract (p q : Proc) (h k : EnvHistory I₁ I₂)
        (eq : (Sigma.mk p (currentView p h) : (i : Proc) × View I₁ I₂ i) =
          Sigma.mk q (currentView q k)) : currentView p h = currentView p k := by
      have pq : p = q := congrArg Sigma.fst eq
      subst q
      exact eq_of_heq (Sigma.mk.inj_iff.mp eq).2
    exact extract _ _ _ _ eq
  exact (each e).symm.trans (each f)

/-- `lem:bounded-common-view`, at the stated earlier round r-D. -/
theorem bounded_common_view [Nontrivial V]
    (A : Set (Nat → Graph)) (D : Nat) (positive : 0 < D)
    (consensus : ∀ g, LivePrefix A g → ∃ σ : StrategyPair V V (Option V) (Option V),
      SolvesBy σ (Residual A g) D)
    (r : Nat) (deep : D ≤ r) (C : Set (EnvHistory I₁ I₂)) (nonempty : C.Nonempty)
    (lengths : ∀ h ∈ C, List.length h = r)
    (alive : ∀ h ∈ C, LivePrefix A (History.graphSequence h))
    (connected : ∀ e f : C, Relation.ReflTransGen
      (fun x y : C => ∃ p, currentView p x.val = currentView p y.val) e f) :
    ∃ p, ∀ h ∈ C, ∀ k ∈ C,
      currentView p (h.take (r-D)) = currentView p (k.take (r-D)) := by
  have ne : Nonempty C := ⟨⟨nonempty.choose, nonempty.choose_spec⟩⟩
  obtain ⟨p, common⟩ := broadcaster_common_roots A D positive consensus
    (fun e : C => e.val.take (r-D)) (fun e : C => e.val.drop (r-D)) (r-D)
    (fun e => by simp [lengths e.val e.property])
    (fun e => by simp only [List.length_drop, lengths e.val e.property]; omega)
    (fun e => by simpa only [List.take_append_drop] using alive e.val e.property) ne
    (by simpa only [List.take_append_drop] using connected)
  exact ⟨p, fun h hh k hk => common ⟨h, hh⟩ ⟨k, hk⟩⟩

end
end Characterisation.ComponentTrees
