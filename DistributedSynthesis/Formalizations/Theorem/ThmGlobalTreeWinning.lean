/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmGlobalTreeTracking
import DistributedSynthesis.Formalizations.Theorem.ThmGlobalJournalChecker

/-!
# The tree strategy wins the boundary game

Stage 1 of the squeeze: every consistent play of the tree strategy
walks an infinite branch of the journal tree.  Each play step emits at
most one tree direction, and legality forces an emission within two
steps, so the walked length is a monotone unbounded step-one function
of time and hence surjective.  Choosing witnesses of surjectivity
yields the branch itself, with the walked nodes as exactly its
prefixes.  Acceptance of the tree then transfers the branch parity to
the sequence of automaton priorities along the walked nodes.
-/

set_option linter.unusedSectionVars false

namespace DistributedSynthesis

/-- Min-even parity is preserved under monotone surjective reindexing
by a map dominated by the identity. -/
theorem natSeqMinEvenParity_comp_of_monotone_surjective
    {s f : Nat -> Nat} (hmono : Monotone f) (hle : ∀ n : Nat, f n ≤ n)
    (hsurj : ∀ k : Nat, ∃ n : Nat, f n = k)
    (h : NatSeqMinEvenParity s) :
    NatSeqMinEvenParity (fun n => s (f n)) := by
  have hseen :
      ∀ p : Nat,
        NatSeqSeenInfinitelyOften (fun n => s (f n)) p ↔
          NatSeqSeenInfinitelyOften s p := by
    intro p
    constructor
    · intro hinf n
      obtain ⟨m, hm⟩ := hsurj n
      obtain ⟨k, hk, hval⟩ := hinf m
      exact ⟨f k, by rw [← hm]; exact hmono hk, hval⟩
    · intro hinf n
      obtain ⟨k, hk, hval⟩ := hinf n
      obtain ⟨m, hm⟩ := hsurj k
      refine ⟨m, ?_, by show s (f m) = p; rw [hm]; exact hval⟩
      calc n ≤ k := hk
        _ = f m := hm.symm
        _ ≤ m := hle m
  obtain ⟨p, hpEven, hpSeen, hpMin⟩ := h
  exact
    ⟨p, hpEven, (hseen p).mpr hpSeen,
      fun q hq => hpMin q ((hseen q).mp hq)⟩

universe u v x y s

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

namespace DetParityAutomaton

variable
  {A :
    DetParityAutomaton.{max u v x y, s}
      (RoundRecord In₁ In₂ Graph Out₁ Out₂)}

variable
  (t :
    TransitionRationalTree.{max u v s, max u v x y s, s}
      (GlobalJournalBranch (In₁ := In₁) A)
      (GlobalJournalLabel (In₁ := In₁) A))

variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂] [DecidableEq A.State]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [DecidableEq t.Control] [Inhabited t.Control]

/-- Each play step emits at most one tree direction. -/
theorem stepDirections_length_le
    (source target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)) :
    (stepDirections t source target).length ≤ 1 := by
  rcases source with atom | ⟨pair, plan⟩ | data | data | data | data <;>
    rcases target with atom' | ⟨pair', plan'⟩ | data' | data' | data' |
      data' <;>
      simp only [stepDirections] <;>
        first
          | simp
          | (split <;> simp)

/-- Walked nodes form a prefix chain. -/
theorem playNodes_prefix
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    {m n : Nat} (h : m ≤ n) :
    playNodes t path m <+: playNodes t path n := by
  induction n with
  | zero =>
      rw [Nat.le_zero.mp h]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · exact
          (ih (Nat.lt_succ_iff.mp hlt)).trans
            ⟨stepDirections t (path n) (path (n + 1)), rfl⟩
      · rw [Nat.le_antisymm h hge]

/-- The walked length grows by at most one per step. -/
theorem playNodes_length_le_succ
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) :
    (playNodes t path (n + 1)).length ≤
      (playNodes t path n).length + 1 := by
  show (playNodes t path n ++ _).length ≤ _
  rw [List.length_append]
  have := stepDirections_length_le t (path n) (path (n + 1))
  omega

/-- The walked length is monotone. -/
theorem playNodes_length_mono
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    {m n : Nat} (h : m ≤ n) :
    (playNodes t path m).length ≤ (playNodes t path n).length :=
  (playNodes_prefix t path h).length_le

/-- The walked length is dominated by time. -/
theorem playNodes_length_le
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (n : Nat) :
    (playNodes t path n).length ≤ n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
      have := playNodes_length_le_succ t path n
      omega

/-- Legal steps from a boundary reach a committed position. -/
theorem step_bnd_committed
    {atom : A.State × A.State}
    {target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) (Sum.inl atom) target) :
    ∃ plan, target = Sum.inr (Sum.inl ((atom.1, atom.1), plan)) :=
  hstep

/-- Legal steps from non-boundary positions emit one direction. -/
theorem stepDirections_length_of_not_bnd
    {source target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) source target)
    (hnb : ∀ atom : A.State × A.State, source ≠ Sum.inl atom) :
    (stepDirections t source target).length = 1 := by
  rcases source with atom | ⟨⟨q, mn⟩, plan⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · exact absurd rfl (hnb atom)
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · subst hnext
      simp only [boundaryBothTarget]
      rfl
    · subst hnext
      simp only [boundaryOpenLeftTarget]
      rw [stepDirections_committed_blockL t _ _ _ ⟨move, rfl⟩]
      rfl
    · subst hnext
      simp only [boundaryOpenRightTarget]
      rw [stepDirections_committed_blockR t _ _ _ ⟨move, rfl⟩]
      rfl
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · subst hnext
      simp only [leftContinueTarget]
      rw [stepDirections_blockL_blockL t _ _ ⟨move, rfl⟩]
      rfl
    · subst hnext
      simp only [leftCloseTarget]
      rfl
    · subst hnext
      simp only [leftReverseTarget]
      rw [stepDirections_blockL_revR t _ _ ⟨move, rfl⟩]
      rfl
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · subst hnext
      simp only [rightContinueTarget]
      rw [stepDirections_blockR_blockR t _ _ ⟨move, rfl⟩]
      rfl
    · subst hnext
      simp only [rightCloseTarget]
      rfl
    · subst hnext
      simp only [rightReverseTarget]
      rw [stepDirections_blockR_revL t _ _ ⟨move, rfl⟩]
      rfl
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · subst hnext
      simp only [revLeftContinueTarget]
      rw [stepDirections_revL_revL t _ _ ⟨move, rfl⟩]
      rfl
    · subst hnext
      simp only [revLeftCloseTarget]
      rfl
    · subst hnext
      simp only [revLeftReverseTarget]
      rw [stepDirections_revL_revR t _ _ ⟨move, rfl⟩]
      rfl
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · subst hnext
      simp only [revRightContinueTarget]
      rw [stepDirections_revR_revR t _ _ ⟨move, rfl⟩]
      rfl
    · subst hnext
      simp only [revRightCloseTarget]
      rfl
    · subst hnext
      simp only [revRightReverseTarget]
      rw [stepDirections_revR_revL t _ _ ⟨move, rfl⟩]
      rfl

/-- The walked length strictly grows over any two legal steps. -/
theorem playNodes_length_lt_add_two
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (n : Nat) :
    (playNodes t path n).length < (playNodes t path (n + 2)).length := by
  have hgrow :
      ∀ m : Nat,
        (∀ atom : A.State × A.State, path m ≠ Sum.inl atom) ->
          (playNodes t path m).length < (playNodes t path (m + 1)).length := by
    intro m hnb
    show
      (playNodes t path m).length <
        (playNodes t path m ++
          stepDirections t (path m) (path (m + 1))).length
    rw [List.length_append,
      stepDirections_length_of_not_bnd t (hplay m) hnb]
    omega
  by_cases hbnd : ∀ atom : A.State × A.State, path n ≠ Sum.inl atom
  · exact
      Nat.lt_of_lt_of_le (hgrow n hbnd)
        (playNodes_length_mono t path (by omega))
  · push Not at hbnd
    obtain ⟨atom, hpos⟩ := hbnd
    have hstep := hplay n
    rw [hpos] at hstep
    obtain ⟨plan, hnext⟩ := step_bnd_committed t hstep
    refine
      Nat.lt_of_le_of_lt (playNodes_length_mono t path (by omega))
        (hgrow (n + 1) ?_)
    intro atom' h
    rw [hnext] at h
    exact absurd h (by simp)

/-- The walked length is unbounded along legal plays. -/
theorem exists_le_playNodes_length
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (k : Nat) :
    ∃ n : Nat, k ≤ (playNodes t path n).length := by
  induction k with
  | zero => exact ⟨0, Nat.zero_le _⟩
  | succ k ih =>
      obtain ⟨n, hn⟩ := ih
      exact
        ⟨n + 2,
          Nat.lt_of_le_of_lt hn (playNodes_length_lt_add_two t path hplay n)⟩

/-- The walked length attains every value along legal plays. -/
theorem exists_playNodes_length_eq
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (k : Nat) :
    ∃ n : Nat, (playNodes t path n).length = k := by
  have hex := exists_le_playNodes_length t path hplay k
  have hfind := Nat.find_spec hex
  refine ⟨Nat.find hex, Nat.le_antisymm ?_ hfind⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
  · rw [hzero]
    show (playNodes t path 0).length ≤ k
    exact Nat.zero_le k
  · have hprev :
        ¬ k ≤ (playNodes t path (Nat.find hex - 1)).length :=
      Nat.find_min hex (by omega)
    have hstep :
        (playNodes t path (Nat.find hex - 1 + 1)).length ≤
          (playNodes t path (Nat.find hex - 1)).length + 1 :=
      playNodes_length_le_succ t path (Nat.find hex - 1)
    have hind : Nat.find hex - 1 + 1 = Nat.find hex := by omega
    rw [hind] at hstep
    omega

/-- The infinite branch walked by a legal play. -/
noncomputable def playBranch
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (k : Nat) : GlobalJournalBranch (In₁ := In₁) A :=
  (playNodes t path
      (Classical.choose (exists_playNodes_length_eq t path hplay (k + 1))))[k]'
    (by
      rw [Classical.choose_spec (exists_playNodes_length_eq t path hplay (k + 1))]
      omega)

/-- Elements of walked nodes are branch values. -/
theorem playNodes_getElem_eq_playBranch
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (n k : Nat) (hk : k < (playNodes t path n).length) :
    (playNodes t path n)[k] = playBranch t path hplay k := by
  have hspec :=
    Classical.choose_spec (exists_playNodes_length_eq t path hplay (k + 1))
  set m := Classical.choose (exists_playNodes_length_eq t path hplay (k + 1))
  rcases Nat.le_total m n with hle | hle
  · have hpre := playNodes_prefix t path hle
    exact (List.IsPrefix.getElem hpre (by omega)).symm
  · have hpre := playNodes_prefix t path hle
    exact List.IsPrefix.getElem hpre hk

/-- Walked nodes are exactly the branch prefixes at their lengths. -/
theorem playNodes_eq_branchNode
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (n : Nat) :
    branchNode (playBranch t path hplay)
        (playNodes t path n).length =
      playNodes t path n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hlen :
          (playNodes t path (n + 1)).length =
            (playNodes t path n).length +
              (stepDirections t (path n) (path (n + 1))).length := by
        show (playNodes t path n ++ _).length = _
        rw [List.length_append]
      have hle := stepDirections_length_le t (path n) (path (n + 1))
      match hdirs : stepDirections t (path n) (path (n + 1)) with
      | [] =>
          have hnode :
              playNodes t path (n + 1) = playNodes t path n := by
            show playNodes t path n ++ _ = _
            rw [hdirs, List.append_nil]
          rw [hnode]
          exact ih
      | [branch] =>
          have hnode :
              playNodes t path (n + 1) =
                playNodes t path n ++ [branch] := by
            show playNodes t path n ++ _ = _
            rw [hdirs]
          have hlen' :
              (playNodes t path (n + 1)).length =
                (playNodes t path n).length + 1 := by
            rw [hnode, List.length_append]
            rfl
          have hbr :
              playBranch t path hplay (playNodes t path n).length =
                branch := by
            have hget :=
              playNodes_getElem_eq_playBranch t path hplay (n + 1)
                (playNodes t path n).length (by omega)
            rw [← hget, List.getElem_eq_iff, hnode]
            simp
          rw [hlen', hnode]
          show
            branchNode (playBranch t path hplay)
                (playNodes t path n).length ++
              [playBranch t path hplay (playNodes t path n).length] = _
          rw [ih, hbr]
      | branch :: branch' :: rest =>
          rw [hdirs] at hle
          exact absurd hle (by simp)

section Acceptance

variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/-- Acceptance yields min-even parity along every branch's prefixes
of the deterministic run. -/
theorem accepts_branch_priorities
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (br : Nat -> GlobalJournalBranch (In₁ := In₁) A) :
    NatSeqMinEvenParity
      (fun k =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            (branchNode br k))) := by
  obtain ⟨run, hrun, hbranch⟩ := hacc
  have hb := hbranch br
  have hfun :
      (fun k =>
          (globalJournalAutomaton A CL CR CC).priority
            (run (branchNode br k))) =
        fun k =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial)) (branchNode br k)) := by
    funext k
    rw [isRun_eq_globalRunIn CL CR CC t.labeledTree run hrun]
    rfl
  rw [← hfun]
  exact hb

/--
Acceptance of the journal tree transfers to the walked nodes: the
automaton priorities of the deterministic run along the walked nodes
satisfy min-even parity.
-/
theorem walked_priorities_min_even_of_accepts
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).Play path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree) :
    NatSeqMinEvenParity
      (fun n =>
        globalJournalPriority A CL CR CC
          (globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            (playNodes t path n))) := by
  have hbase :=
    accepts_branch_priorities t CL CR CC hacc (playBranch t path hplay)
  have hcomp :=
    natSeqMinEvenParity_comp_of_monotone_surjective
      (fun _ _ h => playNodes_length_mono t path h)
      (playNodes_length_le t path)
      (exists_playNodes_length_eq t path hplay) hbase
  have hfun :
      (fun n =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial))
              (branchNode (playBranch t path hplay)
                (playNodes t path n).length))) =
        fun n =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial)) (playNodes t path n)) := by
    funext n
    rw [playNodes_eq_branchNode t path hplay n]
  rw [← hfun]
  exact hcomp

/-! ### The boundary obligation

The G-side of the squeeze: every position carries an obligation, the
priority of the minimum tracked so far (at commitments: of the
boundary state opening the next block).  Along non-boundary steps the
obligation never increases, it is dominated by the emitted priority,
and the step into a boundary emits it.  Hence beyond every round there
is a boundary emitting a priority no larger than the current one.
-/

/-- The pending minimum obligation of a position. -/
def boundaryObligation :
    BoundaryGamePosition (In₁ := In₁) A
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) -> Nat
  | Sum.inl (_, minState) => A.priority minState
  | Sum.inr (Sum.inl ((state, _), _)) => A.priority state
  | Sum.inr (Sum.inr (Sum.inl (_, _, _, _, minState))) =>
      A.priority minState
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl (_, _, _, _, minState)))) =>
      A.priority minState
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
      (_, _, _, _, minState))))) =>
      A.priority minState
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (_, _, _, _, minState))))) =>
      A.priority minState

/-- The tracked minimum never exceeds the incumbent. -/
theorem priority_minPriorityState_le_left (incumbent next : A.State) :
    A.priority (A.minPriorityState incumbent next) ≤
      A.priority incumbent := by
  unfold minPriorityState
  split <;> omega

/-- The tracked minimum never exceeds the newcomer. -/
theorem priority_minPriorityState_le_right (incumbent next : A.State) :
    A.priority (A.minPriorityState incumbent next) ≤
      A.priority next := by
  unfold minPriorityState
  split <;> omega

/-- Boundary predicate of a play round. -/
def IsBoundaryAt
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (m : Nat) : Prop :=
  ∃ atom : A.State × A.State, path m = Sum.inl atom

/-- Along non-boundary steps the obligation never increases. -/
theorem boundaryObligation_step
    {source target :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) source target)
    (hnb : ∀ atom : A.State × A.State, source ≠ Sum.inl atom) :
    boundaryObligation t target ≤ boundaryObligation t source := by
  rcases source with atom | ⟨⟨state, minState⟩, plan⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · exact absurd rfl (hnb atom)
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
      subst hnext
    · exact Nat.le_refl _
    · exact priority_minPriorityState_le_left _ _
    · exact priority_minPriorityState_le_left _ _
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
      subst hnext
    · exact priority_minPriorityState_le_left _ _
    · exact Nat.le_refl _
    · exact priority_minPriorityState_le_left _ _
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
      subst hnext
    · exact priority_minPriorityState_le_left _ _
    · exact Nat.le_refl _
    · exact priority_minPriorityState_le_left _ _
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
      subst hnext
    · exact priority_minPriorityState_le_left _ _
    · exact Nat.le_refl _
    · exact priority_minPriorityState_le_left _ _
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
      subst hnext
    · exact priority_minPriorityState_le_left _ _
    · exact Nat.le_refl _
    · exact priority_minPriorityState_le_left _ _

/-- The obligation is dominated by the emitted priority. -/
theorem boundaryObligation_le_priority
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (m : Nat) :
    boundaryObligation t (path m) ≤
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).priority (path m) := by
  match m with
  | 0 =>
      rw [hplay.1]
      exact Nat.le_refl _
  | m + 1 =>
      have hstep :
          boundaryStep A (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control) (path m) (path (m + 1)) :=
        hplay.2 m
      rcases hpos : path m with atom | ⟨⟨state, minState⟩, plan⟩ |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨plan, chain, control, state, minState⟩ |
        ⟨chain, control, state, minState⟩ |
        ⟨chain, control, state, minState⟩ <;>
          rw [hpos] at hstep
      · obtain ⟨plan, hnext⟩ := step_bnd_committed t hstep
        rw [hnext]
        exact Nat.le_refl _
      · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
          rw [hnext]
        · exact Nat.le_refl _
        · exact priority_minPriorityState_le_right _ _
        · exact priority_minPriorityState_le_right _ _
      · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
          rw [hnext]
        · exact priority_minPriorityState_le_right _ _
        · exact Nat.le_refl _
        · exact priority_minPriorityState_le_right _ _
      · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
          rw [hnext]
        · exact priority_minPriorityState_le_right _ _
        · exact Nat.le_refl _
        · exact priority_minPriorityState_le_right _ _
      · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
          rw [hnext]
        · exact priority_minPriorityState_le_right _ _
        · exact Nat.le_refl _
        · exact priority_minPriorityState_le_right _ _
      · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩ <;>
          rw [hnext]
        · exact priority_minPriorityState_le_right _ _
        · exact Nat.le_refl _
        · exact priority_minPriorityState_le_right _ _

/-- The step into a boundary emits the source obligation. -/
theorem priority_eq_boundaryObligation_of_step_bnd
    {source :
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    {atom : A.State × A.State}
    (hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) source (Sum.inl atom))
    (hnb : ∀ atom' : A.State × A.State, source ≠ Sum.inl atom') :
    A.priority atom.2 = boundaryObligation t source := by
  rcases source with atom' | ⟨⟨state, minState⟩, plan⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨plan, chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · exact absurd rfl (hnb atom')
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · simp only [boundaryBothTarget, Sum.inl.injEq] at hnext
      rw [hnext]
      rfl
    · exact absurd hnext (by simp [boundaryOpenLeftTarget])
    · exact absurd hnext (by simp [boundaryOpenRightTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [leftContinueTarget])
    · simp only [leftCloseTarget, Sum.inl.injEq] at hnext
      rw [hnext]
      rfl
    · exact absurd hnext (by simp [leftReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [rightContinueTarget])
    · simp only [rightCloseTarget, Sum.inl.injEq] at hnext
      rw [hnext]
      rfl
    · exact absurd hnext (by simp [rightReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [revLeftContinueTarget])
    · simp only [revLeftCloseTarget, Sum.inl.injEq] at hnext
      rw [hnext]
      rfl
    · exact absurd hnext (by simp [revLeftReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [revRightContinueTarget])
    · simp only [revRightCloseTarget, Sum.inl.injEq] at hnext
      rw [hnext]
      rfl
    · exact absurd hnext (by simp [revRightReverseTarget])

/--
Beyond every round some boundary emits a priority no larger than the
current one.
-/
theorem exists_boundary_priority_le
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ IsBoundaryAt t path m)
    (m : Nat) :
    ∃ m' : Nat,
      m ≤ m' ∧ IsBoundaryAt t path m' ∧
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path m') ≤
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority (path m) := by
  by_cases hbnd : IsBoundaryAt t path m
  · exact ⟨m, Nat.le_refl m, hbnd, Nat.le_refl _⟩
  · have hex : ∃ j : Nat, IsBoundaryAt t path (m + j) := by
      obtain ⟨m', hm', hbnd'⟩ := hinf m
      exact ⟨m' - m, by rw [show m + (m' - m) = m' by omega]; exact hbnd'⟩
    letI : DecidablePred fun j => IsBoundaryAt t path (m + j) :=
      fun j => Classical.propDecidable _
    have hdpos : 0 < Nat.find hex := by
      rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
      · have hdspec := Nat.find_spec hex
        rw [hzero] at hdspec
        exact absurd hdspec hbnd
      · exact hpos
    have hnb :
        ∀ j : Nat, j < Nat.find hex ->
          ∀ atom : A.State × A.State, path (m + j) ≠ Sum.inl atom := by
      intro j hj atom h
      exact Nat.find_min hex hj ⟨atom, h⟩
    have hchain :
        ∀ j : Nat, j < Nat.find hex ->
          boundaryObligation t (path (m + j)) ≤
            boundaryObligation t (path m) := by
      intro j
      induction j with
      | zero => exact fun _ => Nat.le_refl _
      | succ j ih =>
          intro hj
          have hle := ih (by omega)
          have hstep :
              boundaryStep A (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control) (path (m + j))
                (path (m + j + 1)) :=
            hplay.2 (m + j)
          exact
            Nat.le_trans
              (boundaryObligation_step t hstep (hnb j (by omega))) hle
    obtain ⟨atom, hatom⟩ := Nat.find_spec hex
    refine ⟨m + Nat.find hex, by omega, ⟨atom, hatom⟩, ?_⟩
    have hlast :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (path (m + (Nat.find hex - 1))) (path (m + Nat.find hex)) := by
      have := hplay.2 (m + (Nat.find hex - 1))
      rw [show m + (Nat.find hex - 1) + 1 = m + Nat.find hex by omega]
        at this
      exact this
    rw [hatom] at hlast
    have hemit :=
      priority_eq_boundaryObligation_of_step_bnd t hlast
        (hnb (Nat.find hex - 1) (by omega))
    have hchain' := hchain (Nat.find hex - 1) (by omega)
    have hoblig := boundaryObligation_le_priority t path hplay m
    have hpri :
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority
            (path (m + Nat.find hex)) =
          A.priority atom.2 := by
      rw [hatom]
      rfl
    omega

/-! ### The boundary enumeration -/

section BoundaryEnumeration

variable
  (path :
    Nat ->
      BoundaryGamePosition (In₁ := In₁) A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control))
  (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ IsBoundaryAt t path m)

include hinf in
theorem exists_gt_boundary (n : Nat) :
    ∃ m : Nat, n < m ∧ IsBoundaryAt t path m := by
  obtain ⟨m, hm, h⟩ := hinf (n + 1)
  exact ⟨m, by omega, h⟩

/-- The first boundary round strictly after a round. -/
noncomputable def nextBoundary (n : Nat) : Nat :=
  letI : DecidablePred fun m => n < m ∧ IsBoundaryAt t path m :=
    fun _ => Classical.propDecidable _
  Nat.find (exists_gt_boundary t path hinf n)

theorem nextBoundary_spec (n : Nat) :
    n < nextBoundary t path hinf n ∧
      IsBoundaryAt t path (nextBoundary t path hinf n) := by
  letI : DecidablePred fun m => n < m ∧ IsBoundaryAt t path m :=
    fun _ => Classical.propDecidable _
  unfold nextBoundary
  exact Nat.find_spec (exists_gt_boundary t path hinf n)

theorem nextBoundary_le {n m : Nat} (hm : n < m)
    (hbnd : IsBoundaryAt t path m) :
    nextBoundary t path hinf n ≤ m := by
  letI : DecidablePred fun m' => n < m' ∧ IsBoundaryAt t path m' :=
    fun _ => Classical.propDecidable _
  unfold nextBoundary
  exact Nat.find_min' (exists_gt_boundary t path hinf n) ⟨hm, hbnd⟩

/-- The increasing enumeration of the boundary rounds of a play. -/
noncomputable def boundaryIndex : Nat -> Nat
  | 0 => 0
  | k + 1 => nextBoundary t path hinf (boundaryIndex k)

theorem boundaryIndex_lt_succ (k : Nat) :
    boundaryIndex t path hinf k < boundaryIndex t path hinf (k + 1) :=
  (nextBoundary_spec t path hinf (boundaryIndex t path hinf k)).1

theorem boundaryIndex_strictMono :
    StrictMono (boundaryIndex t path hinf) :=
  strictMono_nat_of_lt_succ (boundaryIndex_lt_succ t path hinf)

theorem le_boundaryIndex (k : Nat) : k ≤ boundaryIndex t path hinf k := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have := boundaryIndex_lt_succ t path hinf k
      omega

theorem boundaryIndex_isBoundary
    (hstart : path 0 = Sum.inl (A.initial, A.initial)) (k : Nat) :
    IsBoundaryAt t path (boundaryIndex t path hinf k) := by
  match k with
  | 0 => exact ⟨(A.initial, A.initial), hstart⟩
  | k + 1 =>
      exact
        (nextBoundary_spec t path hinf (boundaryIndex t path hinf k)).2

/-- The enumeration is exhaustive. -/
theorem exists_boundaryIndex_eq
    {m : Nat} (hbnd : IsBoundaryAt t path m) :
    ∃ k : Nat, boundaryIndex t path hinf k = m := by
  have hex : ∃ k : Nat, m ≤ boundaryIndex t path hinf k :=
    ⟨m, le_boundaryIndex t path hinf m⟩
  have hspec := Nat.find_spec hex
  rcases Nat.eq_or_lt_of_le hspec with heq | hlt
  · exact ⟨Nat.find hex, heq.symm⟩
  · exfalso
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
    · rw [hzero] at hlt
      exact absurd hlt (by simp [boundaryIndex])
    · have hprev : ¬ m ≤ boundaryIndex t path hinf (Nat.find hex - 1) :=
        Nat.find_min hex (by omega)
      have hle :
          boundaryIndex t path hinf (Nat.find hex - 1 + 1) ≤ m := by
        show nextBoundary t path hinf _ ≤ m
        exact nextBoundary_le t path hinf (by omega) hbnd
      rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega] at hle
      omega

end BoundaryEnumeration

/-! ### Regime one: infinitely many boundaries -/

section RegimeOne

variable (CL : LeftThreadChecker (In₁ := In₁) A)
variable (CR : RightThreadChecker (In₁ := In₁) A)
variable (CC : ChainThreadChecker (In₁ := In₁) (A := A))

/-- At a boundary the game emits the automaton priority of the walked
run. -/
theorem walked_priority_eq_of_bnd
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    {n : Nat}
    (htracks : TreeTracks t CL CR CC path (playNodes t path n) n)
    {atom : A.State × A.State} (hpos : path n = Sum.inl atom) :
    globalJournalPriority A CL CR CC
        (globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path n)) =
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).priority (path n) := by
  unfold TreeTracks at htracks
  rw [hpos] at htracks
  obtain ⟨hrun, -⟩ := htracks
  rw [hpos, hrun]
  rfl

/-- Committed positions are preceded by their boundary. -/
theorem bnd_pred_of_committed
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    {m : Nat}
    {pair : A.State × A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (h : path (m + 1) = Sum.inr (Sum.inl (pair, plan))) :
    ∃ atom : A.State × A.State, path m = Sum.inl atom := by
  have hstep :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) (path m) (path (m + 1)) :=
    hplay.2 m
  rcases hpos : path m with atom | ⟨⟨state, minState⟩, plan'⟩ |
    ⟨plan', chain, control, state, minState⟩ |
    ⟨plan', chain, control, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
  · exact ⟨atom, rfl⟩
  all_goals rw [hpos, h] at hstep
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [boundaryBothTarget])
    · exact absurd hnext (by simp [boundaryOpenLeftTarget])
    · exact absurd hnext (by simp [boundaryOpenRightTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [leftContinueTarget])
    · exact absurd hnext (by simp [leftCloseTarget])
    · exact absurd hnext (by simp [leftReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [rightContinueTarget])
    · exact absurd hnext (by simp [rightCloseTarget])
    · exact absurd hnext (by simp [rightReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [revLeftContinueTarget])
    · exact absurd hnext (by simp [revLeftCloseTarget])
    · exact absurd hnext (by simp [revLeftReverseTarget])
  · rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact absurd hnext (by simp [revRightContinueTarget])
    · exact absurd hnext (by simp [revRightCloseTarget])
    · exact absurd hnext (by simp [revRightReverseTarget])

/--
Regime one: with infinitely many boundaries, acceptance of the journal
tree forces min-even parity of the play priorities.
-/
theorem priorities_min_even_of_infinite_boundaries
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        (treeStrategy t) path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ IsBoundaryAt t path m) :
    NatSeqMinEvenParity
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n)) := by
  have htracks := treeTracks_of_consistent t CL CR CC path hplay hcons
  have hwalked :=
    walked_priorities_min_even_of_accepts t CL CR CC path hplay.2 hacc
  have hbseq_eq_walked :
      ∀ k : Nat,
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority
            (path (boundaryIndex t path hinf k)) =
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial))
              (playNodes t path (boundaryIndex t path hinf k))) := by
    intro k
    obtain ⟨atom, hatom⟩ :=
      boundaryIndex_isBoundary t path hinf hplay.1 k
    exact
      (walked_priority_eq_of_bnd t CL CR CC path
        (htracks (boundaryIndex t path hinf k)) hatom).symm
  have hbnd_or_committed :
      ∀ m : Nat,
        (∀ atom : A.State × A.State,
          globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial)) (playNodes t path m) ≠
            Sum.inl atom) ∨
          IsBoundaryAt t path m ∨
            (∃ pair plan,
              path m = Sum.inr (Sum.inl (pair, plan))) := by
    intro m
    have hm := htracks m
    unfold TreeTracks at hm
    rcases hpos : path m with atom | ⟨pair, plan⟩ |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨plan, chain, control, state, minState⟩ |
      ⟨chain, control, entry, state, minState⟩ |
    ⟨chain, control, entry, state, minState⟩
    · exact Or.inr (Or.inl ⟨atom, hpos⟩)
    · exact Or.inr (Or.inr ⟨pair, plan, rfl⟩)
    all_goals
      rw [hpos] at hm
      refine Or.inl fun atom h => ?_
      obtain ⟨⟨checker, threads, hrun, -⟩, -⟩ := hm
      rw [hrun] at h
      exact absurd h (by simp)
  -- transfer between the boundary subsequence and the walked priorities
  have htransfer2 :
      NatSeqMinEvenParity
        (fun k =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (boundaryIndex t path hinf k))) := by
    refine
      (natSeqMinEvenParity_iff_of_recurring_transfer _ _ ?_ ?_).mpr hwalked
    · -- recurring boundary values recur among the walked priorities
      intro w hw n
      obtain ⟨k, hk, hval⟩ := hw n
      refine ⟨boundaryIndex t path hinf k, ?_, ?_⟩
      · exact Nat.le_trans hk (le_boundaryIndex t path hinf k)
      · have hval' :
            (DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)).priority
              (path (boundaryIndex t path hinf k)) = w :=
          hval
        rw [hbseq_eq_walked k] at hval'
        exact hval'
    · -- recurring walked values dominate boundary values frequently
      intro v hv n
      obtain ⟨m, hm, hval⟩ := hv (boundaryIndex t path hinf n + 1)
      have hval' :
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial)) (playNodes t path m)) = v :=
        hval
      rcases hbnd_or_committed m with hblock | hbnd | hcomm
      · -- block mode: the shift dominates every boundary emission
        refine ⟨n, Nat.le_refl n, ?_⟩
        obtain ⟨atom, hatom⟩ :=
          boundaryIndex_isBoundary t path hinf hplay.1 n
        have hlt : A.priority atom.2 < globalShift (In₁ := In₁) A :=
          priority_lt_globalShift (In₁ := In₁) A atom.2
        have hge : globalShift (In₁ := In₁) A ≤ v := by
          rw [← hval']
          rcases hrunval :
              globalRunIn CL CR CC t.labeledTree
                (Sum.inl (A.initial, A.initial)) (playNodes t path m) with
            atom' | ⟨checker, threads⟩ | data | dataL | dataR | u
          · exact absurd hrunval (by intro h; exact hblock atom' h)
          · show globalShift (In₁ := In₁) A ≤
              CL.monitor.priority checker + globalShift (In₁ := In₁) A
            omega
          · obtain ⟨checker, threads⟩ := data
            show globalShift (In₁ := In₁) A ≤
              CR.monitor.priority checker + globalShift (In₁ := In₁) A
            omega
          · obtain ⟨checker, threads⟩ := dataL
            show globalShift (In₁ := In₁) A ≤
              CC.monitor.priority checker + globalShift (In₁ := In₁) A
            omega
          · obtain ⟨checker, threads⟩ := dataR
            show globalShift (In₁ := In₁) A ≤
              CC.monitor.priority checker + globalShift (In₁ := In₁) A
            omega
          · exact Nat.le_refl _
        show
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (boundaryIndex t path hinf n)) ≤ v
        rw [show (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority
            (path (boundaryIndex t path hinf n)) =
          A.priority atom.2 by rw [hatom]; rfl]
        omega
      · -- a boundary round: it is enumerated
        obtain ⟨atom, hatom⟩ := hbnd
        obtain ⟨k, hk⟩ :=
          exists_boundaryIndex_eq t path hinf ⟨atom, hatom⟩
        refine ⟨k, ?_, ?_⟩
        · by_contra hlt
          push Not at hlt
          have :=
            boundaryIndex_strictMono t path hinf
              (show k < n by omega)
          omega
        · show
            (DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)).priority
              (path (boundaryIndex t path hinf k)) ≤ v
          rw [hk,
            ← walked_priority_eq_of_bnd t CL CR CC path (htracks m) hatom,
            hval']
          try exact Nat.le_refl v
      · -- a committed round: its boundary precedes it with equal value
        obtain ⟨pair, plan, hcomm'⟩ := hcomm
        have hmpos : 1 ≤ m := by
          rcases Nat.eq_zero_or_pos m with hzero | hpos
          · rw [hzero] at hcomm'
            rw [hplay.1] at hcomm'
            exact absurd hcomm' (by simp)
          · exact hpos
        obtain ⟨atom, hatom⟩ :=
          bnd_pred_of_committed t path hplay
            (show path (m - 1 + 1) = _ by
              rw [show m - 1 + 1 = m by omega]; exact hcomm')
        have hnodes :
            playNodes t path m = playNodes t path (m - 1) := by
          conv_lhs => rw [show m = m - 1 + 1 by omega]
          show playNodes t path (m - 1) ++ _ = _
          rw [hatom, stepDirections_bnd, List.append_nil]
        obtain ⟨k, hk⟩ :=
          exists_boundaryIndex_eq t path hinf ⟨atom, hatom⟩
        rw [hnodes] at hval'
        refine ⟨k, ?_, ?_⟩
        · by_contra hlt
          push Not at hlt
          have :=
            boundaryIndex_strictMono t path hinf
              (show k < n by omega)
          omega
        · show
            (DetParityAutomaton.boundaryGame A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)).priority
              (path (boundaryIndex t path hinf k)) ≤ v
          rw [hk,
            ← walked_priority_eq_of_bnd t CL CR CC path (htracks (m - 1))
              hatom,
            hval']
          try exact Nat.le_refl v
  -- transfer from the boundary subsequence to the play priorities
  refine
    (natSeqMinEvenParity_iff_of_recurring_transfer _ _ ?_ ?_).mp htransfer2
  · -- boundary values recur among the play priorities
    intro w hw n
    obtain ⟨k, hk, hval⟩ := hw n
    exact
      ⟨boundaryIndex t path hinf k,
        Nat.le_trans hk (le_boundaryIndex t path hinf k), hval⟩
  · -- recurring play values dominate boundary values frequently
    intro v hv n
    obtain ⟨m, hm, hval⟩ := hv (boundaryIndex t path hinf n)
    obtain ⟨m', hm', hbnd', hle'⟩ :=
      exists_boundary_priority_le t path hplay hinf m
    obtain ⟨k, hk⟩ := exists_boundaryIndex_eq t path hinf hbnd'
    have hval' :
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path m) = v :=
      hval
    rw [hval'] at hle'
    refine ⟨k, ?_, ?_⟩
    · by_contra hlt
      push Not at hlt
      have :=
        boundaryIndex_strictMono t path hinf (show k < n by omega)
      omega
    · show
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority
          (path (boundaryIndex t path hinf k)) ≤ v
      rw [hk]
      exact hle'

end RegimeOne

/-! ### Regime two: the play is trapped in one block -/

section RegimeTwo

/-- Once boundaries stop, the play is trapped in a single block after
its last commitment. -/
theorem exists_trapped_block
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    {N : Nat} (hnb : ∀ m : Nat, N ≤ m -> ¬ IsBoundaryAt t path m) :
    ∃ m₀ : Nat,
      (∃ pair plan, path m₀ = Sum.inr (Sum.inl (pair, plan))) ∧
        ((∀ m : Nat, m₀ < m ->
            ∃ data, path m = Sum.inr (Sum.inr (Sum.inl data))) ∨
          (∀ m : Nat, m₀ < m ->
            ∃ data,
              path m = Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ∨
          (∃ m₁ : Nat, m₀ < m₁ ∧
            ∀ m : Nat, m₁ ≤ m ->
              (∃ data,
                path m =
                  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
                (∃ data,
                  path m =
                    Sum.inr (Sum.inr (Sum.inr (Sum.inr
                      (Sum.inr data))))))) := by
  have hcom1 : ∃ pair plan, path 1 = Sum.inr (Sum.inl (pair, plan)) := by
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path 0) (path 1) :=
      hplay.2 0
    rw [hplay.1] at hstep
    obtain ⟨plan, h1⟩ := hstep
    exact ⟨_, plan, h1⟩
  letI :
      DecidablePred fun m =>
        ∃ pair plan, path m = Sum.inr (Sum.inl (pair, plan)) :=
    fun _ => Classical.propDecidable _
  set m₀ :=
    Nat.findGreatest
      (fun m => ∃ pair plan, path m = Sum.inr (Sum.inl (pair, plan)))
      (N + 1) with hm₀def
  have hm₀ : ∃ pair plan, path m₀ = Sum.inr (Sum.inl (pair, plan)) := by
    rw [hm₀def]
    exact
      Nat.findGreatest_spec
        (P := fun m =>
          ∃ pair plan, path m = Sum.inr (Sum.inl (pair, plan)))
        (n := N + 1) (m := 1) (by omega) hcom1
  have hnotcom :
      ∀ k : Nat, m₀ < k ->
        ¬ ∃ pair plan, path k = Sum.inr (Sum.inl (pair, plan)) := by
    intro k hk hcom
    rcases Nat.le_total k (N + 1) with hle | hge
    · refine
        Nat.findGreatest_is_greatest
          (P := fun m =>
            ∃ pair plan, path m = Sum.inr (Sum.inl (pair, plan)))
          ?_ hle hcom
      rw [← hm₀def]
      exact hk
    · obtain ⟨pair, plan, hcom'⟩ := hcom
      obtain ⟨atom, hatom⟩ :=
        bnd_pred_of_committed t path hplay
          (show path (k - 1 + 1) = _ by
            rw [show k - 1 + 1 = k by omega]; exact hcom')
      exact hnb (k - 1) (by omega) ⟨atom, hatom⟩
  have hnobnd : ∀ m : Nat, m₀ < m -> ¬ IsBoundaryAt t path m := by
    rintro m hm ⟨atom, hatom⟩
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path m) (path (m + 1)) :=
      hplay.2 m
    rw [hatom] at hstep
    obtain ⟨plan, hnext⟩ := step_bnd_committed t hstep
    exact hnotcom (m + 1) (by omega) ⟨_, plan, hnext⟩
  have hpersistL :
      ∀ m : Nat, m₀ < m ->
        (∃ data, path m = Sum.inr (Sum.inr (Sum.inl data))) ->
          (∃ data, path (m + 1) = Sum.inr (Sum.inr (Sum.inl data))) ∨
            (∃ data,
              path (m + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) := by
    rintro m hm ⟨⟨plan, chain, control, state, minState⟩, hdata⟩
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path m) (path (m + 1)) :=
      hplay.2 m
    rw [hdata] at hstep
    rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact Or.inl ⟨_, by rw [hnext]; rfl⟩
    · refine absurd ?_ (hnobnd (m + 1) (by omega))
      exact ⟨_, by rw [hnext]; rfl⟩
    · exact Or.inr ⟨_, by rw [hnext]; rfl⟩
  have hpersistR :
      ∀ m : Nat, m₀ < m ->
        (∃ data, path m = Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
          (∃ data,
            path (m + 1) = Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ∨
            (∃ data,
              path (m + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) := by
    rintro m hm ⟨⟨plan, chain, control, state, minState⟩, hdata⟩
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path m) (path (m + 1)) :=
      hplay.2 m
    rw [hdata] at hstep
    rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · exact Or.inl ⟨_, by rw [hnext]; rfl⟩
    · refine absurd ?_ (hnobnd (m + 1) (by omega))
      exact ⟨_, by rw [hnext]; rfl⟩
    · exact Or.inr ⟨_, by rw [hnext]; rfl⟩
  have hrev :
      ∀ m : Nat, m₀ < m ->
        ((∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
          (∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))))) ->
          (∃ data,
            path (m + 1) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
            (∃ data,
              path (m + 1) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) := by
    rintro m hm
      (⟨⟨chain, control, state, minState⟩, hdata⟩ |
        ⟨⟨chain, control, state, minState⟩, hdata⟩) <;>
      · have hstep :
            boundaryStep A (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control) (path m)
              (path (m + 1)) :=
          hplay.2 m
        rw [hdata] at hstep
        rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
        · first
            | exact Or.inl ⟨_, by rw [hnext]; rfl⟩
            | exact Or.inr ⟨_, by rw [hnext]; rfl⟩
        · refine absurd ?_ (hnobnd (m + 1) (by omega))
          exact ⟨_, by rw [hnext]; rfl⟩
        · first
            | exact Or.inl ⟨_, by rw [hnext]; rfl⟩
            | exact Or.inr ⟨_, by rw [hnext]; rfl⟩
  have habsorb :
      ∀ m₁ : Nat, m₀ < m₁ ->
        ((∃ data,
            path m₁ =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
          (∃ data,
            path m₁ =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))))) ->
        ∀ m : Nat, m₁ ≤ m ->
          (∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
            (∃ data,
              path m =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))) := by
    intro m₁ hm₁ h₁ m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = m₁ + k := ⟨m - m₁, by omega⟩
    clear hm
    induction k with
    | zero => exact h₁
    | succ k ih => exact hrev (m₁ + k) (by omega) ih
  refine ⟨m₀, hm₀, ?_⟩
  have hblock1 :
      (∃ data, path (m₀ + 1) = Sum.inr (Sum.inr (Sum.inl data))) ∨
        ∃ data,
          path (m₀ + 1) = Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) := by
    obtain ⟨pair, plan, hcom'⟩ := hm₀
    obtain ⟨q, mn⟩ := pair
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path m₀)
          (path (m₀ + 1)) :=
      hplay.2 m₀
    rw [hcom'] at hstep
    rcases hstep with ⟨move, hnext⟩ | ⟨move, hnext⟩ | ⟨move, hnext⟩
    · refine absurd ?_ (hnobnd (m₀ + 1) (by omega))
      exact ⟨_, by rw [hnext]; rfl⟩
    · exact Or.inl ⟨_, by rw [hnext]; rfl⟩
    · exact Or.inr ⟨_, by rw [hnext]; rfl⟩
  rcases hblock1 with hL | hR
  · letI :
        DecidablePred fun j =>
          ¬ ∃ data,
            path (m₀ + 1 + j) = Sum.inr (Sum.inr (Sum.inl data)) :=
      fun _ => Classical.propDecidable _
    by_cases hall :
        ∀ m : Nat, m₀ < m ->
          ∃ data, path m = Sum.inr (Sum.inr (Sum.inl data))
    · exact Or.inl hall
    · push Not at hall
      obtain ⟨m₂, hm₂, hnotL⟩ := hall
      have hexj :
          ∃ j : Nat,
            ¬ ∃ data,
              path (m₀ + 1 + j) = Sum.inr (Sum.inr (Sum.inl data)) :=
        ⟨m₂ - (m₀ + 1), by
          rw [show m₀ + 1 + (m₂ - (m₀ + 1)) = m₂ by omega]
          exact fun ⟨data, hdata⟩ => hnotL data hdata⟩
      have hj₀pos : Nat.find hexj ≠ 0 := by
        intro h0
        exact (h0 ▸ Nat.find_spec hexj) hL
      have hprev :
          ∃ data,
            path (m₀ + 1 + (Nat.find hexj - 1)) =
              Sum.inr (Sum.inr (Sum.inl data)) := by
        by_contra hno
        exact Nat.find_min hexj (m := Nat.find hexj - 1) (by omega) hno
      have hstep' :=
        hpersistL (m₀ + 1 + (Nat.find hexj - 1)) (by omega) hprev
      rw [show m₀ + 1 + (Nat.find hexj - 1) + 1 =
        m₀ + 1 + Nat.find hexj by omega] at hstep'
      rcases hstep' with hL' | hrev'
      · exact absurd hL' (Nat.find_spec hexj)
      · refine Or.inr (Or.inr ⟨m₀ + 1 + Nat.find hexj, by omega, ?_⟩)
        exact
          habsorb (m₀ + 1 + Nat.find hexj) (by omega) (Or.inr hrev')
  · letI :
        DecidablePred fun j =>
          ¬ ∃ data,
            path (m₀ + 1 + j) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :=
      fun _ => Classical.propDecidable _
    by_cases hall :
        ∀ m : Nat, m₀ < m ->
          ∃ data, path m = Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))
    · exact Or.inr (Or.inl hall)
    · push Not at hall
      obtain ⟨m₂, hm₂, hnotR⟩ := hall
      have hexj :
          ∃ j : Nat,
            ¬ ∃ data,
              path (m₀ + 1 + j) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :=
        ⟨m₂ - (m₀ + 1), by
          rw [show m₀ + 1 + (m₂ - (m₀ + 1)) = m₂ by omega]
          exact fun ⟨data, hdata⟩ => hnotR data hdata⟩
      have hj₀pos : Nat.find hexj ≠ 0 := by
        intro h0
        exact (h0 ▸ Nat.find_spec hexj) hR
      have hprev :
          ∃ data,
            path (m₀ + 1 + (Nat.find hexj - 1)) =
              Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) := by
        by_contra hno
        exact Nat.find_min hexj (m := Nat.find hexj - 1) (by omega) hno
      have hstep' :=
        hpersistR (m₀ + 1 + (Nat.find hexj - 1)) (by omega) hprev
      rw [show m₀ + 1 + (Nat.find hexj - 1) + 1 =
        m₀ + 1 + Nat.find hexj by omega] at hstep'
      rcases hstep' with hR' | hrev'
      · exact absurd hR' (Nat.find_spec hexj)
      · refine Or.inr (Or.inr ⟨m₀ + 1 + Nat.find hexj, by omega, ?_⟩)
        exact
          habsorb (m₀ + 1 + Nat.find hexj) (by omega) (Or.inl hrev')

/-- Sender-branch embedding of a left-block word. -/
def senderLNode (w : TreeNode In₂) :
    TreeNode (GlobalJournalBranch (In₁ := In₁) A) :=
  w.map fun x => Sum.inr (Sum.inl x)

/-- The narrowed left-block label tree below a node. -/
def narrowedLeftAt
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    LabeledTree In₂
      (NarrowedBlockLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
  fun w =>
    GlobalJournalLabel.leftNarrowed
      (t.labeledTree (node₀ ++ senderLNode (A := A) w))

@[simp]
theorem narrowedLeftAt_nil
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    narrowedLeftAt t node₀ [] =
      GlobalJournalLabel.leftNarrowed (t.labeledTree node₀) := by
  simp [narrowedLeftAt, senderLNode]

theorem senderLNode_append (w : TreeNode In₂) (x : In₂) :
    senderLNode (A := A) (w ++ [x]) =
      senderLNode (A := A) w ++ [Sum.inr (Sum.inl x)] := by
  simp [senderLNode]

/-- Within a trapped left block the run threads the left checker
through the narrowed labels. -/
theorem globalRunIn_trapped_left
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₂) (x : In₂),
      ∃ threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            (node₀ ++ senderLNode (A := A) (w ++ [x])) =
          Sum.inr (Sum.inl
            (DeterministicBlockMonitor.controlIn CL.monitor
                (narrowedLeftAt t node₀) (CL.start atom₀.1) (w ++ [x]),
              threads)) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x
      refine ⟨leftOpenSubset atom₀
              (GlobalJournalLabel.leftNarrowed (t.labeledTree node₀)) x, ?_⟩
      rw [show senderLNode (A := A) (([] : TreeNode In₂) ++ [x]) =
        [Sum.inr (Sum.inl x)] from rfl]
      rw [globalRunIn_append, hrun₀]
      show
        globalJournalStep A CL CR CC (Sum.inl atom₀)
            (t.labeledTree node₀) (Sum.inr (Sum.inl x)) =
          Sum.inr (Sum.inl
            (CL.monitor.step (CL.start atom₀.1)
                (narrowedLeftAt t node₀ []) x,
              leftOpenSubset atom₀
              (GlobalJournalLabel.leftNarrowed (t.labeledTree node₀)) x))
      rw [narrowedLeftAt_nil]
      rfl
  | append_singleton w x' ih =>
      intro x
      obtain ⟨threads, hih⟩ := ih x'
      refine
        ⟨leftStepSubset threads
            (GlobalJournalLabel.leftNarrowed
              (t.labeledTree
                (node₀ ++ senderLNode (A := A) (w ++ [x'])))) x, ?_⟩
      rw [show node₀ ++ senderLNode (A := A) ((w ++ [x']) ++ [x]) =
        (node₀ ++ senderLNode (A := A) (w ++ [x'])) ++
          [Sum.inr (Sum.inl x)] from by
        rw [senderLNode_append (A := A) (w ++ [x']) x, List.append_assoc]]
      rw [globalRunIn_append, hih,
        DeterministicBlockMonitor.controlIn_append CL.monitor (w ++ [x'])]
      simp only [globalJournalStep, narrowedLeftAt]

/-- Branch splicing a node prefix with a left-sender continuation. -/
def splicedLeftBranch
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂) (k : Nat) :
    GlobalJournalBranch (In₁ := In₁) A :=
  if h : k < node₀.length then node₀[k]
  else Sum.inr (Sum.inl (branch (k - node₀.length)))

theorem branchNode_spliced_take
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂) :
    ∀ j : Nat, j ≤ node₀.length ->
      branchNode (splicedLeftBranch (A := A) node₀ branch) j =
        node₀.take j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      show
        branchNode (splicedLeftBranch (A := A) node₀ branch) j ++
            [splicedLeftBranch (A := A) node₀ branch j] =
          node₀.take (j + 1)
      rw [ih (by omega)]
      have hlt : j < node₀.length := by omega
      rw [show splicedLeftBranch (A := A) node₀ branch j = node₀[j] by
        simp only [splicedLeftBranch]; rw [dif_pos hlt]]
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      rfl

theorem branchNode_spliced_extend
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂) :
    ∀ j : Nat,
      branchNode (splicedLeftBranch (A := A) node₀ branch)
          (node₀.length + j) =
        node₀ ++ senderLNode (A := A) (branchNode branch j) := by
  intro j
  induction j with
  | zero =>
      rw [show node₀.length + 0 = node₀.length by omega,
        branchNode_spliced_take (A := A) node₀ branch node₀.length
          (Nat.le_refl _),
        List.take_length]
      simp [senderLNode, branchNode]
  | succ j ih =>
      show
        branchNode (splicedLeftBranch (A := A) node₀ branch)
            (node₀.length + j) ++
          [splicedLeftBranch (A := A) node₀ branch (node₀.length + j)] =
          _
      rw [ih]
      rw [show splicedLeftBranch (A := A) node₀ branch
          (node₀.length + j) =
        Sum.inr (Sum.inl (branch j)) by
        simp only [splicedLeftBranch]
        rw [dif_neg (by omega)]
        rw [show node₀.length + j - node₀.length = j by omega]]
      rw [show branchNode branch (j + 1) =
        branchNode branch j ++ [branch j] from rfl]
      rw [senderLNode_append (A := A), ← List.append_assoc]

/-- Acceptance forces the left checker to win the narrowed subtree of
a trapped block. -/
theorem winningTree_of_trapped_left
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    DeterministicBlockMonitor.WinningTree
      { CL.monitor with initial := CL.start atom₀.1 }
      (narrowedLeftAt t node₀) := by
  intro branch
  have hs :=
    accepts_branch_priorities t CL CR CC hacc
      (splicedLeftBranch (A := A) node₀ branch)
  have hs1 := (natSeqMinEvenParity_shift _ (node₀.length + 1)).mpr hs
  have hfun :
      (fun j =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial))
              (branchNode (splicedLeftBranch (A := A) node₀ branch)
                (node₀.length + 1 + j)))) =
        fun j =>
          CL.monitor.priority
              (CL.monitor.controlIn (narrowedLeftAt t node₀)
                (CL.start atom₀.1) (branchNode branch (j + 1))) +
            globalShift (In₁ := In₁) A := by
    funext j
    rw [show node₀.length + 1 + j = node₀.length + (j + 1) by omega]
    rw [branchNode_spliced_extend (A := A) node₀ branch (j + 1)]
    rw [show branchNode branch (j + 1) =
      branchNode branch j ++ [branch j] from rfl]
    obtain ⟨threads, hth⟩ :=
      globalRunIn_trapped_left t CL CR CC node₀ atom₀ hrun₀
        (branchNode branch j) (branch j)
    rw [hth]
    rfl
  rw [hfun] at hs1
  have hs3 :=
    (natSeqMinEvenParity_add_const
      (globalShift_even (In₁ := In₁) (A := A))).mp hs1
  have hs4 :=
    (natSeqMinEvenParity_shift
      (fun n =>
        CL.monitor.priority
          (CL.monitor.controlIn (narrowedLeftAt t node₀)
            (CL.start atom₀.1) (branchNode branch n))) 1).mp
      (by
        have hidx :
            (fun j =>
                CL.monitor.priority
                  (CL.monitor.controlIn (narrowedLeftAt t node₀)
                    (CL.start atom₀.1) (branchNode branch (j + 1)))) =
              fun n =>
                CL.monitor.priority
                  (CL.monitor.controlIn (narrowedLeftAt t node₀)
                    (CL.start atom₀.1) (branchNode branch (1 + n))) := by
          funext j
          rw [show 1 + j = j + 1 by omega]
        rw [← hidx]
        exact hs3)
  have hfin :
      (fun n =>
          ({ CL.monitor with initial := CL.start atom₀.1 } :
              DeterministicBlockMonitor In₂
                (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
                  (A.State × A.State))).priority
            (DeterministicBlockMonitor.control _ (narrowedLeftAt t node₀)
              (branchNode branch n))) =
        fun n =>
          CL.monitor.priority
            (CL.monitor.controlIn (narrowedLeftAt t node₀)
              (CL.start atom₀.1) (branchNode branch n)) := by
    funext n
    show
      CL.monitor.priority
          (({ CL.monitor with initial := CL.start atom₀.1 } :
              DeterministicBlockMonitor In₂
                (NarrowedBlockLabel In₁ In₂ Out₁ Out₂
                  (A.State × A.State))).controlIn
            (narrowedLeftAt t node₀) (CL.start atom₀.1)
            (branchNode branch n)) =
        _
    rw [DeterministicBlockMonitor.controlIn_update_initial]
  rw [hfin]
  exact hs4

/--
Regime two, left orientation: after the last commitment the play's
thread is a narrowed monitor thread of the trapped block, so
acceptance forces min-even parity of the play priorities.
-/
theorem priorities_min_even_of_trapped_left
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        (treeStrategy t) path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    {m₀ : Nat}
    {pair : A.State × A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (hcom : path m₀ = Sum.inr (Sum.inl (pair, plan)))
    (htail :
      ∀ m : Nat, m₀ < m ->
        ∃ data, path m = Sum.inr (Sum.inr (Sum.inl data))) :
    NatSeqMinEvenParity
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n)) := by
  have htracks := treeTracks_of_consistent t CL CR CC path hplay hcons
  have hm₀ := htracks m₀
  unfold TreeTracks at hm₀
  rw [hcom] at hm₀
  obtain ⟨⟨atom₀, hrun₀, hpair⟩, hplan⟩ := hm₀
  subst hpair
  subst hplan
  have hwin :=
    (CL.winning_iff atom₀.1 (narrowedLeftAt t (playNodes t path m₀))).mp
      (winningTree_of_trapped_left t CL CR CC hacc (playNodes t path m₀)
        atom₀ hrun₀)
  have hdchoice :
      ∀ k : Nat,
        ∃ data,
          path (m₀ + 1 + k) = Sum.inr (Sum.inr (Sum.inl data)) :=
    fun k => htail (m₀ + 1 + k) (by omega)
  have hd :
      ∀ k : Nat,
        path (m₀ + 1 + k) =
          Sum.inr (Sum.inr (Sum.inl (Classical.choose (hdchoice k)))) :=
    fun k => Classical.choose_spec (hdchoice k)
  have hstep₀ :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) (path m₀) (path (m₀ + 1)) :=
    hplay.2 m₀
  rw [show m₀ + 1 = m₀ + 1 + 0 by omega] at hstep₀
  rw [hcom, hd 0] at hstep₀
  have hopen' := exists_openLeft_of_step t hstep₀
  have hcont' :
      ∀ k : Nat,
        ∃ move : In₁ × In₂,
          (Sum.inr (Sum.inr (Sum.inl (Classical.choose (hdchoice (k + 1))))) :
              BoundaryGamePosition (In₁ := In₁) A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)) =
            A.leftContinueTarget (Classical.choose (hdchoice k)).1
              (Classical.choose (hdchoice k)).2.1
              (Classical.choose (hdchoice k)).2.2.1
              (Classical.choose (hdchoice k)).2.2.2.1
              (Classical.choose (hdchoice k)).2.2.2.2 move := by
    intro k
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (m₀ + 1 + k))
          (path (m₀ + 1 + k + 1)) :=
      hplay.2 (m₀ + 1 + k)
    rw [show m₀ + 1 + k + 1 = m₀ + 1 + (k + 1) by omega] at hstep
    rw [hd k, hd (k + 1)] at hstep
    exact exists_continueL_of_step t hstep
  set e0 := Classical.choose hopen' with he0
  let env : Nat -> In₁ × In₂ := fun k =>
    Nat.casesOn k e0 fun j => Classical.choose (hcont' j)
  have htrack :
      ∀ k : Nat,
        (Classical.choose (hdchoice k)).2.2.2 =
          narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (narrowedLeftAt t (playNodes t path m₀)) env (k + 1) ∧
        playNodes t path (m₀ + 1 + k) =
          playNodes t path m₀ ++
            senderLNode (A := A)
              (senderWord (branchNode env (k + 1))) := by
    intro k
    induction k with
    | zero =>
        constructor
        · have hspec' :=
            Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Classical.choose_spec hopen')))
          rw [← he0] at hspec'
          rw [hspec']
          show
            _ =
              (A.leftBlockMonitor atom₀.1).step (atom₀.1, atom₀.1)
                (narrowedRecord (A.leftBlockMonitor atom₀.1)
                  (narrowedLeftAt t (playNodes t path m₀) [])
                  (atom₀.1, atom₀.1) e0)
          rw [narrowedLeftAt_nil]
          rfl
        · show
            playNodes t path m₀ ++
                stepDirections t (path m₀) (path (m₀ + 1 + 0)) =
              _
          rw [hcom, hd 0,
            stepDirections_committed_blockL t _ _ _ hopen', ← he0]
          rfl
    | succ k ih =>
        have henv : env (k + 1) = Classical.choose (hcont' k) := rfl
        constructor
        · have hspec' :=
            Sum.inl.inj
              (Sum.inr.inj
                (Sum.inr.inj (Classical.choose_spec (hcont' k))))
          have hiw := ih.2
          rcases hsplit : Classical.choose (hdchoice k) with
            ⟨pl, ch, c, q, mn⟩
          have htk := htracks (m₀ + 1 + k)
          unfold TreeTracks at htk
          rw [hd k, hsplit] at htk
          obtain ⟨-, hc, ⟨root, hpl⟩, -⟩ := htk
          subst hc
          subst hpl
          have h1 :
              (Classical.choose (hdchoice k)).1 = treeLeftPlan t root := by
            rw [hsplit]
          have h2 :
              (Classical.choose (hdchoice k)).2.2.1 =
                ULift.up (t.controlAt (playNodes t path (m₀ + 1 + k))) := by
            rw [hsplit]
          have htables :
              ((Classical.choose (hdchoice k)).1.label
                  (Classical.choose (hdchoice k)).2.2.1) =
                narrowedLeftAt t (playNodes t path m₀)
                  (senderWord (branchNode env (k + 1))) := by
            rw [h1, h2]
            show
              GlobalJournalLabel.leftNarrowed
                  (t.labelOf
                    (t.controlAt (playNodes t path (m₀ + 1 + k)))) =
                _
            rw [hiw]
            rfl
          rw [hspec']
          show
            _ =
              narrowedControl (A.leftBlockMonitor atom₀.1)
                (narrowedLeftAt t (playNodes t path m₀))
                (branchNode env (k + 1) ++ [env (k + 1)])
          rw [narrowedControl_append]
          rw [show narrowedControl (A.leftBlockMonitor atom₀.1)
              (narrowedLeftAt t (playNodes t path m₀))
              (branchNode env (k + 1)) =
            (Classical.choose (hdchoice k)).2.2.2 from ih.1.symm]
          rw [← htables]
          rfl
        · show
            playNodes t path (m₀ + 1 + k) ++
                stepDirections t (path (m₀ + 1 + k))
                  (path (m₀ + 1 + (k + 1))) =
              _
          rw [hd k, hd (k + 1),
            stepDirections_blockL_blockL t _ _ (hcont' k), ih.2]
          rw [show branchNode env (k + 1 + 1) =
            branchNode env (k + 1) ++ [env (k + 1)] from rfl]
          rw [senderWord_append, senderLNode_append (A := A),
            ← List.append_assoc, henv]
  have hthread_parity := hwin env
  have hshift1 :=
    (natSeqMinEvenParity_shift
      (fun n =>
        (A.leftBlockMonitor atom₀.1).priority
          (narrowedThreadState (A.leftBlockMonitor atom₀.1)
            (narrowedLeftAt t (playNodes t path m₀)) env n)) 1).mpr
      hthread_parity
  have hbridge :
      (fun k =>
          (A.leftBlockMonitor atom₀.1).priority
            (narrowedThreadState (A.leftBlockMonitor atom₀.1)
              (narrowedLeftAt t (playNodes t path m₀)) env (1 + k))) =
        fun k =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (m₀ + 1 + k)) := by
    funext k
    rw [show (1 : Nat) + k = k + 1 by omega]
    rw [hd k]
    rw [← (htrack k).1]
    rfl
  rw [hbridge] at hshift1
  exact
    (natSeqMinEvenParity_shift
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n))
      (m₀ + 1)).mp hshift1

/-! ### The right-orientation mirror -/

/-- Sender-branch embedding of a right-block word. -/
def senderRNode (w : TreeNode In₁) :
    TreeNode (GlobalJournalBranch (In₁ := In₁) A) :=
  w.map fun x => Sum.inr (Sum.inr x)

/-- The narrowed right-block label tree below a node. -/
def narrowedRightAt
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    LabeledTree In₁
      (NarrowedBlockLabel In₂ In₁ Out₂ Out₁ (A.State × A.State)) :=
  fun w =>
    GlobalJournalLabel.rightNarrowed
      (t.labeledTree (node₀ ++ senderRNode (A := A) w))

@[simp]
theorem narrowedRightAt_nil
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    narrowedRightAt t node₀ [] =
      GlobalJournalLabel.rightNarrowed (t.labeledTree node₀) := by
  simp [narrowedRightAt, senderRNode]

theorem senderRNode_append (w : TreeNode In₁) (x : In₁) :
    senderRNode (A := A) (w ++ [x]) =
      senderRNode (A := A) w ++ [Sum.inr (Sum.inr x)] := by
  simp [senderRNode]

/-- Within a trapped right block the run threads the right checker
through the narrowed labels. -/
theorem globalRunIn_trapped_right
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    ∀ (w : TreeNode In₁) (x : In₁),
      ∃ threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            (node₀ ++ senderRNode (A := A) (w ++ [x])) =
          Sum.inr (Sum.inr (Sum.inl
            (DeterministicBlockMonitor.controlIn CR.monitor
                (narrowedRightAt t node₀) (CR.start atom₀.1) (w ++ [x]),
              threads))) := by
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x
      refine ⟨rightOpenSubset atom₀
              (GlobalJournalLabel.rightNarrowed (t.labeledTree node₀)) x, ?_⟩
      rw [show senderRNode (A := A) (([] : TreeNode In₁) ++ [x]) =
        [Sum.inr (Sum.inr x)] from rfl]
      rw [globalRunIn_append, hrun₀]
      show
        globalJournalStep A CL CR CC (Sum.inl atom₀)
            (t.labeledTree node₀) (Sum.inr (Sum.inr x)) =
          Sum.inr (Sum.inr (Sum.inl
            (CR.monitor.step (CR.start atom₀.1)
                (narrowedRightAt t node₀ []) x,
              rightOpenSubset atom₀
              (GlobalJournalLabel.rightNarrowed (t.labeledTree node₀)) x)))
      rw [narrowedRightAt_nil]
      rfl
  | append_singleton w x' ih =>
      intro x
      obtain ⟨threads, hih⟩ := ih x'
      refine
        ⟨rightStepSubset threads
            (GlobalJournalLabel.rightNarrowed
              (t.labeledTree
                (node₀ ++ senderRNode (A := A) (w ++ [x'])))) x, ?_⟩
      rw [show node₀ ++ senderRNode (A := A) ((w ++ [x']) ++ [x]) =
        (node₀ ++ senderRNode (A := A) (w ++ [x'])) ++
          [Sum.inr (Sum.inr x)] from by
        rw [senderRNode_append (A := A) (w ++ [x']) x, List.append_assoc]]
      rw [globalRunIn_append, hih,
        DeterministicBlockMonitor.controlIn_append CR.monitor (w ++ [x'])]
      simp only [globalJournalStep, narrowedRightAt]

/-- Branch splicing a node prefix with a right-sender continuation. -/
def splicedRightBranch
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₁) (k : Nat) :
    GlobalJournalBranch (In₁ := In₁) A :=
  if h : k < node₀.length then node₀[k]
  else Sum.inr (Sum.inr (branch (k - node₀.length)))

theorem branchNode_splicedRight_take
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₁) :
    ∀ j : Nat, j ≤ node₀.length ->
      branchNode (splicedRightBranch (A := A) node₀ branch) j =
        node₀.take j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      show
        branchNode (splicedRightBranch (A := A) node₀ branch) j ++
            [splicedRightBranch (A := A) node₀ branch j] =
          node₀.take (j + 1)
      rw [ih (by omega)]
      have hlt : j < node₀.length := by omega
      rw [show splicedRightBranch (A := A) node₀ branch j = node₀[j] by
        simp only [splicedRightBranch]; rw [dif_pos hlt]]
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      rfl

theorem branchNode_splicedRight_extend
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₁) :
    ∀ j : Nat,
      branchNode (splicedRightBranch (A := A) node₀ branch)
          (node₀.length + j) =
        node₀ ++ senderRNode (A := A) (branchNode branch j) := by
  intro j
  induction j with
  | zero =>
      rw [show node₀.length + 0 = node₀.length by omega,
        branchNode_splicedRight_take (A := A) node₀ branch node₀.length
          (Nat.le_refl _),
        List.take_length]
      simp [senderRNode, branchNode]
  | succ j ih =>
      show
        branchNode (splicedRightBranch (A := A) node₀ branch)
            (node₀.length + j) ++
          [splicedRightBranch (A := A) node₀ branch (node₀.length + j)] =
          _
      rw [ih]
      rw [show splicedRightBranch (A := A) node₀ branch
          (node₀.length + j) =
        Sum.inr (Sum.inr (branch j)) by
        simp only [splicedRightBranch]
        rw [dif_neg (by omega)]
        rw [show node₀.length + j - node₀.length = j by omega]]
      rw [show branchNode branch (j + 1) =
        branchNode branch j ++ [branch j] from rfl]
      rw [senderRNode_append (A := A), ← List.append_assoc]

/-- Acceptance forces the right checker to win the narrowed subtree of
a trapped block. -/
theorem winningTree_of_trapped_right
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (node₀ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (atom₀ : A.State × A.State)
    (hrun₀ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₀ =
        Sum.inl atom₀) :
    DeterministicBlockMonitor.WinningTree
      { CR.monitor with initial := CR.start atom₀.1 }
      (narrowedRightAt t node₀) := by
  intro branch
  have hs :=
    accepts_branch_priorities t CL CR CC hacc
      (splicedRightBranch (A := A) node₀ branch)
  have hs1 := (natSeqMinEvenParity_shift _ (node₀.length + 1)).mpr hs
  have hfun :
      (fun j =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial))
              (branchNode (splicedRightBranch (A := A) node₀ branch)
                (node₀.length + 1 + j)))) =
        fun j =>
          CR.monitor.priority
              (CR.monitor.controlIn (narrowedRightAt t node₀)
                (CR.start atom₀.1) (branchNode branch (j + 1))) +
            globalShift (In₁ := In₁) A := by
    funext j
    rw [show node₀.length + 1 + j = node₀.length + (j + 1) by omega]
    rw [branchNode_splicedRight_extend (A := A) node₀ branch (j + 1)]
    rw [show branchNode branch (j + 1) =
      branchNode branch j ++ [branch j] from rfl]
    obtain ⟨threads, hth⟩ :=
      globalRunIn_trapped_right t CL CR CC node₀ atom₀ hrun₀
        (branchNode branch j) (branch j)
    rw [hth]
    rfl
  rw [hfun] at hs1
  have hs3 :=
    (natSeqMinEvenParity_add_const
      (globalShift_even (In₁ := In₁) (A := A))).mp hs1
  have hs4 :=
    (natSeqMinEvenParity_shift
      (fun n =>
        CR.monitor.priority
          (CR.monitor.controlIn (narrowedRightAt t node₀)
            (CR.start atom₀.1) (branchNode branch n))) 1).mp
      (by
        have hidx :
            (fun j =>
                CR.monitor.priority
                  (CR.monitor.controlIn (narrowedRightAt t node₀)
                    (CR.start atom₀.1) (branchNode branch (j + 1)))) =
              fun n =>
                CR.monitor.priority
                  (CR.monitor.controlIn (narrowedRightAt t node₀)
                    (CR.start atom₀.1) (branchNode branch (1 + n))) := by
          funext j
          rw [show 1 + j = j + 1 by omega]
        rw [← hidx]
        exact hs3)
  have hfin :
      (fun n =>
          ({ CR.monitor with initial := CR.start atom₀.1 } :
              DeterministicBlockMonitor In₁
                (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
                  (A.State × A.State))).priority
            (DeterministicBlockMonitor.control _ (narrowedRightAt t node₀)
              (branchNode branch n))) =
        fun n =>
          CR.monitor.priority
            (CR.monitor.controlIn (narrowedRightAt t node₀)
              (CR.start atom₀.1) (branchNode branch n)) := by
    funext n
    show
      CR.monitor.priority
          (({ CR.monitor with initial := CR.start atom₀.1 } :
              DeterministicBlockMonitor In₁
                (NarrowedBlockLabel In₂ In₁ Out₂ Out₁
                  (A.State × A.State))).controlIn
            (narrowedRightAt t node₀) (CR.start atom₀.1)
            (branchNode branch n)) =
        _
    rw [DeterministicBlockMonitor.controlIn_update_initial]
  rw [hfin]
  exact hs4

/--
Regime two, right orientation: the mirror of the left tail parity.
-/
theorem priorities_min_even_of_trapped_right
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hcons :
      CountableParityGame.Strategy.Consistent
        (G :=
          DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control))
        (treeStrategy t) path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    {m₀ : Nat}
    {pair : A.State × A.State}
    {plan :
      BoundaryPlan (In₁ := In₁) A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)}
    (hcom : path m₀ = Sum.inr (Sum.inl (pair, plan)))
    (htail :
      ∀ m : Nat, m₀ < m ->
        ∃ data, path m = Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) :
    NatSeqMinEvenParity
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n)) := by
  have htracks := treeTracks_of_consistent t CL CR CC path hplay hcons
  have hm₀ := htracks m₀
  unfold TreeTracks at hm₀
  rw [hcom] at hm₀
  obtain ⟨⟨atom₀, hrun₀, hpair⟩, hplan⟩ := hm₀
  subst hpair
  subst hplan
  have hwin :=
    (CR.winning_iff atom₀.1 (narrowedRightAt t (playNodes t path m₀))).mp
      (winningTree_of_trapped_right t CL CR CC hacc (playNodes t path m₀)
        atom₀ hrun₀)
  have hdchoice :
      ∀ k : Nat,
        ∃ data,
          path (m₀ + 1 + k) =
            Sum.inr (Sum.inr (Sum.inr (Sum.inl data))) :=
    fun k => htail (m₀ + 1 + k) (by omega)
  have hd :
      ∀ k : Nat,
        path (m₀ + 1 + k) =
          Sum.inr (Sum.inr (Sum.inr (Sum.inl
            (Classical.choose (hdchoice k))))) :=
    fun k => Classical.choose_spec (hdchoice k)
  have hstep₀ :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) (path m₀) (path (m₀ + 1)) :=
    hplay.2 m₀
  rw [show m₀ + 1 = m₀ + 1 + 0 by omega] at hstep₀
  rw [hcom, hd 0] at hstep₀
  have hopen' := exists_openRight_of_step t hstep₀
  have hcont' :
      ∀ k : Nat,
        ∃ move : In₂ × In₁,
          (Sum.inr (Sum.inr (Sum.inr (Sum.inl
              (Classical.choose (hdchoice (k + 1)))))) :
              BoundaryGamePosition (In₁ := In₁) A
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)
                (ULift.{max u v x y, s} t.Control)) =
            A.rightContinueTarget (Classical.choose (hdchoice k)).1
              (Classical.choose (hdchoice k)).2.1
              (Classical.choose (hdchoice k)).2.2.1
              (Classical.choose (hdchoice k)).2.2.2.1
              (Classical.choose (hdchoice k)).2.2.2.2 move := by
    intro k
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (m₀ + 1 + k))
          (path (m₀ + 1 + k + 1)) :=
      hplay.2 (m₀ + 1 + k)
    rw [show m₀ + 1 + k + 1 = m₀ + 1 + (k + 1) by omega] at hstep
    rw [hd k, hd (k + 1)] at hstep
    exact exists_continueR_of_step t hstep
  set e0 := Classical.choose hopen' with he0
  let env : Nat -> In₂ × In₁ := fun k =>
    Nat.casesOn k e0 fun j => Classical.choose (hcont' j)
  have htrack :
      ∀ k : Nat,
        (Classical.choose (hdchoice k)).2.2.2 =
          narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (narrowedRightAt t (playNodes t path m₀)) env (k + 1) ∧
        playNodes t path (m₀ + 1 + k) =
          playNodes t path m₀ ++
            senderRNode (A := A)
              (senderWord (branchNode env (k + 1))) := by
    intro k
    induction k with
    | zero =>
        constructor
        · have hspec' :=
            Sum.inl.inj
              (Sum.inr.inj
                (Sum.inr.inj (Sum.inr.inj (Classical.choose_spec hopen'))))
          rw [← he0] at hspec'
          rw [hspec']
          show
            _ =
              (A.rightBlockMonitor atom₀.1).step (atom₀.1, atom₀.1)
                (narrowedRecord (A.rightBlockMonitor atom₀.1)
                  (narrowedRightAt t (playNodes t path m₀) [])
                  (atom₀.1, atom₀.1) e0)
          rw [narrowedRightAt_nil]
          rfl
        · show
            playNodes t path m₀ ++
                stepDirections t (path m₀) (path (m₀ + 1 + 0)) =
              _
          rw [hcom, hd 0,
            stepDirections_committed_blockR t _ _ _ hopen', ← he0]
          rfl
    | succ k ih =>
        have henv : env (k + 1) = Classical.choose (hcont' k) := rfl
        constructor
        · have hspec' :=
            Sum.inl.inj
              (Sum.inr.inj
                (Sum.inr.inj
                  (Sum.inr.inj (Classical.choose_spec (hcont' k)))))
          have hiw := ih.2
          rcases hsplit : Classical.choose (hdchoice k) with
            ⟨pl, ch, c, q, mn⟩
          have htk := htracks (m₀ + 1 + k)
          unfold TreeTracks at htk
          rw [hd k, hsplit] at htk
          obtain ⟨-, hc, ⟨root, hpl⟩, -⟩ := htk
          subst hc
          subst hpl
          have h1 :
              (Classical.choose (hdchoice k)).1 = treeRightPlan t root := by
            rw [hsplit]
          have h2 :
              (Classical.choose (hdchoice k)).2.2.1 =
                ULift.up (t.controlAt (playNodes t path (m₀ + 1 + k))) := by
            rw [hsplit]
          have htables :
              ((Classical.choose (hdchoice k)).1.label
                  (Classical.choose (hdchoice k)).2.2.1) =
                narrowedRightAt t (playNodes t path m₀)
                  (senderWord (branchNode env (k + 1))) := by
            rw [h1, h2]
            show
              GlobalJournalLabel.rightNarrowed
                  (t.labelOf
                    (t.controlAt (playNodes t path (m₀ + 1 + k)))) =
                _
            rw [hiw]
            rfl
          rw [hspec']
          show
            _ =
              narrowedControl (A.rightBlockMonitor atom₀.1)
                (narrowedRightAt t (playNodes t path m₀))
                (branchNode env (k + 1) ++ [env (k + 1)])
          rw [narrowedControl_append]
          rw [show narrowedControl (A.rightBlockMonitor atom₀.1)
              (narrowedRightAt t (playNodes t path m₀))
              (branchNode env (k + 1)) =
            (Classical.choose (hdchoice k)).2.2.2 from ih.1.symm]
          rw [← htables]
          rfl
        · show
            playNodes t path (m₀ + 1 + k) ++
                stepDirections t (path (m₀ + 1 + k))
                  (path (m₀ + 1 + (k + 1))) =
              _
          rw [hd k, hd (k + 1),
            stepDirections_blockR_blockR t _ _ (hcont' k), ih.2]
          rw [show branchNode env (k + 1 + 1) =
            branchNode env (k + 1) ++ [env (k + 1)] from rfl]
          rw [senderWord_append, senderRNode_append (A := A),
            ← List.append_assoc, henv]
  have hthread_parity := hwin env
  have hshift1 :=
    (natSeqMinEvenParity_shift
      (fun n =>
        (A.rightBlockMonitor atom₀.1).priority
          (narrowedThreadState (A.rightBlockMonitor atom₀.1)
            (narrowedRightAt t (playNodes t path m₀)) env n)) 1).mpr
      hthread_parity
  have hbridge :
      (fun k =>
          (A.rightBlockMonitor atom₀.1).priority
            (narrowedThreadState (A.rightBlockMonitor atom₀.1)
              (narrowedRightAt t (playNodes t path m₀)) env (1 + k))) =
        fun k =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (m₀ + 1 + k)) := by
    funext k
    rw [show (1 : Nat) + k = k + 1 by omega]
    rw [hd k]
    rw [← (htrack k).1]
    rfl
  rw [hbridge] at hshift1
  exact
    (natSeqMinEvenParity_shift
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n))
      (m₀ + 1)).mp hshift1

/-! ### The chain-regime machinery -/

/-- Direction embedding of a reversal-chain word. -/
def chainDirNode (w : TreeNode (In₂ ⊕ In₁)) :
    TreeNode (GlobalJournalBranch (In₁ := In₁) A) :=
  w.map Sum.inr

theorem chainDirNode_append (w : TreeNode (In₂ ⊕ In₁)) (x : In₂ ⊕ In₁) :
    chainDirNode (A := A) (w ++ [x]) =
      chainDirNode (A := A) w ++ [Sum.inr x] := by
  simp [chainDirNode]

/-- The reversed-block mode after a chain word: the sort of the last
consumed direction, the entry mode on the empty word (`true` is the
reversed-left mode). -/
def chainModeIsL (entryL : Bool) (w : TreeNode (In₂ ⊕ In₁)) : Bool :=
  match w.getLast? with
  | some (Sum.inl _) => true
  | some (Sum.inr _) => false
  | none => entryL

@[simp]
theorem chainModeIsL_append_inl (entryL : Bool)
    (w : TreeNode (In₂ ⊕ In₁)) (x : In₂) :
    chainModeIsL entryL (w ++ [Sum.inl x]) = true := by
  simp [chainModeIsL, List.getLast?_concat]

@[simp]
theorem chainModeIsL_append_inr (entryL : Bool)
    (w : TreeNode (In₂ ⊕ In₁)) (x : In₁) :
    chainModeIsL entryL (w ++ [Sum.inr x]) = false := by
  simp [chainModeIsL, List.getLast?_concat]

/-- The reversed four-value label tree along a chain below a node:
the mode selects the reversed-left or reversed-right label. -/
def chainNarrowedAt (entryL : Bool)
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)) :
    LabeledTree (In₂ ⊕ In₁)
      (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)) :=
  fun w =>
    if chainModeIsL entryL w then
      Sum.inl
        (GlobalJournalLabel.revLeft
          (t.labeledTree (node₁ ++ chainDirNode (A := A) w)))
    else
      Sum.inr
        (GlobalJournalLabel.revRight
          (t.labeledTree (node₁ ++ chainDirNode (A := A) w)))

theorem chainNarrowedAt_eq_left {entryL : Bool}
    {node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)}
    {w : TreeNode (In₂ ⊕ In₁)} (h : chainModeIsL entryL w = true) :
    chainNarrowedAt t entryL node₁ w =
      Sum.inl
        (GlobalJournalLabel.revLeft
          (t.labeledTree (node₁ ++ chainDirNode (A := A) w))) := by
  simp [chainNarrowedAt, h]

theorem chainNarrowedAt_eq_right {entryL : Bool}
    {node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A)}
    {w : TreeNode (In₂ ⊕ In₁)} (h : chainModeIsL entryL w = false) :
    chainNarrowedAt t entryL node₁ w =
      Sum.inr
        (GlobalJournalLabel.revRight
          (t.labeledTree (node₁ ++ chainDirNode (A := A) w))) := by
  simp [chainNarrowedAt, h]

/-- The reversed-mode automaton state of the given mode. -/
def revModePos (b : Bool)
    (checker : CC.monitor.State) (threads : Finset (ChainThread A)) :
    GlobalJournalState (In₁ := In₁) A CL CR CC :=
  if b then Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads))))
  else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (checker, threads)))))

theorem globalJournalPriority_revModePos (b : Bool)
    (checker : CC.monitor.State)
    (threads : Finset (ChainThread A)) :
    globalJournalPriority A CL CR CC
        (revModePos (In₁ := In₁) CL CR CC b checker threads) =
      CC.monitor.priority checker + globalShift (In₁ := In₁) A := by
  rcases b with - | - <;> rfl

/-- Within a trapped reversal chain the run threads the chain checker
through the mode-selected reversed labels. -/
theorem globalRunIn_trapped_chain (entryL : Bool)
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (T₀ : Finset (ChainThread A))
    (hrun₁ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₁ =
        revModePos (In₁ := In₁) CL CR CC entryL (CC.start T₀) T₀) :
    ∀ (w : TreeNode (In₂ ⊕ In₁)) (x : In₂ ⊕ In₁),
      ∃ threads,
        globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
            (node₁ ++ chainDirNode (A := A) (w ++ [x])) =
          revModePos (In₁ := In₁) CL CR CC
            (chainModeIsL entryL (w ++ [x]))
            (DeterministicBlockMonitor.controlIn CC.monitor
              (chainNarrowedAt t entryL node₁) (CC.start T₀) (w ++ [x]))
            threads := by
  have hnil :
      ∀ b : Bool,
        chainNarrowedAt t b node₁ [] =
          if b then
            Sum.inl (GlobalJournalLabel.revLeft (t.labeledTree node₁))
          else
            Sum.inr (GlobalJournalLabel.revRight (t.labeledTree node₁)) := by
    intro b
    rcases b with - | -
    · rw [chainNarrowedAt_eq_right t (by rfl),
        show node₁ ++ chainDirNode (A := A)
            ([] : TreeNode (In₂ ⊕ In₁)) = node₁ by
          simp [chainDirNode]]
      rfl
    · rw [chainNarrowedAt_eq_left t (by rfl),
        show node₁ ++ chainDirNode (A := A)
            ([] : TreeNode (In₂ ⊕ In₁)) = node₁ by
          simp [chainDirNode]]
      rfl
  intro w
  induction w using List.reverseRecOn with
  | nil =>
      intro x
      rw [show chainDirNode (A := A) (([] : TreeNode (In₂ ⊕ In₁)) ++ [x]) =
        [Sum.inr x] from rfl]
      rw [globalRunIn_append, hrun₁]
      cases entryL <;> rcases x with x | x
      · refine
          ⟨revRightReverseSubset T₀
              (GlobalJournalLabel.revRight (t.labeledTree node₁)) x, ?_⟩
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC false (CC.start T₀) T₀)
              (t.labeledTree node₁) (Sum.inr (Sum.inl x)) =
            revModePos (In₁ := In₁) CL CR CC true
              (CC.monitor.step (CC.start T₀)
                (chainNarrowedAt t false node₁ []) (Sum.inl x))
              (revRightReverseSubset T₀
                (GlobalJournalLabel.revRight (t.labeledTree node₁)) x)
        rw [hnil false]
        rfl
      · refine
          ⟨revRightStepSubset T₀
              (GlobalJournalLabel.revRight (t.labeledTree node₁)) x, ?_⟩
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC false (CC.start T₀) T₀)
              (t.labeledTree node₁) (Sum.inr (Sum.inr x)) =
            revModePos (In₁ := In₁) CL CR CC false
              (CC.monitor.step (CC.start T₀)
                (chainNarrowedAt t false node₁ []) (Sum.inr x))
              (revRightStepSubset T₀
                (GlobalJournalLabel.revRight (t.labeledTree node₁)) x)
        rw [hnil false]
        rfl
      · refine
          ⟨revLeftStepSubset T₀
              (GlobalJournalLabel.revLeft (t.labeledTree node₁)) x, ?_⟩
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC true (CC.start T₀) T₀)
              (t.labeledTree node₁) (Sum.inr (Sum.inl x)) =
            revModePos (In₁ := In₁) CL CR CC true
              (CC.monitor.step (CC.start T₀)
                (chainNarrowedAt t true node₁ []) (Sum.inl x))
              (revLeftStepSubset T₀
                (GlobalJournalLabel.revLeft (t.labeledTree node₁)) x)
        rw [hnil true]
        rfl
      · refine
          ⟨revLeftReverseSubset T₀
              (GlobalJournalLabel.revLeft (t.labeledTree node₁)) x, ?_⟩
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC true (CC.start T₀) T₀)
              (t.labeledTree node₁) (Sum.inr (Sum.inr x)) =
            revModePos (In₁ := In₁) CL CR CC false
              (CC.monitor.step (CC.start T₀)
                (chainNarrowedAt t true node₁ []) (Sum.inr x))
              (revLeftReverseSubset T₀
                (GlobalJournalLabel.revLeft (t.labeledTree node₁)) x)
        rw [hnil true]
        rfl
  | append_singleton w x' ih =>
      intro x
      obtain ⟨threads, hih⟩ := ih x'
      have hsplit :
          node₁ ++ chainDirNode (A := A) ((w ++ [x']) ++ [x]) =
            (node₁ ++ chainDirNode (A := A) (w ++ [x'])) ++
              [Sum.inr x] := by
        rw [chainDirNode_append (A := A) (w ++ [x']) x, List.append_assoc]
      rcases hm : chainModeIsL entryL (w ++ [x']) with - | - <;>
        rcases x with x | x
      · refine
          ⟨revRightReverseSubset threads
              (GlobalJournalLabel.revRight
                (t.labeledTree
                  (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x, ?_⟩
        rw [hsplit, globalRunIn_append, hih, hm,
          chainModeIsL_append_inl,
          DeterministicBlockMonitor.controlIn_append CC.monitor
            (w ++ [x'])]
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC false
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                threads)
              (t.labeledTree
                (node₁ ++ chainDirNode (A := A) (w ++ [x'])))
              (Sum.inr (Sum.inl x)) =
            revModePos (In₁ := In₁) CL CR CC true
              (CC.monitor.step
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                (chainNarrowedAt t entryL node₁ (w ++ [x']))
                (Sum.inl x))
              (revRightReverseSubset threads
                (GlobalJournalLabel.revRight
                  (t.labeledTree
                    (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x)
        rw [chainNarrowedAt_eq_right t hm]
        rfl
      · refine
          ⟨revRightStepSubset threads
              (GlobalJournalLabel.revRight
                (t.labeledTree
                  (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x, ?_⟩
        rw [hsplit, globalRunIn_append, hih, hm,
          chainModeIsL_append_inr,
          DeterministicBlockMonitor.controlIn_append CC.monitor
            (w ++ [x'])]
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC false
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                threads)
              (t.labeledTree
                (node₁ ++ chainDirNode (A := A) (w ++ [x'])))
              (Sum.inr (Sum.inr x)) =
            revModePos (In₁ := In₁) CL CR CC false
              (CC.monitor.step
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                (chainNarrowedAt t entryL node₁ (w ++ [x']))
                (Sum.inr x))
              (revRightStepSubset threads
                (GlobalJournalLabel.revRight
                  (t.labeledTree
                    (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x)
        rw [chainNarrowedAt_eq_right t hm]
        rfl
      · refine
          ⟨revLeftStepSubset threads
              (GlobalJournalLabel.revLeft
                (t.labeledTree
                  (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x, ?_⟩
        rw [hsplit, globalRunIn_append, hih, hm,
          chainModeIsL_append_inl,
          DeterministicBlockMonitor.controlIn_append CC.monitor
            (w ++ [x'])]
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC true
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                threads)
              (t.labeledTree
                (node₁ ++ chainDirNode (A := A) (w ++ [x'])))
              (Sum.inr (Sum.inl x)) =
            revModePos (In₁ := In₁) CL CR CC true
              (CC.monitor.step
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                (chainNarrowedAt t entryL node₁ (w ++ [x']))
                (Sum.inl x))
              (revLeftStepSubset threads
                (GlobalJournalLabel.revLeft
                  (t.labeledTree
                    (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x)
        rw [chainNarrowedAt_eq_left t hm]
        rfl
      · refine
          ⟨revLeftReverseSubset threads
              (GlobalJournalLabel.revLeft
                (t.labeledTree
                  (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x, ?_⟩
        rw [hsplit, globalRunIn_append, hih, hm,
          chainModeIsL_append_inr,
          DeterministicBlockMonitor.controlIn_append CC.monitor
            (w ++ [x'])]
        show
          globalJournalStep A CL CR CC
              (revModePos (In₁ := In₁) CL CR CC true
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                threads)
              (t.labeledTree
                (node₁ ++ chainDirNode (A := A) (w ++ [x'])))
              (Sum.inr (Sum.inr x)) =
            revModePos (In₁ := In₁) CL CR CC false
              (CC.monitor.step
                (DeterministicBlockMonitor.controlIn CC.monitor
                  (chainNarrowedAt t entryL node₁) (CC.start T₀)
                  (w ++ [x']))
                (chainNarrowedAt t entryL node₁ (w ++ [x']))
                (Sum.inr x))
              (revLeftReverseSubset threads
                (GlobalJournalLabel.revLeft
                  (t.labeledTree
                    (node₁ ++ chainDirNode (A := A) (w ++ [x'])))) x)
        rw [chainNarrowedAt_eq_left t hm]
        rfl

/-- Branch splicing a node prefix with a chain continuation. -/
def splicedChainBranch
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂ ⊕ In₁) (k : Nat) :
    GlobalJournalBranch (In₁ := In₁) A :=
  if h : k < node₁.length then node₁[k]
  else Sum.inr (branch (k - node₁.length))

theorem branchNode_splicedChain_take
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂ ⊕ In₁) :
    ∀ j : Nat, j ≤ node₁.length ->
      branchNode (splicedChainBranch (A := A) node₁ branch) j =
        node₁.take j := by
  intro j
  induction j with
  | zero =>
      intro _
      rfl
  | succ j ih =>
      intro hj
      show
        branchNode (splicedChainBranch (A := A) node₁ branch) j ++
            [splicedChainBranch (A := A) node₁ branch j] =
          node₁.take (j + 1)
      rw [ih (by omega)]
      have hlt : j < node₁.length := by omega
      rw [show splicedChainBranch (A := A) node₁ branch j = node₁[j] by
        simp only [splicedChainBranch]; rw [dif_pos hlt]]
      rw [List.take_add_one, List.getElem?_eq_getElem hlt]
      rfl

theorem branchNode_splicedChain_extend
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (branch : Nat -> In₂ ⊕ In₁) :
    ∀ j : Nat,
      branchNode (splicedChainBranch (A := A) node₁ branch)
          (node₁.length + j) =
        node₁ ++ chainDirNode (A := A) (branchNode branch j) := by
  intro j
  induction j with
  | zero =>
      rw [show node₁.length + 0 = node₁.length by omega,
        branchNode_splicedChain_take (A := A) node₁ branch node₁.length
          (Nat.le_refl _),
        List.take_length]
      simp [chainDirNode, branchNode]
  | succ j ih =>
      show
        branchNode (splicedChainBranch (A := A) node₁ branch)
            (node₁.length + j) ++
          [splicedChainBranch (A := A) node₁ branch (node₁.length + j)] =
          _
      rw [ih]
      rw [show splicedChainBranch (A := A) node₁ branch
          (node₁.length + j) =
        Sum.inr (branch j) by
        simp only [splicedChainBranch]
        rw [dif_neg (by omega)]
        rw [show node₁.length + j - node₁.length = j by omega]]
      rw [show branchNode branch (j + 1) =
        branchNode branch j ++ [branch j] from rfl]
      rw [chainDirNode_append (A := A), ← List.append_assoc]

/-- Acceptance forces the chain checker to win the mode-selected
reversed subtree of a trapped chain. -/
theorem winningTree_of_trapped_chain
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (entryL : Bool)
    (node₁ : TreeNode (GlobalJournalBranch (In₁ := In₁) A))
    (T₀ : Finset (ChainThread A))
    (hrun₁ :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          node₁ =
        revModePos (In₁ := In₁) CL CR CC entryL (CC.start T₀) T₀) :
    DeterministicBlockMonitor.WinningTree
      { CC.monitor with initial := CC.start T₀ }
      (chainNarrowedAt t entryL node₁) := by
  intro branch
  have hs :=
    accepts_branch_priorities t CL CR CC hacc
      (splicedChainBranch (A := A) node₁ branch)
  have hs1 := (natSeqMinEvenParity_shift _ (node₁.length + 1)).mpr hs
  have hfun :
      (fun j =>
          globalJournalPriority A CL CR CC
            (globalRunIn CL CR CC t.labeledTree
              (Sum.inl (A.initial, A.initial))
              (branchNode (splicedChainBranch (A := A) node₁ branch)
                (node₁.length + 1 + j)))) =
        fun j =>
          CC.monitor.priority
              (CC.monitor.controlIn (chainNarrowedAt t entryL node₁)
                (CC.start T₀) (branchNode branch (j + 1))) +
            globalShift (In₁ := In₁) A := by
    funext j
    rw [show node₁.length + 1 + j = node₁.length + (j + 1) by omega]
    rw [branchNode_splicedChain_extend (A := A) node₁ branch (j + 1)]
    rw [show branchNode branch (j + 1) =
      branchNode branch j ++ [branch j] from rfl]
    obtain ⟨threads, hth⟩ :=
      globalRunIn_trapped_chain t CL CR CC entryL node₁ T₀ hrun₁
        (branchNode branch j) (branch j)
    rw [hth]
    rw [globalJournalPriority_revModePos]
  rw [hfun] at hs1
  have hs3 :=
    (natSeqMinEvenParity_add_const
      (globalShift_even (In₁ := In₁) (A := A))).mp hs1
  have hs4 :=
    (natSeqMinEvenParity_shift
      (fun n =>
        CC.monitor.priority
          (CC.monitor.controlIn (chainNarrowedAt t entryL node₁)
            (CC.start T₀) (branchNode branch n))) 1).mp
      (by
        have hidx :
            (fun j =>
                CC.monitor.priority
                  (CC.monitor.controlIn (chainNarrowedAt t entryL node₁)
                    (CC.start T₀) (branchNode branch (j + 1)))) =
              fun n =>
                CC.monitor.priority
                  (CC.monitor.controlIn (chainNarrowedAt t entryL node₁)
                    (CC.start T₀) (branchNode branch (1 + n))) := by
          funext j
          rw [show 1 + j = j + 1 by omega]
        rw [← hidx]
        exact hs3)
  have hfin :
      (fun n =>
          ({ CC.monitor with initial := CC.start T₀ } :
              DeterministicBlockMonitor (In₂ ⊕ In₁)
                (ChainLabel In₁ In₂ Out₁ Out₂
                  (A.State × A.State))).priority
            (DeterministicBlockMonitor.control _
              (chainNarrowedAt t entryL node₁) (branchNode branch n))) =
        fun n =>
          CC.monitor.priority
            (CC.monitor.controlIn (chainNarrowedAt t entryL node₁)
              (CC.start T₀) (branchNode branch n)) := by
    funext n
    show
      CC.monitor.priority
          (({ CC.monitor with initial := CC.start T₀ } :
              DeterministicBlockMonitor (In₂ ⊕ In₁)
                (ChainLabel In₁ In₂ Out₁ Out₂
                  (A.State × A.State))).controlIn
            (chainNarrowedAt t entryL node₁) (CC.start T₀)
            (branchNode branch n)) =
        _
    rw [DeterministicBlockMonitor.controlIn_update_initial]
  rw [hfin]
  exact hs4

/-! ### The endpoint: acceptance makes the tree strategy win -/

/--
The chain-regime obligation of the boundary game: along any consistent
play of the tree strategy that is eventually trapped in the directly
reversed tiers, acceptance of the journal tree forces min-even parity
of the play priorities.  This is the boundary-game counterpart of the
chain-tail regime of the tau tree; it is discharged from the chain
checker's `winning_iff` by splicing the reversed suffix into an
accepted branch (M2-5).
-/
def TrappedChainMinEven : Prop :=
  ∀ (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)),
    (DetParityAutomaton.boundaryGame A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)).PlayFrom
      (Sum.inl (A.initial, A.initial)) path ->
    CountableParityGame.Strategy.Consistent
      (G :=
        DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
      (treeStrategy t) path ->
    (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree ->
    ∀ m₁ : Nat,
      (∀ m : Nat, m₁ ≤ m ->
        (∃ data,
          path m =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
          (∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))))) ->
      NatSeqMinEvenParity
        (fun n =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority (path n))

theorem chainFold_concat
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State))) :
    ∀ (steps : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
      (word : List (In₂ ⊕ In₁)) (qm : ChainThread A)
      (st : (In₁ × In₂) × (In₂ ⊕ In₁)),
      chainFold A narrowed word qm (steps ++ [st]) =
        chainThreadStep A (chainFold A narrowed word qm steps)
          (narrowed (word ++ steps.map Prod.snd)) st.2 st.1
  | [], word, qm, st => by simp [chainFold]
  | s :: rest, word, qm, st => by
      show chainFold A narrowed (word ++ [s.2])
          (chainThreadStep A qm (narrowed word) s.2 s.1) (rest ++ [st]) =
        _
      rw [chainFold_concat narrowed rest (word ++ [s.2]) _ st,
        List.append_assoc]
      rfl

theorem chainFold_concat_nil
    (narrowed :
      LabeledTree (In₂ ⊕ In₁)
        (ChainLabel In₁ In₂ Out₁ Out₂ (A.State × A.State)))
    (steps : TreeNode ((In₁ × In₂) × (In₂ ⊕ In₁)))
    (qm : ChainThread A) (st : (In₁ × In₂) × (In₂ ⊕ In₁)) :
    chainFold A narrowed [] qm (steps ++ [st]) =
      chainThreadStep A (chainFold A narrowed [] qm steps)
        (narrowed (steps.map Prod.snd)) st.2 st.1 := by
  rw [chainFold_concat]
  rfl

/-- The reversed game tier of the given mode (`true` is the
reversed-left tier). -/
def revTierPos (b : Bool)
    (data :
      (ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)) ×
        ULift.{max u v x y, s} t.Control × (A.State × A.State) ×
          A.State × A.State) :
    BoundaryGamePosition (In₁ := In₁) A
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control)
      (ULift.{max u v x y, s} t.Control) :=
  if b then Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))
  else Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))

theorem boundaryPriority_revTierPos (b : Bool)
    (data :
      (ChainPlan (In₁ := In₁) (In₂ := In₂) (Out₁ := Out₁)
          (Out₂ := Out₂) A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)) ×
        ULift.{max u v x y, s} t.Control × (A.State × A.State) ×
          A.State × A.State) :
    boundaryPriority A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (revTierPos t b data) =
      A.priority data.2.2.2.1 := by
  rcases b with - | - <;> rfl

/-- The chain tail from a reversed-right entry out of a left block:
the played thread is a composed chain thread of the trapped chain, so
acceptance forces min-even parity of the play priorities. -/
theorem chainTail_min_even_from_revR
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (M : Nat) (thr : Finset (A.State × A.State))
    {chk : CL.monitor.State} {root : t.Control} {q mn : A.State}
    (hrevAfter :
      ∀ m : Nat, M < m ->
        (∃ data,
          path m =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
          (∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))))
    (hrunM :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path M) =
        Sum.inr (Sum.inl (chk, thr)))
    (hmem : (q, mn) ∈ thr)
    (hposM :
      path M =
        Sum.inr (Sum.inr (Sum.inl
          (treeLeftPlan t root, treeChainPlan t,
            ULift.up (t.controlAt (playNodes t path M)), q, mn))))
    (hex :
      ∃ mv : In₁ × In₂,
        path (M + 1) =
          A.leftReverseTarget (treeLeftPlan t root) (treeChainPlan t)
            (ULift.up (t.controlAt (playNodes t path M))) q mn mv) :
    NatSeqMinEvenParity
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n)) := by
  have hM1 := Classical.choose_spec hex
  set mv := Classical.choose hex with hmvdef
  -- normal form of the entry position
  have hM1' :
      path (M + 1) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
          (treeChainPlan t,
            ULift.up
              (t.step (t.controlAt (playNodes t path M))
                (Sum.inr (Sum.inr mv.1))),
            (A.step q
                (rightRoundRecord (mv.2, mv.1)
                  (GlobalJournalLabel.leftRev (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv.1)
                  (GlobalJournalLabel.leftClose (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv)),
              A.minPriorityState mn
                (A.step q
                  (rightRoundRecord (mv.2, mv.1)
                    (GlobalJournalLabel.leftRev (t.labelOf
                        (t.controlAt (playNodes t path M)))
                      (q, mn) mv.1)
                    (GlobalJournalLabel.leftClose (t.labelOf
                        (t.controlAt (playNodes t path M)))
                      (q, mn) mv)))),
            A.step q
              (rightRoundRecord (mv.2, mv.1)
                (GlobalJournalLabel.leftRev (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) mv.1)
                (GlobalJournalLabel.leftClose (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) mv)),
            A.minPriorityState mn
              (A.step q
                (rightRoundRecord (mv.2, mv.1)
                  (GlobalJournalLabel.leftRev (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv.1)
                  (GlobalJournalLabel.leftClose (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv)))))))) := by
    rw [hM1]
    rfl
  have hc :
      ∃ move' : In₁ × In₂,
        path (M + 1) =
          A.leftReverseTarget
            (treeLeftPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).1
            (treeLeftPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.1
            (treeLeftPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.1
            (treeLeftPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.2.1
            (treeLeftPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.2.2
            move' :=
    ⟨mv, hM1⟩
  rw [hM1'] at hc
  have hnode1 :
      playNodes t path (M + 1) =
        playNodes t path M ++
          [Sum.inr (Sum.inr (Classical.choose hc).1)] := by
    show
      playNodes t path M ++
          stepDirections t (path M) (path (M + 1)) =
        _
    rw [hposM, hM1', stepDirections_blockL_revR t _ _ hc]
  have hspec := Classical.choose_spec hc
  set m' := Classical.choose hc with hm'def
  simp only [leftReverseTarget, treeLeftPlan, treeChainPlan,
    Sum.inr.injEq, Prod.mk.injEq, true_and] at hspec
  obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
  -- the handoff thread set and the entry run state
  set T₀ :=
    leftReverseSubset thr
      (GlobalJournalLabel.leftClose (t.labeledTree (playNodes t path M)))
      (GlobalJournalLabel.leftRev (t.labeledTree (playNodes t path M)))
      m'.1 with hT₀def
  have hrun1 :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path (M + 1)) =
        revModePos (In₁ := In₁) CL CR CC false (CC.start T₀) T₀ := by
    rw [hnode1, globalRunIn_append, hrunM]
    rfl
  set node₁ := playNodes t path (M + 1) with hnode₁def
  set Q1 :=
    A.step q
      (rightRoundRecord (mv.2, mv.1)
        (GlobalJournalLabel.leftRev (t.labelOf
            (t.controlAt (playNodes t path M)))
          (q, mn) mv.1)
        (GlobalJournalLabel.leftClose (t.labelOf
            (t.controlAt (playNodes t path M)))
          (q, mn) mv)) with hQ1def
  have hqm :
      ((Q1, A.minPriorityState mn Q1), Q1, A.minPriorityState mn Q1) ∈
        T₀ := by
    refine
      Finset.mem_biUnion.mpr
        ⟨(q, mn), hmem,
          Finset.mem_image.mpr ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
    show
      ((A.step q
            (rightRoundRecord (m'.2, m'.1)
              (GlobalJournalLabel.leftRev (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m'.1)
              (GlobalJournalLabel.leftClose (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m')),
          A.minPriorityState mn
            (A.step q
              (rightRoundRecord (m'.2, m'.1)
                (GlobalJournalLabel.leftRev (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) m'.1)
                (GlobalJournalLabel.leftClose (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) m')))),
        A.step q
          (rightRoundRecord (m'.2, m'.1)
            (GlobalJournalLabel.leftRev (t.labelOf
                (t.controlAt (playNodes t path M)))
              (q, mn) m'.1)
            (GlobalJournalLabel.leftClose (t.labelOf
                (t.controlAt (playNodes t path M)))
              (q, mn) m')),
        A.minPriorityState mn
          (A.step q
            (rightRoundRecord (m'.2, m'.1)
              (GlobalJournalLabel.leftRev (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m'.1)
              (GlobalJournalLabel.leftClose (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m')))) =
        _
    rw [hQ1def, ← hnEq]
  have hwin :=
    (CC.winning_iff T₀ (chainNarrowedAt t false node₁)).mp
      (winningTree_of_trapped_chain t CL CR CC hacc false node₁ T₀
        hrun1)
      ((Q1, A.minPriorityState mn Q1), Q1, A.minPriorityState mn Q1)
      hqm
  -- the entry position, tier form
  have hd1 :
      path (M + 1) =
        revTierPos t false
          (treeChainPlan t,
            ULift.up (t.controlAt node₁),
            (Q1, A.minPriorityState mn Q1),
            Q1, A.minPriorityState mn Q1) := by
    rw [hM1']
    show _ =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
        (treeChainPlan t, ULift.up (t.controlAt node₁),
          (Q1, A.minPriorityState mn Q1),
          Q1, A.minPriorityState mn Q1)))))
    have hcEq' :
        (ULift.up
            (t.step (t.controlAt (playNodes t path M))
              (Sum.inr (Sum.inr mv.1))) :
          ULift.{max u v x y, s} t.Control) =
          ULift.up
            (t.step (t.controlAt (playNodes t path M))
              (Sum.inr (Sum.inr m'.1))) := hcEq
    rw [hnode1, controlAt_concat, hcEq']
  -- the per-round packaged step
  have hexk :
      ∀ k : Nat,
        ∃ st : (In₁ × In₂) × (In₂ ⊕ In₁),
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revLeftContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inl st.1.2) ∨
              (path (M + 1 + (k + 1)) =
                  A.revLeftReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inr st.1.1)) ∧
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revRightContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inr st.1.1) ∨
              (path (M + 1 + (k + 1)) =
                  A.revRightReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inl st.1.2)) := by
    intro k
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (M + 1 + k))
          (path (M + 1 + k + 1)) :=
      hplay.2 (M + 1 + k)
    rcases hrevAfter (M + 1 + k) (by omega) with ⟨d₀, hd₀⟩ | ⟨d₀, hd₀⟩
    · rw [hd₀] at hstep
      rcases hstep with ⟨mv', hn⟩ | ⟨mv', hn⟩ | ⟨mv', hn⟩
      · refine ⟨(mv', Sum.inl mv'.2), fun data hdata => ?_, fun data hdata => ?_⟩
        · obtain rfl :=
            Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inl ⟨hn, rfl⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
      · exact
          absurd hn
            (by
              rcases hrevAfter (M + 1 + k + 1) (by omega) with
                ⟨d, hd⟩ | ⟨d, hd⟩ <;>
                · intro hn'
                  rw [hn'] at hd
                  exact absurd hd (by simp [revLeftCloseTarget]))
      · refine ⟨(mv', Sum.inr mv'.1), fun data hdata => ?_, fun data hdata => ?_⟩
        · obtain rfl :=
            Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inr ⟨hn, rfl⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
    · rw [hd₀] at hstep
      rcases hstep with ⟨mv', hn⟩ | ⟨mv', hn⟩ | ⟨mv', hn⟩
      · refine ⟨(mv', Sum.inr mv'.1), fun data hdata => ?_, fun data hdata => ?_⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
        · obtain rfl :=
            Sum.inr.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inl ⟨hn, rfl⟩
      · exact
          absurd hn
            (by
              rcases hrevAfter (M + 1 + k + 1) (by omega) with
                ⟨d, hd⟩ | ⟨d, hd⟩ <;>
                · intro hn'
                  rw [hn'] at hd
                  exact absurd hd (by simp [revRightCloseTarget]))
      · refine ⟨(mv', Sum.inl mv'.2), fun data hdata => ?_, fun data hdata => ?_⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
        · obtain rfl :=
            Sum.inr.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inr ⟨hn, rfl⟩
  obtain ⟨env, henv⟩ :
      ∃ env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁),
        ∀ k : Nat,
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revLeftContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inl (env k).1.2) ∨
              (path (M + 1 + (k + 1)) =
                  A.revLeftReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inr (env k).1.1)) ∧
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revRightContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inr (env k).1.1) ∨
              (path (M + 1 + (k + 1)) =
                  A.revRightReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inl (env k).1.2)) :=
    ⟨fun k => Classical.choose (hexk k),
      fun k => Classical.choose_spec (hexk k)⟩
  -- the tail invariant
  have hinv :
      ∀ k : Nat,
        path (M + 1 + k) =
          revTierPos t
            (chainModeIsL false ((branchNode env k).map Prod.snd))
            (treeChainPlan t,
              ULift.up
                (t.controlAt
                  (node₁ ++
                    chainDirNode (A := A)
                      ((branchNode env k).map Prod.snd))),
              (chainFold A (chainNarrowedAt t false node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).1,
              (chainFold A (chainNarrowedAt t false node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).2.1,
              (chainFold A (chainNarrowedAt t false node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).2.2) := by
    intro k
    induction k with
    | zero =>
        rw [show M + 1 + 0 = M + 1 by omega, hd1]
        rw [show node₁ ++
            chainDirNode (A := A)
              ((branchNode env 0).map Prod.snd) = node₁ by
          simp [branchNode, chainDirNode]]
        rfl
    | succ k ih =>
        have hstk := henv k
        have hbranch :
            branchNode env (k + 1) = branchNode env k ++ [env k] := rfl
        rcases hm :
            chainModeIsL false ((branchNode env k).map Prod.snd) with
          - | -
        · -- reversed-right mode
          have hpos := ih
          rw [hm] at hpos
          have hcl := hstk.2 _ hpos
          rcases hcl with ⟨hn, hdir⟩ | ⟨hn, hdir⟩
          · -- continue in reversed-right mode
            rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_right t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inr, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
          · -- reverse into the reversed-left mode
            rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_right t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inl, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
        · -- reversed-left mode
          have hpos := ih
          rw [hm] at hpos
          have hcl := hstk.1 _ hpos
          rcases hcl with ⟨hn, hdir⟩ | ⟨hn, hdir⟩
          · rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_left t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inl, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
          · rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_left t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inr, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
  -- assemble: the play priorities are the composed-thread priorities
  have hfin := hwin env
  have hbridge :
      (fun k =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (M + 1 + k))) =
        fun k =>
          A.priority
            (chainFold A (chainNarrowedAt t false node₁) []
                ((Q1, A.minPriorityState mn Q1),
                  Q1, A.minPriorityState mn Q1)
                (branchNode env k)).2.1 := by
    funext k
    show
      boundaryPriority A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (M + 1 + k)) =
        _
    rw [hinv k, boundaryPriority_revTierPos]
  exact
    (natSeqMinEvenParity_shift
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n))
      (M + 1)).mp (by rw [hbridge]; exact hfin)

/-- The chain tail from a reversed-left entry out of a right block:
the orientation mirror. -/
theorem chainTail_min_even_from_revL
    (path :
      Nat ->
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
    (hplay :
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).PlayFrom
        (Sum.inl (A.initial, A.initial)) path)
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree)
    (M : Nat) (thr : Finset (A.State × A.State))
    {chk : CR.monitor.State} {root : t.Control} {q mn : A.State}
    (hrevAfter :
      ∀ m : Nat, M < m ->
        (∃ data,
          path m =
            Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))) ∨
          (∃ data,
            path m =
              Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))))
    (hrunM :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path M) =
        Sum.inr (Sum.inr (Sum.inl (chk, thr))))
    (hmem : (q, mn) ∈ thr)
    (hposM :
      path M =
        Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (treeRightPlan t root, treeChainPlan t,
            ULift.up (t.controlAt (playNodes t path M)), q, mn)))))
    (hex :
      ∃ mv : In₂ × In₁,
        path (M + 1) =
          A.rightReverseTarget (treeRightPlan t root) (treeChainPlan t)
            (ULift.up (t.controlAt (playNodes t path M))) q mn mv) :
    NatSeqMinEvenParity
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n)) := by
  have hM1 := Classical.choose_spec hex
  set mv := Classical.choose hex with hmvdef
  -- normal form of the entry position
  have hM1' :
      path (M + 1) =
        Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
          (treeChainPlan t,
            ULift.up
              (t.step (t.controlAt (playNodes t path M))
                (Sum.inr (Sum.inl mv.1))),
            (A.step q
                (leftRoundRecord (mv.2, mv.1)
                  (GlobalJournalLabel.rightClose (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv)
                  (GlobalJournalLabel.rightRev (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv.1)),
              A.minPriorityState mn
                (A.step q
                  (leftRoundRecord (mv.2, mv.1)
                    (GlobalJournalLabel.rightClose (t.labelOf
                        (t.controlAt (playNodes t path M)))
                      (q, mn) mv)
                    (GlobalJournalLabel.rightRev (t.labelOf
                        (t.controlAt (playNodes t path M)))
                      (q, mn) mv.1)))),
            A.step q
              (leftRoundRecord (mv.2, mv.1)
                (GlobalJournalLabel.rightClose (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) mv)
                (GlobalJournalLabel.rightRev (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) mv.1)),
            A.minPriorityState mn
              (A.step q
                (leftRoundRecord (mv.2, mv.1)
                  (GlobalJournalLabel.rightClose (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv)
                  (GlobalJournalLabel.rightRev (t.labelOf
                      (t.controlAt (playNodes t path M)))
                    (q, mn) mv.1)))))))) := by
    rw [hM1]
    rfl
  have hc :
      ∃ move' : In₂ × In₁,
        path (M + 1) =
          A.rightReverseTarget
            (treeRightPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).1
            (treeRightPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.1
            (treeRightPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.1
            (treeRightPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.2.1
            (treeRightPlan t root, treeChainPlan t,
              ULift.up.{max u v x y, s}
                (t.controlAt (playNodes t path M)), q, mn).2.2.2.2
            move' :=
    ⟨mv, hM1⟩
  rw [hM1'] at hc
  have hnode1 :
      playNodes t path (M + 1) =
        playNodes t path M ++
          [Sum.inr (Sum.inl (Classical.choose hc).1)] := by
    show
      playNodes t path M ++
          stepDirections t (path M) (path (M + 1)) =
        _
    rw [hposM, hM1', stepDirections_blockR_revL t _ _ hc]
  have hspec := Classical.choose_spec hc
  set m' := Classical.choose hc with hm'def
  simp only [rightReverseTarget, treeRightPlan, treeChainPlan,
    Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq, true_and] at hspec
  obtain ⟨hcEq, heEq, hnEq, hmEq⟩ := hspec
  -- the handoff thread set and the entry run state
  set T₀ :=
    rightReverseSubset thr
      (GlobalJournalLabel.rightClose (t.labeledTree (playNodes t path M)))
      (GlobalJournalLabel.rightRev (t.labeledTree (playNodes t path M)))
      m'.1 with hT₀def
  have hrun1 :
      globalRunIn CL CR CC t.labeledTree (Sum.inl (A.initial, A.initial))
          (playNodes t path (M + 1)) =
        revModePos (In₁ := In₁) CL CR CC true (CC.start T₀) T₀ := by
    rw [hnode1, globalRunIn_append, hrunM]
    rfl
  set node₁ := playNodes t path (M + 1) with hnode₁def
  set Q1 :=
    A.step q
      (leftRoundRecord (mv.2, mv.1)
        (GlobalJournalLabel.rightClose (t.labelOf
            (t.controlAt (playNodes t path M)))
          (q, mn) mv)
        (GlobalJournalLabel.rightRev (t.labelOf
            (t.controlAt (playNodes t path M)))
          (q, mn) mv.1)) with hQ1def
  have hqm :
      ((Q1, A.minPriorityState mn Q1), Q1, A.minPriorityState mn Q1) ∈
        T₀ := by
    refine
      Finset.mem_biUnion.mpr
        ⟨(q, mn), hmem,
          Finset.mem_image.mpr ⟨m'.2, Finset.mem_univ _, ?_⟩⟩
    show
      ((A.step q
            (leftRoundRecord (m'.2, m'.1)
              (GlobalJournalLabel.rightClose (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m')
              (GlobalJournalLabel.rightRev (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m'.1)),
          A.minPriorityState mn
            (A.step q
              (leftRoundRecord (m'.2, m'.1)
                (GlobalJournalLabel.rightClose (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) m')
                (GlobalJournalLabel.rightRev (t.labelOf
                    (t.controlAt (playNodes t path M)))
                  (q, mn) m'.1)))),
        A.step q
          (leftRoundRecord (m'.2, m'.1)
            (GlobalJournalLabel.rightClose (t.labelOf
                (t.controlAt (playNodes t path M)))
              (q, mn) m')
            (GlobalJournalLabel.rightRev (t.labelOf
                (t.controlAt (playNodes t path M)))
              (q, mn) m'.1)),
        A.minPriorityState mn
          (A.step q
            (leftRoundRecord (m'.2, m'.1)
              (GlobalJournalLabel.rightClose (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m')
              (GlobalJournalLabel.rightRev (t.labelOf
                  (t.controlAt (playNodes t path M)))
                (q, mn) m'.1)))) =
        _
    rw [hQ1def, ← hnEq]
  have hwin :=
    (CC.winning_iff T₀ (chainNarrowedAt t true node₁)).mp
      (winningTree_of_trapped_chain t CL CR CC hacc true node₁ T₀
        hrun1)
      ((Q1, A.minPriorityState mn Q1), Q1, A.minPriorityState mn Q1)
      hqm
  -- the entry position, tier form
  have hd1 :
      path (M + 1) =
        revTierPos t true
          (treeChainPlan t,
            ULift.up (t.controlAt node₁),
            (Q1, A.minPriorityState mn Q1),
            Q1, A.minPriorityState mn Q1) := by
    rw [hM1']
    show _ =
      Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl
        (treeChainPlan t, ULift.up (t.controlAt node₁),
          (Q1, A.minPriorityState mn Q1),
          Q1, A.minPriorityState mn Q1)))))
    have hcEq' :
        (ULift.up
            (t.step (t.controlAt (playNodes t path M))
              (Sum.inr (Sum.inl mv.1))) :
          ULift.{max u v x y, s} t.Control) =
          ULift.up
            (t.step (t.controlAt (playNodes t path M))
              (Sum.inr (Sum.inl m'.1))) := hcEq
    rw [hnode1, controlAt_concat, hcEq']
  -- the per-round packaged step
  have hexk :
      ∀ k : Nat,
        ∃ st : (In₁ × In₂) × (In₂ ⊕ In₁),
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revLeftContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inl st.1.2) ∨
              (path (M + 1 + (k + 1)) =
                  A.revLeftReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inr st.1.1)) ∧
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revRightContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inr st.1.1) ∨
              (path (M + 1 + (k + 1)) =
                  A.revRightReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 st.1 ∧
                st.2 = Sum.inl st.1.2)) := by
    intro k
    have hstep :
        boundaryStep A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (M + 1 + k))
          (path (M + 1 + k + 1)) :=
      hplay.2 (M + 1 + k)
    rcases hrevAfter (M + 1 + k) (by omega) with ⟨d₀, hd₀⟩ | ⟨d₀, hd₀⟩
    · rw [hd₀] at hstep
      rcases hstep with ⟨mv', hn⟩ | ⟨mv', hn⟩ | ⟨mv', hn⟩
      · refine ⟨(mv', Sum.inl mv'.2), fun data hdata => ?_, fun data hdata => ?_⟩
        · obtain rfl :=
            Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inl ⟨hn, rfl⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
      · exact
          absurd hn
            (by
              rcases hrevAfter (M + 1 + k + 1) (by omega) with
                ⟨d, hd⟩ | ⟨d, hd⟩ <;>
                · intro hn'
                  rw [hn'] at hd
                  exact absurd hd (by simp [revLeftCloseTarget]))
      · refine ⟨(mv', Sum.inr mv'.1), fun data hdata => ?_, fun data hdata => ?_⟩
        · obtain rfl :=
            Sum.inl.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inr ⟨hn, rfl⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
    · rw [hd₀] at hstep
      rcases hstep with ⟨mv', hn⟩ | ⟨mv', hn⟩ | ⟨mv', hn⟩
      · refine ⟨(mv', Sum.inr mv'.1), fun data hdata => ?_, fun data hdata => ?_⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
        · obtain rfl :=
            Sum.inr.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inl ⟨hn, rfl⟩
      · exact
          absurd hn
            (by
              rcases hrevAfter (M + 1 + k + 1) (by omega) with
                ⟨d, hd⟩ | ⟨d, hd⟩ <;>
                · intro hn'
                  rw [hn'] at hd
                  exact absurd hd (by simp [revRightCloseTarget]))
      · refine ⟨(mv', Sum.inl mv'.2), fun data hdata => ?_, fun data hdata => ?_⟩
        · exact absurd (hd₀.symm.trans hdata) (by simp)
        · obtain rfl :=
            Sum.inr.inj
              (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj (Sum.inr.inj
                (hd₀.symm.trans hdata)))))
          exact Or.inr ⟨hn, rfl⟩
  obtain ⟨env, henv⟩ :
      ∃ env : Nat -> (In₁ × In₂) × (In₂ ⊕ In₁),
        ∀ k : Nat,
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revLeftContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inl (env k).1.2) ∨
              (path (M + 1 + (k + 1)) =
                  A.revLeftReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inr (env k).1.1)) ∧
          (∀ data,
            path (M + 1 + k) =
                Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data)))) ->
              (path (M + 1 + (k + 1)) =
                  A.revRightContinueTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inr (env k).1.1) ∨
              (path (M + 1 + (k + 1)) =
                  A.revRightReverseTarget data.1 data.2.1 data.2.2.1
                    data.2.2.2.1 data.2.2.2.2 (env k).1 ∧
                (env k).2 = Sum.inl (env k).1.2)) :=
    ⟨fun k => Classical.choose (hexk k),
      fun k => Classical.choose_spec (hexk k)⟩
  -- the tail invariant
  have hinv :
      ∀ k : Nat,
        path (M + 1 + k) =
          revTierPos t
            (chainModeIsL true ((branchNode env k).map Prod.snd))
            (treeChainPlan t,
              ULift.up
                (t.controlAt
                  (node₁ ++
                    chainDirNode (A := A)
                      ((branchNode env k).map Prod.snd))),
              (chainFold A (chainNarrowedAt t true node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).1,
              (chainFold A (chainNarrowedAt t true node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).2.1,
              (chainFold A (chainNarrowedAt t true node₁) []
                  ((Q1, A.minPriorityState mn Q1),
                    Q1, A.minPriorityState mn Q1)
                  (branchNode env k)).2.2) := by
    intro k
    induction k with
    | zero =>
        rw [show M + 1 + 0 = M + 1 by omega, hd1]
        rw [show node₁ ++
            chainDirNode (A := A)
              ((branchNode env 0).map Prod.snd) = node₁ by
          simp [branchNode, chainDirNode]]
        rfl
    | succ k ih =>
        have hstk := henv k
        have hbranch :
            branchNode env (k + 1) = branchNode env k ++ [env k] := rfl
        rcases hm :
            chainModeIsL true ((branchNode env k).map Prod.snd) with
          - | -
        · -- reversed-right mode
          have hpos := ih
          rw [hm] at hpos
          have hcl := hstk.2 _ hpos
          rcases hcl with ⟨hn, hdir⟩ | ⟨hn, hdir⟩
          · -- continue in reversed-right mode
            rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_right t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inr, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
          · -- reverse into the reversed-left mode
            rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_right t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inl, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
        · -- reversed-left mode
          have hpos := ih
          rw [hm] at hpos
          have hcl := hstk.1 _ hpos
          rcases hcl with ⟨hn, hdir⟩ | ⟨hn, hdir⟩
          · rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_left t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inl, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
          · rw [hn, hbranch]
            simp only [List.map_append, List.map_cons, List.map_nil]
            rw [chainFold_concat_nil, chainNarrowedAt_eq_left t hm]
            simp only [hdir]
            rw [chainModeIsL_append_inr, chainDirNode_append (A := A),
              ← List.append_assoc, controlAt_concat]
            rfl
  -- assemble: the play priorities are the composed-thread priorities
  have hfin := hwin env
  have hbridge :
      (fun k =>
          (DetParityAutomaton.boundaryGame A
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)
              (ULift.{max u v x y, s} t.Control)).priority
            (path (M + 1 + k))) =
        fun k =>
          A.priority
            (chainFold A (chainNarrowedAt t true node₁) []
                ((Q1, A.minPriorityState mn Q1),
                  Q1, A.minPriorityState mn Q1)
                (branchNode env k)).2.1 := by
    funext k
    show
      boundaryPriority A (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control) (path (M + 1 + k)) =
        _
    rw [hinv k, boundaryPriority_revTierPos]
  exact
    (natSeqMinEvenParity_shift
      (fun n =>
        (DetParityAutomaton.boundaryGame A
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)
            (ULift.{max u v x y, s} t.Control)).priority (path n))
      (M + 1)).mp (by rw [hbridge]; exact hfin)

/-- Acceptance discharges the chain regime: a consistent play of the
tree strategy that is eventually trapped in the reversed tiers has
min-even priorities. -/
theorem trappedChainMinEven_of_accepts :
    TrappedChainMinEven (In₁ := In₁) t CL CR CC := by
  intro path hplay hcons hacc m₁ htail
  have htracks := treeTracks_of_consistent t CL CR CC path hplay hcons
  set RevL : Nat -> Prop := fun m =>
    ∃ data,
      path m = Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl data))))
    with hRevLdef
  set RevR : Nat -> Prop := fun m =>
    ∃ data,
      path m = Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr data))))
    with hRevRdef
  letI : DecidablePred fun m => ¬ (RevL m ∨ RevR m) :=
    fun _ => Classical.propDecidable _
  have hP0 : ¬ (RevL 0 ∨ RevR 0) := by
    rintro (⟨d, h⟩ | ⟨d, h⟩) <;>
      · rw [hplay.1] at h
        simp at h
  set M := Nat.findGreatest (fun m => ¬ (RevL m ∨ RevR m)) m₁ with hMdef
  have hPM : ¬ (RevL M ∨ RevR M) := by
    rw [hMdef]
    exact
      Nat.findGreatest_spec (P := fun m => ¬ (RevL m ∨ RevR m))
        (m := 0) (Nat.zero_le m₁) hP0
  have hMle : M ≤ m₁ := Nat.findGreatest_le m₁
  have hMlt : M < m₁ := by
    rcases Nat.lt_or_ge M m₁ with h | h
    · exact h
    · exfalso
      have hMeq : M = m₁ := Nat.le_antisymm hMle h
      apply hPM
      rw [hMeq]
      exact htail m₁ (Nat.le_refl m₁)
  have hrevAfter : ∀ m : Nat, M < m -> RevL m ∨ RevR m := by
    intro m hm
    rcases Nat.le_total m₁ m with h | h
    · exact htail m h
    · by_contra hno
      exact
        Nat.findGreatest_is_greatest (P := fun m => ¬ (RevL m ∨ RevR m))
          (by rw [← hMdef]; exact hm) h hno
  have hrev1 := hrevAfter (M + 1) (by omega)
  have hstepM :
      boundaryStep A (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control) (path M) (path (M + 1)) :=
    hplay.2 M
  -- the entry classification: the last non-reversed position closes
  -- into the chain through a block reversal
  rcases hposM : path M with atom | ⟨pr, pl⟩ |
    ⟨pl, ch, ctl, q, mn⟩ | ⟨pl, ch, ctl, q, mn⟩ | dat | dat
  · rw [hposM] at hstepM
    obtain ⟨plan', hn⟩ := hstepM
    rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;> rw [hn] at hd <;>
      exact absurd hd (by simp)
  · rw [hposM] at hstepM
    rcases hstepM with ⟨mv, hn⟩ | ⟨mv, hn⟩ | ⟨mv, hn⟩ <;>
      rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;> rw [hn] at hd <;>
      exact absurd hd (by
        simp [boundaryBothTarget, boundaryOpenLeftTarget,
          boundaryOpenRightTarget])
  · -- left block: the reversal enters the reversed-right mode
    rw [hposM] at hstepM
    have hM := htracks M
    unfold TreeTracks at hM
    rw [hposM] at hM
    obtain ⟨⟨chk, thr, hrunM, hmem⟩, hctl, ⟨root, hpl⟩, hchain⟩ := hM
    subst hpl
    subst hctl
    subst hchain
    rcases hstepM with ⟨mv, hn⟩ | ⟨mv, hn⟩ | ⟨mv, hn⟩
    · exact absurd hn (by
        rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
          · rw [hd]
            simp [leftContinueTarget])
    · exact absurd hn (by
        rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
          · rw [hd]
            simp [leftCloseTarget])
    · exact
        chainTail_min_even_from_revR t CL CR CC path hplay hacc
          M thr hrevAfter hrunM hmem hposM ⟨mv, hn⟩
  · -- right block: the reversal enters the reversed-left mode
    rw [hposM] at hstepM
    have hM := htracks M
    unfold TreeTracks at hM
    rw [hposM] at hM
    obtain ⟨⟨chk, thr, hrunM, hmem⟩, hctl, ⟨root, hpl⟩, hchain⟩ := hM
    subst hpl
    subst hctl
    subst hchain
    rcases hstepM with ⟨mv, hn⟩ | ⟨mv, hn⟩ | ⟨mv, hn⟩
    · exact absurd hn (by
        rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
          · rw [hd]
            simp [rightContinueTarget])
    · exact absurd hn (by
        rcases hrev1 with ⟨d, hd⟩ | ⟨d, hd⟩ <;>
          · rw [hd]
            simp [rightCloseTarget])
    · exact
        chainTail_min_even_from_revL t CL CR CC path hplay hacc
          M thr hrevAfter hrunM hmem hposM ⟨mv, hn⟩
  · exact absurd (Or.inl ⟨dat, hposM⟩) hPM
  · exact absurd (Or.inr ⟨dat, hposM⟩) hPM

/--
If the global journal automaton accepts the tree, the tree strategy
wins the boundary game from the initial boundary.
-/
theorem treeStrategy_winningFrom_of_accepts
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree) :
    CountableParityGame.Strategy.WinningFrom
      (G :=
        DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control))
      (treeStrategy t) (Sum.inl (A.initial, A.initial)) := by
  refine ⟨treeStrategy_legal t, ?_⟩
  intro path hplay hcons
  show
    (DetParityAutomaton.boundaryGame A
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)
        (ULift.{max u v x y, s} t.Control)).MinPriorityEven path
  by_cases hinf : ∀ n : Nat, ∃ m : Nat, n ≤ m ∧ IsBoundaryAt t path m
  · exact
      priorities_min_even_of_infinite_boundaries t CL CR CC path hplay
        hcons hacc hinf
  · push Not at hinf
    obtain ⟨N, hN⟩ := hinf
    obtain ⟨m₀, ⟨pair, plan, hcom⟩, htail⟩ :=
      exists_trapped_block t path hplay (N := N) fun m hm => hN m hm
    rcases htail with htail | htail | ⟨m₁, hm₁, htail⟩
    · exact
        priorities_min_even_of_trapped_left t CL CR CC path hplay hcons
          hacc hcom htail
    · exact
        priorities_min_even_of_trapped_right t CL CR CC path hplay hcons
          hacc hcom htail
    · exact
        trappedChainMinEven_of_accepts t CL CR CC path hplay hcons hacc
          m₁ htail

/-- The initial boundary lies in Even's winning region. -/
theorem bnd_initial_mem_winningRegion_of_accepts
    (hacc : (globalJournalAutomaton A CL CR CC).acceptsTree t.labeledTree) :
    (Sum.inl (A.initial, A.initial) :
        BoundaryGamePosition (In₁ := In₁) A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)) ∈
      (DetParityAutomaton.boundaryGame A
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)
          (ULift.{max u v x y, s} t.Control)).WinningRegion
        ParityPlayer.even :=
  ⟨treeStrategy t,
    treeStrategy_winningFrom_of_accepts t CL CR CC hacc⟩

end RegimeTwo

end Acceptance

end DetParityAutomaton

end DistributedSynthesis
