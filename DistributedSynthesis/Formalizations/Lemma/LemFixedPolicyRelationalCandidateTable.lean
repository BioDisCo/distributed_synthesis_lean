/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemRelationalFamilySaturation
import DistributedSynthesis.Formalizations.Lemma.LemFixedPolicyPointedFamilyTable

/-!
# One fixed-policy table over tagged relational candidate sets

This file joins the two pieces which remain valid without decoding one hidden
descriptor at a receive.  The public state is a finite set of tagged
`(family, descriptor)` candidates.  Its successor is the finite saturation by
all exact, control-correct successors.  A proof-side cursor retains one actual
live candidate and proves that it remains in every advertised set.

The table is totalized with `Option Move`.  `none` is permitted only when the
current candidate set contains no live candidate.  Consequently an actual
branch always uses a genuine move.  Fixed-policy parity is proved independently
for the literal word of that same finite table.

The construction deliberately does not project the tagged set to the
coordinatewise union of its public families: that projection does not reflect
provenance.  It also exposes no selected candidate, orientation, lane, or
strict-leader signal.  Its sole new uniformity input is
`RelationalCandidateCommonMoveExists`: at every finite set containing a live
candidate, one public move must be semantically valid for every live candidate
in the set.  The final theorem shows that descriptor-pointed totality supplies
all other one-step obligations.
-/

namespace DistributedSynthesis

universe f d m q i₁ i₂ o₁ o₂ pa

/-! ## Candidate-wide validity and live successor coverage -/

/-- A finite tagged candidate set is active when it contains at least one
candidate with genuine semantic provenance. -/
def RelationalCandidateSetActive
    {Family : Type f} {Descriptor : Type d}
    (Live : Descriptor → Family → Prop)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor)) : Prop :=
  ∃ candidate ∈ candidates, Live candidate.2 candidate.1

/-- One public move is valid simultaneously for every live tagged candidate.
No condition is imposed on deliberately retained non-live over-approximants. -/
def RelationalCandidateCommonMove
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) : Prop :=
  ∀ candidate ∈ candidates,
    Live candidate.2 candidate.1 →
      CandidateValid candidate.2 candidate.1 move

/-- The one genuine uniformity boundary of the candidate-set construction. -/
def RelationalCandidateCommonMoveExists
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop) : Prop :=
  ∀ candidates : Finset (RelationalFamilyCandidate Family Descriptor),
    RelationalCandidateSetActive Live candidates →
      ∃ move, RelationalCandidateCommonMove Live CandidateValid candidates move

/-- Optional completion of candidate-wide validity.  The fallback is legal
exactly on sets with no live candidate. -/
def RelationalCandidateOptionValid
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor)) :
    Option Move → Prop
  | some move => RelationalCandidateCommonMove Live CandidateValid candidates move
  | none => ¬ RelationalCandidateSetActive Live candidates

/-- Per-live-candidate successor coverage.  The selected target is both an
exact member of the saturation relation and live at its retained family tag. -/
def RelationalCandidateLiveSuccessorCoverage
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop) : Prop :=
  ∀ source move query,
    Live source.2 source.1 →
    CandidateValid source.2 source.1 move →
      ∃ target,
        RelationalFamilyCandidateGood ExactEdge ControlStep source move query
            target ∧
          Live target.2 target.1

theorem relationalCandidateOptionValid_total
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (common : RelationalCandidateCommonMoveExists Live CandidateValid)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor)) :
    ∃ move, RelationalCandidateOptionValid Live CandidateValid candidates move := by
  by_cases hactive : RelationalCandidateSetActive Live candidates
  · obtain ⟨move, hmove⟩ := common candidates hactive
    exact ⟨some move, hmove⟩
  · exact ⟨none, hactive⟩

/-- A live member rules out the optional fallback and exposes the common
candidate-wide validity of the genuine move. -/
theorem relationalCandidateOptionValid_some_of_live
    {Family : Type f} {Descriptor : Type d} {Move : Type m}
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (selected : Option Move)
    (hvalid : RelationalCandidateOptionValid Live CandidateValid candidates
      selected)
    (actual : RelationalFamilyCandidate Family Descriptor)
    (hactual : actual ∈ candidates)
    (hlive : Live actual.2 actual.1) :
    ∃ move, selected = some move ∧
      RelationalCandidateCommonMove Live CandidateValid candidates move := by
  cases selected with
  | none =>
      exact False.elim (hvalid ⟨actual, hactual, hlive⟩)
  | some move =>
      exact ⟨move, rfl, hvalid⟩

/-- The chosen live successor is contained in the full finite saturation;
the saturation may retain additional over-approximating candidates. -/
theorem exists_live_mem_relationalFamilySaturation
    {Family : Type f} {Descriptor : Type d} {Move : Type m} {Query : Type q}
    [Fintype Family] [Fintype Descriptor]
    (Live : Descriptor → Family → Prop)
    (CandidateValid : Descriptor → Family → Move → Prop)
    (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
    (ControlStep : Descriptor → Descriptor → Prop)
    (coverage : RelationalCandidateLiveSuccessorCoverage Live CandidateValid
      ExactEdge ControlStep)
    (candidates : Finset (RelationalFamilyCandidate Family Descriptor))
    (move : Move) (query : Query)
    (actual : RelationalFamilyCandidate Family Descriptor)
    (hactual : actual ∈ candidates)
    (hlive : Live actual.2 actual.1)
    (hvalid : RelationalCandidateCommonMove Live CandidateValid candidates move) :
    ∃ target ∈ relationalFamilySaturation ExactEdge ControlStep candidates
        move query,
      RelationalFamilyCandidateGood ExactEdge ControlStep actual move query
          target ∧
        Live target.2 target.1 := by
  obtain ⟨target, hgood, htargetLive⟩ :=
    coverage actual move query hlive (hvalid actual hactual hlive)
  refine ⟨target, ?_, hgood, htargetLive⟩
  exact (mem_relationalFamilySaturation_iff ExactEdge ControlStep candidates
    move query target).2 ⟨actual, hactual, hgood⟩

/-! ## A valid public candidate-set tree and its actual branch -/

section CandidateTree

variable {Family : Type f} {Descriptor : Type d} {Move : Type m}
  {Query : Type q}
variable [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Query]
variable [Inhabited Query]

variable
  (Live : Descriptor → Family → Prop)
  (CandidateValid : Descriptor → Family → Move → Prop)
  (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
  (ControlStep : Descriptor → Descriptor → Prop)

private abbrev CandidateSet (Family : Type f) (Descriptor : Type d) :=
  Finset (RelationalFamilyCandidate Family Descriptor)

private abbrev Observation (Family : Type f) (Descriptor : Type d)
    (Query : Type q) :=
  Query × CandidateSet Family Descriptor

/-- Canonical optional label selected solely from the current tagged set. -/
noncomputable def relationalCandidateCanonicalMove
    (common : RelationalCandidateCommonMoveExists Live CandidateValid)
    (candidates : CandidateSet (Family := Family) (Descriptor := Descriptor)) :
    Option Move :=
  Classical.choose
    (relationalCandidateOptionValid_total Live CandidateValid common candidates)

omit [Fintype Family] [Fintype Descriptor] [Fintype Move] in
theorem relationalCandidateCanonicalMove_valid
    (common : RelationalCandidateCommonMoveExists Live CandidateValid)
    (candidates : CandidateSet (Family := Family) (Descriptor := Descriptor)) :
    RelationalCandidateOptionValid Live CandidateValid candidates
      (relationalCandidateCanonicalMove Live CandidateValid common candidates) :=
  Classical.choose_spec
    (relationalCandidateOptionValid_total Live CandidateValid common candidates)

/-- Total source tree used only for the fixed-policy finite-table extraction.
Its labels depend on the public candidate set and on no hidden coordinate. -/
noncomputable def relationalCandidateCanonicalTree
    (common : RelationalCandidateCommonMoveExists Live CandidateValid)
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor)) :
    LabeledTree (Observation (Family := Family) (Descriptor := Descriptor)
      (Query := Query)) (Option Move) := fun node =>
  relationalCandidateCanonicalMove Live CandidateValid common
    (observableAt ((default : Query), initial) node).2

omit [Fintype Query] [Fintype Family] [Fintype Descriptor] [Fintype Move] in
theorem relationalCandidateCanonicalTree_movesValid
    (common : RelationalCandidateCommonMoveExists Live CandidateValid)
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor)) :
    ObservableMovesValid ((default : Query), initial)
      (fun observation move ↦
        RelationalCandidateOptionValid Live CandidateValid observation.2 move)
      (relationalCandidateCanonicalTree Live CandidateValid common initial) := by
  intro node
  exact relationalCandidateCanonicalMove_valid Live CandidateValid common
    (observableAt ((default : Query), initial) node).2

/-- Minimal monitor-independent package for following one actual live
candidate through a public tree over saturated candidate sets. -/
structure RelationalCandidateTreeBranchPackage
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor))
    (initialActual : RelationalFamilyCandidate Family Descriptor) where
  coverage : RelationalCandidateLiveSuccessorCoverage Live CandidateValid
    ExactEdge ControlStep
  initial_mem : initialActual ∈ initial
  initial_live : Live initialActual.2 initialActual.1
  tree : LabeledTree (Observation (Family := Family) (Descriptor := Descriptor)
    (Query := Query)) (Option Move)
  movesValid : ObservableMovesValid ((default : Query), initial)
    (fun observation move ↦
      RelationalCandidateOptionValid Live CandidateValid observation.2 move)
    tree

namespace RelationalCandidateTreeBranchPackage

variable {Live CandidateValid ExactEdge ControlStep}
variable {initial : CandidateSet (Family := Family) (Descriptor := Descriptor)}
variable {initialActual : RelationalFamilyCandidate Family Descriptor}
variable (package : RelationalCandidateTreeBranchPackage Live CandidateValid
  ExactEdge ControlStep initial initialActual)

/-- One reached public node coupled to one genuine actual candidate. -/
structure Cursor where
  node : TreeNode (Observation (Family := Family) (Descriptor := Descriptor)
    (Query := Query))
  candidates : CandidateSet (Family := Family) (Descriptor := Descriptor)
  actual : RelationalFamilyCandidate Family Descriptor
  /-- Literal public-table label at this node; retaining this equation makes
  the cursor definition depend on the concrete package. -/
  treeLabel : Option Move
  treeLabel_eq : treeLabel = package.tree node
  candidates_eq : candidates =
    (observableAt ((default : Query), initial) node).2
  actual_mem : actual ∈ candidates
  actual_live : Live actual.2 actual.1

def initialCursor : package.Cursor where
  node := []
  candidates := initial
  actual := initialActual
  treeLabel := package.tree []
  treeLabel_eq := rfl
  candidates_eq := rfl
  actual_mem := package.initial_mem
  actual_live := package.initial_live

omit [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Query] in
theorem Cursor.exists_move (cursor : package.Cursor) :
    ∃ move,
      package.tree cursor.node = some move ∧
        RelationalCandidateCommonMove Live CandidateValid cursor.candidates
          move := by
  have hvalid := package.movesValid cursor.node
  change RelationalCandidateOptionValid Live CandidateValid
    (observableAt ((default : Query), initial) cursor.node).2
      (package.tree cursor.node) at hvalid
  rw [← cursor.candidates_eq] at hvalid
  exact relationalCandidateOptionValid_some_of_live Live CandidateValid
    cursor.candidates (package.tree cursor.node) hvalid cursor.actual
    cursor.actual_mem cursor.actual_live

noncomputable def Cursor.move (cursor : package.Cursor) : Move :=
  Classical.choose (Cursor.exists_move package cursor)

section
omit [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Query]

theorem Cursor.tree_eq_some_move (cursor : package.Cursor) :
    package.tree cursor.node = some (Cursor.move package cursor) :=
  (Classical.choose_spec (Cursor.exists_move package cursor)).1

theorem Cursor.move_common (cursor : package.Cursor) :
    RelationalCandidateCommonMove Live CandidateValid cursor.candidates
      (Cursor.move package cursor) :=
  (Classical.choose_spec (Cursor.exists_move package cursor)).2

theorem Cursor.move_valid_actual (cursor : package.Cursor) :
    CandidateValid cursor.actual.2 cursor.actual.1
      (Cursor.move package cursor) :=
  (Cursor.move_common package cursor) cursor.actual cursor.actual_mem
    cursor.actual_live

end

omit [Fintype Move] [Fintype Query] in
theorem Cursor.exists_target (cursor : package.Cursor) (query : Query) :
    ∃ target ∈ relationalFamilySaturation ExactEdge ControlStep
        cursor.candidates (Cursor.move package cursor) query,
      RelationalFamilyCandidateGood ExactEdge ControlStep cursor.actual
          (Cursor.move package cursor) query target ∧
        Live target.2 target.1 :=
  exists_live_mem_relationalFamilySaturation Live CandidateValid ExactEdge
    ControlStep package.coverage cursor.candidates (Cursor.move package cursor)
    query cursor.actual cursor.actual_mem cursor.actual_live
    (Cursor.move_common package cursor)

noncomputable def Cursor.target (cursor : package.Cursor) (query : Query) :
    RelationalFamilyCandidate Family Descriptor :=
  Classical.choose (Cursor.exists_target package cursor query)

section
omit [Fintype Move] [Fintype Query]

theorem Cursor.target_mem (cursor : package.Cursor) (query : Query) :
    Cursor.target package cursor query ∈
      relationalFamilySaturation ExactEdge ControlStep cursor.candidates
        (Cursor.move package cursor) query :=
  (Classical.choose_spec (Cursor.exists_target package cursor query)).1

theorem Cursor.target_good (cursor : package.Cursor) (query : Query) :
    RelationalFamilyCandidateGood ExactEdge ControlStep cursor.actual
      (Cursor.move package cursor) query
      (Cursor.target package cursor query) :=
  (Classical.choose_spec (Cursor.exists_target package cursor query)).2.1

theorem Cursor.target_live (cursor : package.Cursor) (query : Query) :
    Live (Cursor.target package cursor query).2
      (Cursor.target package cursor query).1 :=
  (Classical.choose_spec (Cursor.exists_target package cursor query)).2.2

end

noncomputable def Cursor.step (cursor : package.Cursor) (query : Query) :
    package.Cursor where
  node := cursor.node ++ [(query,
    relationalFamilySaturation ExactEdge ControlStep cursor.candidates
      (Cursor.move package cursor) query)]
  candidates := relationalFamilySaturation ExactEdge ControlStep
    cursor.candidates (Cursor.move package cursor) query
  actual := Cursor.target package cursor query
  treeLabel := package.tree (cursor.node ++ [(query,
    relationalFamilySaturation ExactEdge ControlStep cursor.candidates
      (Cursor.move package cursor) query)])
  treeLabel_eq := rfl
  candidates_eq := by simp [observableAt]
  actual_mem := Cursor.target_mem package cursor query
  actual_live := Cursor.target_live package cursor query

noncomputable def cursorAt (query : Nat → Query) : Nat → package.Cursor
  | 0 => initialCursor package
  | n + 1 => Cursor.step package (cursorAt query n) (query n)

noncomputable def observationBranch (query : Nat → Query) (n : Nat) :
    Observation (Family := Family) (Descriptor := Descriptor) (Query := Query) :=
  let cursor := cursorAt package query n
  (query n, relationalFamilySaturation ExactEdge ControlStep cursor.candidates
    (Cursor.move package cursor) (query n))

omit [Fintype Move] [Fintype Query] in
theorem cursorAt_node (query : Nat → Query) : ∀ n,
    (cursorAt package query n).node =
      branchNode (observationBranch package query) n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change (cursorAt package query n).node ++
        [observationBranch package query n] = _
      rw [ih]
      rfl

noncomputable def moveAt (query : Nat → Query) (n : Nat) : Move :=
  Cursor.move package (cursorAt package query n)

noncomputable def candidateAt (query : Nat → Query) (n : Nat) :
    RelationalFamilyCandidate Family Descriptor :=
  (cursorAt package query n).actual

/-- The literal table word followed by the saturation branch. -/
noncomputable def word (query : Nat → Query) :
    OmegaWord (Option Move ×
      Observation (Family := Family) (Descriptor := Descriptor)
        (Query := Query)) := fun n =>
  (some (moveAt package query n), observationBranch package query n)

section
omit [Fintype Move] [Fintype Query]

theorem word_eq_observableThreadWord (query : Nat → Query) :
    word package query = observableThreadWord package.tree
      (observationBranch package query) := by
  funext n
  change (some (Cursor.move package (cursorAt package query n)),
      observationBranch package query n) =
    (package.tree (branchNode (observationBranch package query) n),
      observationBranch package query n)
  rw [← cursorAt_node package query n,
    Cursor.tree_eq_some_move package (cursorAt package query n)]

/-- The actual proof-side candidate is live at every depth. -/
theorem candidateAt_live (query : Nat → Query) (n : Nat) :
    Live (candidateAt package query n).2 (candidateAt package query n).1 :=
  (cursorAt package query n).actual_live

/-- The actual proof-side candidate belongs to every publicly carried tagged
set. -/
theorem candidateAt_mem (query : Nat → Query) (n : Nat) :
    candidateAt package query n ∈ (cursorAt package query n).candidates :=
  (cursorAt package query n).actual_mem

end

/-- The actual candidates form one genuine exact/control-correct thread. -/
noncomputable def exactThread (query : Nat → Query) :
    RelationalFamilyExactThread ExactEdge ControlStep initial
      (moveAt package query) query where
  candidate := candidateAt package query
  initial_mem := package.initial_mem
  exact := by
    intro n
    exact Cursor.target_good package (cursorAt package query n) (query n)

omit [Fintype Move] [Fintype Query] in
/-- The public set stored by the cursor is literally the iterated saturation,
not merely an unrelated over-approximation. -/
theorem cursorCandidates_eq_saturationAt (query : Nat → Query) : ∀ n,
    (cursorAt package query n).candidates =
      relationalFamilySaturationAt ExactEdge ControlStep initial
        (moveAt package query) query n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change relationalFamilySaturation ExactEdge ControlStep
          (cursorAt package query n).candidates
          (Cursor.move package (cursorAt package query n)) (query n) = _
      rw [relationalFamilySaturationAt_succ, ← ih]
      rfl

end RelationalCandidateTreeBranchPackage

end CandidateTree

/-! ## Fixed-policy finite-table extraction -/

namespace DetParityAutomaton

variable {In₁ : Type i₁} {In₂ : Type i₂} {Out₁ : Type o₁} {Out₂ : Type o₂}
variable
  (A : DetParityAutomaton.{max i₁ i₂ o₁ o₂, pa}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]
variable {initialState : PairedProfiledTreeState A}
variable (policy :
  (pairedProfiledEntryRunAutomaton A initialState).RationalTransitionPolicy)

variable {Family : Type f} {Descriptor : Type d} {Move : Type m}
  {Query : Type q}
variable [Fintype Family] [Fintype Descriptor] [Fintype Move] [Fintype Query]
variable [Inhabited Query]

variable
  (Live : Descriptor → Family → Prop)
  (CandidateValid : Descriptor → Family → Move → Prop)
  (ExactEdge : Descriptor → Move → Query → Family → Descriptor → Prop)
  (ControlStep : Descriptor → Descriptor → Prop)

private abbrev CandidateSet (Family : Type f) (Descriptor : Type d) :=
  Finset (RelationalFamilyCandidate Family Descriptor)

private abbrev Observation (Family : Type f) (Descriptor : Type d)
    (Query : Type q) :=
  Query × CandidateSet Family Descriptor

local instance : DecidableRel
    (fun observation : Observation (Family := Family) (Descriptor := Descriptor)
        (Query := Query) => fun move : Option Move =>
      RelationalCandidateOptionValid Live CandidateValid observation.2 move) :=
  fun _ _ ↦ Classical.propDecidable _

private abbrev FixedPolicyCandidateMonitor
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor)) :=
  observableThreadTreeMonitor
    (ProfiledFixedPolicyThreadState.system A policy
      (Option Move × Observation (Family := Family) (Descriptor := Descriptor)
        (Query := Query)) initialRoot)
    ((default : Query), initial)
    (fun observation move ↦
      RelationalCandidateOptionValid Live CandidateValid observation.2 move)

/-- One literal finite table with independent fixed-policy parity and one
genuine live exact candidate branch for every query word. -/
structure FixedPolicyRelationalCandidateTablePackage
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor))
    (initialActual : RelationalFamilyCandidate Family Descriptor) where
  table : RunParityTreeAutomaton.StateControlledTreeTable
    (FixedPolicyCandidateMonitor (A := A) (policy := policy) (Live := Live)
      (CandidateValid := CandidateValid) initialRoot initial
      (Move := Move) (Query := Query)).toRunAutomaton
  fixedPolicyWinning :
    (FixedPolicyCandidateMonitor (A := A) (policy := policy) (Live := Live)
      (CandidateValid := CandidateValid) initialRoot initial
      (Move := Move) (Query := Query)).WinningTree
        table.toTransitionRationalTree.labeledTree
  branch : RelationalCandidateTreeBranchPackage Live CandidateValid ExactEdge
    ControlStep initial initialActual
  branch_tree_eq : branch.tree =
    table.toTransitionRationalTree.labeledTree

namespace FixedPolicyRelationalCandidateTablePackage

variable {Live CandidateValid ExactEdge ControlStep}
variable {initialRoot : ProfiledFixedPolicyRoot A policy}
variable {initial : CandidateSet (Family := Family) (Descriptor := Descriptor)}
variable {initialActual : RelationalFamilyCandidate Family Descriptor}

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Fixed-policy parity holds on the same literal word which carries the
actual live candidate through the saturated public sets. -/
theorem fixedPolicy_accepts_candidateWord
    (package : FixedPolicyRelationalCandidateTablePackage A policy Live
      CandidateValid ExactEdge ControlStep initialRoot initial initialActual)
    (query : Nat → Query) :
    (ProfiledFixedPolicyThreadState.system A policy
      (Option Move × Observation (Family := Family) (Descriptor := Descriptor)
        (Query := Query)) initialRoot).universalRunDPA.Accepts
      (package.branch.word query) := by
  rw [package.branch.word_eq_observableThreadWord query, package.branch_tree_eq]
  exact ((observableThreadTreeMonitor_winning_iff
    (ProfiledFixedPolicyThreadState.system A policy
      (Option Move × Observation (Family := Family) (Descriptor := Descriptor)
        (Query := Query)) initialRoot)
    ((default : Query), initial)
    (fun observation move ↦
      RelationalCandidateOptionValid Live CandidateValid observation.2 move)
    package.table.toTransitionRationalTree.labeledTree).mp
      package.fixedPolicyWinning).2
        (package.branch.observationBranch query)

end FixedPolicyRelationalCandidateTablePackage

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Extract the candidate-set table.  Apart from ordinary live successor
coverage, the only uniformity premise is `common`: one move for every live
candidate in the currently carried finite set. -/
theorem exists_fixedPolicyRelationalCandidateTable
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initial : CandidateSet (Family := Family) (Descriptor := Descriptor))
    (initialActual : RelationalFamilyCandidate Family Descriptor)
    (hinitialMem : initialActual ∈ initial)
    (hinitialLive : Live initialActual.2 initialActual.1)
    (coverage : RelationalCandidateLiveSuccessorCoverage Live CandidateValid
      ExactEdge ControlStep)
    (common : RelationalCandidateCommonMoveExists Live CandidateValid) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy Live
        CandidateValid ExactEdge ControlStep initialRoot initial initialActual,
      ∀ query : Nat → Query,
        Nonempty (RelationalFamilyExactThread ExactEdge ControlStep initial
          (package.branch.moveAt query) query) := by
  let sourceTree : LabeledTree
      (Observation (Family := Family) (Descriptor := Descriptor) (Query := Query))
      (Option Move) :=
    relationalCandidateCanonicalTree Live CandidateValid common initial
  have hsourceValid : ObservableMovesValid ((default : Query), initial)
      (fun observation move ↦
        RelationalCandidateOptionValid Live CandidateValid observation.2 move)
      sourceTree :=
    relationalCandidateCanonicalTree_movesValid Live CandidateValid common
      initial
  obtain ⟨table, hwinning⟩ :=
    ProfiledFixedPolicyThreadState.exists_finite_observableTable_of_movesValid
      A policy initialRoot hinitial ((default : Query), initial)
      (fun observation move ↦
        RelationalCandidateOptionValid Live CandidateValid observation.2 move)
      sourceTree hsourceValid
  have htableValid : ObservableMovesValid ((default : Query), initial)
      (fun observation move ↦
        RelationalCandidateOptionValid Live CandidateValid observation.2 move)
      table.toTransitionRationalTree.labeledTree :=
    observableThreadTreeMonitor_valid_of_winning
      (ProfiledFixedPolicyThreadState.system A policy
        (Option Move × Observation (Family := Family) (Descriptor := Descriptor)
          (Query := Query)) initialRoot)
      ((default : Query), initial)
      (fun observation move ↦
        RelationalCandidateOptionValid Live CandidateValid observation.2 move)
      table.toTransitionRationalTree.labeledTree hwinning
  let branch : RelationalCandidateTreeBranchPackage Live CandidateValid
      ExactEdge ControlStep initial initialActual :=
    { coverage := coverage
      initial_mem := hinitialMem
      initial_live := hinitialLive
      tree := table.toTransitionRationalTree.labeledTree
      movesValid := htableValid }
  let package : FixedPolicyRelationalCandidateTablePackage A policy Live
      CandidateValid ExactEdge ControlStep initialRoot initial initialActual :=
    { table := table
      fixedPolicyWinning := hwinning
      branch := branch
      branch_tree_eq := rfl }
  refine ⟨package, ?_⟩
  intro query
  exact ⟨package.branch.exactThread query⟩

/-! ## Direct bridge from descriptor-pointed totality -/

universe c mi dc

variable {Code : Type c} {MoveIdentity : Type mi}
variable (D : DetParityAutomaton.{c, dc} Code)
variable [Fintype Code] [Fintype MoveIdentity]

variable
  (Represented : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (DescriptorLive : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)
  (DescriptorExactEdge : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    Move → Query →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity) → Prop)
  (Valid : HiddenDescriptorTwoFibreFamily D
      (MoveIdentity := MoveIdentity) → Move → Prop)
  (Supported : HiddenCodeControlDescriptor D
      (MoveIdentity := MoveIdentity) →
    HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) →
    Move → Query →
      HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity) → Prop)

omit [Fintype Move] [Fintype Query] [Inhabited Query] in
/-- Pointed totality supplies live successor coverage for the candidate-set
construction, one tagged source at a time. -/
theorem relationalCandidateLiveSuccessorCoverage_of_pointedTotality
    (totality : PointedHiddenDescriptorFamilyTotality D Represented
      DescriptorLive DescriptorExactEdge Valid Supported) :
    RelationalCandidateLiveSuccessorCoverage DescriptorLive
      (fun _ family move ↦ Valid family move) DescriptorExactEdge
      (fun current target ↦
        target.control = D.step current.control target.code) := by
  intro source move query hlive hvalid
  obtain ⟨nextFamily, hsupported⟩ := totality.supported_exists source.2
    source.1 move query hlive hvalid
  obtain ⟨target, hedge, hcontrol⟩ := totality.covers source.2 source.1
    move query nextFamily hlive hvalid hsupported
  refine ⟨(nextFamily, target), ⟨hedge, hcontrol⟩, ?_⟩
  exact totality.target_live source.2 source.1 move query nextFamily target
    hlive hvalid hsupported hedge

omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Final one-arrow form.  Descriptor-pointed totality discharges exact
successor existence and liveness.  The only additional model theorem is the
candidate-wide common-move law; it neither decodes a descriptor nor tells a
process which side is informed. -/
theorem exists_fixedPolicyRelationalCandidateTable_of_pointedTotality
    (initialRoot : ProfiledFixedPolicyRoot A policy)
    (hinitial : initialRoot.state A policy = policy.run [])
    (initial : Finset (RelationalFamilyCandidate
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity))))
    (initialActual : RelationalFamilyCandidate
      (HiddenDescriptorTwoFibreFamily D (MoveIdentity := MoveIdentity))
      (HiddenCodeControlDescriptor D (MoveIdentity := MoveIdentity)))
    (hinitialMem : initialActual ∈ initial)
    (hinitialLive : DescriptorLive initialActual.2 initialActual.1)
    (totality : PointedHiddenDescriptorFamilyTotality D Represented
      DescriptorLive DescriptorExactEdge Valid Supported)
    (common : RelationalCandidateCommonMoveExists DescriptorLive
      (fun _ family move ↦ Valid family move)) :
    ∃ package : FixedPolicyRelationalCandidateTablePackage A policy
        DescriptorLive (fun _ family move ↦ Valid family move)
        DescriptorExactEdge
        (fun current target ↦
          target.control = D.step current.control target.code)
        initialRoot initial initialActual,
      ∀ query : Nat → Query,
        Nonempty (RelationalFamilyExactThread DescriptorExactEdge
          (fun current target ↦
            target.control = D.step current.control target.code)
          initial (package.branch.moveAt query) query) := by
  apply exists_fixedPolicyRelationalCandidateTable A policy DescriptorLive
    (fun _ family move ↦ Valid family move) DescriptorExactEdge
    (fun current target ↦
      target.control = D.step current.control target.code)
    initialRoot hinitial initial initialActual hinitialMem hinitialLive
    (relationalCandidateLiveSuccessorCoverage_of_pointedTotality D Represented
      DescriptorLive DescriptorExactEdge Valid Supported totality)
    common

end

end DetParityAutomaton

end DistributedSynthesis
