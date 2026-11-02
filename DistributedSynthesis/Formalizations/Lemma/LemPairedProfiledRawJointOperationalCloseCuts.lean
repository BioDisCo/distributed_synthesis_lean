/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointUnitScheduledPhysicalSlicesOperational

/-!
# Operational close cuts

The old recurrent recut may place several simultaneous rounds inside one
epoch.  That is too coarse for a literal raw-joint close query, whose open
record list has one strict graph throughout.  This file gives the positive
replacement at the graph level.

At a strict round, the next cut is the first position at which that strict
graph changes.  Hence the last round before the next cut is the unique
closing round and every earlier round is a homogeneous strict open record.
At a simultaneous round, the next cut is the following position.  Thus every
simultaneous round, including each member of a consecutive run, is a
zero-open close block.

The construction is entirely proof-side.  It introduces no side, row,
orientation, or leader component into either local controller.
-/

namespace DistributedSynthesis

/-! ## Termination of strict runs -/

/-- Every strict run eventually changes graph.  This is the weakest
productivity assumption needed by the operational close clock; in particular
it follows from recurrent simultaneous rounds. -/
def OperationalStrictRunsTerminate (graphs : Nat → Graph) : Prop :=
  ∀ n : Nat, graphs n ≠ .both →
    ∃ m : Nat, n < m ∧ graphs m ≠ graphs n

/-- Recurrent simultaneous rounds terminate every strict run. -/
theorem operationalStrictRunsTerminate_of_graphBothRecurrent
    {graphs : Nat → Graph} (hboth : GraphBothRecurrent graphs) :
    OperationalStrictRunsTerminate graphs := by
  intro n hn
  rcases hboth (n + 1) with ⟨m, hm, hgraph⟩
  refine ⟨m, by omega, ?_⟩
  rw [hgraph]
  exact Ne.symm hn

/-- Recurrence of both strict directions terminates every strict run.  This
is a proof-side graph fact: the case distinction below does not expose the
current direction, or any leader bit, to a local controller. -/
theorem operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent
    {graphs : Nat → Graph} (hstrict : BothStrictDirectionsRecurrent graphs) :
    OperationalStrictRunsTerminate graphs := by
  intro n hn
  cases hgraph : graphs n with
  | left =>
      rcases hstrict.2 (n + 1) with ⟨m, hm, hright⟩
      refine ⟨m, by omega, ?_⟩
      rw [hright]
      exact Graph.noConfusion
  | right =>
      rcases hstrict.1 (n + 1) with ⟨m, hm, hleft⟩
      refine ⟨m, by omega, ?_⟩
      rw [hleft]
      exact Graph.noConfusion
  | both =>
      exact False.elim (hn hgraph)

/-- A persistent strict-reversal tail therefore supports the operational
close clock.  The `EventuallyNoBoth` component identifies the physical
acceptance regime; productivity itself uses only recurrence of both strict
directions. -/
theorem PersistentStrictReversalTail.operationalStrictRunsTerminate
    {graphs : Nat → Graph} (h : PersistentStrictReversalTail graphs) :
    OperationalStrictRunsTerminate graphs :=
  operationalStrictRunsTerminate_of_bothStrictDirectionsRecurrent h.2

/-! ## One operational close -/

/-- End of the next operational close block.  A `.both` round is consumed as
a singleton zero-open block.  A strict round consumes its complete maximal
homogeneous run. -/
noncomputable def operationalCloseNext
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (n : Nat) : Nat :=
  if hgraph : graphs n = .both then n + 1
  else Nat.find (hterm n hgraph)

@[simp] theorem operationalCloseNext_of_both
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    {n : Nat} (hgraph : graphs n = .both) :
    operationalCloseNext graphs hterm n = n + 1 := by
  simp [operationalCloseNext, hgraph]

theorem operationalCloseNext_of_strict
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    {n : Nat} (hgraph : graphs n ≠ .both) :
    operationalCloseNext graphs hterm n = Nat.find (hterm n hgraph) := by
  simp [operationalCloseNext, hgraph]

/-- Every operational close consumes at least its closing round. -/
theorem lt_operationalCloseNext
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (n : Nat) : n < operationalCloseNext graphs hterm n := by
  by_cases hgraph : graphs n = .both
  · simp [operationalCloseNext, hgraph]
  · rw [operationalCloseNext_of_strict graphs hterm hgraph]
    exact (Nat.find_spec (hterm n hgraph)).1

/-- A strict block ends at the first graph change. -/
theorem operationalCloseNext_graph_ne_of_strict
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    {n : Nat} (hgraph : graphs n ≠ .both) :
    graphs (operationalCloseNext graphs hterm n) ≠ graphs n := by
  rw [operationalCloseNext_of_strict graphs hterm hgraph]
  exact (Nat.find_spec (hterm n hgraph)).2

/-- Every round before the next cut has the graph present at the current
cut.  For strict starts this is minimality of the first change; for `.both`
starts the interval is a singleton. -/
theorem operationalCloseNext_graph_eq_of_mem
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    {n j : Nat} (hlower : n ≤ j)
    (hupper : j < operationalCloseNext graphs hterm n) :
    graphs j = graphs n := by
  by_cases hgraph : graphs n = .both
  · rw [operationalCloseNext_of_both graphs hterm hgraph] at hupper
    have : j = n := by omega
    subst j
    rfl
  · rw [operationalCloseNext_of_strict graphs hterm hgraph] at hupper
    rcases hlower.eq_or_lt with rfl | hlt
    · rfl
    · by_contra hne
      exact Nat.find_min (hterm n hgraph) hupper ⟨hlt, hne⟩

/-! ## Iterated operational close cuts -/

/-- Iterate the one-close operation, starting at physical offset zero. -/
noncomputable def operationalCloseCuts
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs) :
    Nat → Nat
  | 0 => 0
  | k + 1 => operationalCloseNext graphs hterm
      (operationalCloseCuts graphs hterm k)

@[simp] theorem operationalCloseCuts_zero
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs) :
    operationalCloseCuts graphs hterm 0 = 0 :=
  rfl

@[simp] theorem operationalCloseCuts_succ
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    operationalCloseCuts graphs hterm (k + 1) =
      operationalCloseNext graphs hterm
        (operationalCloseCuts graphs hterm k) :=
  rfl

/-- The refined cuts are productive. -/
theorem operationalCloseCuts_strictMono
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs) :
    StrictMono (operationalCloseCuts graphs hterm) :=
  strictMono_nat_of_lt_succ fun k ↦ by
    rw [operationalCloseCuts_succ]
    exact lt_operationalCloseNext graphs hterm _

/-- Number of open records in block `k`.  The final physical round is the
single closing receive and is excluded, matching `cutBlockMin` and
`CloseQuery.records`. -/
noncomputable def operationalCloseOpenLength
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) : Nat :=
  operationalCloseCuts graphs hterm (k + 1) -
    operationalCloseCuts graphs hterm k - 1

/-- Exact decomposition into open records plus one closing round. -/
theorem operationalCloseCuts_succ_eq_start_add_openLength_add_one
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    operationalCloseCuts graphs hterm (k + 1) =
      operationalCloseCuts graphs hterm k +
        operationalCloseOpenLength graphs hterm k + 1 := by
  have hlt : operationalCloseCuts graphs hterm k <
      operationalCloseCuts graphs hterm (k + 1) :=
    operationalCloseCuts_strictMono graphs hterm (Nat.lt_succ_self k)
  unfold operationalCloseOpenLength
  omega

/-- The unique closing round sits immediately after the open records. -/
theorem operationalCloseCuts_closing_eq_start_add_openLength
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    operationalCloseCuts graphs hterm (k + 1) - 1 =
      operationalCloseCuts graphs hterm k +
        operationalCloseOpenLength graphs hterm k := by
  rw [operationalCloseCuts_succ_eq_start_add_openLength_add_one]
  omega

/-- The closing round is the last round of the homogeneous block. -/
theorem operationalCloseCuts_closing_graph_eq
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    graphs (operationalCloseCuts graphs hterm (k + 1) - 1) =
      graphs (operationalCloseCuts graphs hterm k) := by
  apply operationalCloseNext_graph_eq_of_mem graphs hterm
  · have hlt := operationalCloseCuts_strictMono graphs hterm
      (Nat.lt_succ_self k)
    rw [operationalCloseCuts_succ] at hlt ⊢
    omega
  · rw [operationalCloseCuts_succ]
    have hlt := lt_operationalCloseNext graphs hterm
      (operationalCloseCuts graphs hterm k)
    omega

/-- Every open record has the same graph as its block's closing round. -/
theorem operationalCloseCuts_open_graph_eq
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k j : Nat) (hj : j < operationalCloseOpenLength graphs hterm k) :
    graphs (operationalCloseCuts graphs hterm k + j) =
      graphs (operationalCloseCuts graphs hterm k) := by
  apply operationalCloseNext_graph_eq_of_mem graphs hterm
  · omega
  · rw [← operationalCloseCuts_succ]
    rw [operationalCloseCuts_succ_eq_start_add_openLength_add_one]
    omega

/-- A simultaneous round is consumed immediately and therefore has no open
records.  Consecutive `.both` rounds are handled one by one by this law. -/
theorem operationalCloseOpenLength_eq_zero_of_both
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat)
    (hgraph : graphs (operationalCloseCuts graphs hterm k) = .both) :
    operationalCloseOpenLength graphs hterm k = 0 := by
  unfold operationalCloseOpenLength
  rw [operationalCloseCuts_succ,
    operationalCloseNext_of_both graphs hterm hgraph]
  omega

/-- A simultaneous cut advances by exactly one physical round. -/
theorem operationalCloseCuts_succ_eq_add_one_of_both
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat)
    (hgraph : graphs (operationalCloseCuts graphs hterm k) = .both) :
    operationalCloseCuts graphs hterm (k + 1) =
      operationalCloseCuts graphs hterm k + 1 := by
  rw [operationalCloseCuts_succ,
    operationalCloseNext_of_both graphs hterm hgraph]

/-- No simultaneous round occurs in the represented open records.  The
statement is unconditional: a `.both` start has zero open length. -/
theorem operationalCloseCuts_open_graph_ne_both
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k j : Nat) (hj : j < operationalCloseOpenLength graphs hterm k) :
    graphs (operationalCloseCuts graphs hterm k + j) ≠ .both := by
  by_cases hgraph : graphs (operationalCloseCuts graphs hterm k) = .both
  · rw [operationalCloseOpenLength_eq_zero_of_both graphs hterm k hgraph]
      at hj
    omega
  · rw [operationalCloseCuts_open_graph_eq graphs hterm k j hj]
    exact hgraph

/-- At a strict start, the following cut is exactly the first graph change;
this is the maximality half of the construction. -/
theorem operationalCloseCuts_next_graph_ne_of_strict
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat)
    (hgraph : graphs (operationalCloseCuts graphs hterm k) ≠ .both) :
    graphs (operationalCloseCuts graphs hterm (k + 1)) ≠
      graphs (operationalCloseCuts graphs hterm k) := by
  rw [operationalCloseCuts_succ]
  exact operationalCloseNext_graph_ne_of_strict graphs hterm hgraph

/-! ## Literal finite graph slice -/

/-- The list of graphs represented by the open records of block `k`. -/
noncomputable def operationalCloseOpenGraphs
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) : List Graph :=
  DetParityAutomaton.omegaPrefix
    (OmegaWord.drop graphs (operationalCloseCuts graphs hterm k))
    (operationalCloseOpenLength graphs hterm k)

@[simp] theorem operationalCloseOpenGraphs_length
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    (operationalCloseOpenGraphs graphs hterm k).length =
      operationalCloseOpenLength graphs hterm k := by
  simp [operationalCloseOpenGraphs, DetParityAutomaton.omegaPrefix]

/-- Exact homogeneous-list form consumed by a typed close query. -/
theorem operationalCloseOpenGraphs_eq_replicate
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    operationalCloseOpenGraphs graphs hterm k =
      List.replicate (operationalCloseOpenLength graphs hterm k)
        (graphs (operationalCloseCuts graphs hterm k)) := by
  apply List.ext_get
  · simp
  · intro j hjLeft hjRight
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [operationalCloseOpenGraphs, DetParityAutomaton.omegaPrefix,
      List.getElem_ofFn, List.getElem_replicate]
    have hj : j < operationalCloseOpenLength graphs hterm k := by
      simpa using hjRight
    exact operationalCloseCuts_open_graph_eq graphs hterm k j hj

/-- List-level no-internal-`.both` theorem. -/
theorem both_not_mem_operationalCloseOpenGraphs
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs)
    (k : Nat) :
    .both ∉ operationalCloseOpenGraphs graphs hterm k := by
  rw [operationalCloseOpenGraphs_eq_replicate]
  by_cases hgraph : graphs (operationalCloseCuts graphs hterm k) = .both
  · have hzero := operationalCloseOpenLength_eq_zero_of_both graphs hterm k
      hgraph
    rw [hzero]
    simp
  · intro hmem
    exact hgraph (List.eq_of_mem_replicate hmem).symm

/-! ## Reusable package and the exact typed-carrier residual -/

/-- All graph and arithmetic facts required of the refined operational clock.
The package is finite-block data even though the source word is infinite. -/
structure OperationalCloseCutPackage (graphs : Nat → Graph) where
  cuts : Nat → Nat
  cuts_zero : cuts 0 = 0
  cuts_strictMono : StrictMono cuts
  openLength : Nat → Nat
  step_eq : ∀ k, cuts (k + 1) = cuts k + openLength k + 1
  closing_graph_eq : ∀ k, graphs (cuts (k + 1) - 1) = graphs (cuts k)
  open_graph_ne_both : ∀ k j, j < openLength k → graphs (cuts k + j) ≠ .both
  homogeneous : ∀ k j, j < openLength k →
    graphs (cuts k + j) = graphs (cuts k)
  zero_open_of_both : ∀ k, graphs (cuts k) = .both → openLength k = 0
  maximal_of_strict : ∀ k, graphs (cuts k) ≠ .both →
    graphs (cuts (k + 1)) ≠ graphs (cuts k)

/-- Rebase an operational-close schedule at one of its own cuts.  The
relative cut `k` is the old cut `p + k` with the old cut `p` subtracted. -/
noncomputable def OperationalCloseCutPackage.dropAt
    {graphs : Nat → Graph} (package : OperationalCloseCutPackage graphs)
    (p : Nat) :
    OperationalCloseCutPackage (fun n ↦ graphs (package.cuts p + n)) where
  cuts := fun k ↦ package.cuts (p + k) - package.cuts p
  cuts_zero := by simp
  cuts_strictMono := by
    intro a b hab
    have hindex : p + a < p + b := by omega
    have hstrict := package.cuts_strictMono hindex
    have hbase : package.cuts p ≤ package.cuts (p + a) := by
      exact package.cuts_strictMono.monotone (by omega)
    exact Nat.sub_lt_sub_right hbase hstrict
  openLength := fun k ↦ package.openLength (p + k)
  step_eq := by
    intro k
    have hstep := package.step_eq (p + k)
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hindex : p + (k + 1) = (p + k) + 1 := by omega
    rw [hindex]
    omega
  closing_graph_eq := by
    intro k
    have hclose := package.closing_graph_eq (p + k)
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hnextBase : package.cuts p ≤ package.cuts (p + (k + 1)) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hnextStrict : package.cuts p < package.cuts (p + (k + 1)) := by
      exact package.cuts_strictMono (by omega)
    have hnextIndex : p + (k + 1) = (p + k) + 1 := by omega
    change
      graphs
            (package.cuts p +
              (package.cuts (p + (k + 1)) - package.cuts p - 1)) =
          graphs
            (package.cuts p +
              (package.cuts (p + k) - package.cuts p))
    have hclosingIndex :
        package.cuts p +
            (package.cuts (p + (k + 1)) - package.cuts p - 1) =
          package.cuts (p + (k + 1)) - 1 := by
      omega
    rw [hclosingIndex, Nat.add_sub_of_le hbase, hnextIndex]
    exact hclose
  open_graph_ne_both := by
    intro k j hj
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hold := package.open_graph_ne_both (p + k) j hj
    change
      graphs
          (package.cuts p +
            ((package.cuts (p + k) - package.cuts p) + j)) ≠ .both
    rw [← Nat.add_assoc, Nat.add_sub_of_le hbase]
    exact hold
  homogeneous := by
    intro k j hj
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hold := package.homogeneous (p + k) j hj
    change
      graphs
          (package.cuts p +
            ((package.cuts (p + k) - package.cuts p) + j)) =
        graphs
          (package.cuts p +
            (package.cuts (p + k) - package.cuts p))
    rw [← Nat.add_assoc, Nat.add_sub_of_le hbase]
    exact hold
  zero_open_of_both := by
    intro k hgraph
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    apply package.zero_open_of_both (p + k)
    change
      graphs
          (package.cuts p +
            (package.cuts (p + k) - package.cuts p)) = .both at hgraph
    rw [Nat.add_sub_of_le hbase] at hgraph
    exact hgraph
  maximal_of_strict := by
    intro k hstrict
    have hbase : package.cuts p ≤ package.cuts (p + k) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hnextBase : package.cuts p ≤ package.cuts (p + (k + 1)) := by
      exact package.cuts_strictMono.monotone (by omega)
    have hold : graphs (package.cuts (p + k)) ≠ .both := by
      change
        graphs
            (package.cuts p +
              (package.cuts (p + k) - package.cuts p)) ≠ .both at hstrict
      rw [Nat.add_sub_of_le hbase] at hstrict
      exact hstrict
    have hmax := package.maximal_of_strict (p + k) hold
    have hnextIndex : p + (k + 1) = (p + k) + 1 := by omega
    change
      graphs
          (package.cuts p +
            (package.cuts (p + (k + 1)) - package.cuts p)) ≠
        graphs
          (package.cuts p +
            (package.cuts (p + k) - package.cuts p))
    rw [Nat.add_sub_of_le hnextBase, Nat.add_sub_of_le hbase, hnextIndex]
    exact hmax

/-- Canonical operational-close package. -/
noncomputable def operationalCloseCutPackage
    (graphs : Nat → Graph) (hterm : OperationalStrictRunsTerminate graphs) :
    OperationalCloseCutPackage graphs where
  cuts := operationalCloseCuts graphs hterm
  cuts_zero := operationalCloseCuts_zero graphs hterm
  cuts_strictMono := operationalCloseCuts_strictMono graphs hterm
  openLength := operationalCloseOpenLength graphs hterm
  step_eq := operationalCloseCuts_succ_eq_start_add_openLength_add_one graphs
    hterm
  closing_graph_eq := operationalCloseCuts_closing_graph_eq graphs hterm
  open_graph_ne_both := operationalCloseCuts_open_graph_ne_both graphs hterm
  homogeneous := operationalCloseCuts_open_graph_eq graphs hterm
  zero_open_of_both := operationalCloseOpenLength_eq_zero_of_both graphs hterm
  maximal_of_strict := operationalCloseCuts_next_graph_ne_of_strict graphs hterm

/-- Direct package constructor for the recurrent-synchronization regime. -/
noncomputable def operationalCloseCutPackageOfGraphBothRecurrent
    (graphs : Nat → Graph) (hboth : GraphBothRecurrent graphs) :
    OperationalCloseCutPackage graphs :=
  operationalCloseCutPackage graphs
    (operationalStrictRunsTerminate_of_graphBothRecurrent hboth)

/-- Direct canonical package for the persistent strict-reversal-tail regime.
It uses the same operational close cuts as the recurrent-synchronization
branch; only the proof of strict-run termination differs. -/
noncomputable def operationalCloseCutPackageOfPersistentStrictReversalTail
    (graphs : Nat → Graph) (h : PersistentStrictReversalTail graphs) :
    OperationalCloseCutPackage graphs :=
  operationalCloseCutPackage graphs h.operationalStrictRunsTerminate

/-
The remaining typed-carrier invariant is deliberately not hidden in this
graph package.  At every refined cut the completed carrier must choose a
`CloseQuery` whose `records.length` is `openLength k`, whose source/row is the
actual fresh-matched global control, and whose `past ++ [move]` is the literal
physical input block (open records plus the closing round).  It must also
identify the original DPA state at the cut with `query.entryState`.

These are precisely `recordsLengthAt`, `controlAndEnvironmentAt`, and
`entryStateAt` of
`ProfiledRawJointUnitPolicyScheduledOperationalAlignment`.  The graph clock
proves all shape facts needed by those fields, but selecting the dependently
typed source and row is completed-carrier mathematics and cannot be inferred
from graphs alone.
-/

end DistributedSynthesis
