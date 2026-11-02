/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import Mathlib.Order.KonigLemma
import Mathlib.Tactic

/-!
# Finite-width Streett ranking infrastructure

This file factors out the graph-theoretic core used by the
Miyano-Hayashi/Vardi-Wolper alternation-removal construction.

The literature argument for one Streett pair works on a finite-width leveled
graph.  A bad thread is an infinite path that eventually avoids the grant set
and visits the request set infinitely often.

The correct certificate is an odd ranking on grant-free suffixes, not a
countdown that decreases at every finite request.  Ranks are nonincreasing
along grant-free edges; request vertices receive even ranks; and every
grant-free infinite path eventually stabilizes at an odd rank.  This file
proves the reusable soundness direction for that certificate.  The converse
direction, used to build the nondeterministic monitor from an accepting
alternating run tree, is the finite-width peeling construction that this
interface is designed to receive.
-/

namespace DistributedSynthesis

universe u

namespace FiniteWidthStreett

/-- A leveled directed graph with vertices in one fixed finite-width carrier. -/
structure LeveledGraph (Vertex : Type u) where
  edge : Nat -> Vertex -> Vertex -> Prop

namespace LeveledGraph

variable {Vertex : Type u}

/-- An infinite timed thread through a leveled graph. -/
def Thread (G : LeveledGraph Vertex) (path : Nat -> Vertex) : Prop :=
  ∀ n : Nat, G.edge n (path n) (path (n + 1))

/-- A predicate holds infinitely often along a path. -/
def SeenInfinitelyOften (predicate : Vertex -> Prop) (path : Nat -> Vertex) :
    Prop :=
  ∀ n : Nat, ∃ k : Nat, n ≤ k ∧ predicate (path k)

/-- From some point on, the path avoids the grant set. -/
def EventuallyAvoids (grant : Vertex -> Prop) (path : Nat -> Vertex) :
    Prop :=
  ∃ start : Nat, ∀ n : Nat, start ≤ n -> ¬ grant (path n)

/--
A bad Streett thread for one pair `(request, grant)`: it is a graph thread
that eventually avoids grants but sees requests infinitely often.
-/
def BadStreettThread
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (path : Nat -> Vertex) :
    Prop :=
  G.Thread path ∧
    EventuallyAvoids grant path ∧
      SeenInfinitelyOften request path

/-- Grant-free timed edges. -/
def GrantFreeEdge
    (G : LeveledGraph Vertex)
    (grant : Vertex -> Prop)
    (n : Nat)
    (source target : Vertex) :
    Prop :=
  G.edge n source target ∧ ¬ grant source ∧ ¬ grant target

/-- A finite timed path of length `length` starting at level `start`. -/
structure FinitePath
    (G : LeveledGraph Vertex)
    (start : Nat)
    (source : Vertex)
    (length : Nat) where
  vertex : Nat -> Vertex
  start_vertex : vertex 0 = source
  edge :
    ∀ (i : Nat) (_hi : i < length),
      G.edge (start + i)
        (vertex i)
        (vertex (i + 1))

namespace FinitePath

variable {G : LeveledGraph Vertex}

@[simp]
theorem vertex_zero
    {start : Nat} {source : Vertex} {length : Nat}
    (path : G.FinitePath start source length) :
    path.vertex 0 = source :=
  path.start_vertex

/-- The vertex function obtained by prefixing a source to a tail path. -/
def consVertex (source : Vertex) (tail : Nat -> Vertex) : Nat -> Vertex :=
  fun index => if index = 0 then source else tail (index - 1)

/-- Prefix one edge to a finite path. -/
def cons
    {start : Nat} {source target : Vertex} {length : Nat}
    (hedge : G.edge start source target)
    (tail : G.FinitePath (start + 1) target length) :
    G.FinitePath start source (length + 1) where
  vertex := consVertex source tail.vertex
  start_vertex := by
    simp [consVertex]
  edge := by
    intro i hi
    by_cases hzero : i = 0
    · subst i
      simpa [consVertex, tail.start_vertex] using hedge
    · have hi_pos : 0 < i := Nat.pos_of_ne_zero hzero
      have hpred_lt : i - 1 < length := by omega
      have htail := tail.edge (i - 1) hpred_lt
      have hstart_eq : start + i = start + 1 + (i - 1) := by omega
      have htarget_sub : i + 1 - 1 = i := by omega
      have hpred_succ : i - 1 + 1 = i := by omega
      simpa [consVertex, hzero, hstart_eq, htarget_sub, hpred_succ,
        Nat.succ_eq_add_one, Nat.add_assoc] using htail

/-- Concatenate two finite timed paths. -/
def append
    {start : Nat} {source : Vertex} {length₁ length₂ : Nat}
    (first : G.FinitePath start source length₁)
    (second : G.FinitePath (start + length₁) (first.vertex length₁) length₂) :
    G.FinitePath start source (length₁ + length₂) where
  vertex := fun index =>
    if index < length₁ then first.vertex index
    else second.vertex (index - length₁)
  start_vertex := by
    by_cases hzero : 0 < length₁
    · simp [hzero, first.start_vertex]
    · have hlen : length₁ = 0 := by omega
      simp [hlen, first.start_vertex, second.start_vertex]
  edge := by
    intro i hi
    by_cases htargetFirst : i + 1 < length₁
    · have hsourceFirst : i < length₁ := by omega
      have hedge := first.edge i hsourceFirst
      simpa [htargetFirst, hsourceFirst] using hedge
    · by_cases hsourceFirst : i < length₁
      · have hboundary : i + 1 = length₁ := by omega
        have hedge := first.edge i hsourceFirst
        have htargetNotFirst : ¬ i + 1 < length₁ := htargetFirst
        have htargetSub : i + 1 - length₁ = 0 := by omega
        simpa [hsourceFirst, htargetNotFirst, hboundary, htargetSub,
          second.start_vertex] using hedge
      · have hsecondIndex_lt : i - length₁ < length₂ := by omega
        have hedge := second.edge (i - length₁) hsecondIndex_lt
        have htargetNotFirst : ¬ i + 1 < length₁ := by omega
        have hlevel : start + i = start + length₁ + (i - length₁) := by omega
        have htargetSub : i + 1 - length₁ = i - length₁ + 1 := by omega
        simpa [hsourceFirst, htargetNotFirst, hlevel, htargetSub,
          Nat.add_assoc] using hedge

end FinitePath

/-- An infinite path starting from a specified level and vertex. -/
def ThreadFrom
    (G : LeveledGraph Vertex)
    (start : Nat)
    (source : Vertex)
    (path : Nat -> Vertex) :
    Prop :=
  path 0 = source ∧
    ∀ i : Nat, G.edge (start + i) (path i) (path (i + 1))

/--
A bad Streett suffix starts at an arbitrary level and vertex.  This is the
formal counterpart of the paper's cutoff graph `H_s`: the finite-width peeling
argument is local to every suffix, not only to paths that start at level `0`.
-/
def BadStreettSuffix
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (start : Nat)
    (source : Vertex)
    (path : Nat -> Vertex) :
    Prop :=
  G.ThreadFrom start source path ∧
    (∀ i : Nat, ¬ grant (path i)) ∧
      SeenInfinitelyOften request path

/-- No bad Streett suffix exists from any timed vertex. -/
def NoBadStreettSuffix
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop) :
    Prop :=
  ¬ ∃ start : Nat,
    ∃ source : Vertex,
      ∃ path : Nat -> Vertex,
        G.BadStreettSuffix request grant start source path

/-- A stage predicate is closed under an infinite timed continuation. -/
def InfiniteFrom
    (G : LeveledGraph Vertex)
    (stage : Nat -> Vertex -> Prop)
    (start : Nat)
    (source : Vertex) :
    Prop :=
  ∃ path : Nat -> Vertex,
    G.ThreadFrom start source path ∧
      ∀ i : Nat, stage (start + i) (path i)

/-- Prefix one edge to an infinite continuation inside a stage predicate. -/
theorem infiniteFrom_cons
    {G : LeveledGraph Vertex}
    {stage : Nat -> Vertex -> Prop}
    {start : Nat} {source target : Vertex}
    (hsource : stage start source)
    (hedge : G.edge start source target)
    (htail : G.InfiniteFrom stage (start + 1) target) :
    G.InfiniteFrom stage start source := by
  rcases htail with ⟨tail, htailThread, htailStage⟩
  refine ⟨fun i => Nat.rec source (fun j _ => tail j) i, ?_, ?_⟩
  · constructor
    · rfl
    · intro i
      cases i with
      | zero =>
          simpa [htailThread.1] using hedge
      | succ i =>
          have htailEdge := htailThread.2 i
          have hlevel : start + (i + 1) = start + 1 + i := by omega
          simpa [hlevel, Nat.add_assoc, Nat.succ_eq_add_one] using htailEdge
  · intro i
    cases i with
    | zero =>
        simpa using hsource
    | succ i =>
        have htailLive := htailStage i
        have hlevel : start + (i + 1) = start + 1 + i := by omega
        simpa [hlevel, Nat.add_assoc, Nat.succ_eq_add_one] using htailLive

/-- Tail an infinite continuation. -/
theorem infiniteFrom_tail_of_witness
    {G : LeveledGraph Vertex}
    {stage : Nat -> Vertex -> Prop}
    {start : Nat} {source : Vertex}
    {path : Nat -> Vertex}
    (hthread : G.ThreadFrom start source path)
    (hstage : ∀ i : Nat, stage (start + i) (path i))
    (offset : Nat) :
    G.InfiniteFrom stage (start + offset) (path offset) := by
  refine ⟨fun i => path (offset + i), ?_, ?_⟩
  · constructor
    · simp
    · intro i
      have hedge := hthread.2 (offset + i)
      have hlevel : start + offset + i = start + (offset + i) := by omega
      have htarget : offset + i + 1 = offset + (i + 1) := by omega
      simpa [hlevel, htarget, Nat.add_assoc] using hedge
  · intro i
    have hlive := hstage (offset + i)
    have hlevel : start + offset + i = start + (offset + i) := by omega
    simpa [hlevel, Nat.add_assoc] using hlive

/-- Reachability, inside a stage predicate, to a request vertex. -/
def ReachesRequest
    (G : LeveledGraph Vertex)
    (stage : Nat -> Vertex -> Prop)
    (request : Vertex -> Prop)
    (start : Nat)
    (source : Vertex) :
    Prop :=
  ∃ length : Nat,
    ∃ path : G.FinitePath start source length,
      (∀ i : Nat, i ≤ length -> stage (start + i) (path.vertex i)) ∧
        request (path.vertex length)

/-- A request vertex reaches a request in zero steps. -/
def reachesRequest_zero
    {G : LeveledGraph Vertex}
    {stage : Nat -> Vertex -> Prop}
    {request : Vertex -> Prop}
    {start : Nat} {source : Vertex}
    (hlive : stage start source)
    (hrequest : request source) :
    G.ReachesRequest stage request start source := by
  refine ⟨0, ?_, ?_, ?_⟩
  · exact
      { vertex := fun _ => source
        start_vertex := rfl
        edge := by
          intro i hi
          omega }
  · intro i hi
    have hi0 : i = 0 := by omega
    simpa [hi0] using hlive
  · simpa using hrequest

/-- Prefix one edge to a reachability-to-request witness. -/
def reachesRequest_cons
    {G : LeveledGraph Vertex}
    {stage : Nat -> Vertex -> Prop}
    {request : Vertex -> Prop}
    {start : Nat} {source target : Vertex}
    (hsource : stage start source)
    (hedge : G.edge start source target)
    (htail : G.ReachesRequest stage request (start + 1) target) :
    G.ReachesRequest stage request start source := by
  rcases htail with ⟨length, tail, htailStage, htailRequest⟩
  refine ⟨length + 1, tail.cons hedge, ?_, ?_⟩
  · intro i hi
    by_cases hzero : i = 0
    · simpa [hzero, FinitePath.cons] using hsource
    · have hpred_lt : i - 1 < length + 1 := by
        omega
      have hstage := htailStage (i - 1) (by omega)
      have hlevel : start + i = start + 1 + (i - 1) := by omega
      simpa [FinitePath.cons, FinitePath.consVertex, hzero, hlevel] using hstage
  · have hlast_ne : length + 1 ≠ 0 := by omega
    simpa [FinitePath.cons, FinitePath.consVertex, hlast_ne] using htailRequest

/--
The peeling stages from the English proof.

Stage `0` is the grant-free graph.  Even-to-odd removes finite vertices;
odd-to-even removes vertices that cannot reach a request inside the current
stage.
-/
def PeelingLive
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop) :
    Nat -> Nat -> Vertex -> Prop
  | 0, _n, vertex => ¬ grant vertex
  | stage + 1, n, vertex =>
      PeelingLive G request grant stage n vertex ∧
        if Even stage then
          G.InfiniteFrom (PeelingLive G request grant stage) n vertex
        else
          G.ReachesRequest (PeelingLive G request grant stage) request n vertex

/-- The vertices removed in the passage from stage `stage` to `stage + 1`. -/
def RemovedAt
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (stage n : Nat)
    (vertex : Vertex) :
    Prop :=
  G.PeelingLive request grant stage n vertex ∧
    ¬ G.PeelingLive request grant (stage + 1) n vertex

/--
After an even finite-vertex deletion, every surviving vertex has an infinite
continuation inside the new stage.  This formalizes the English proof's tail
argument: an infinite path witnessing non-finiteness cannot pass through a
vertex that is finite in the previous stage, because the remaining tail would
witness non-finiteness there as well.
-/
theorem infiniteFrom_peelingLive_succ_of_even
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex}
    (hEven : Even stage)
    (hlive : G.PeelingLive request grant (stage + 1) n vertex) :
    G.InfiniteFrom (G.PeelingLive request grant (stage + 1)) n vertex := by
  classical
  have hliveData := hlive
  rw [PeelingLive] at hliveData
  have hinfPrev :
      G.InfiniteFrom (G.PeelingLive request grant stage) n vertex := by
    simpa [hEven] using hliveData.2
  rcases hinfPrev with ⟨path, hthread, hstage⟩
  refine ⟨path, hthread, ?_⟩
  intro offset
  rw [PeelingLive]
  refine ⟨hstage offset, ?_⟩
  have htail :
      G.InfiniteFrom (G.PeelingLive request grant stage)
        (n + offset) (path offset) :=
    infiniteFrom_tail_of_witness hthread hstage offset
  simpa [hEven] using htail

/-- The finite set of live vertices on one level of a peeling stage. -/
noncomputable def levelLive
    [Fintype Vertex]
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (stage n : Nat) :
    Finset Vertex := by
  classical
  exact Finset.univ.filter
    (fun vertex => G.PeelingLive request grant stage n vertex)

theorem mem_levelLive
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex} :
    vertex ∈ G.levelLive request grant stage n ↔
      G.PeelingLive request grant stage n vertex := by
  classical
  simp [levelLive]

/--
Eventual width of a peeling stage.  `EventuallyWidth stage r` means that all
sufficiently high levels of this stage have at most `r` live vertices.
-/
def EventuallyWidth
    [Fintype Vertex]
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (stage width : Nat) :
    Prop :=
  ∃ cutoff : Nat,
    ∀ n : Nat, cutoff ≤ n ->
      (G.levelLive request grant stage n).card ≤ width

theorem levelLive_card_le_card
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} :
    (G.levelLive request grant stage n).card ≤ Fintype.card Vertex := by
  classical
  simpa using Finset.card_le_univ (G.levelLive request grant stage n)

/-- The initial grant-free stage has eventual width bounded by the carrier. -/
theorem eventuallyWidth_stage_zero
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop} :
    G.EventuallyWidth request grant 0 (Fintype.card Vertex) := by
  refine ⟨0, ?_⟩
  intro n _hn
  exact levelLive_card_le_card

/--
If an even stage is eventually empty on all high levels, then the following
finite-vertex deletion removes every remaining vertex.  This is the formal
version of the last middle-step sentence in the English proof.
-/
theorem no_live_after_even_finite_deletion_of_eventuallyWidth_zero
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage : Nat}
    (hEven : Even stage)
    (hwidth : G.EventuallyWidth request grant stage 0) :
    ∀ n : Nat, ∀ vertex : Vertex,
      ¬ G.PeelingLive request grant (stage + 1) n vertex := by
  intro n vertex hliveSucc
  have hliveData := hliveSucc
  rw [PeelingLive] at hliveData
  have hinfinite :
      G.InfiniteFrom (G.PeelingLive request grant stage) n vertex := by
    simpa [hEven] using hliveData.2
  rcases hinfinite with ⟨path, _hthread, hstage⟩
  rcases hwidth with ⟨cutoff, hcutoff⟩
  have hmem :
      path cutoff ∈
        G.levelLive request grant stage (n + cutoff) := by
    rw [mem_levelLive]
    exact hstage cutoff
  have hpositive :
      0 < (G.levelLive request grant stage (n + cutoff)).card :=
    Finset.card_pos.mpr ⟨path cutoff, hmem⟩
  have hzero :
      (G.levelLive request grant stage (n + cutoff)).card ≤ 0 :=
    hcutoff (n + cutoff) (by omega)
  omega

/--
A level is bad for the width-drop argument if it is nonempty and every live
vertex on it can reach a request while staying inside the current live stage.
-/
def AllReachRequestLevel
    (G : LeveledGraph Vertex)
    (live : Nat -> Vertex -> Prop)
    (request : Vertex -> Prop)
    (n : Nat) :
    Prop :=
  (∃ vertex : Vertex, live n vertex) ∧
    ∀ vertex : Vertex, live n vertex ->
      G.ReachesRequest live request n vertex

theorem exists_segment_to_later_allReachRequestLevel
    {G : LeveledGraph Vertex}
    {live : Nat -> Vertex -> Prop}
    {request : Vertex -> Prop}
    (hclosed :
      ∀ n : Nat, ∀ vertex : Vertex,
        live n vertex -> G.InfiniteFrom live n vertex)
    (hfrequent :
      ∀ cutoff : Nat,
        ∃ level : Nat,
          cutoff ≤ level ∧ G.AllReachRequestLevel live request level)
    {n : Nat} {vertex : Vertex}
    (hlevel : G.AllReachRequestLevel live request n)
    (hlive : live n vertex) :
    ∃ next : Nat,
      n < next ∧
        G.AllReachRequestLevel live request next ∧
          ∃ segment : G.FinitePath n vertex (next - n),
            (∀ i : Nat, i ≤ next - n ->
              live (n + i) (segment.vertex i)) ∧
              ∃ hit : Nat,
                hit ≤ next - n ∧ request (segment.vertex hit) := by
  classical
  rcases hlevel.2 vertex hlive with
    ⟨requestLength, requestPath, hrequestLive, hrequestHit⟩
  let requestEnd := n + requestLength
  let requestVertex := requestPath.vertex requestLength
  have hrequestEndLive : live requestEnd requestVertex := by
    dsimp [requestEnd, requestVertex]
    simpa using hrequestLive requestLength (le_rfl)
  rcases hclosed requestEnd requestVertex hrequestEndLive with
    ⟨tail, htailThread, htailLive⟩
  rcases hfrequent (requestEnd + 1) with
    ⟨next, hnext_ge, hnextLevel⟩
  have hnext_gt_n : n < next := by
    dsimp [requestEnd] at hnext_ge
    omega
  let transportLength := next - requestEnd
  have hlength_sum :
      requestLength + transportLength = next - n := by
    dsimp [transportLength, requestEnd]
    omega
  let tailPrefix :
      G.FinitePath requestEnd requestVertex transportLength :=
    { vertex := tail
      start_vertex := htailThread.1
      edge := by
        intro i hi
        exact htailThread.2 i }
  let segmentRaw :
      G.FinitePath n vertex (requestLength + transportLength) :=
    requestPath.append tailPrefix
  refine ⟨next, hnext_gt_n, hnextLevel, ?_⟩
  rw [← hlength_sum]
  refine ⟨segmentRaw, ?_, ?_⟩
  · intro i hi
    by_cases hfirst : i < requestLength
    · have hlive_i := hrequestLive i (by omega)
      simpa [segmentRaw, FinitePath.append, hfirst] using hlive_i
    · have htailIndexLevel :
          n + i = requestEnd + (i - requestLength) := by
        dsimp [requestEnd]
        omega
      have hliveTail := htailLive (i - requestLength)
      have hnotFirst : ¬ i < requestLength := hfirst
      simpa [segmentRaw, FinitePath.append, hnotFirst,
        htailIndexLevel, requestVertex, requestEnd] using hliveTail
  · refine ⟨requestLength, ?_, ?_⟩
    · omega
    · have hnotFirst : ¬ requestLength < requestLength := by omega
      simpa [segmentRaw, FinitePath.append, hnotFirst,
        requestVertex] using hrequestHit

theorem self_le_of_strict_succ_cuts
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    ∀ k : Nat, k ≤ cuts k := by
  intro k
  induction k with
  | zero =>
      exact Nat.zero_le _
  | succ k ih =>
      have hstep := hstrict k
      omega

theorem monotone_of_strict_succ_cuts
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1)) :
    Monotone cuts := by
  intro i j hij
  induction j generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      rcases Nat.eq_or_lt_of_le hij with rfl | hijlt
      · exact le_rfl
      · have hijle : i ≤ j := by omega
        exact Nat.le_trans (ih hijle) (Nat.le_of_lt (hstrict j))

/--
König compactness for leveled graph prefixes with one request in each interval
`[cuts k, cuts (k+1)]`.  This is the graph version of the prefix extraction
used in the Piterman backend.
-/
theorem exists_threadFrom_of_arbitrarily_long_live_prefixes_with_request_intervals
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {live : Nat -> Vertex -> Prop}
    {request : Vertex -> Prop}
    {start : Nat} {source : Vertex}
    (cuts : Nat -> Nat)
    (hstrict : ∀ k : Nat, cuts k < cuts (k + 1))
    (hprefix :
      ∀ m : Nat,
        ∃ pref : Fin (cuts m + 1) -> Vertex,
          pref 0 = source ∧
            (∀ (i : Nat) (hi : i < cuts m),
              G.edge (start + i)
                (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
                (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) ∧
            (∀ (i : Nat) (hi : i ≤ cuts m),
              live (start + i)
                (pref ⟨i, Nat.lt_succ_of_le hi⟩)) ∧
            (∀ (k : Nat) (hk : k < m),
              ∃ hit : Nat,
                ∃ _hhitLeft : cuts k ≤ hit,
                ∃ hhitRight : hit ≤ cuts (k + 1),
                  request
                    (pref
                      ⟨hit,
                        Nat.lt_succ_of_le
                          (Nat.le_trans hhitRight
                            (monotone_of_strict_succ_cuts cuts hstrict
                              (by omega : k + 1 ≤ m)))⟩))) :
    ∃ path : Nat -> Vertex,
      G.ThreadFrom start source path ∧
        (∀ i : Nat, live (start + i) (path i)) ∧
          SeenInfinitelyOften request path := by
  classical
  have hmono : Monotone cuts :=
    monotone_of_strict_succ_cuts cuts hstrict
  have hself : ∀ k : Nat, k ≤ cuts k :=
    self_le_of_strict_succ_cuts cuts hstrict
  let Prefix : Nat -> Type u := fun m =>
    { pref : Fin (cuts m + 1) -> Vertex //
      pref 0 = source ∧
        (∀ (i : Nat) (hi : i < cuts m),
          G.edge (start + i)
            (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
            (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) ∧
        (∀ (i : Nat) (hi : i ≤ cuts m),
          live (start + i)
            (pref ⟨i, Nat.lt_succ_of_le hi⟩)) ∧
        (∀ (k : Nat) (hk : k < m),
          ∃ hit : Nat,
            ∃ hhitLeft : cuts k ≤ hit,
            ∃ hhitRight : hit ≤ cuts (k + 1),
              request
                (pref
                  ⟨hit,
                    Nat.lt_succ_of_le
                      (Nat.le_trans hhitRight
                        (hmono (by omega : k + 1 ≤ m)))⟩)) }
  have hnonempty : ∀ m : Nat, Nonempty (Prefix m) := by
    intro m
    rcases hprefix m with
      ⟨pref, hstart, hvalid, hlive, hrequest⟩
    exact ⟨⟨pref, hstart, hvalid, hlive, hrequest⟩⟩
  letI : ∀ m : Nat, Nonempty (Prefix m) := hnonempty
  haveI : Finite (Prefix 0) := inferInstance
  let proj : {i j : Nat} -> i ≤ j -> Prefix j -> Prefix i :=
    fun {i j} hij pref =>
      ⟨fun idx => pref.1 (Fin.castLE (Nat.succ_le_succ (hmono hij)) idx), by
        constructor
        · have hzero :
            Fin.castLE (Nat.succ_le_succ (hmono hij)) (0 : Fin (cuts i + 1)) =
              (0 : Fin (cuts j + 1)) := by
              ext
              simp
          simpa [hzero] using pref.2.1
        · constructor
          · intro n hn
            have hnj : n < cuts j :=
              Nat.lt_of_lt_of_le hn (hmono hij)
            have hstep := pref.2.2.1 n hnj
            simpa using hstep
          · constructor
            · intro n hn
              have hnj : n ≤ cuts j :=
                Nat.le_trans hn (hmono hij)
              have hlive := pref.2.2.2.1 n hnj
              simpa using hlive
            · intro k hk
              have hkj : k < j := Nat.lt_of_lt_of_le hk hij
              rcases pref.2.2.2.2 k hkj with
                ⟨hit, hhitLeft, hhitRight, hrequestHit⟩
              refine ⟨hit, hhitLeft, hhitRight, ?_⟩
              simpa using hrequestHit⟩
  have hproj_refl :
      ∀ ⦃i : Nat⦄ (pref : Prefix i), proj (le_refl i) pref = pref := by
    intro i pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hproj_trans :
      ∀ ⦃i j k : Nat⦄ (hij : i ≤ j) (hjk : j ≤ k)
        (pref : Prefix k),
        proj hij (proj hjk pref) = proj (Nat.le_trans hij hjk) pref := by
    intro i j k hij hjk pref
    apply Subtype.ext
    funext idx
    simp [proj]
  have hfin :
      ∀ (i : Nat) (pref : Prefix i),
        {next : Prefix (i + 1) | proj (Nat.le_add_right i 1) next = pref}.Finite := by
    intro i pref
    exact Set.toFinite _
  rcases exists_seq_forall_proj_of_forall_finite
      (α := Prefix) proj hproj_refl hproj_trans hfin with
    ⟨prefixes, hprefixes⟩
  let path : Nat -> Vertex :=
    fun n => (prefixes n).1
      ⟨n, Nat.lt_succ_of_le (hself n)⟩
  have hstartPath : path 0 = source := by
    simpa [path] using (prefixes 0).2.1
  have hstepPath :
      ∀ n : Nat, G.edge (start + n) (path n) (path (n + 1)) := by
    intro n
    have hnCut : n < cuts (n + 1) := by
      exact Nat.lt_of_le_of_lt (hself n) (hstrict n)
    have hvalid := (prefixes (n + 1)).2.2.1 n hnCut
    have hproj :
        proj (Nat.le_succ n) (prefixes (n + 1)) = prefixes n :=
      hprefixes (Nat.le_succ n)
    have hsource :
        path n =
          (prefixes (n + 1)).1
            ⟨n, Nat.lt_succ_of_lt hnCut⟩ := by
      have hval := congrArg Subtype.val hproj
      have happ := congrFun hval
        ⟨n, Nat.lt_succ_of_le (hself n)⟩
      simpa [path, proj] using happ.symm
    have htarget :
        path (n + 1) =
          (prefixes (n + 1)).1
            ⟨n + 1, Nat.succ_lt_succ hnCut⟩ := by
      simp [path]
    simpa [hsource, htarget] using hvalid
  have hlivePath : ∀ i : Nat, live (start + i) (path i) := by
    intro i
    simpa [path] using (prefixes i).2.2.2.1 i (hself i)
  have hrequests : SeenInfinitelyOften request path := by
    intro n
    let k := n
    have hkBig : k < cuts (k + 1) := by
      exact Nat.lt_of_le_of_lt (hself k) (hstrict k)
    rcases (prefixes (cuts (k + 1))).2.2.2.2 k hkBig with
      ⟨hit, hhitLeft, hhitRight, hrequestHit⟩
    refine ⟨hit, ?_, ?_⟩
    · exact le_trans (hself n) hhitLeft
    · have hhit_le_self : hit ≤ cuts hit := hself hit
      have hpath_hit :
          path hit =
            (prefixes (cuts (k + 1))).1
              ⟨hit,
                Nat.lt_succ_of_le
                  (Nat.le_trans hhitRight
                    (hmono (hself (k + 1))))⟩ := by
        have hproj_hit :
            proj hhitRight (prefixes (cuts (k + 1))) = prefixes hit :=
          hprefixes hhitRight
        have hval := congrArg Subtype.val hproj_hit
        have happ := congrFun hval
          ⟨hit, Nat.lt_succ_of_le hhit_le_self⟩
        simpa [path, proj] using happ.symm
      rw [hpath_hit]
      exact hrequestHit
  exact ⟨path, ⟨hstartPath, hstepPath⟩, hlivePath, hrequests⟩

/--
If the levels on which every live vertex can reach a request occur cofinally,
then there is a bad Streett suffix.  This is the formal compactness version of
the English proof's repeated concatenation argument.
-/
theorem exists_badStreettSuffix_of_frequently_allReachRequestLevel
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {live : Nat -> Vertex -> Prop}
    {request grant : Vertex -> Prop}
    (hclosed :
      ∀ n : Nat, ∀ vertex : Vertex,
        live n vertex -> G.InfiniteFrom live n vertex)
    (hnotGrant :
      ∀ n : Nat, ∀ vertex : Vertex,
        live n vertex -> ¬ grant vertex)
    (hfrequent :
      ∀ cutoff : Nat,
        ∃ level : Nat,
          cutoff ≤ level ∧ G.AllReachRequestLevel live request level) :
    ∃ start : Nat,
      ∃ source : Vertex,
        ∃ path : Nat -> Vertex,
          G.BadStreettSuffix request grant start source path := by
  classical
  rcases hfrequent 0 with ⟨start, _hstart_ge, hstartLevel⟩
  rcases hstartLevel.1 with ⟨source, hsourceLive⟩
  let ChainState : Type u :=
    { pair : Nat × Vertex //
      G.AllReachRequestLevel live request pair.1 ∧ live pair.1 pair.2 }
  let level : ChainState -> Nat := fun state => state.1.1
  let vertexOf : ChainState -> Vertex := fun state => state.1.2
  let initial : ChainState :=
    ⟨(start, source), hstartLevel, hsourceLive⟩
  have step_exists :
      ∀ state : ChainState,
        ∃ next : ChainState,
          level state < level next ∧
            ∃ segment :
              G.FinitePath (level state) (vertexOf state)
                (level next - level state),
              (∀ i : Nat, i ≤ level next - level state ->
                live (level state + i) (segment.vertex i)) ∧
                (∃ hit : Nat,
                  hit ≤ level next - level state ∧
                    request (segment.vertex hit)) ∧
                segment.vertex (level next - level state) = vertexOf next := by
    intro state
    rcases exists_segment_to_later_allReachRequestLevel
        (G := G)
        (live := live)
        (request := request)
        hclosed hfrequent state.2.1 state.2.2 with
      ⟨nextLevel, hnext_gt, hnextLevel, segment, hliveSegment,
        hrequestSegment⟩
    let nextState : ChainState :=
      ⟨(nextLevel, segment.vertex (nextLevel - level state)),
        hnextLevel,
        by
          have hliveEnd :=
            hliveSegment (nextLevel - level state) (le_rfl)
          have hlevel_end :
              state.1.1 + (nextLevel - level state) = nextLevel := by
            dsimp [level]
            omega
          simpa [hlevel_end] using hliveEnd⟩
    refine ⟨nextState, ?_, ?_⟩
    · simpa [nextState, level] using hnext_gt
    · dsimp [nextState, level, vertexOf]
      exact ⟨segment, hliveSegment, hrequestSegment, rfl⟩
  let nextState : ChainState -> ChainState :=
    fun state => Classical.choose (step_exists state)
  have nextState_spec :
      ∀ state : ChainState,
        level state < level (nextState state) ∧
          ∃ segment :
            G.FinitePath (level state) (vertexOf state)
              (level (nextState state) - level state),
            (∀ i : Nat, i ≤ level (nextState state) - level state ->
              live (level state + i) (segment.vertex i)) ∧
              (∃ hit : Nat,
                hit ≤ level (nextState state) - level state ∧
                  request (segment.vertex hit)) ∧
              segment.vertex (level (nextState state) - level state) =
                vertexOf (nextState state) := by
    intro state
    exact Classical.choose_spec (step_exists state)
  let states : Nat -> ChainState :=
    Nat.rec initial (fun _ state => nextState state)
  have states_succ :
      ∀ k : Nat, states (k + 1) = nextState (states k) := by
    intro k
    rfl
  let cuts : Nat -> Nat := fun k => level (states k) - start
  have level_initial : level (states 0) = start := by
    rfl
  have vertex_initial : vertexOf (states 0) = source := by
    rfl
  have level_ge_start : ∀ k : Nat, start ≤ level (states k) := by
    intro k
    induction k with
    | zero =>
        simp [level_initial]
    | succ k ih =>
        have hgt := (nextState_spec (states k)).1
        simpa [states_succ k] using (show start ≤ level (nextState (states k)) by omega)
  have start_add_cuts :
      ∀ k : Nat, start + cuts k = level (states k) := by
    intro k
    dsimp [cuts]
    have hge := level_ge_start k
    omega
  have cuts_strict : ∀ k : Nat, cuts k < cuts (k + 1) := by
    intro k
    have hgt := (nextState_spec (states k)).1
    have hge := level_ge_start k
    have hgeSucc := level_ge_start (k + 1)
    dsimp [cuts]
    rw [states_succ k] at hgeSucc ⊢
    omega
  let segmentAt (k : Nat) :
      G.FinitePath (level (states k)) (vertexOf (states k))
        (level (nextState (states k)) - level (states k)) := by
    exact Classical.choose (nextState_spec (states k)).2
  have segmentAt_live :
      ∀ k : Nat, ∀ i : Nat,
        i ≤ level (nextState (states k)) - level (states k) ->
          live (level (states k) + i) ((segmentAt k).vertex i) := by
    intro k i hi
    exact (Classical.choose_spec (nextState_spec (states k)).2).1 i hi
  have segmentAt_request :
      ∀ k : Nat,
        ∃ hit : Nat,
          hit ≤ level (nextState (states k)) - level (states k) ∧
            request ((segmentAt k).vertex hit) := by
    intro k
    exact (Classical.choose_spec (nextState_spec (states k)).2).2.1
  have segmentAt_endpoint :
      ∀ k : Nat,
        (segmentAt k).vertex
            (level (nextState (states k)) - level (states k)) =
          vertexOf (nextState (states k)) := by
    intro k
    exact (Classical.choose_spec (nextState_spec (states k)).2).2.2
  have prefix_exists :
      ∀ m : Nat,
        ∃ pref : Nat -> Vertex,
          pref 0 = source ∧
            (∀ i : Nat, i < cuts m ->
              G.edge (start + i) (pref i) (pref (i + 1))) ∧
          (∀ i : Nat, i ≤ cuts m ->
            live (start + i) (pref i)) ∧
            (∀ k : Nat, k < m ->
              ∃ hit : Nat,
                cuts k ≤ hit ∧ hit ≤ cuts (k + 1) ∧
                  request (pref hit)) ∧
            pref (cuts m) = vertexOf (states m) := by
    intro m
    induction m with
    | zero =>
        have hcuts0 : cuts 0 = 0 := by
          dsimp [cuts]
          simp [level_initial]
        refine ⟨fun _ => source, rfl, ?_, ?_, ?_, ?_⟩
        · intro i hi
          omega
        · intro i hi
          have hi0 : i = 0 := by omega
          subst i
          simpa using hsourceLive
        · intro k hk
          omega
        · simp [vertex_initial]
    | succ m ih =>
        rcases ih with
          ⟨pref, hpref0, hedgePref, hlivePref, hrequestPref, hendpoint⟩
        have hstart_level_m : start + cuts m = level (states m) :=
          start_add_cuts m
        let stepLength := level (nextState (states m)) - level (states m)
        have hlength :
            cuts m + stepLength = cuts (m + 1) := by
          dsimp [cuts]
          have hge_m := level_ge_start m
          have hge_succ := level_ge_start (m + 1)
          have hsuccLevel :
              level (states (m + 1)) = level (nextState (states m)) := by
            rw [states_succ m]
          have hgt := (nextState_spec (states m)).1
          dsimp [stepLength]
          omega
        let combined : Nat -> Vertex := fun i =>
          if i < cuts m then pref i else (segmentAt m).vertex (i - cuts m)
        refine ⟨combined, ?_, ?_, ?_, ?_, ?_⟩
        · by_cases hfirst0 : 0 < cuts m
          · simpa [combined, hfirst0] using hpref0
          · have hcutsm0 : cuts m = 0 := by omega
            have hselfm := self_le_of_strict_succ_cuts cuts cuts_strict m
            have hm0 : m = 0 := by omega
            have hsegStart : (segmentAt m).vertex 0 = vertexOf (states m) :=
              (segmentAt m).start_vertex
            have hcombined0 : combined 0 = (segmentAt m).vertex 0 := by
              simp [combined, hcutsm0]
            rw [hcombined0, hsegStart, hm0, vertex_initial]
        · intro i hi
          have hi_raw : i < cuts m + stepLength := by
            rw [hlength]
            exact hi
          by_cases htargetFirst : i + 1 < cuts m
          · have hsourceFirst : i < cuts m := by omega
            have hedge := hedgePref i hsourceFirst
            simpa [combined, hsourceFirst, htargetFirst] using hedge
          · by_cases hsourceFirst : i < cuts m
            · have hboundary : i + 1 = cuts m := by omega
              have hedge := hedgePref i hsourceFirst
              have hsegStart : (segmentAt m).vertex 0 = vertexOf (states m) :=
                (segmentAt m).start_vertex
              have htargetSub : i + 1 - cuts m = 0 := by omega
              simpa [combined, hsourceFirst, htargetFirst, hboundary,
                htargetSub, hendpoint, hsegStart] using hedge
            · have hindex_lt : i - cuts m < stepLength := by omega
              have hedge := (segmentAt m).edge (i - cuts m) hindex_lt
              have htargetNotFirst : ¬ i + 1 < cuts m := by omega
              have hlevel_i :
                  start + i = level (states m) + (i - cuts m) := by
                omega
              have htargetSub : i + 1 - cuts m = i - cuts m + 1 := by omega
              simpa [combined, hsourceFirst, htargetNotFirst,
                hlevel_i, htargetSub, stepLength] using hedge
        · intro i hi
          have hi_raw : i ≤ cuts m + stepLength := by
            rw [hlength]
            exact hi
          by_cases hfirst : i < cuts m
          · simpa [combined, hfirst] using hlivePref i (by omega)
          · have hindex_le : i - cuts m ≤ stepLength := by omega
            have hlevel_i :
                start + i = level (states m) + (i - cuts m) := by
              omega
            have hlive_i := segmentAt_live m (i - cuts m) (by
              simpa [stepLength] using hindex_le)
            simpa [combined, hfirst, hlevel_i, stepLength] using hlive_i
        · intro k hk
          rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hk) with hklt | hkeq
          · rcases hrequestPref k hklt with
              ⟨hit, hleft, hright, hrequestHit⟩
            refine ⟨hit, hleft, ?_, ?_⟩
            · have hle_k : k + 1 ≤ m := by omega
              have hcuts_le :
                  cuts (k + 1) ≤ cuts m :=
                monotone_of_strict_succ_cuts cuts cuts_strict hle_k
              have hcuts_m_succ : cuts m ≤ cuts (m + 1) :=
                Nat.le_of_lt (cuts_strict m)
              omega
            · have hle_k : k + 1 ≤ m := by omega
              have hcuts_le :
                  cuts (k + 1) ≤ cuts m :=
                monotone_of_strict_succ_cuts cuts cuts_strict hle_k
              have hhit_le_m : hit ≤ cuts m := le_trans hright hcuts_le
              by_cases hhit_first : hit < cuts m
              · simpa [combined, hhit_first] using hrequestHit
              · have hhit_eq : hit = cuts m := by omega
                have hsegStart : (segmentAt m).vertex 0 = vertexOf (states m) :=
                  (segmentAt m).start_vertex
                simpa [combined, hhit_first, hhit_eq, hendpoint, hsegStart] using
                  hrequestHit
          · rcases segmentAt_request m with
              ⟨localHit, hlocalLe, hlocalRequest⟩
            let hit := cuts m + localHit
            refine ⟨hit, ?_, ?_, ?_⟩
            · dsimp [hit]
              rw [hkeq]
              omega
            · dsimp [hit]
              rw [hkeq]
              have hhi : localHit ≤ stepLength := by
                simpa [stepLength] using hlocalLe
              omega
            · have hhit_not_first : ¬ hit < cuts m := by
                dsimp [hit]
                omega
              have hhit_sub : hit - cuts m = localHit := by
                dsimp [hit]
                omega
              simpa [combined, hhit_not_first, hhit_sub] using hlocalRequest
        · have hlast_not_first : ¬ cuts (m + 1) < cuts m := by
            exact not_lt.mpr (Nat.le_of_lt (cuts_strict m))
          have hlast_sub :
              cuts (m + 1) - cuts m = stepLength := by
            rw [← hlength]
            omega
          have hstepEndpoint :
              (segmentAt m).vertex stepLength =
                  vertexOf (states (m + 1)) := by
            rw [states_succ m]
            simpa [stepLength] using segmentAt_endpoint m
          simpa [combined, hlast_not_first, hlast_sub] using hstepEndpoint
  have hprefix_for_compactness :
      ∀ m : Nat,
        ∃ pref : Fin (cuts m + 1) -> Vertex,
          pref 0 = source ∧
            (∀ (i : Nat) (hi : i < cuts m),
              G.edge (start + i)
                (pref ⟨i, Nat.lt_succ_of_lt hi⟩)
                (pref ⟨i + 1, Nat.succ_lt_succ hi⟩)) ∧
            (∀ (i : Nat) (hi : i ≤ cuts m),
              live (start + i)
                (pref ⟨i, Nat.lt_succ_of_le hi⟩)) ∧
            (∀ (k : Nat) (hk : k < m),
              ∃ hit : Nat,
                ∃ hhitLeft : cuts k ≤ hit,
                ∃ hhitRight : hit ≤ cuts (k + 1),
                  request
                    (pref
                      ⟨hit, by
                        exact Nat.lt_succ_of_le
                          (Nat.le_trans hhitRight
                            (monotone_of_strict_succ_cuts cuts cuts_strict
                              (by omega : k + 1 ≤ m)))⟩)) := by
    intro m
    rcases prefix_exists m with
      ⟨pref, hpref0, hedgePref, hlivePref, hrequestPref, _hend⟩
    refine ⟨fun idx => pref idx, ?_, ?_, ?_, ?_⟩
    · exact hpref0
    · intro i hi
      exact hedgePref i hi
    · intro i hi
      exact hlivePref i hi
    · intro k hk
      rcases hrequestPref k hk with
        ⟨hit, hleft, hright, hrequestHit⟩
      refine ⟨hit, hleft, hright, ?_⟩
      simpa using hrequestHit
  rcases exists_threadFrom_of_arbitrarily_long_live_prefixes_with_request_intervals
      (G := G)
      (live := live)
      (request := request)
      (start := start)
      (source := source)
      cuts cuts_strict hprefix_for_compactness with
    ⟨path, hthread, hlivePath, hrequests⟩
  refine ⟨start, source, path, ?_⟩
  refine ⟨hthread, ?_, hrequests⟩
  intro i
  exact hnotGrant (start + i) (path i) (hlivePath i)

theorem peelingLive_zero_iff
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {n : Nat} {vertex : Vertex} :
    G.PeelingLive request grant 0 n vertex ↔ ¬ grant vertex :=
  Iff.rfl

theorem peelingLive_of_succ
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex}
    (hlive : G.PeelingLive request grant (stage + 1) n vertex) :
    G.PeelingLive request grant stage n vertex := by
  simpa [PeelingLive] using hlive.1

theorem peelingLive_zero_of_stage
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex}
    (hlive : G.PeelingLive request grant stage n vertex) :
    G.PeelingLive request grant 0 n vertex := by
  induction stage with
  | zero =>
      exact hlive
  | succ stage ih =>
      exact ih (peelingLive_of_succ hlive)

theorem notGrant_of_peelingLive
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex}
    (hlive : G.PeelingLive request grant stage n vertex) :
    ¬ grant vertex := by
  simpa [PeelingLive] using
    (peelingLive_zero_of_stage (G := G) (request := request)
      (grant := grant) hlive)

theorem eventually_not_allReachRequestLevel_of_no_badStreettSuffix
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {live : Nat -> Vertex -> Prop}
    {request grant : Vertex -> Prop}
    (hclosed :
      ∀ n : Nat, ∀ vertex : Vertex,
        live n vertex -> G.InfiniteFrom live n vertex)
    (hnotGrant :
      ∀ n : Nat, ∀ vertex : Vertex,
        live n vertex -> ¬ grant vertex)
    (hnoBad : G.NoBadStreettSuffix request grant) :
    ∃ cutoff : Nat,
      ∀ n : Nat, cutoff ≤ n ->
        ¬ G.AllReachRequestLevel live request n := by
  classical
  by_contra hnotEventually
  push Not at hnotEventually
  rcases exists_badStreettSuffix_of_frequently_allReachRequestLevel
      (G := G)
      (live := live)
      (request := request)
      (grant := grant)
      hclosed hnotGrant hnotEventually with
    ⟨start, source, path, hbad⟩
  exact hnoBad ⟨start, source, path, hbad⟩

theorem eventuallyWidth_drop_of_no_badStreettSuffix
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage width : Nat}
    (hEven : Even stage)
    (hnoBad : G.NoBadStreettSuffix request grant)
    (hwidth : G.EventuallyWidth request grant stage (width + 1)) :
    G.EventuallyWidth request grant (stage + 2) width := by
  classical
  let liveNext : Nat -> Vertex -> Prop :=
    G.PeelingLive request grant (stage + 1)
  have hclosed :
      ∀ n : Nat, ∀ vertex : Vertex,
        liveNext n vertex -> G.InfiniteFrom liveNext n vertex := by
    intro n vertex hlive
    exact infiniteFrom_peelingLive_succ_of_even
      (G := G) (request := request) (grant := grant)
      (stage := stage) hEven hlive
  have hnotGrantLiveNext :
      ∀ n : Nat, ∀ vertex : Vertex,
        liveNext n vertex -> ¬ grant vertex := by
    intro n vertex hlive
    exact notGrant_of_peelingLive
      (G := G) (request := request) (grant := grant) hlive
  rcases eventually_not_allReachRequestLevel_of_no_badStreettSuffix
      (G := G)
      (live := liveNext)
      (request := request)
      (grant := grant)
      hclosed hnotGrantLiveNext hnoBad with
    ⟨goodCutoff, hgood⟩
  rcases hwidth with ⟨widthCutoff, hwidthCutoff⟩
  refine ⟨max goodCutoff widthCutoff, ?_⟩
  intro n hn
  have hnGood : goodCutoff ≤ n := by omega
  have hnWidth : widthCutoff ≤ n := by omega
  let current := G.levelLive request grant stage n
  let afterFinite := G.levelLive request grant (stage + 1) n
  let afterRound := G.levelLive request grant (stage + 2) n
  have hafterFinite_subset_current : afterFinite ⊆ current := by
    intro vertex hvertex
    rw [mem_levelLive] at hvertex ⊢
    exact peelingLive_of_succ hvertex
  have hafterFinite_card :
      afterFinite.card ≤ width + 1 := by
    have hcurrent_card : current.card ≤ width + 1 :=
      hwidthCutoff n hnWidth
    have hsubset_card : afterFinite.card ≤ current.card :=
      Finset.card_le_card hafterFinite_subset_current
    exact le_trans hsubset_card hcurrent_card
  have hnotEvenSucc : ¬ Even (stage + 1) := by
    rintro ⟨k, hk⟩
    rcases hEven with ⟨j, hj⟩
    omega
  have hafterRound_subset_afterFinite : afterRound ⊆ afterFinite := by
    intro vertex hvertex
    rw [mem_levelLive] at hvertex ⊢
    exact peelingLive_of_succ hvertex
  change afterRound.card ≤ width
  by_cases hnonempty : ∃ vertex : Vertex, liveNext n vertex
  · have hnotAll := hgood n hnGood
    have hnotForall :
        ¬ ∀ vertex : Vertex, liveNext n vertex ->
          G.ReachesRequest liveNext request n vertex := by
      intro hall
      exact hnotAll ⟨hnonempty, hall⟩
    push Not at hnotForall
    rcases hnotForall with ⟨missing, hmissingLive, hmissingNoReach⟩
    have hmissing_mem : missing ∈ afterFinite := by
      rw [mem_levelLive]
      exact hmissingLive
    have hmissing_not_mem_round : missing ∉ afterRound := by
      intro hmissingRound
      rw [mem_levelLive] at hmissingRound
      have hroundData := hmissingRound
      rw [show stage + 2 = (stage + 1) + 1 by omega, PeelingLive] at hroundData
      have hreach :
          G.ReachesRequest liveNext request n missing := by
        simpa [liveNext, hnotEvenSucc] using hroundData.2
      exact hmissingNoReach hreach
    have hproper : afterRound ⊂ afterFinite := by
      refine ⟨hafterRound_subset_afterFinite, ?_⟩
      intro hreverse
      exact hmissing_not_mem_round (hreverse hmissing_mem)
    have hcard_lt : afterRound.card < afterFinite.card :=
      Finset.card_lt_card hproper
    omega
  · have hafterFinite_empty : afterFinite.card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext vertex
      constructor
      · intro hmem
        rw [mem_levelLive] at hmem
        exact False.elim (hnonempty ⟨vertex, hmem⟩)
      · intro hmem
        simp at hmem
    have hcard_le_zero : afterRound.card ≤ 0 := by
      have hsubset_card : afterRound.card ≤ afterFinite.card :=
        Finset.card_le_card hafterRound_subset_afterFinite
      omega
    omega

theorem eventuallyWidth_even_rounds_of_no_badStreettSuffix
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hnoBad : G.NoBadStreettSuffix request grant) :
    ∀ i : Nat, i ≤ Fintype.card Vertex ->
      G.EventuallyWidth request grant (2 * i) (Fintype.card Vertex - i) := by
  intro i hi
  induction i with
  | zero =>
      simpa using
        (eventuallyWidth_stage_zero
          (G := G) (request := request) (grant := grant))
  | succ i ih =>
      have hi_le : i ≤ Fintype.card Vertex := by omega
      have hi_lt : i < Fintype.card Vertex := by omega
      have hprev := ih hi_le
      have hwidthEq :
          Fintype.card Vertex - i =
            (Fintype.card Vertex - (i + 1)) + 1 := by
        omega
      have hprev' :
          G.EventuallyWidth request grant (2 * i)
            ((Fintype.card Vertex - (i + 1)) + 1) := by
        simpa [hwidthEq] using hprev
      have hEven : Even (2 * i) := by
        exact ⟨i, by omega⟩
      have hdrop :=
        eventuallyWidth_drop_of_no_badStreettSuffix
          (G := G)
          (request := request)
          (grant := grant)
          (stage := 2 * i)
          (width := Fintype.card Vertex - (i + 1))
          hEven hnoBad hprev'
      have hstage : 2 * i + 2 = 2 * (i + 1) := by omega
      simpa [hstage] using hdrop

theorem exists_removedAt_le_of_live_zero_not_live_succ
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {bound n : Nat} {vertex : Vertex}
    (hlive0 : G.PeelingLive request grant 0 n vertex)
    (hnotLive : ¬ G.PeelingLive request grant (bound + 1) n vertex) :
    ∃ stage : Nat,
      stage ≤ bound ∧ G.RemovedAt request grant stage n vertex := by
  induction bound with
  | zero =>
      exact ⟨0, by omega, hlive0, by simpa using hnotLive⟩
  | succ bound ih =>
      by_cases hlive : G.PeelingLive request grant (bound + 1) n vertex
      · exact ⟨bound + 1, by omega, hlive, by simpa [Nat.add_assoc] using hnotLive⟩
      · rcases ih hlive with ⟨stage, hstage, hremoved⟩
        exact ⟨stage, by omega, hremoved⟩

theorem peelingLive_succ_of_target_succ
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {source target : Vertex}
    (hsource : G.PeelingLive request grant stage n source)
    (hedge : G.edge n source target)
    (htarget :
      G.PeelingLive request grant (stage + 1) (n + 1) target) :
    G.PeelingLive request grant (stage + 1) n source := by
  classical
  have htargetData := htarget
  rw [PeelingLive] at htargetData ⊢
  refine ⟨hsource, ?_⟩
  by_cases hEven : Even stage
  · simp [hEven] at htargetData ⊢
    exact infiniteFrom_cons hsource (by simpa using hedge) htargetData.2
  · simp [hEven] at htargetData ⊢
    exact reachesRequest_cons hsource (by simpa using hedge) htargetData.2

theorem exists_removedAt_target_le_of_edge_removedAt
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {source target : Vertex}
    (hsourceRemoved : G.RemovedAt request grant stage n source)
    (hedge : G.edge n source target)
    (htargetLive0 : G.PeelingLive request grant 0 (n + 1) target) :
    ∃ targetStage : Nat,
      targetStage ≤ stage ∧
        G.RemovedAt request grant targetStage (n + 1) target := by
  have htargetNotLive :
      ¬ G.PeelingLive request grant (stage + 1) (n + 1) target := by
    intro htarget
    exact hsourceRemoved.2
      (peelingLive_succ_of_target_succ
        hsourceRemoved.1 hedge htarget)
  exact exists_removedAt_le_of_live_zero_not_live_succ
    htargetLive0 htargetNotLive

theorem even_of_removedAt_request
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {stage n : Nat} {vertex : Vertex}
    (hremoved : G.RemovedAt request grant stage n vertex)
    (hrequest : request vertex) :
    Even stage := by
  classical
  by_cases hEven : Even stage
  · exact hEven
  · exfalso
    have hsucc :
        G.PeelingLive request grant (stage + 1) n vertex := by
      rw [PeelingLive]
      refine ⟨hremoved.1, ?_⟩
      simp [hEven, reachesRequest_zero hremoved.1 hrequest]
    exact hremoved.2 hsucc

/-- The uniform finite-width rank bound for a fixed finite carrier. -/
def rankBound (Vertex : Type u) [Fintype Vertex] : Nat :=
  2 * Fintype.card Vertex

theorem no_live_after_bound_of_no_badStreettSuffix
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hnoBad : G.NoBadStreettSuffix request grant) :
    ∀ n : Nat, ∀ vertex : Vertex,
      ¬ G.PeelingLive request grant (rankBound Vertex + 1) n vertex := by
  classical
  have hwidthZero :
      G.EventuallyWidth request grant (rankBound Vertex) 0 := by
    have hrounds :=
      eventuallyWidth_even_rounds_of_no_badStreettSuffix
        (G := G) (request := request) (grant := grant)
        hnoBad (Fintype.card Vertex) (le_rfl)
    simpa [rankBound] using hrounds
  have hEvenBound : Even (rankBound Vertex) := by
    exact ⟨Fintype.card Vertex, by simp [rankBound]; omega⟩
  have hempty :=
    no_live_after_even_finite_deletion_of_eventuallyWidth_zero
      (G := G)
      (request := request)
      (grant := grant)
      (stage := rankBound Vertex)
      hEvenBound hwidthZero
  intro n vertex
  simpa using hempty n vertex

/-- The first peeling stage, bounded by `rankBound`, at which a vertex is removed. -/
noncomputable def peelingRank
    [Fintype Vertex]
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop)
    (n : Nat)
    (vertex : Vertex) :
    Nat := by
  classical
  if h :
      ∃ stage : Nat,
        stage ≤ rankBound Vertex ∧ G.RemovedAt request grant stage n vertex then
    exact Nat.find h
  else
    exact 0

theorem peelingRank_spec
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {n : Nat} {vertex : Vertex}
    (h :
      ∃ stage : Nat,
        stage ≤ rankBound Vertex ∧ G.RemovedAt request grant stage n vertex) :
    peelingRank G request grant n vertex ≤ rankBound Vertex ∧
      G.RemovedAt request grant
        (peelingRank G request grant n vertex) n vertex := by
  classical
  rw [peelingRank]
  simpa [h] using (Nat.find_spec h)

theorem peelingRank_le_of_removedAt
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    {n stage : Nat} {vertex : Vertex}
    (hstage : stage ≤ rankBound Vertex)
    (hremoved : G.RemovedAt request grant stage n vertex) :
    peelingRank G request grant n vertex ≤ stage := by
  classical
  let h :
      ∃ candidate : Nat,
        candidate ≤ rankBound Vertex ∧
          G.RemovedAt request grant candidate n vertex :=
    ⟨stage, hstage, hremoved⟩
  have hmin := Nat.find_min' h ⟨hstage, hremoved⟩
  rw [peelingRank]
  simpa [h] using hmin

theorem peelingRank_removedAt_of_notGrant
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hremovedBound :
      ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
        ∃ stage : Nat,
          stage ≤ rankBound Vertex ∧
            G.RemovedAt request grant stage n vertex)
    {n : Nat} {vertex : Vertex}
    (hnotGrant : ¬ grant vertex) :
    G.RemovedAt request grant
      (peelingRank G request grant n vertex) n vertex :=
  (peelingRank_spec (hremovedBound n vertex hnotGrant)).2

theorem peelingRank_le_bound_of_notGrant
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hremovedBound :
      ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
        ∃ stage : Nat,
          stage ≤ rankBound Vertex ∧
            G.RemovedAt request grant stage n vertex)
    {n : Nat} {vertex : Vertex}
    (hnotGrant : ¬ grant vertex) :
    peelingRank G request grant n vertex ≤ rankBound Vertex :=
  (peelingRank_spec (hremovedBound n vertex hnotGrant)).1

theorem peelingRank_edge_nonincreasing_of_removedBound
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hremovedBound :
      ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
        ∃ stage : Nat,
          stage ≤ rankBound Vertex ∧
            G.RemovedAt request grant stage n vertex)
    {n : Nat} {source target : Vertex}
    (hedge : G.edge n source target)
    (hsourceNotGrant : ¬ grant source)
    (htargetNotGrant : ¬ grant target) :
    peelingRank G request grant (n + 1) target ≤
      peelingRank G request grant n source := by
  classical
  let sourceRank := peelingRank G request grant n source
  have hsourceRemoved :
      G.RemovedAt request grant sourceRank n source :=
    peelingRank_removedAt_of_notGrant hremovedBound hsourceNotGrant
  have htargetLive0 :
      G.PeelingLive request grant 0 (n + 1) target := by
    simpa [PeelingLive] using htargetNotGrant
  rcases exists_removedAt_target_le_of_edge_removedAt
      hsourceRemoved hedge htargetLive0 with
    ⟨targetStage, htargetStageLe, htargetRemoved⟩
  have hsourceRankBound :
      sourceRank ≤ rankBound Vertex :=
    peelingRank_le_bound_of_notGrant hremovedBound hsourceNotGrant
  have htargetStageBound : targetStage ≤ rankBound Vertex :=
    le_trans htargetStageLe hsourceRankBound
  have hrankTargetLe :
      peelingRank G request grant (n + 1) target ≤ targetStage :=
    peelingRank_le_of_removedAt htargetStageBound htargetRemoved
  exact le_trans hrankTargetLe htargetStageLe

theorem peelingRank_request_even_of_removedBound
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hremovedBound :
      ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
        ∃ stage : Nat,
          stage ≤ rankBound Vertex ∧
            G.RemovedAt request grant stage n vertex)
    {n : Nat} {vertex : Vertex}
    (hnotGrant : ¬ grant vertex)
    (hrequest : request vertex) :
    Even (peelingRank G request grant n vertex) := by
  exact even_of_removedAt_request
    (peelingRank_removedAt_of_notGrant hremovedBound hnotGrant)
    hrequest

theorem removedByBound_of_no_live_after_bound
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hempty :
      ∀ n : Nat, ∀ vertex : Vertex,
        ¬ G.PeelingLive request grant (rankBound Vertex + 1) n vertex) :
    ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
      ∃ stage : Nat,
        stage ≤ rankBound Vertex ∧
          G.RemovedAt request grant stage n vertex := by
  intro n vertex hnotGrant
  have hlive0 : G.PeelingLive request grant 0 n vertex := by
    simpa [PeelingLive] using hnotGrant
  exact exists_removedAt_le_of_live_zero_not_live_succ
    (bound := rankBound Vertex)
    hlive0
    (hempty n vertex)

/--
An odd-ranking certificate on grant-free suffixes.

The rank is allowed to depend on the level.  After `cutoff`, every grant-free
edge is nonincreasing, every request vertex has even rank, and every
grant-free infinite path eventually stabilizes at an odd rank.  The bound
`2 * Fintype.card Vertex` is the finite-width bound for this fixed carrier.
-/
structure RankingCertificate
    [Fintype Vertex]
    (G : LeveledGraph Vertex)
    (request grant : Vertex -> Prop) where
  rank : Nat -> Vertex -> Nat
  cutoff : Nat
  rank_le_bound :
    ∀ {n : Nat} {vertex : Vertex},
      cutoff ≤ n ->
        ¬ grant vertex ->
          rank n vertex ≤ 2 * Fintype.card Vertex
  edge_nonincreasing :
    ∀ {n : Nat} {source target : Vertex},
      cutoff ≤ n ->
        G.edge n source target ->
          ¬ grant source ->
            ¬ grant target ->
              rank (n + 1) target ≤ rank n source
  request_even :
    ∀ {n : Nat} {vertex : Vertex},
      cutoff ≤ n ->
        ¬ grant vertex ->
          request vertex ->
            Even (rank n vertex)
  eventually_stabilizes_odd :
    ∀ {path : Nat -> Vertex},
      (start : Nat) ->
        cutoff ≤ start ->
          (∀ n : Nat, start ≤ n -> G.edge n (path n) (path (n + 1))) ->
            (∀ n : Nat, start ≤ n -> ¬ grant (path n)) ->
              ∃ stable value : Nat,
                start ≤ stable ∧
                  Odd value ∧
                    ∀ n : Nat, stable ≤ n -> rank n (path n) = value

/-- Local copy used before the public lemma below. -/
private theorem eventually_constant_of_antitone_for_rank {measure : Nat -> Nat}
    (hanti : Antitone measure) :
    ∃ start value : Nat, ∀ k : Nat, start ≤ k -> measure k = value := by
  classical
  have hnonempty : (Set.range measure).Nonempty := ⟨measure 0, 0, rfl⟩
  obtain ⟨start, hstart⟩ := Nat.sInf_mem hnonempty
  refine ⟨start, sInf (Set.range measure), ?_⟩
  intro k hk
  have hle : measure k ≤ measure start := hanti hk
  have hge : sInf (Set.range measure) ≤ measure k :=
    Nat.sInf_le ⟨k, rfl⟩
  rw [hstart] at hle
  omega

/--
Package bounded peeling removal into an odd-ranking certificate.

This theorem is the formal version of the last half of the English peeling
proof: once the process is known to remove every grant-free vertex by the
finite-width bound, the deletion stage is a valid odd ranking.
-/
noncomputable def rankingCertificate_of_removedByBound
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hremovedBound :
      ∀ n : Nat, ∀ vertex : Vertex, ¬ grant vertex ->
        ∃ stage : Nat,
          stage ≤ rankBound Vertex ∧
            G.RemovedAt request grant stage n vertex) :
    G.RankingCertificate request grant where
  rank := peelingRank G request grant
  cutoff := 0
  rank_le_bound := by
    intro n vertex _hcutoff hnotGrant
    simpa [rankBound] using
      (peelingRank_le_bound_of_notGrant hremovedBound
        (n := n) (vertex := vertex) hnotGrant)
  edge_nonincreasing := by
    intro n source target _hcutoff hedge hsourceNotGrant htargetNotGrant
    exact peelingRank_edge_nonincreasing_of_removedBound
      hremovedBound hedge hsourceNotGrant htargetNotGrant
  request_even := by
    intro n vertex _hcutoff hnotGrant hrequest
    exact peelingRank_request_even_of_removedBound
      hremovedBound hnotGrant hrequest
  eventually_stabilizes_odd := by
    intro path start _hcutoff hthreadFrom havoids
    let measure : Nat -> Nat :=
      fun offset =>
        peelingRank G request grant (start + offset) (path (start + offset))
    have hstep_le : ∀ offset : Nat, measure (offset + 1) ≤ measure offset := by
      intro offset
      dsimp [measure]
      have hedge :
          G.edge (start + offset)
            (path (start + offset)) (path (start + offset + 1)) := by
        simpa [Nat.add_assoc] using
          hthreadFrom (start + offset) (by omega)
      have hsourceNotGrant : ¬ grant (path (start + offset)) :=
        havoids (start + offset) (by omega)
      have htargetNotGrant : ¬ grant (path (start + (offset + 1))) := by
        exact havoids (start + (offset + 1)) (by omega)
      have hle :=
        peelingRank_edge_nonincreasing_of_removedBound
          (G := G)
          (request := request)
          (grant := grant)
          hremovedBound
          (n := start + offset)
          (source := path (start + offset))
          (target := path (start + offset + 1))
          hedge hsourceNotGrant
          (by simpa [Nat.add_assoc] using htargetNotGrant)
      simpa [Nat.add_assoc] using hle
    have hanti : Antitone measure :=
      antitone_nat_of_succ_le hstep_le
    rcases eventually_constant_of_antitone_for_rank hanti with
      ⟨stableOffset, value, hconstant⟩
    let stable := start + stableOffset
    have hnotEvenValue : ¬ Even value := by
      intro hEvenValue
      have hnotGrantStable : ¬ grant (path stable) := by
        exact havoids stable (by dsimp [stable]; omega)
      have hremovedStable :
          G.RemovedAt request grant
            (peelingRank G request grant stable (path stable))
            stable (path stable) :=
        peelingRank_removedAt_of_notGrant hremovedBound hnotGrantStable
      have hrankStable :
          peelingRank G request grant stable (path stable) = value := by
        have hconst := hconstant stableOffset (by omega)
        simpa [measure, stable] using hconst
      have hremovedValue :
          G.RemovedAt request grant value stable (path stable) := by
        simpa [hrankStable] using hremovedStable
      have hinfinite :
          G.InfiniteFrom
            (G.PeelingLive request grant value) stable (path stable) := by
        refine ⟨fun i => path (stable + i), ?_, ?_⟩
        · constructor
          · rfl
          · intro i
            have hedge := hthreadFrom (stable + i) (by
              dsimp [stable]
              omega)
            simpa [Nat.add_assoc] using hedge
        · intro i
          have hnotGrant : ¬ grant (path (stable + i)) := by
            exact havoids (stable + i) (by dsimp [stable]; omega)
          have hremovedAtRank :
              G.RemovedAt request grant
                (peelingRank G request grant (stable + i) (path (stable + i)))
                (stable + i) (path (stable + i)) :=
            peelingRank_removedAt_of_notGrant hremovedBound hnotGrant
          have hrank :
              peelingRank G request grant (stable + i) (path (stable + i)) =
                value := by
            have hconst := hconstant (stableOffset + i) (by omega)
            have hlevel : start + (stableOffset + i) = stable + i := by
              dsimp [stable]
              omega
            simpa [measure, hlevel] using hconst
          simpa [hrank] using hremovedAtRank.1
      have hsucc :
          G.PeelingLive request grant (value + 1) stable (path stable) := by
        rw [PeelingLive]
        refine ⟨hremovedValue.1, ?_⟩
        simp [hEvenValue, hinfinite]
      exact hremovedValue.2 hsucc
    refine ⟨stable, value, by dsimp [stable]; omega,
      Nat.not_even_iff_odd.mp hnotEvenValue, ?_⟩
    intro n hn
    let offset := n - start
    have hoffset_eq : start + offset = n := by
      dsimp [offset]
      omega
    have hoffset_ge : stableOffset ≤ offset := by
      dsimp [offset, stable] at hn
      omega
    have hconst := hconstant offset hoffset_ge
    simpa [measure, hoffset_eq] using hconst

noncomputable def rankingCertificate_of_no_live_after_bound
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hempty :
      ∀ n : Nat, ∀ vertex : Vertex,
        ¬ G.PeelingLive request grant (rankBound Vertex + 1) n vertex) :
    G.RankingCertificate request grant :=
  rankingCertificate_of_removedByBound
    (G := G)
    (request := request)
    (grant := grant)
    (removedByBound_of_no_live_after_bound hempty)

/--
Construct the bounded odd-ranking certificate from the absence of bad suffixes.
This is the full finite-width peeling direction of the English proof.
-/
noncomputable def rankingCertificate_of_no_badStreettSuffix
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (hnoBad : G.NoBadStreettSuffix request grant) :
    G.RankingCertificate request grant :=
  rankingCertificate_of_no_live_after_bound
    (G := G)
    (request := request)
    (grant := grant)
    (no_live_after_bound_of_no_badStreettSuffix hnoBad)

/--
An antitone natural-valued sequence is eventually constant.

This elementary fact is the termination argument behind finite ranking proofs:
after the rank has reached the minimum value in its range, it cannot change.
-/
theorem eventually_constant_of_antitone {measure : Nat -> Nat}
    (hanti : Antitone measure) :
    ∃ start value : Nat, ∀ k : Nat, start ≤ k -> measure k = value := by
  classical
  have hnonempty : (Set.range measure).Nonempty := ⟨measure 0, 0, rfl⟩
  obtain ⟨start, hstart⟩ := Nat.sInf_mem hnonempty
  refine ⟨start, sInf (Set.range measure), ?_⟩
  intro k hk
  have hle : measure k ≤ measure start := hanti hk
  have hge : sInf (Set.range measure) ≤ measure k :=
    Nat.sInf_le ⟨k, rfl⟩
  rw [hstart] at hle
  omega

/--
Soundness of an odd-ranking Streett certificate.

If every grant-free suffix is protected by an odd ranking, then no bad
Streett thread can exist.  This is the checked reusable part of the standard
ranking argument and deliberately does not impose any response obligation on
finite one-shot requests.
-/
theorem no_badStreettThread_of_rankingCertificate
    [Fintype Vertex]
    {G : LeveledGraph Vertex}
    {request grant : Vertex -> Prop}
    (certificate : G.RankingCertificate request grant) :
    ¬ ∃ path : Nat -> Vertex, G.BadStreettThread request grant path := by
  rintro ⟨path, hthread, havoids, hrequests⟩
  rcases havoids with ⟨avoidStart, havoid⟩
  let start := max certificate.cutoff avoidStart
  have hcutoff_start : certificate.cutoff ≤ start := by
    dsimp [start]
    omega
  have havoids_start :
      ∀ n : Nat, start ≤ n -> ¬ grant (path n) := by
    intro n hn
    exact havoid n (by dsimp [start] at hn ⊢; omega)
  rcases certificate.eventually_stabilizes_odd
      (path := path) start hcutoff_start
      (fun n _hn => hthread n) havoids_start with
    ⟨stable, value, hstart_stable, hvalueOdd, hstable⟩
  rcases hrequests stable with ⟨requestTime, hstable_requestTime, hrequest⟩
  have hcutoff_requestTime : certificate.cutoff ≤ requestTime := by
    omega
  have hnotGrant_requestTime : ¬ grant (path requestTime) :=
    havoids_start requestTime (le_trans hstart_stable hstable_requestTime)
  have hvalue_eq :
      certificate.rank requestTime (path requestTime) = value :=
    hstable requestTime hstable_requestTime
  have hvalueEven : Even value := by
    rw [← hvalue_eq]
    exact certificate.request_even
      hcutoff_requestTime hnotGrant_requestTime hrequest
  exact (Nat.not_even_iff_odd.mpr hvalueOdd) hvalueEven

end LeveledGraph

end FiniteWidthStreett

end DistributedSynthesis
