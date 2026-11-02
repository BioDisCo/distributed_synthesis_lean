/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemReachableRangeCollapse

/-!
# The regular hull: the concrete choice of `Reach`

Exact model reachability is not regular: model-generated paths have
lengths `1, 3, 3^2, 3^3, ...` (every substitution triples the path), so
no finite deterministic monitor decides exact membership from the path
word, and `ReachWindowDetermined` cannot hold for it.  The concrete
`Reach` is therefore the **regular hull** `Reach_1`: the initial paths
together with all one-step range words from arbitrary sources,

  `RangeHull Init d = Init d ∪ ⋃_{p, u} SuccessorWords_{d.other, p} (u)`.

The hull is closed the right way around for the collapse machinery:
every substitution output lands in it
(`mem_rangeHull_of_successorWords`), and the relative level-one proof
needs `Reach` only on source paths.  `rangeHull_reachWindowDetermined`
reduces `ReachWindowDetermined` to two monitor facts: base summaries
determine `Init`-membership, and base summaries determine
range-word-membership (`IsSuccessorWordFrom`).

The three remaining model facts, in order:

1. every real block path after the first expansion lies in the hull
   (real paths ARE one-step range words of their predecessors);
2. a finite monitor decides `IsSuccessorWordFrom` for the concrete
   scheme -- for `automatonSubstitutionScheme` this is the 3-periodic
   block checker with a feasible-incoming-label subset state --
   discharging `rangeHull_reachWindowDetermined`'s second input;
3. `EntryRestartExchange` holds on the hull.

**Witness-semantics guard**: a failure of the restart exchange on a
spurious hull path (a range word from an unreal source) is NOT yet an
`AlternatingProfileDepthWitness` for the actual model; it becomes a
genuine negative witness only if the failing paths are iteratively
model-reachable.
-/

namespace DistributedSynthesis

universe u v w x y z v' r

section RangeHull

variable {EdgeType : Proc -> Type u} {Label : Type w}
variable [Fintype Label] [DecidableEq Label]
variable [∀ d, Fintype (EdgeType d)] [∀ d, DecidableEq (EdgeType d)]
variable {Param : Proc -> Type w}
variable [∀ d, Fintype (Param d)] [∀ d, DecidableEq (Param d)]
variable (schemeAt : (d : Proc) -> Param d ->
  FiniteSubstitutionScheme (EdgeType d) (EdgeType (d.other)) Label)

/-- A one-step range word of the side-`e` substitution: an output of
some source at some closing parameter. -/
def IsSuccessorWordFrom (e : Proc) (out : TypedPath (EdgeType e.other)) :
    Prop :=
  ∃ (p : Param e) (u : TypedPath (EdgeType e)),
    out ∈ (schemeAt e p).SuccessorWords u

/-- The regular hull `Reach_1`: initial paths plus all one-step range
words from arbitrary sources. -/
def RangeHull (Init : (d : Proc) -> TypedPath (EdgeType d) -> Prop) :
    (d : Proc) -> TypedPath (EdgeType d) -> Prop
  | Proc.one, out =>
      Init Proc.one out ∨ IsSuccessorWordFrom schemeAt Proc.two out
  | Proc.two, out =>
      Init Proc.two out ∨ IsSuccessorWordFrom schemeAt Proc.one out

variable (Init : (d : Proc) -> TypedPath (EdgeType d) -> Prop)

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → Fintype (EdgeType d)]
    [(d : Proc) → DecidableEq (EdgeType d)] [(d : Proc) → Fintype (Param d)]
    [(d : Proc) → DecidableEq (Param d)] in
theorem mem_rangeHull_of_init {d : Proc} {out : TypedPath (EdgeType d)}
    (h : Init d out) : RangeHull schemeAt Init d out := by
  cases d
  · exact Or.inl h
  · exact Or.inl h

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → Fintype (EdgeType d)]
    [(d : Proc) → DecidableEq (EdgeType d)] [(d : Proc) → Fintype (Param d)]
    [(d : Proc) → DecidableEq (Param d)] in
/-- Every substitution output lies in the hull: the closure the
collapse machinery consumes. -/
theorem mem_rangeHull_of_successorWords {d : Proc} {p : Param d}
    {u : TypedPath (EdgeType d)} {out : TypedPath (EdgeType d.other)}
    (h : out ∈ (schemeAt d p).SuccessorWords u) :
    RangeHull schemeAt Init d.other out := by
  cases d
  · exact Or.inr ⟨p, u, h⟩
  · exact Or.inr ⟨p, u, h⟩

variable (base : (d : Proc) -> PathSummarySemigroup.{u, max u w} (EdgeType d))

omit [Fintype Label] [DecidableEq Label] [(d : Proc) → Fintype (EdgeType d)]
    [(d : Proc) → DecidableEq (EdgeType d)] [(d : Proc) → Fintype (Param d)]
    [(d : Proc) → DecidableEq (Param d)] in
/-- `ReachWindowDetermined` for the hull reduces to two monitor facts:
base summaries determine `Init`-membership and range-word-membership. -/
theorem rangeHull_reachWindowDetermined
    (hinit : ∀ (d : Proc) (u v : TypedPath (EdgeType d)),
      pathSummaryValue (base d) u = pathSummaryValue (base d) v ->
        (Init d u ↔ Init d v))
    (hrange : ∀ (e : Proc) (u v : TypedPath (EdgeType e.other)),
      pathSummaryValue (base e.other) u = pathSummaryValue (base e.other) v ->
        (IsSuccessorWordFrom schemeAt e u ↔
          IsSuccessorWordFrom schemeAt e v)) :
    ReachWindowDetermined (RangeHull schemeAt Init) base := by
  intro d u v hval
  cases d
  · exact or_congr (hinit Proc.one u v hval) (hrange Proc.two u v hval)
  · exact or_congr (hinit Proc.two u v hval) (hrange Proc.one u v hval)

end RangeHull

end DistributedSynthesis
