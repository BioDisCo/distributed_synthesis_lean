/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Definition.DefViews

/-!
# Delayed information order (`lem:delayonehierarchy`)

This file formalizes Lemma `lem:delayonehierarchy` from `paper.tex`: the two
processes' information about the settled past -- the length-`t` prefix, one round
back -- is totally ordered by refinement, with the order fixed by the last graph.

The strict (delay-zero) order does *not* hold: at the current round the
more-past-informed process still carries the pending acknowledgement fringe about
that very round (`thm:onebitfringe`), so the one-round delay is essential. At the
delay it is immediate from the receive semantics of Definition `def:views`: a
receive stores the sender's *entire* prior view, so equal receiver views force
equal sender prefixes by constructor injectivity of `View.recv`. Concretely, after
a `→` round process two's view exposes `currentView Proc.one h`, after a `←` round
process one's view exposes `currentView Proc.two h`, and after a `↔` round each
process's view exposes *both* prefix views (the joint-view determinacy of
`lem:jointviewsdeterminehistory`, here read off the single `recv` constructor).
-/

namespace DistributedSynthesis

universe u v x y

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}

/-- `lem:delayonehierarchy`, `→` case: after a right round, process two's view
determines process one's prefix view, so equal process-two views force equal
process-one prefixes.  Process two is at least as informed about the settled
past. -/
theorem delayOneHierarchy_right
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = Graph.right) (hr' : r'.graph = Graph.right)
    (hview :
      currentView Proc.two (History.append h r) =
        currentView Proc.two (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' := by
  simp only [currentView_two_append, hr, hr', View.recv.injEq] at hview
  exact hview.2.2.1

/-- `lem:delayonehierarchy`, `←` case: the mirror.  After a left round, process
one's view determines process two's prefix view. -/
theorem delayOneHierarchy_left
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = Graph.left) (hr' : r'.graph = Graph.left)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    currentView Proc.two h = currentView Proc.two h' := by
  simp only [currentView_one_append, hr, hr', View.recv.injEq] at hview
  exact hview.2.2.1

/-- `lem:delayonehierarchy`, `↔` case: after a both round each process's view
determines the *whole* prefix.  Equal process-one views force equal prefixes for
both processes, so the two prefix relations coincide. -/
theorem delayOneHierarchy_both
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = Graph.both) (hr' : r'.graph = Graph.both)
    (hview :
      currentView Proc.one (History.append h r) =
        currentView Proc.one (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' ∧
      currentView Proc.two h = currentView Proc.two h' := by
  simp only [currentView_one_append, hr, hr', View.recv.injEq] at hview
  exact ⟨hview.1, hview.2.2.1⟩

end DistributedSynthesis
