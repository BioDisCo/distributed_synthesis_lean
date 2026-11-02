/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.DelayedHierarchy

/-! A client of only the public view/hierarchy API. -/
open DistributedSynthesis

example {In₁ In₂ Out₁ Out₂ : Type}
    (h h' : History In₁ In₂ Graph Out₁ Out₂)
    (r r' : RoundRecord In₁ In₂ Graph Out₁ Out₂)
    (hr : r.graph = Graph.right) (hr' : r'.graph = Graph.right)
    (hv : currentView Proc.two (History.append h r) =
      currentView Proc.two (History.append h' r')) :
    currentView Proc.one h = currentView Proc.one h' :=
  delayOneHierarchy_right h h' r r' hr hr' hv

#guard_msgs (drop info) in
#check DistributedSynthesis.delayOneHierarchy_left
#guard_msgs (drop info) in
#check DistributedSynthesis.delayOneHierarchy_both
