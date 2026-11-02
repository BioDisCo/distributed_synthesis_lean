/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenIndexedBeliefNode

/-!
# Indexed tags at one shared family-controller node

The public indexed belief code names family roots by a persistent finite
lineage type `I`, whereas a classified family controller expects its own
source-subtype tags.  The total decoder in the belief node uses a canonical
source member for absent or malformed slots.  On a valid active lane it
decodes an active slot to precisely the root stored in that slot.

Mapping a tagged belief history through this decoder does not change its
physical input history.  Thus all active candidates can query one complete
response table at one shared controller node and then use the single semantic
past supplied by table provenance.  The tags and fallback are proof-side
coordinates; no process observes a lineage, orientation, or leader bit.
-/

namespace DistributedSynthesis

universe i u v x y s

namespace DetParityAutomaton

variable {I : Type i}
variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Fintype I]
variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

/-! ## Active source-member decoding -/

section
omit [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]

/-- An active right slot of a valid right lane denotes a member of the
classified source carried by that lane's public table. -/
theorem profiledOpenIndexedRightSlot_root_mem_source_of_laneValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (lineage : I) (root : ProfiledOpenRightRoot A)
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hslot : code.rightSlots lineage = some (.right root)) :
    root ∈ source.1 := by
  classical
  have hslotMem :
      ProfiledOpenClassifiedAnchor.right root ∈
        profiledOpenIndexedSlotRoots A code.rightSlots := by
    simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    refine ⟨lineage, ?_⟩
    simp [hslot]
  have hsourceMem :
      ProfiledOpenClassifiedAnchor.right root ∈
        profiledOpenRightClassifiedRoots A source := by
    rw [hvalid.2]
    exact hslotMem
  simpa [profiledOpenRightClassifiedRoots] using hsourceMem

/-- Hence the total right decoder takes its membership branch and recovers
the literal active root. -/
@[simp] theorem profiledOpenIndexedRightSourceMember_val_of_laneValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (table : ProfiledOpenRightClassifiedTable A source)
    (lineage : I) (root : ProfiledOpenRightRoot A)
    (hvalid : ProfiledOpenIndexedRightLaneValid A code.rightSlots
      (.right source table))
    (hslot : code.rightSlots lineage = some (.right root)) :
    (profiledOpenIndexedRightSourceMember A code source lineage).1 = root := by
  classical
  have hmem :=
    profiledOpenIndexedRightSlot_root_mem_source_of_laneValid A code source
      table lineage root hvalid hslot
  simp [profiledOpenIndexedRightSourceMember, hslot, hmem]

/-- Active left slots likewise denote actual members of their classified
source. -/
theorem profiledOpenIndexedLeftSlot_root_mem_source_of_laneValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (lineage : I) (root : ProfiledOpenLeftRoot A)
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hslot : code.leftSlots lineage = some (.left root)) :
    root ∈ source.1 := by
  classical
  have hslotMem :
      ProfiledOpenClassifiedAnchor.left root ∈
        profiledOpenIndexedSlotRoots A code.leftSlots := by
    simp only [profiledOpenIndexedSlotRoots, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    refine ⟨lineage, ?_⟩
    simp [hslot]
  have hsourceMem :
      ProfiledOpenClassifiedAnchor.left root ∈
        profiledOpenLeftClassifiedRoots A source := by
    rw [hvalid.2]
    exact hslotMem
  simpa [profiledOpenLeftClassifiedRoots] using hsourceMem

/-- The total left decoder recovers the literal root on a valid active slot. -/
@[simp] theorem profiledOpenIndexedLeftSourceMember_val_of_laneValid
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (table : ProfiledOpenLeftClassifiedTable A source)
    (lineage : I) (root : ProfiledOpenLeftRoot A)
    (hvalid : ProfiledOpenIndexedLeftLaneValid A code.leftSlots
      (.left source table))
    (hslot : code.leftSlots lineage = some (.left root)) :
    (profiledOpenIndexedLeftSourceMember A code source lineage).1 = root := by
  classical
  have hmem :=
    profiledOpenIndexedLeftSlot_root_mem_source_of_laneValid A code source
      table lineage root hvalid hslot
  simp [profiledOpenIndexedLeftSourceMember, hslot, hmem]

end

/-! ## Physical projection of the shared node -/

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Decoding right-lineage tags changes only the hidden family tag.  Its
physical `In₂ × In₁` history is definitionally the original history. -/
@[simp] theorem profiledOpenIndexedRightSharedNode_physical
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenRightViewClass A)
    (past : List ((I × In₂) × In₁)) :
    (profiledOpenIndexedRightSharedNode A code source past).map
        (fun old => (old.1.2, old.2)) =
      past.map (fun old => (old.1.2, old.2)) := by
  simp [profiledOpenIndexedRightSharedNode]

omit [Fintype I] [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
/-- Left physical-projection mirror. -/
@[simp] theorem profiledOpenIndexedLeftSharedNode_physical
    (code : ProfiledOpenIndexedBiBeliefCode A (I := I))
    (source : ProfiledOpenLeftViewClass A)
    (past : List ((I × In₁) × In₂)) :
    (profiledOpenIndexedLeftSharedNode A code source past).map
        (fun old => (old.1.2, old.2)) =
      past.map (fun old => (old.1.2, old.2)) := by
  simp [profiledOpenIndexedLeftSharedNode]

end

end DetParityAutomaton

end DistributedSynthesis
