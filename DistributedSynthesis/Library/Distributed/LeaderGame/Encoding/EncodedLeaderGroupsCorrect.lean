/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedLeaderGroups
import DistributedSynthesis.Library.Distributed.LeaderGame.NumberedLeaderMoves
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

/-! The generated groups are exactly the original ShapeLeaderGroup type,
for either process. Equal names mean equal local views in every represented
history family. This does not permit additional leader observations. -/
namespace Characterisation.EncodedLeaderGroups
open DistributedSynthesis
local instance : BEq (List Nat) := instBEqOfDecidableEq

variable {H : Type} {R : Nat} (root : H ≃ Fin R) (shape : InputShape H) (p : Proc)

def dataEncode : Data :=
  (R,FiniteFunctionCodes.encode (FiniteFunctionCodes.prod root root)
    (fun hk => finTwoEquiv.symm (shape p hk.1 hk.2)))
def encode (g : ShapeLeaderGroup shape p) :=
  FiniteFunctionCodes.encode root (fun h => finTwoEquiv.symm (g.val h))

local notation "input" => dataEncode root shape p

theorem row_encode (h : H) : row input (root h).val = encode root shape p (shapeLeaderGroup shape p h) := by
  unfold row encode FiniteFunctionCodes.encode
  apply FiniteSearch.tabulate_eq_ofFn
  intro k
  have entry := FiniteFunctionCodes.eval_encode (FiniteFunctionCodes.prod root root)
    (fun hk => finTwoEquiv.symm (shape p hk.1 hk.2)) (h,root.symm k)
  have split : (FiniteFunctionCodes.prod root root (h,root.symm k)).val = k.val+R*(root h).val := by
    change (root (root.symm k)).val+R*(root h).val = _
    rw [Equiv.apply_symm_apply]
  rw [split] at entry
  exact entry

theorem encode_injective : Function.Injective (encode root shape p) := by
  intro g g' eq
  apply Subtype.ext
  funext h
  apply finTwoEquiv.symm.injective
  apply Fin.ext
  have same := congrArg (fun xs : List Nat => xs.getD (root h).val 0) eq
  simpa only [encode,FiniteFunctionCodes.eval_encode] using same

theorem encode_mem (g : ShapeLeaderGroup shape p) : encode root shape p g ∈ rows input := by
  obtain ⟨h,hh⟩ := g.property
  have same : shapeLeaderGroup shape p h = g := Subtype.ext hh
  rw [← same,← row_encode]
  exact List.mem_map.mpr ⟨(root h).val,List.mem_range.mpr (root h).isLt,rfl⟩

theorem encode_sound (code : List Nat) (member : code ∈ rows input) :
    ∃ g : ShapeLeaderGroup shape p, encode root shape p g = code := by
  obtain ⟨h,hh,rfl⟩ := List.mem_map.mp member
  have bound : h < R := List.mem_range.mp hh
  refine ⟨shapeLeaderGroup shape p (root.symm ⟨h,bound⟩),?_⟩
  simpa only [Equiv.apply_symm_apply] using (row_encode root shape p (root.symm ⟨h,bound⟩)).symm

variable [Fintype H] [DecidableEq H]
noncomputable def number : ShapeLeaderGroup shape p ≃ Fin (count input) :=
  FiniteCodeNumbering.equiv (rows input) (encode root shape p)
    (encode_injective root shape p) (encode_mem root shape p) (encode_sound root shape p)

section
omit [Fintype H] [DecidableEq H]

theorem name_encode (h : H) : name input (root h).val =
    (number root shape p (shapeLeaderGroup shape p h)).val := by
  unfold name
  rw [row_encode]
  rfl

theorem assignment_encode : assignment input =
    FiniteFunctionCodes.encode root (number root shape p ∘ shapeLeaderGroup shape p) := by
  unfold assignment FiniteFunctionCodes.encode
  apply FiniteSearch.tabulate_eq_ofFn
  intro h
  simpa only [Equiv.apply_symm_apply,Function.comp_apply] using name_encode root shape p (root.symm h)

/-- Exact agreement with the leader's actual local information. -/
theorem name_eq_iff_view_eq {I₁ I₂ : Type} (past : H → EnvHistory I₁ I₂)
    (rep : RepresentsInputShape past shape) (h k : H) :
    name input (root h).val = name input (root k).val ↔
      currentView p (past h) = currentView p (past k) := by
  rw [name_encode,name_encode,← Fin.ext_iff,(number root shape p).injective.eq_iff]
  exact shapeLeaderGroup_exact past shape rep p h k

end

variable {O : Nat}
noncomputable def tableEncode (leader : ShapeLeaderGroup shape p → Fin O) :=
  FiniteFunctionCodes.encode (number root shape p) leader

section
omit [Fintype H] [DecidableEq H]

theorem table_mem (leader : ShapeLeaderGroup shape p → Fin O) :
    tableEncode root shape p leader ∈ FiniteSearch.tables O (count input) :=
  FiniteFunctionCodes.encode_mem _ _

theorem table_sound (table : List Nat) (member : table ∈ FiniteSearch.tables O (count input)) :
    ∃ leader : ShapeLeaderGroup shape p → Fin O, tableEncode root shape p leader = table := by
  obtain ⟨policy,equal⟩ := (FiniteSearch.mem_tables_iff_policy table).mp member
  refine ⟨fun g => policy (number root shape p g),?_⟩
  simpa only [tableEncode,FiniteFunctionCodes.encode,Equiv.apply_symm_apply] using equal

theorem outputs_encode (leader : ShapeLeaderGroup shape p → Fin O) :
    outputs input (tableEncode root shape p leader) =
      FiniteFunctionCodes.encode root (leader ∘ shapeLeaderGroup shape p) := by
  unfold outputs FiniteFunctionCodes.encode
  apply FiniteSearch.tabulate_eq_ofFn
  intro h
  have hname := name_encode root shape p (root.symm h)
  simp only [Equiv.apply_symm_apply] at hname
  rw [hname]
  exact FiniteFunctionCodes.eval_encode (number root shape p) leader (shapeLeaderGroup shape p (root.symm h))

end

end Characterisation.EncodedLeaderGroups
