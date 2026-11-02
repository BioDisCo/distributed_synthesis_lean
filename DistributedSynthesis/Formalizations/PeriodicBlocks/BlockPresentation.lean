/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Formalizations.PeriodicBlocks.FinitePresentation
import DistributedSynthesis.Formalizations.PeriodicBlocks.EncodedBlockSolver
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockGame
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingLayersCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

section
variable {I₁ I₂ O₁ O₂ G Q : Type} {B D E V S N N₁ N₂ P₁ P₂ : Nat}
variable [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂]
variable (env : (I₁ × I₂ × Graph) ≃ Fin E) (output : (O₁ × O₂) ≃ Fin V)
variable (one : I₁ ≃ Fin N₁) (two : I₂ ≃ Fin N₂)
variable (outOne : O₁ ≃ Fin P₁) (outTwo : O₂ ≃ Fin P₂)
variable (graph : G ≃ Fin S) (objective : Q ≃ Fin N)

def blockContext : EncodedBlock.Context :=
  (B,D,S,N,E,V,
    List.ofFn (fun i => EncodedClosingObservations.roundEncode one two (env.symm i)),
    List.ofFn (fun i => ((outOne (output.symm i).1).val,(outTwo (output.symm i).2).val)))

def shapeEquiv : InputShape (BlockSlots B) ≃
    ((BlockSlots B × BlockSlots B) → Bool × Bool) where
  toFun shape x := (shape .one x.1 x.2,shape .two x.1 x.2)
  invFun f p i j := match p with | .one => (f (i,j)).1 | .two => (f (i,j)).2
  left_inv := by intro shape; funext p i j; cases p <;> rfl
  right_inv := by intro f; funext x; rfl

def boundaryPresentation : FinitePresentation (BlockBoundary G Q B) EncodedBlock.Boundary :=
  (((FinitePresentation.table (FiniteFunctionCodes.prod (Equiv.refl _) (Equiv.refl _))
      FinitePresentation.views).transport shapeEquiv).prod
    ((FinitePresentation.table (Equiv.refl (BlockSlots B)) ((FinitePresentation.fin S).transport graph)).prod
      (FinitePresentation.table (Equiv.refl (BlockSlots B)) ((FinitePresentation.fin N).transport objective)))).transport
    { toFun := fun b => (b.shape,b.graph,b.objective)
      invFun := fun b => ⟨b.1,b.2.1,b.2.2⟩
      left_inv := by intro b; cases b; rfl
      right_inv := by intro b; rfl }

abbrev endNumber : BlockEnd I₁ I₂ B D ≃ Fin (EncodedClosingLayers.count (B+1,E,D)) :=
  EncodedClosingLayers.number (Equiv.refl _) env

def maskPresentation : FinitePresentation (ComponentMask I₁ I₂ B D) (List Bool) :=
  FinitePresentation.table (endNumber env) FinitePresentation.bool

def maskNumber : ComponentMask I₁ I₂ B D ≃
    Fin (FiniteCodeNumbering.unique (maskPresentation (B:=B) (D:=D) env).codes).length :=
  (maskPresentation env).number

def responsePresentation : FinitePresentation (BlockResponse I₁ I₂ B D) EncodedBlock.Response :=
  ((FinitePresentation.table (Equiv.refl (BlockSlots B))
    ((FinitePresentation.fin _).transport (endNumber env))).prod
    (FinitePresentation.table (endNumber env) (FinitePresentation.fin (B+1)))).transport
    { toFun := fun r => (r.keep,r.fold)
      invFun := fun r => ⟨r.1,r.2⟩
      left_inv := by intro r; cases r; rfl
      right_inv := by intro r; rfl }

def policyBankEquiv : ClosingPolicy (BlockSlots B) I₁ I₂ O₁ O₂ D ≃
    (BlockSlots B → LeaderClosingPlan I₁ I₂ O₁ O₂ D) where
  toFun policy i s := policy s.2.1 (closingLayerFromWord i (s.2.1.val+1) s.2.2)
  invFun bank t s := bank (closingLayerRoot _ s) ((),⟨t,closingLayerWord _ s⟩)
  left_inv := by
    intro policy
    funext t s
    dsimp only
    rw [EncodedClosingObservations.layerFromWord_word]
  right_inv := by
    intro bank
    funext i s
    rcases s with ⟨⟨⟩,t,w⟩
    simp only [closingLayerRoot_fromWord,closingLayerWord_fromWord]

def bankPresentation : FinitePresentation
    (BlockSlots B → LeaderClosingPlan I₁ I₂ O₁ O₂ D) EncodedClosingBanks.Bank where
  codes := FiniteSearch.words (EncodedClosingPlans.plans (E,D) V) (B+1)
  encode := EncodedClosingBanks.bankEncode (Equiv.refl _) env output
  injective := EncodedClosingBanks.bankEncode_injective (Equiv.refl _) env output
  member := EncodedClosingBanks.bankEncode_mem (Equiv.refl _) env one two output outOne outTwo
    (fun _ _ _ => false)
  complete := EncodedClosingBanks.bankEncode_sound (Equiv.refl _) env one two output outOne outTwo
    (fun _ _ _ => false)

def movePresentation : FinitePresentation (BlockMove I₁ I₂ O₁ O₂ G Q B D) EncodedBlock.Move :=
  ((boundaryPresentation graph objective).prod
    (((bankPresentation env output one two outOne outTwo).transport policyBankEquiv).prod
      (FinitePresentation.table (maskNumber env) (responsePresentation env)))).transport
    { toFun := fun m => (m.source,m.policy,m.response)
      invFun := fun m => ⟨m.1,m.2.1,m.2.2⟩
      left_inv := by intro m; cases m; rfl
      right_inv := by intro m; rfl }

def outcomePresentation : FinitePresentation (BlockOutcome I₁ I₂ G Q B D) EncodedBlock.Outcome :=
  (((maskPresentation env).dedup).prod (boundaryPresentation graph objective)).transport
    { toFun := fun b => (b.component,b.target)
      invFun := fun b => ⟨b.1,b.2⟩
      left_inv := by intro b; cases b; rfl
      right_inv := by intro b; rfl }

local notation "ctx" => blockContext (B:=B) (D:=D) (S:=S) (N:=N) env output one two outOne outTwo

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem boundary_codes : (boundaryPresentation (B:=B) graph objective).codes =
    EncodedBlock.boundaries ctx := rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem mask_codes : FiniteCodeNumbering.unique (maskPresentation (B:=B) (D:=D) env).codes =
    EncodedBlock.masks ctx := rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem response_codes : (responsePresentation (B:=B) (D:=D) env).codes =
    EncodedBlock.responses ctx := rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem move_codes : FiniteCodeNumbering.unique
    (movePresentation (B:=B) (D:=D) env output one two outOne outTwo graph objective).codes =
    EncodedBlock.moves ctx := rfl

omit [Fintype I₁] [Fintype I₂] [DecidableEq I₁] [DecidableEq I₂] in
theorem outcome_codes : FiniteCodeNumbering.unique
    (outcomePresentation (B:=B) (D:=D) env graph objective).codes =
    EncodedBlock.outcomes ctx := rfl

end
end
end Characterisation.PeriodicBlocks
