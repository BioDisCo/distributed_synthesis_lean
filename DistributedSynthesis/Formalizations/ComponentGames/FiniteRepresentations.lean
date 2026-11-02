/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedParityPresentation
import DistributedSynthesis.Formalizations.ComponentGames.RepresentationHistories
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex

namespace Characterisation.ComponentGames.Representation
open scoped Characterisation.ComponentGames.Representation
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {H J G Q : Type}

def dataEquiv : Data H G Q ≃ InputShape H × (H → G) × (H → Q) where
  toFun a := (a.shape,a.graph,a.state)
  invFun a := ⟨a.1,a.2.1,a.2.2⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro a; rfl

instance dataFintype [Fintype H] [DecidableEq H] [Fintype G] [Fintype Q] : Fintype (Data H G Q) :=
  Fintype.ofEquiv _ dataEquiv.symm

instance dataDecidableEq [Fintype H] [DecidableEq G] [DecidableEq Q] : DecidableEq (Data H G Q) :=
  fun a b => decidable_of_iff (dataEquiv a = dataEquiv b) dataEquiv.injective.eq_iff

def rename (e : H ≃ J) (a : Data H G Q) : Data J G Q where
  shape := restrictInputShape a.shape e.symm
  graph := a.graph ∘ e.symm
  state := a.state ∘ e.symm

def renameIso (e : H ≃ J) (a : Data H G Q) : Iso a (rename e a) where
  toEquiv := e
  shape_same := by intro p h k; simp [rename,restrictInputShape]
  graph_same := by intro h; simp [rename]
  state_same := by intro h; simp [rename]

def Iso.symm {a : Data H G Q} {b : Data J G Q} (e : Iso a b) : Iso b a where
  toEquiv := e.toEquiv.symm
  shape_same := by intro p h k; simpa using (e.shape_same p (e.toEquiv.symm h) (e.toEquiv.symm k)).symm
  graph_same := by intro h; simpa using (e.graph_same (e.toEquiv.symm h)).symm
  state_same := by intro h; simpa using (e.state_same (e.toEquiv.symm h)).symm

def Iso.trans {K : Type} {a : Data H G Q} {b : Data J G Q} {c : Data K G Q}
    (e : Iso a b) (f : Iso b c) : Iso a c where
  toEquiv := e.toEquiv.trans f.toEquiv
  shape_same := by intro p h k; exact (f.shape_same p _ _).trans (e.shape_same p h k)
  graph_same := by intro h; exact (f.graph_same _).trans (e.graph_same h)
  state_same := by intro h; exact (f.state_same _).trans (e.state_same h)

/-- A fixed computable numbering of each finite component. Sorting is used
only to choose the injection eta_K; no mathematical order is added to views. -/
abbrev numberSubset {α : Type} [LinearOrder α] (K : Finset α) : K ≃ Fin K.card :=
  (K.orderIsoOfFin rfl).toEquiv.symm

scoped instance graphLinearOrder : LinearOrder Graph :=
  LinearOrder.lift' EncodedParityPresentation.graphNumber EncodedParityPresentation.graphNumber.injective

scoped instance layerLinearOrder {I₁ I₂ : Type} [LinearOrder H] [LinearOrder I₁] [LinearOrder I₂]
    (n : Nat) : LinearOrder (ClosingLayer H I₁ I₂ n) := by
  induction n with
  | zero => exact inferInstanceAs (LinearOrder H)
  | succ n ih =>
    letI := ih
    exact LinearOrder.lift'
      (fun s : ClosingLayer H I₁ I₂ (n+1) => toLex (s.1,toLex (s.2.1,toLex (s.2.2.1,s.2.2.2))))
      (fun _ _ eq => eq)

/-- These are precisely bounded finite carriers with two Boolean view
relations and the two state assignments. The count need not be supplied. -/
abbrev Position (G Q : Type) (B : Nat) := (n : Fin (B+1)) × Data (Fin n.val) G Q

instance positionFintype [Fintype G] [Fintype Q] (B : Nat) : Fintype (Position G Q B) :=
  inferInstanceAs (Fintype ((n : Fin (B+1)) × Data (Fin n.val) G Q))

instance positionDecidableEq [DecidableEq G] [DecidableEq Q] (B : Nat) : DecidableEq (Position G Q B) :=
  inferInstanceAs (DecidableEq ((n : Fin (B+1)) × Data (Fin n.val) G Q))

abbrev Position.Root {B : Nat} (P : Position G Q B) := Fin P.1.val

def pack {α : Type} [LinearOrder α] {B : Nat} (K : Finset α) (bound : K.card ≤ B)
    (a : Data K G Q) : Position G Q B :=
  ⟨⟨K.card,by omega⟩,rename (numberSubset K) a⟩

def packIso {α : Type} [LinearOrder α] {B : Nat} (K : Finset α) (bound : K.card ≤ B)
    (a : Data K G Q) : Iso a (pack K bound a).2 := renameIso (numberSubset K) a

end Characterisation.ComponentGames.Representation
