/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.FiniteSwitchInterface
import DistributedSynthesis.Library.Distributed.LeaderPhases.TableComposition

/-! Response tables for pieces with named shared views. A name is internal
compiler data, not an additional observation available to a process. -/
namespace Characterisation
open DistributedSynthesis

structure PieceDescription (S Hub Q : Type*) where
  shape : InputShape S
  mark : Proc → S → Option Hub
  label : S → Q

instance pieceDescription_finite {S Hub Q : Type*} [Finite S] [Finite Hub] [Finite Q] :
    Finite (PieceDescription S Hub Q) := by
  apply Finite.of_injective (fun d : PieceDescription S Hub Q => (d.shape,d.mark,d.label))
  intro a b eq
  cases a
  cases b
  simpa using eq

abbrev BoundedPieceDescription (Q : Type*) (B C : Nat) :=
  Σ n : Fin (B+1), PieceDescription (Fin n.val) (Fin C) Q

instance boundedPieceDescription_finite {Q : Type*} [Finite Q] (B C : Nat) :
    Finite (BoundedPieceDescription Q B C) := by
  unfold BoundedPieceDescription
  infer_instance

/-- A piece table agrees internally and with the prescribed outputs at its
named shared views. There may be several slots with the same name. -/
def PieceResponse {S Hub Q O₁ O₂ : Type*} (desc : PieceDescription S Hub Q)
    (hubOne : Hub → O₁) (hubTwo : Hub → O₂) (out : S → O₁ × O₂) : Prop :=
  ShapeCoherent desc.shape out ∧
  (∀ s a, desc.mark .one s = some a → (out s).1 = hubOne a) ∧
  (∀ s a, desc.mark .two s = some a → (out s).2 = hubTwo a)

/-- Occurrences of a piece type have the same within-piece observations.
Named views have the same actual value in every occurrence. -/
def RepresentsPiece {S Hub Q I₁ I₂ : Type*}
    (desc : PieceDescription S Hub Q) (past : S → EnvHistory I₁ I₂)
    (hubView : (p : Proc) → Hub → View I₁ I₂ p) : Prop :=
  RepresentsInputShape past desc.shape ∧
  ∀ p s a, desc.mark p s = some a → currentView p (past s) = hubView p a

theorem strategy_piece_response {S Hub Q I₁ I₂ O₁ O₂ : Type*}
    (desc : PieceDescription S Hub Q) (past : S → EnvHistory I₁ I₂)
    (hubView : (p : Proc) → Hub → View I₁ I₂ p)
    (represents : RepresentsPiece desc past hubView) (σ : StrategyPair I₁ I₂ O₁ O₂) :
    PieceResponse desc (fun a => σ.one (hubView .one a)) (fun a => σ.two (hubView .two a))
      (fun s => (σ.one (currentView .one (past s)), σ.two (currentView .two (past s)))) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro s t eq
    exact congrArg σ.one ((represents.1 .one s t).mp eq)
  · intro s t eq
    exact congrArg σ.two ((represents.1 .two s t).mp eq)
  · intro s a mark
    exact congrArg σ.one (represents.2 .one s a mark)
  · intro s a mark
    exact congrArg σ.two (represents.2 .two s a mark)

/-- Gluing uses shared-view names only where different occurrences overlap.
It does not require that either process can identify its piece occurrence. -/
theorem piece_responses_compatible {T Hub Q I₁ I₂ O₁ O₂ : Type*}
    {J S : T → Type*} (desc : (t : T) → PieceDescription (S t) Hub Q)
    (past : (t : T) → J t → S t → EnvHistory I₁ I₂)
    (hubView : (p : Proc) → Hub → View I₁ I₂ p)
    (represents : ∀ t j, RepresentsPiece (desc t) (past t j) hubView)
    (overlap : ∀ p t u (j : J t) (k : J u) s r,
      (Sigma.mk t j : Sigma J) ≠ Sigma.mk u k →
      currentView p (past t j s) = currentView p (past u k r) →
      ∃ a, (desc t).mark p s = some a ∧ (desc u).mark p r = some a)
    (hubOne : Hub → O₁) (hubTwo : Hub → O₂)
    (out : (t : T) → S t → O₁ × O₂)
    (valid : ∀ t, Nonempty (J t) → PieceResponse (desc t) hubOne hubTwo (out t)) :
    TablesCompatible (fun x : Sigma J => past x.1 x.2) (fun x : Sigma J => out x.1) := by
  constructor
  · intro x y s r eq
    by_cases same : x = y
    · subst y
      exact (valid x.1 ⟨x.2⟩).1.1 s r (((represents x.1 x.2).1 .one s r).mpr eq)
    · obtain ⟨a,ha,hb⟩ := overlap .one x.1 y.1 x.2 y.2 s r same eq
      exact ((valid x.1 ⟨x.2⟩).2.1 s a ha).trans ((valid y.1 ⟨y.2⟩).2.1 r a hb).symm
  · intro x y s r eq
    by_cases same : x = y
    · subst y
      exact (valid x.1 ⟨x.2⟩).1.2 s r (((represents x.1 x.2).1 .two s r).mpr eq)
    · obtain ⟨a,ha,hb⟩ := overlap .two x.1 y.1 x.2 y.2 s r same eq
      exact ((valid x.1 ⟨x.2⟩).2.2 s a ha).trans ((valid y.1 ⟨y.2⟩).2.2 r a hb).symm

/-- Multiplicity can be removed for local response constraints: select one
table per occurring description, preserving the original shared-view outputs
and every supplied constraint that depends only on that description/table.
This does not assert preservation of a temporal winning condition. -/
theorem normalize_piece_responses {T Hub Q I₁ I₂ O₁ O₂ : Type*}
    [Nonempty O₁] [Nonempty O₂] {J S : T → Type*}
    (desc : (t : T) → PieceDescription (S t) Hub Q)
    (past : (t : T) → J t → S t → EnvHistory I₁ I₂)
    (hubView : (p : Proc) → Hub → View I₁ I₂ p)
    (represents : ∀ t j, RepresentsPiece (desc t) (past t j) hubView)
    (overlap : ∀ p t u (j : J t) (k : J u) s r,
      (Sigma.mk t j : Sigma J) ≠ Sigma.mk u k →
      currentView p (past t j s) = currentView p (past u k r) →
      ∃ a, (desc t).mark p s = some a ∧ (desc u).mark p r = some a)
    (good : (t : T) → (S t → O₁ × O₂) → Prop)
    (σ : StrategyPair I₁ I₂ O₁ O₂)
    (satisfies : ∀ t j, good t (fun s =>
      (σ.one (currentView .one (past t j s)), σ.two (currentView .two (past t j s))))) :
    ∃ out : (t : T) → S t → O₁ × O₂,
      (∀ t, Nonempty (J t) → good t (out t) ∧
        PieceResponse (desc t) (fun a => σ.one (hubView .one a))
          (fun a => σ.two (hubView .two a)) (out t)) ∧
      ∃ τ : StrategyPair I₁ I₂ O₁ O₂, ∀ t j s,
        τ.one (currentView .one (past t j s)) = (out t s).1 ∧
        τ.two (currentView .two (past t j s)) = (out t s).2 := by
  classical
  let original t (j : J t) s :=
    (σ.one (currentView .one (past t j s)), σ.two (currentView .two (past t j s)))
  let out t := if h : Nonempty (J t) then original t (Classical.choice h)
    else fun _ => (Classical.choice (inferInstance : Nonempty O₁),
      Classical.choice (inferInstance : Nonempty O₂))
  have valid : ∀ t, Nonempty (J t) → good t (out t) ∧
      PieceResponse (desc t) (fun a => σ.one (hubView .one a))
        (fun a => σ.two (hubView .two a)) (out t) := by
    intro t inhabited
    simp only [out, dif_pos inhabited]
    exact ⟨satisfies t _,strategy_piece_response (desc t) (past t _) hubView (represents t _) σ⟩
  refine ⟨out,valid,?_⟩
  have compatible := piece_responses_compatible desc past hubView represents overlap
    (fun a => σ.one (hubView .one a)) (fun a => σ.two (hubView .two a)) out
    (fun t ht => (valid t ht).2)
  obtain ⟨τ,hτ⟩ := (tables_compatible_iff_local _ _).mp compatible
  exact ⟨τ,fun t j s => hτ ⟨t,j⟩ s⟩

end Characterisation
