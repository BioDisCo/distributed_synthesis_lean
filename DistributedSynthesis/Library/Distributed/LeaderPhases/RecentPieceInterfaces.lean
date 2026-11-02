/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.LeaderPhases.BoundedOldViews
import DistributedSynthesis.Library.Distributed.LeaderPhases.PieceResponses

/-! Finite descriptions of actual recent pieces, with names for their old
coordinator views. Descriptions retain all internal observation equalities. -/
namespace Characterisation
open DistributedSynthesis

theorem finite_piece_description {H I₁ I₂ Q : Type*} [Finite H]
    (B C : Nat) (bound : Nat.card H ≤ B)
    (past : H → EnvHistory I₁ I₂) (label : H → Q)
    (mark : Proc → H → Option (Fin C))
    (hubView : (p : Proc) → Fin C → View I₁ I₂ p)
    (sound : ∀ p h a, mark p h = some a → currentView p (past h) = hubView p a) :
    ∃ summary : BoundedPieceDescription Q B C, ∃ e : Fin summary.1.val ≃ H,
      RepresentsPiece summary.2 (past ∘ e) hubView ∧
      (∀ i, summary.2.label i = label (e i)) ∧
      (∀ p i, summary.2.mark p i = mark p (e i)) := by
  obtain ⟨small,e,represents,labels⟩ := finite_switch_interface B bound past label
  refine ⟨⟨small.1,⟨small.2.1,fun p i => mark p (e i),small.2.2⟩⟩,e,?_,labels,?_⟩
  · exact ⟨represents,fun p i a ha => sound p (e i) a ha⟩
  · intro p i
    rfl

/-- A shared recent view joins the two roots by the recent relation. -/
theorem shared_view_between_pieces_is_old {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d : Nat) (h k : EnvHistory I₁ I₂) (p q : Proc)
    (liveH : P (History.graphSequence h)) (liveK : P (History.graphSequence k))
    (recent : RecentOther P d (History.graphSequence h) p)
    (separate : ¬ RecentConnected P d h k)
    (same : currentView q h = currentView q k) :
    q = p ∧ d ≤ silentAge (currentView q h) := by
  have age : d ≤ silentAge (currentView q h) := by
    by_contra bad
    apply separate
    exact Relation.ReflTransGen.single ⟨liveH,liveK,q,same,by omega⟩
  exact ⟨old_view_owner P d h p q recent age,age⟩

/-- An injective naming of old coordinator views gives exactly the shared
name required by the piece-response gluing theorem. -/
theorem shared_view_has_common_name {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d C : Nat) (root h k : EnvHistory I₁ I₂) (p : Proc)
    (code : OldCoordinatorViews P d root p → Fin C)
    (hc : InputConnected P root h) (kc : InputConnected P root k)
    (same : currentView p h = currentView p k)
    (old : d ≤ silentAge (currentView p h)) :
    code ⟨currentView p h,⟨h,hc,rfl,old⟩⟩ =
      code ⟨currentView p k,⟨k,kc,rfl,by rwa [← same]⟩⟩ := by
  apply congrArg code
  exact Subtype.ext same

/-- The bounded old-view family admits global names and a readback map.
Names are shared by all recent pieces inside this component. -/
theorem name_old_coordinator_views {I₁ I₂ : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (d : Nat) (root : EnvHistory I₁ I₂) (p : Proc)
    (recent : RecentOther P d (History.graphSequence root) p) :
    ∃ code : OldCoordinatorViews P d root p →
        Fin (Nat.card (Fin d → Option (PSum I₁ I₂))),
      Function.Injective code ∧
      ∃ hubView : (q : Proc) → Fin (Nat.card (Fin d → Option (PSum I₁ I₂))) → View I₁ I₂ q,
        ∀ v, hubView p (code v) = v.val := by
  classical
  have bounds := bounded_old_coordinator_views P d root p recent
  letI : Finite (OldCoordinatorViews P d root p) := bounds.1
  letI := Fintype.ofFinite (OldCoordinatorViews P d root p)
  obtain ⟨embedding⟩ := Function.Embedding.nonempty_of_card_le
    (α:=OldCoordinatorViews P d root p)
    (β:=Fin (Nat.card (Fin d → Option (PSum I₁ I₂))))
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using bounds.2)
  letI : Nonempty (View I₁ I₂ p) := ⟨.empty p⟩
  obtain ⟨decode,correct⟩ := factor_local_response embedding (fun v => v.val)
    (fun x y eq => congrArg Subtype.val (embedding.injective eq))
  let hubView (q : Proc) a : View I₁ I₂ q :=
    if eq : q = p then eq.symm ▸ decode a else .empty q
  refine ⟨embedding,embedding.injective,hubView,?_⟩
  intro v
  simpa [hubView] using correct v

noncomputable def markOldView {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d C : Nat) (root : EnvHistory I₁ I₂) (p : Proc)
    (code : OldCoordinatorViews P d root p → Fin C)
    (q : Proc) (k : InputHistoryComponent P root) : Option (Fin C) := by
  classical
  exact if condition : q = p ∧ d ≤ silentAge (currentView p k.val)
    then some (code ⟨currentView p k.val,⟨k.val,k.property,rfl,condition.2⟩⟩) else none

theorem markOldView_sound {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d C : Nat) (root : EnvHistory I₁ I₂) (p : Proc)
    (code : OldCoordinatorViews P d root p → Fin C)
    (hubView : (q : Proc) → Fin C → View I₁ I₂ q)
    (correct : ∀ v, hubView p (code v) = v.val)
    (q : Proc) (k : InputHistoryComponent P root) (a : Fin C)
    (marked : markOldView P d C root p code q k = some a) :
    currentView q k.val = hubView q a := by
  classical
  unfold markOldView at marked
  split at marked
  · rename_i condition
    have same := condition.1
    subst q
    have name := Option.some.inj marked
    rw [← name,correct]
  · cases marked

/-- Across distinct actual recent pieces, every shared view has the same
global name. This discharges the geometric part of the gluing hypothesis. -/
theorem markOldView_overlap {I₁ I₂ : Type*}
    (P : List Graph → Prop) (d C : Nat) (root : EnvHistory I₁ I₂) (p : Proc)
    (code : OldCoordinatorViews P d root p → Fin C)
    (recent : RecentOther P d (History.graphSequence root) p)
    (h k : InputHistoryComponent P root)
    (liveH : P (History.graphSequence h.val)) (liveK : P (History.graphSequence k.val))
    (separate : ¬ RecentConnected P d h.val k.val)
    (q : Proc) (same : currentView q h.val = currentView q k.val) :
    ∃ a, markOldView P d C root p code q h = some a ∧
      markOldView P d C root p code q k = some a := by
  classical
  have recentH := (recentOther_component_invariant P d
    (inputConnected_projects P h.property) p).mp recent
  obtain ⟨owner,old⟩ := shared_view_between_pieces_is_old P d h.val k.val p q
    liveH liveK recentH separate same
  subst q
  have oldK : d ≤ silentAge (currentView p k.val) := by rwa [← same]
  let v : OldCoordinatorViews P d root p := ⟨currentView p h.val,⟨h.val,h.property,rfl,old⟩⟩
  refine ⟨code v,?_,?_⟩
  · unfold markOldView
    rw [dif_pos (show p = p ∧ d ≤ silentAge (currentView p h.val) from ⟨rfl,old⟩)]
  · unfold markOldView
    rw [dif_pos (show p = p ∧ d ≤ silentAge (currentView p k.val) from ⟨rfl,oldK⟩)]
    apply congrArg some
    apply congrArg code
    exact Subtype.ext same.symm

/-- Each bounded recent piece has a finite description using the component's
single shared naming of its old coordinator views. -/
theorem describe_recent_piece {I₁ I₂ Q : Type*} [Finite I₁] [Finite I₂]
    (P : List Graph → Prop) (d B C : Nat) (root : EnvHistory I₁ I₂) (p : Proc)
    (code : OldCoordinatorViews P d root p → Fin C)
    (hubView : (q : Proc) → Fin C → View I₁ I₂ q)
    (correct : ∀ v, hubView p (code v) = v.val)
    (label : EnvHistory I₁ I₂ → Q) (h : InputHistoryComponent P root)
    (finite : Finite (RecentPiece P d h.val)) (bound : Nat.card (RecentPiece P d h.val) ≤ B) :
    ∃ summary : BoundedPieceDescription Q B C,
      ∃ e : Fin summary.1.val ≃ RecentPiece P d h.val,
        RepresentsPiece summary.2 (fun i => (e i).val) hubView ∧
        (∀ i, summary.2.label i = label (e i).val) ∧
        (∀ q i, summary.2.mark q i = markOldView P d C root p code q
          ⟨(e i).val,h.property.trans (recentConnected_projects P d (e i).property)⟩) := by
  letI : Finite (RecentPiece P d h.val) := finite
  let member (k : RecentPiece P d h.val) : InputHistoryComponent P root :=
    ⟨k.val,h.property.trans (recentConnected_projects P d k.property)⟩
  exact finite_piece_description B C bound (fun k => k.val) (fun k => label k.val)
    (fun q k => markOldView P d C root p code q (member k)) hubView
    (fun q k a marked => markOldView_sound P d C root p code hubView correct q (member k) a marked)

end Characterisation
