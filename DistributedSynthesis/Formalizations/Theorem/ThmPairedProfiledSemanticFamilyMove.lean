/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledPhaseRootFamily
import DistributedSynthesis.Formalizations.Theorem.ThmCrossAnchorLocalNarrowing

/-!
# Semantic construction of a concrete profiled family move

The outer move must be chosen before the two hidden anchors are rationalized
independently.  Equal blind-side local views identify their complete semantic
sender strategies.  We narrow that one sender simultaneously against the two
receiver continuations and materialize the result directly in the finite move
alphabet of `ThmPairedProfiledRootFamilyAutomaton`.
-/

namespace DistributedSynthesis

universe u v x y s

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

section

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

omit [Inhabited In₁] [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal process-one views turn the two semantic right-block senders into
one shared sender. -/
private theorem profiledRight_sharedSender_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → ProfiledRightRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledRightFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    ∀ anchor env,
      (profiledRightFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history false)) env) := by
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderOne_eq_of_view_eq strategy hview]
      exact hwin true env

/-- Concrete finite right-family move selected from the original semantic
strategy at two locally indistinguishable histories. -/
noncomputable def profiledRightFamilyPairMoveOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → ProfiledRightRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledRightFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    ProfiledRightFamilyPairMove A :=
  ⟨source,
    finiteRootFamilyTable (profiledRightFamilyRootMonitors A source) receiver
      (blockSenderOne strategy (history false))
      (profiledRight_sharedSender_wins A strategy history hview source receiver
        hwin)⟩

/-- The semantic right-family move is valid in the concrete outer
automaton. -/
theorem profiledRightFamilyPairMoveOfViewEq_valid
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → ProfiledRightRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledRightFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    ProfiledBankRootMove.Valid A
      (.inr (.inl (profiledRightFamilyPairMoveOfViewEq A strategy history
        hview source receiver hwin))) := by
  simpa [ProfiledBankRootMove.Valid,
    profiledRightFamilyPairMoveOfViewEq] using
    (finiteRootFamilyTable_wins (profiledRightFamilyRootMonitors A source)
      receiver (blockSenderOne strategy (history false))
      (profiledRight_sharedSender_wins A strategy history hview source receiver
        hwin))

/-- Exact `Allowed` edge contributed by the semantic right-family move. -/
theorem profiledRightFamilyAllowed_of_viewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.one (history false) =
      currentView Proc.one (history true))
    (source : Bool → ProfiledRightRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₂ In₁
      (ProfiledRightReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledRightFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderOne strategy (history anchor)) env)) :
    let move := profiledRightFamilyPairMoveOfViewEq A strategy history hview
      source receiver hwin
    ProfiledBankRootFamilyAllowed A
      (profiledBankRightPairRoots A source)
      (ProfiledBankRootMove.successor A
        (.inr (.inl move) : ProfiledBankRootMove A)) := by
  dsimp only
  let move := profiledRightFamilyPairMoveOfViewEq A strategy history hview
    source receiver hwin
  exact ⟨.inr (.inl move),
    profiledRightFamilyPairMoveOfViewEq_valid A strategy history hview source
      receiver hwin, rfl, rfl⟩

/-! ## Left mirror -/

omit [Inhabited In₂] [Inhabited Out₁] [Inhabited Out₂] in
private theorem profiledLeft_sharedSender_wins
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → ProfiledLeftRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledLeftFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    ∀ anchor env,
      (profiledLeftFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history false)) env) := by
  intro anchor env
  cases anchor with
  | false => exact hwin false env
  | true =>
      rw [blockSenderTwo_eq_of_view_eq strategy hview]
      exact hwin true env

noncomputable def profiledLeftFamilyPairMoveOfViewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → ProfiledLeftRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledLeftFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    ProfiledLeftFamilyPairMove A :=
  ⟨source,
    finiteRootFamilyTable (profiledLeftFamilyRootMonitors A source) receiver
      (blockSenderTwo strategy (history false))
      (profiledLeft_sharedSender_wins A strategy history hview source receiver
        hwin)⟩

theorem profiledLeftFamilyPairMoveOfViewEq_valid
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → ProfiledLeftRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledLeftFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    ProfiledBankRootMove.Valid A
      (.inr (.inr (profiledLeftFamilyPairMoveOfViewEq A strategy history
        hview source receiver hwin))) := by
  simpa [ProfiledBankRootMove.Valid,
    profiledLeftFamilyPairMoveOfViewEq] using
    (finiteRootFamilyTable_wins (profiledLeftFamilyRootMonitors A source)
      receiver (blockSenderTwo strategy (history false))
      (profiledLeft_sharedSender_wins A strategy history hview source receiver
        hwin))

/-- Left semantic family edge in the concrete outer relation. -/
theorem profiledLeftFamilyAllowed_of_viewEq
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (history : Bool → History In₁ In₂ Graph Out₁ Out₂)
    (hview : currentView Proc.two (history false) =
      currentView Proc.two (history true))
    (source : Bool → ProfiledLeftRestartRoot A)
    (receiver : ∀ anchor, ReceiverBlockStrategy In₁ In₂
      (ProfiledLeftReceiverOutput A))
    (hwin : ∀ anchor env,
      (profiledLeftFamilyRootMonitors A source anchor).WinsPlay
        (pairPlay (receiver anchor)
          (blockSenderTwo strategy (history anchor)) env)) :
    let move := profiledLeftFamilyPairMoveOfViewEq A strategy history hview
      source receiver hwin
    ProfiledBankRootFamilyAllowed A
      (profiledBankLeftPairRoots A source)
      (ProfiledBankRootMove.successor A
        (.inr (.inr move) : ProfiledBankRootMove A)) := by
  dsimp only
  let move := profiledLeftFamilyPairMoveOfViewEq A strategy history hview
    source receiver hwin
  exact ⟨.inr (.inr move),
    profiledLeftFamilyPairMoveOfViewEq_valid A strategy history hview source
      receiver hwin, rfl, rfl⟩

end


end


end DetParityAutomaton

end DistributedSynthesis
