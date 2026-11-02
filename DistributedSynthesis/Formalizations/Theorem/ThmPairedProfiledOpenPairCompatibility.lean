/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Theorem.ThmPairedProfiledOpenFamilyHandoff

/-!
# Pair compatibility for pre-policy profiled roots

Individual open roots only assert nonemptiness of their input-free objective
languages.  Recursive distributed readback needs a strictly stronger fact:
the two roots hidden from the next blind sender must admit one common sender.

This file gives that condition a first-class finite-root interface, proves it
for pairs represented by one winning distributed strategy and one blind local
view, and extracts the corresponding finite simultaneous table.  It also
names the exact handoff-closure law still required by an outer recursion.
-/

namespace DistributedSynthesis

universe u v x y s w

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

/-- Two right-oriented open roots are compatible when their receiver
continuations can be paired with one and the same blind process-one sender.
The Boolean index is proof-side data and is not an input of `sender`. -/
def ProfiledOpenRightPairCompatible
    (source : Bool → ProfiledOpenRightRoot A) : Prop :=
  ∃ receiver : ∀ anchor : Bool,
      ReceiverBlockStrategy In₂ In₁ (ProfiledRightReceiverOutput A),
    ∃ sender : SenderBlockStrategy In₁ Out₁,
      ∀ anchor env,
        (profiledOpenRightRootMonitor.{u, v, x, y, s, w}
          A (source anchor)).WinsPlay
          (pairPlay (receiver anchor) sender env)

/-- Left-oriented mirror. -/
def ProfiledOpenLeftPairCompatible
    (source : Bool → ProfiledOpenLeftRoot A) : Prop :=
  ∃ receiver : ∀ anchor : Bool,
      ReceiverBlockStrategy In₁ In₂ (ProfiledLeftReceiverOutput A),
    ∃ sender : SenderBlockStrategy In₂ Out₂,
      ∀ anchor env,
        (profiledOpenLeftRootMonitor.{u, v, x, y, s, w}
          A (source anchor)).WinsPlay
          (pairPlay (receiver anchor) sender env)

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal raw process-one views yield a compatible pre-policy right pair. -/
theorem profiledOpenRightPairCompatible_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : Bool → ProcOnePairedEntryRep strategy)
    (minimum : Bool → A.State)
    (hview : currentView Proc.one (entry false).leftHistory =
      currentView Proc.one (entry true).leftHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenRightPairCompatible.{u, v, x, y, s, w} A (fun anchor =>
      profiledOpenRightRootOfWinning A strategy hwin (entry anchor)
        (minimum anchor) basis) := by
  refine ⟨(fun anchor => profiledRightReceiverStrategy A
      (entry anchor).code (entry anchor).lambdaOfStrategy),
    pairedRightSenderStrategy (entry false).lambdaOfStrategy, ?_⟩
  exact profiledOpenRight_sharedSender_wins A strategy hwin entry minimum
    hview basis

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Equal raw process-two views yield a compatible pre-policy left pair. -/
theorem profiledOpenLeftPairCompatible_of_winning
    (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
    (hwin : ∀ env : EnvironmentSequence In₁ In₂,
      A.Accepts (execution strategy env))
    (entry : Bool → ProcTwoPairedEntryRep strategy)
    (minimum : Bool → A.State)
    (hview : currentView Proc.two (entry false).rightHistory =
      currentView Proc.two (entry true).rightHistory)
    (basis : ∀ state : PairedProfiledTreeState A,
      (pairedProfiledEntryRunAutomaton A state).RationalRunBasis) :
    ProfiledOpenLeftPairCompatible.{u, v, x, y, s, w} A (fun anchor =>
      profiledOpenLeftRootOfWinning A strategy hwin (entry anchor)
        (minimum anchor) basis) := by
  refine ⟨(fun anchor => profiledLeftReceiverStrategy A
      (entry anchor).code (entry anchor).lambdaOfStrategy),
    pairedLeftSenderStrategy (entry false).lambdaOfStrategy, ?_⟩
  exact profiledOpenLeft_sharedSender_wins A strategy hwin entry minimum
    hview basis

/-- The two opposite-orientation roots emitted by a fixed right table and a
fixed compressed direction. -/
noncomputable def profiledOpenRightPairChildren
    (source : Bool → ProfiledOpenRightRoot A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (Bool × In₂) In₁ (ProfiledRightReceiverOutput A)
        Out₁ (finiteRootFamilyMonitor
          (profiledOpenRightRootMonitors.{0, u, v, x, y, s, w}
            A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (profiledOpenRightRootMonitors.{0, u, v, x, y, s, w} A source))
      family.labeledTree)
    (row : PairedEntryRow) (past : List (In₂ × In₁))
    (input : In₂ × In₁) : Bool → ProfiledOpenLeftRoot A :=
  fun anchor => profiledOpenRightFamilyChild A source family hfamily anchor
    (omegaOfList (past ++ [input])) past.length row

/-- Left-oriented mirror. -/
noncomputable def profiledOpenLeftPairChildren
    (source : Bool → ProfiledOpenLeftRoot A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (Bool × In₁) In₂ (ProfiledLeftReceiverOutput A)
        Out₂ (finiteRootFamilyMonitor
          (profiledOpenLeftRootMonitors.{0, u, v, x, y, s, w}
            A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (profiledOpenLeftRootMonitors.{0, u, v, x, y, s, w} A source))
      family.labeledTree)
    (row : PairedEntryRow) (past : List (In₁ × In₂))
    (input : In₁ × In₂) : Bool → ProfiledOpenRightRoot A :=
  fun anchor => profiledOpenLeftFamilyChild A source family hfamily anchor
    (omegaOfList (past ++ [input])) past.length row

/-- Exact recursive closure obligation for one valid right table.  This is
stronger than individual child nonemptiness: every emitted pair must again
admit one common sender after the orientation changes. -/
def ProfiledOpenRightTableHandoffClosed
    (source : Bool → ProfiledOpenRightRoot A)
    (family : TransitionRationalTree In₁
      (NarrowedBlockLabel (Bool × In₂) In₁ (ProfiledRightReceiverOutput A)
        Out₁ (finiteRootFamilyMonitor
          (profiledOpenRightRootMonitors.{0, u, v, x, y, s, w}
            A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (profiledOpenRightRootMonitors.{0, u, v, x, y, s, w} A source))
      family.labeledTree) : Prop :=
  ∀ row past input,
    ProfiledOpenLeftPairCompatible.{u, v, x, y, s, w} A
      (profiledOpenRightPairChildren A source family hfamily row past input)

/-- Left-oriented mirror. -/
def ProfiledOpenLeftTableHandoffClosed
    (source : Bool → ProfiledOpenLeftRoot A)
    (family : TransitionRationalTree In₂
      (NarrowedBlockLabel (Bool × In₁) In₂ (ProfiledLeftReceiverOutput A)
        Out₂ (finiteRootFamilyMonitor
          (profiledOpenLeftRootMonitors.{0, u, v, x, y, s, w}
            A source)).State))
    (hfamily : NarrowedAllThreadsWin
      (finiteRootFamilyMonitor
        (profiledOpenLeftRootMonitors.{0, u, v, x, y, s, w} A source))
      family.labeledTree) : Prop :=
  ∀ row past input,
    ProfiledOpenRightPairCompatible.{u, v, x, y, s, w} A
      (profiledOpenLeftPairChildren A source family hfamily row past input)

end

end

end DetParityAutomaton

end DistributedSynthesis
