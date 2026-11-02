/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemPairedProfiledRawJointFinitePhysicalSiblingFreshPolicyHandoff

/-!
# Fixed rerooting from reachable local-control equations

The root-oriented acceptance theorem asks for `TraceOperationalAt` at every
graph/root match.  That trace equality is not an additional invariant of the
carrier: the operational-close module already proves it from four concrete
reachable control shapes.  A right query may be stored either in a completed
matched-left pair or in the receiver/receiver cross; a left query has the two
mirror shapes.

This file packages those four cases as one inductive local equation and proves
the exact adapter to `ProfiledRawJointUnitPolicyFixedRerootInvariant`.  It also
replaces the abstract record-length equation by the literal length of the
finite input list carried by the scheduled query.

The graph/root match, global state, and schedule are proof-side arguments.
No process receives a graph, orientation, row, cut, or leader bit.
-/

namespace DistributedSynthesis

universe u v x y s i₁ i₂ e₁ e₂

namespace DetParityAutomaton

variable {In₁ : Type u} {In₂ : Type v} {Out₁ : Type x} {Out₂ : Type y}
variable
  (A : DetParityAutomaton.{max u v x y, s}
    (RoundRecord In₁ In₂ Graph Out₁ Out₂))

noncomputable section

variable [Inhabited In₁] [Inhabited In₂] [Inhabited Out₁]
  [Inhabited Out₂]
variable [Fintype In₁] [Fintype In₂] [Fintype Out₁] [Fintype Out₂]
variable [DecidableEq In₁] [DecidableEq In₂]

variable
  (strategy : StrategyPair In₁ In₂ Out₁ Out₂)
  (initial : ProfiledRawJointOneSidedSemanticState A strategy (I := Unit))
  (policy : ProfiledRawJointOneSidedProvenanceRationalPolicy A strategy
    (initial.code A))
  (bank : ProfiledRawJointUnitPolicyControllerBank A strategy initial policy)

private abbrev UnitKernel
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo) :=
  profiledRawJointUnitPolicyLeaderFreeKernel A strategy initial policy bank
    adapter

namespace ProfiledRawJointUnitPolicyCloseQuery

/-- Exact reachable local-control equation at one scheduled cut.

The constructors are precisely the four hypotheses consumed by the checked
matched/cross trace theorems.  The equation is a predicate on the proof-side
joint state; it adds no constructor or signal to either local controller. -/
inductive ReachableControlEquationAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂)
    (base : Nat) (cuts : Nat → Nat) (k : Nat) :
    (root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy) →
    ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy root → Prop
  | rightMatchedLeft
      (source : ProfiledRawJointUnitRightPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (move : In₂ × In₁)
      (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
        policy)
      (owner : ProfiledRawJointUnitLeftPolicyOwnerControl A strategy initial
        policy bank)
      (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
      (control_eq :
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitMatchedLeftState A strategy initial policy bank
            adapter left owner oldOutputOne oldOutputTwo)
      (target_eq : profiledRawJointUnitPolicyLeftReceiverTarget A strategy
        initial policy bank left = source)
      (row_eq : left.2.1 = row)
      (environment_eq : ∀ j : Nat, j < past.length →
        OmegaWord.drop physicalEnv (base + cuts k) j =
          profiledRawJointUnitStrictRightEnvironment
            (omegaOfList (past ++ [move])) j) :
      ReachableControlEquationAt adapter physicalEnv base cuts k
        (.inl source) (.right source row past move)
  | rightCross
      (source : ProfiledRawJointUnitRightPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₂ × In₁))
      (move : In₂ × In₁)
      (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
        policy)
      (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
        initial policy)
      (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
      (control_eq :
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitCrossState A strategy initial policy bank adapter
            left right oldOutputOne oldOutputTwo)
      (target_eq : profiledRawJointUnitPolicyLeftReceiverTarget A strategy
        initial policy bank left = source)
      (row_eq : left.2.1 = row)
      (environment_eq : ∀ j : Nat, j < past.length →
        OmegaWord.drop physicalEnv (base + cuts k) j =
          profiledRawJointUnitStrictRightEnvironment
            (omegaOfList (past ++ [move])) j) :
      ReachableControlEquationAt adapter physicalEnv base cuts k
        (.inl source) (.right source row past move)
  | leftMatchedRight
      (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (move : In₁ × In₂)
      (owner : ProfiledRawJointUnitRightPolicyOwnerControl A strategy initial
        policy bank)
      (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
        initial policy)
      (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
      (control_eq :
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitMatchedRightState A strategy initial policy bank
            adapter owner right oldOutputOne oldOutputTwo)
      (target_eq : profiledRawJointUnitPolicyRightReceiverTarget A strategy
        initial policy bank right = source)
      (row_eq : right.2.1 = row)
      (environment_eq : ∀ j : Nat, j < past.length →
        OmegaWord.drop physicalEnv (base + cuts k) j =
          profiledRawJointUnitStrictLeftEnvironment
            (omegaOfList (past ++ [move])) j) :
      ReachableControlEquationAt adapter physicalEnv base cuts k
        (.inr source) (.left source row past move)
  | leftCross
      (source : ProfiledRawJointUnitLeftPolicyMacro A strategy
        (initial.code A) policy)
      (row : PairedEntryRow) (past : List (In₁ × In₂))
      (move : In₁ × In₂)
      (left : ProfiledRawJointUnitLeftPolicyReceiverControl A strategy initial
        policy)
      (right : ProfiledRawJointUnitRightPolicyReceiverControl A strategy
        initial policy)
      (oldOutputOne : Out₁) (oldOutputTwo : Out₂)
      (control_eq :
        (UnitKernel A strategy initial policy bank adapter).globalMachine.globalStateTrace
            physicalEnv (base + cuts k) =
          profiledRawJointUnitCrossState A strategy initial policy bank adapter
            left right oldOutputOne oldOutputTwo)
      (target_eq : profiledRawJointUnitPolicyRightReceiverTarget A strategy
        initial policy bank right = source)
      (row_eq : right.2.1 = row)
      (environment_eq : ∀ j : Nat, j < past.length →
        OmegaWord.drop physicalEnv (base + cuts k) j =
          profiledRawJointUnitStrictLeftEnvironment
            (omegaOfList (past ++ [move])) j) :
      ReachableControlEquationAt adapter physicalEnv base cuts k
        (.inr source) (.left source row past move)

/-- Literal input-prefix length carried by a close query.  It is kept as a
separate projection so schedule equations never have to perform a dependent
match on the scheduled root. -/
def inputListLength
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) : Nat :=
  match query with
  | .right _ _ past _ => past.length
  | .left _ _ past _ => past.length

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The query's literal record list has exactly the length of its finite input
prefix. -/
theorem records_length_eq_inputListLength
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    (query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root) :
    (query.records A strategy initial policy bank).length =
      query.inputListLength A strategy initial policy := by
  cases query <;>
    simp [ProfiledRawJointUnitPolicyCloseQuery.records, inputListLength,
      profiledRawJointUnitRightPhysicalPrefixRecords,
      profiledRawJointUnitLeftPhysicalPrefixRecords, omegaPrefix]

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- The four reachable local-control equations discharge the abstract
trace-operational premise. -/
theorem ReachableControlEquationAt.traceOperationalAt
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {root : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂}
    {base : Nat} {cuts : Nat → Nat} {k : Nat}
    {query : ProfiledRawJointUnitPolicyCloseQuery A strategy initial policy
      root}
    (equation : ReachableControlEquationAt A strategy initial policy bank
      adapter physicalEnv base cuts k root query) :
    query.TraceOperationalAt A strategy initial policy bank adapter physicalEnv
      base cuts k := by
  cases equation with
  | rightMatchedLeft source row past move left owner oldOne oldTwo hcontrol
      htarget hrow henv =>
      exact profiledRawJointUnitRightQuery_traceOperationalAt_of_matchedLeft A
        strategy initial policy bank adapter source row past move left owner
          oldOne oldTwo physicalEnv base cuts k hcontrol htarget hrow henv
  | rightCross source row past move left right oldOne oldTwo hcontrol htarget
      hrow henv =>
      exact profiledRawJointUnitRightQuery_traceOperationalAt_of_cross A
        strategy initial policy bank adapter source row past move left right
          oldOne oldTwo physicalEnv base cuts k hcontrol htarget hrow henv
  | leftMatchedRight source row past move owner right oldOne oldTwo hcontrol
      htarget hrow henv =>
      exact profiledRawJointUnitLeftQuery_traceOperationalAt_of_matchedRight A
        strategy initial policy bank adapter source row past move owner right
          oldOne oldTwo physicalEnv base cuts k hcontrol htarget hrow henv
  | leftCross source row past move left right oldOne oldTwo hcontrol htarget
      hrow henv =>
      exact profiledRawJointUnitLeftQuery_traceOperationalAt_of_cross A
        strategy initial policy bank adapter source row past move left right
          oldOne oldTwo physicalEnv base cuts k hcontrol htarget hrow henv

end ProfiledRawJointUnitPolicyCloseQuery

/-! ## Schedule-level adapter -/

/-- Carrier-facing equations at the root-oriented cuts.

Compared with `ProfiledRawJointUnitPolicyFixedRerootInvariant`, the infinite
trace field has disappeared.  It is replaced by constructor-level equations
for the actual reachable pair of local controls.  Record length is stated as
the literal finite input-list length of the selected query. -/
structure ProfiledRawJointUnitPolicyFixedRerootControlEquations
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy)
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy) : Prop where
  dpaStateAt : ∀ k : Nat,
    A.run
        ((UnitKernel A strategy initial policy bank adapter).globalMachine.globalMachineTraceWord
          (UnitKernel A strategy initial policy bank adapter).globalOutputOne
          (UnitKernel A strategy initial policy bank adapter).globalOutputTwo
          physicalEnv)
        (base + profiledRawJointUnitPolicyRootOrientedCuts A strategy initial
          policy bank physicalEnv base hterm seed schedule k) =
      (schedule k
        (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
          seed schedule k)).entryState A strategy initial policy
  inputListLengthAt : ∀ k : Nat,
    let query := schedule k
      (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy bank
        seed schedule k)
    query.inputListLength A strategy initial policy =
      profiledRawJointUnitPolicyRootOrientedOpenLength A strategy initial
        policy bank physicalEnv base hterm seed schedule k
  reachableControlAt_of_match : ∀ k : Nat,
    profiledRawJointPhysicalGraphTail physicalEnv base
        (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
          bank physicalEnv base hterm seed schedule k) =
      profiledRawJointUnitPolicyScheduledGraph A strategy initial policy bank
        seed schedule k →
      ProfiledRawJointUnitPolicyCloseQuery.ReachableControlEquationAt A
        strategy initial policy bank adapter physicalEnv base
          (profiledRawJointUnitPolicyRootOrientedCuts A strategy initial policy
            bank physicalEnv base hterm seed schedule) k
          (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
            bank seed schedule k)
          (schedule k
            (profiledRawJointUnitPolicyScheduledRoot A strategy initial policy
              bank seed schedule k))

omit [Inhabited Out₁] [Inhabited Out₂] in
/-- Reachable control equations imply the complete fixed-reroot invariant. -/
theorem ProfiledRawJointUnitPolicyFixedRerootControlEquations.toFixedRerootInvariant
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    {adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy initial
      policy bank InitialOne InitialTwo ExceptionalOne ExceptionalTwo}
    {physicalEnv : EnvironmentSequence In₁ In₂} {base : Nat}
    {hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base)}
    {seed : ProfiledRawJointUnitFixedPolicyRoot A strategy (initial.code A)
      policy}
    {schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy initial
      policy}
    (equations : ProfiledRawJointUnitPolicyFixedRerootControlEquations A
      strategy initial policy bank adapter physicalEnv base hterm seed
        schedule) :
    ProfiledRawJointUnitPolicyFixedRerootInvariant A strategy initial policy
      bank adapter physicalEnv base hterm seed schedule where
  entryStateAt := equations.dpaStateAt
  recordsLengthAt k := by
    rw [ProfiledRawJointUnitPolicyCloseQuery.records_length_eq_inputListLength]
    exact equations.inputListLengthAt k
  traceOperationalAt_of_match k hmatch :=
    (equations.reachableControlAt_of_match k hmatch).traceOperationalAt A
      strategy initial policy bank

namespace ProfiledRawJointSiblingFreshPolicyPackage

variable {strategy : StrategyPair In₁ In₂ Out₁ Out₂}
variable {target : ProfiledRawJointIncidenceCode A (I := Unit)}

/-- Fresh-policy end-to-end acceptance from reachable local-control equations.
After this theorem, no infinite trace equality remains in the premise. -/
theorem physicalTrace_accepts_of_fixedRerootControlEquations
    {InitialOne : Type i₁} {InitialTwo : Type i₂}
    {ExceptionalOne : Type e₁} {ExceptionalTwo : Type e₂}
    [Fintype InitialOne] [Fintype InitialTwo]
    [Fintype ExceptionalOne] [Fintype ExceptionalTwo]
    (package : ProfiledRawJointSiblingFreshPolicyPackage A strategy target)
    (adapter : ProfiledRawJointUnitPolicyExceptionalAdapter A strategy
      package.initial package.policy (package.bank A) InitialOne InitialTwo
        ExceptionalOne ExceptionalTwo)
    (physicalEnv : EnvironmentSequence In₁ In₂) (base : Nat)
    (hterm : OperationalStrictRunsTerminate
      (profiledRawJointPhysicalGraphTail physicalEnv base))
    (schedule : ProfiledRawJointUnitPolicyCloseSchedule A strategy
      package.initial package.policy)
    (equations : ProfiledRawJointUnitPolicyFixedRerootControlEquations A
      strategy package.initial package.policy (package.bank A) adapter
        physicalEnv base hterm package.seed schedule) :
    A.Accepts
      ((profiledRawJointUnitPolicyLeaderFreeKernel A strategy package.initial
        package.policy (package.bank A) adapter).globalMachine.globalMachineTraceWord
          (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
            package.initial package.policy
              (package.bank A) adapter).globalOutputOne
          (profiledRawJointUnitPolicyLeaderFreeKernel A strategy
            package.initial package.policy
              (package.bank A) adapter).globalOutputTwo
          physicalEnv) :=
  package.physicalTrace_accepts_of_fixedRerootInvariant A adapter physicalEnv
    base hterm schedule equations.toFixedRerootInvariant

end ProfiledRawJointSiblingFreshPolicyPackage

end

end DetParityAutomaton

end DistributedSynthesis
