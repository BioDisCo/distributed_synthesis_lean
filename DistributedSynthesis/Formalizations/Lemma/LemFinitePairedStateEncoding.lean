/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFinitePairedMealyReceiptMemory

/-!
# Finite distributed encoding of an arbitrary finite state

Each endpoint keeps a tag in `Bool × Bool` and four state values. The joint
decoder uses one endpoint's table, indexed by the other's tag. Given any
three requested successors, two receive updates realize the strict-left,
strict-right, and simultaneous successors, while blind updates do nothing.
Neither receive update is given the actual graph.
-/

namespace DistributedSynthesis
namespace FinitePairedStateEncoding

universe s
abbrev Tag := Bool × Bool
abbrev Control (State : Type s) := Tag × (Tag → State)

variable {State : Type s}

/-- A proof-side decoder, also available on receive from the delivered pair.
It is not available to a blind endpoint. -/
def decode (one two : Control State) : State :=
  if one.1.1 = two.1.1 then one.2 two.1 else two.2 one.1

def initial (state : State) : Control State := ((false, false), fun _ ↦ state)

@[simp] theorem decode_initial (state : State) :
    decode (initial state) (initial state) = state := rfl

/-- New row tag matches the old column's first bit but differs from the
old row tag. The new column tag is constructed dually. -/
def nextOneTag (one two : Tag) : Tag := (two.1, !one.2)
def nextTwoTag (one two : Tag) : Tag := (!one.1, !two.2)

theorem nextOneTag_ne (one two : Tag) : nextOneTag one two ≠ one := by
  rcases one with ⟨a,b⟩
  rcases two with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

theorem nextTwoTag_ne (one two : Tag) : nextTwoTag one two ≠ two := by
  rcases one with ⟨a,b⟩
  rcases two with ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> decide

def receiveOne (one two : Control State) (left both : State) : Control State :=
  (nextOneTag one.1 two.1, fun tag ↦ if tag = two.1 then left else both)

def receiveTwo (one two : Control State) (right both : State) : Control State :=
  (nextTwoTag one.1 two.1, fun tag ↦ if tag = one.1 then right else both)

theorem decode_left (one two : Control State) (left both : State) :
    decode (receiveOne one two left both) two = left := by
  simp [decode, receiveOne, nextOneTag]

theorem decode_right (one two : Control State) (right both : State) :
    decode one (receiveTwo one two right both) = right := by
  cases h : one.1.1 <;> simp [decode, receiveTwo, nextTwoTag, h]

theorem decode_both (one two : Control State) (left right both : State) :
    decode (receiveOne one two left both) (receiveTwo one two right both) = both := by
  unfold decode receiveOne receiveTwo
  dsimp only
  split <;> simp [nextOneTag_ne, nextTwoTag_ne]

/-- All three equations hold for the same two receive updates. This is the
essential compatibility law, not three graph-dependent local choices. -/
theorem three_successors (one two : Control State) (left right both : State) :
    let one' := receiveOne one two left both
    let two' := receiveTwo one two right both
    decode one' two = left ∧ decode one two' = right ∧ decode one' two' = both :=
  ⟨decode_left one two left both, decode_right one two right both,
    decode_both one two left right both⟩

theorem card_control [Fintype State] :
    Fintype.card (Control State) = 4 * Fintype.card State ^ 4 := by
  simp [Control, Tag, Fintype.card_prod, Fintype.card_fun]

universe u v
variable {In₁ : Type u} {In₂ : Type v}

/-- An arbitrary finite global transition system can be monitored by genuine
finite local maps. Its state is jointly decodable, not locally observable. -/
def monitor (G : FiniteGlobalRoundMachine In₁ In₂) :
    FinitePairedMealyController In₁ In₂ Unit Unit where
  OneControl := Control G.State
  TwoControl := Control G.State
  oneFinite := inferInstance
  twoFinite := inferInstance
  initialOne := initial G.initial
  initialTwo := initial G.initial
  noRecvOne := fun one _ ↦ (one, ())
  noRecvTwo := fun two _ ↦ (two, ())
  recvOne := fun one i two j ↦
    (receiveOne one two (G.step (decode one two) ⟨i,j,.left⟩)
      (G.step (decode one two) ⟨i,j,.both⟩), ())
  recvTwo := fun two j one i ↦
    (receiveTwo one two (G.step (decode one two) ⟨i,j,.right⟩)
      (G.step (decode one two) ⟨i,j,.both⟩), ())

theorem monitor_step (G : FiniteGlobalRoundMachine In₁ In₂)
    (s : (monitor G).OneControl × (monitor G).TwoControl)
    (e : EnvironmentRound In₁ In₂) :
    let t := (monitor G).semanticAdvanceControls s e
    decode t.1 t.2 = G.step (decode s.1 s.2) e := by
  rcases e with ⟨i,j,g⟩
  cases g <;> simp [FinitePairedMealyController.semanticAdvanceControls,
    monitor, decode_left, decode_right, decode_both]

theorem monitor_trace (G : FiniteGlobalRoundMachine In₁ In₂)
    (env : EnvironmentSequence In₁ In₂) (n : Nat) :
    let s := (monitor G).semanticControlTrace env n
    decode s.1 s.2 = G.globalStateTrace env n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [FinitePairedMealyController.semanticControlTrace]
    rw [monitor_step, ih]
    rfl

end FinitePairedStateEncoding
end DistributedSynthesis
