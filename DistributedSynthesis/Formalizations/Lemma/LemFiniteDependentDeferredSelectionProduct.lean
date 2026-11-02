/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemFiniteAcknowledgedExactClosingDependentBank

/-!
# A finite product bank before a dependent key is delivered

Suppose one endpoint does not yet know the finite key of a controller fibre,
while its informed partner already does.  The blind endpoint can retain the
dependent product of *all* its candidate controls and advance every component
from its own input.  The informed endpoint retains one dependent sigma and,
on every receive, evaluates the delivered product at its stored key.

This module proves the arbitrary-prefix selection fact for that construction.
It deliberately does not manufacture a physical blind output.  A local blind
transition has only one output, whereas the product contains one candidate
output per key.  `BlindOutputCoherentAt` is the exact additional premise under
which any fixed projection is the selected fibre's physical output.

Likewise, semantic correctness is parameterized by a selected-fibre relation.
The arbitrary-prefix theorem reduces its preservation to one honest local
step.  Thus neither a reset to the canonical fibre root nor an unproved
cross-output equality can be hidden in this adapter.

No operation receives a graph, orientation, hierarchy side, leader bit,
history, or view.  The sigma key is stored finite control at the informed
endpoint; it is not available to the blind endpoint.
-/

namespace DistributedSynthesis

universe k b i xb xi yb yi

namespace FiniteAcknowledgedDelayedCarrier

/-- Finite dependent local transitions for a blind product and one selected
informed fibre.  The informed transition may inspect the delivered blind
product at its own stored key, exactly as an ordinary receive handler may
inspect the delivered partner control. -/
structure FiniteDependentDeferredSelectionFamily
    (Key : Type k) (BlindInput : Type xb) (InformedInput : Type xi)
    (BlindOutput : Type yb) (InformedOutput : Type yi) where
  Blind : Key → Type b
  Informed : Key → Type i
  blindFinite : ∀ key, Fintype (Blind key)
  informedFinite : ∀ key, Fintype (Informed key)
  blindStep : ∀ key,
    Blind key → BlindInput → Blind key × BlindOutput
  informedStep : ∀ key,
    Informed key → InformedInput → Blind key → BlindInput →
      Informed key × InformedOutput

namespace FiniteDependentDeferredSelectionFamily

variable {Key : Type k} {BlindInput : Type xb} {InformedInput : Type xi}
variable {BlindOutput : Type yb} {InformedOutput : Type yi}

variable
  (family : FiniteDependentDeferredSelectionFamily Key BlindInput
    InformedInput BlindOutput InformedOutput)

/-- Blind control containing one current value in every finite dependent
fibre. -/
abbrev BlindBank := ∀ key : Key, family.Blind key

/-- The informed endpoint's one selected dependent fibre. -/
abbrev SelectedInformed := Σ key : Key, family.Informed key

/-- Joint proof-side state.  Its two projections remain executable local
states: the first transition uses only a blind input; the second uses its own
input and the delivered blind bank/input. -/
abbrev DeferredSelectionState := family.BlindBank × family.SelectedInformed

noncomputable instance blindBankFintype [Fintype Key] :
    Fintype family.BlindBank := by
  classical
  letI (key : Key) : Fintype (family.Blind key) := family.blindFinite key
  infer_instance

noncomputable instance selectedInformedFintype [Fintype Key] :
    Fintype family.SelectedInformed := by
  classical
  letI (key : Key) : Fintype (family.Informed key) := family.informedFinite key
  infer_instance

noncomputable instance deferredSelectionStateFintype [Fintype Key] :
    Fintype family.DeferredSelectionState := by
  classical infer_instance

/-- Evaluate the blind product at the key stored by the informed endpoint. -/
def selectedBlind (bank : family.BlindBank)
    (selected : family.SelectedInformed) : family.Blind selected.1 :=
  bank selected.1

/-- Pointwise blind state advance.  Candidate outputs are retained only as
proof-side projections below. -/
def blindAdvance (bank : family.BlindBank) (input : BlindInput) :
    family.BlindBank :=
  fun key ↦ (family.blindStep key (bank key) input).1

/-- Output proposed by one candidate fibre. -/
def blindCandidateOutput (bank : family.BlindBank) (key : Key)
    (input : BlindInput) : BlindOutput :=
  (family.blindStep key (bank key) input).2

/-- Exact condition under which the blind product has one physically usable
output at this local state and input. -/
def BlindOutputCoherentAt (bank : family.BlindBank)
    (input : BlindInput) : Prop :=
  ∀ left right : Key,
    family.blindCandidateOutput bank left input =
      family.blindCandidateOutput bank right input

/-- A total local blind transition, projected at any fixed construction-time
key.  Its state evolution is independent of that projection. -/
def blindNoRecv (outputKey : Key) (bank : family.BlindBank)
    (input : BlindInput) : family.BlindBank × BlindOutput :=
  (family.blindAdvance bank input,
    family.blindCandidateOutput bank outputKey input)

/-- Under output coherence, the fixed local projection is exactly the output
of the fibre selected at the informed endpoint. -/
theorem blindNoRecv_output_eq_selected
    (outputKey : Key) (bank : family.BlindBank)
    (selected : family.SelectedInformed) (input : BlindInput)
    (hcoherent : family.BlindOutputCoherentAt bank input) :
    (family.blindNoRecv outputKey bank input).2 =
      (family.blindStep selected.1 (bank selected.1) input).2 := by
  exact hcoherent outputKey selected.1

/-- The informed receive dispatches to its stored key in the delivered blind
product and preserves that key. -/
def informedRecv (selected : family.SelectedInformed)
    (ownInput : InformedInput) (deliveredBank : family.BlindBank)
    (deliveredInput : BlindInput) :
    family.SelectedInformed × InformedOutput :=
  ⟨⟨selected.1,
      (family.informedStep selected.1 selected.2 ownInput
        (deliveredBank selected.1) deliveredInput).1⟩,
    (family.informedStep selected.1 selected.2 ownInput
      (deliveredBank selected.1) deliveredInput).2⟩

@[simp] theorem informedRecv_key
    (selected : family.SelectedInformed) (ownInput : InformedInput)
    (deliveredBank : family.BlindBank) (deliveredInput : BlindInput) :
    (family.informedRecv selected ownInput deliveredBank deliveredInput).1.1 =
      selected.1 :=
  rfl

/-- One homogeneous round, written proof-side as the product of its two local
transitions. -/
def step (state : family.DeferredSelectionState)
    (input : BlindInput × InformedInput) : family.DeferredSelectionState :=
  (family.blindAdvance state.1 input.1,
    (family.informedRecv state.2 input.2 state.1 input.1).1)

/-- Iterate an arbitrary finite homogeneous prefix. -/
def run (state : family.DeferredSelectionState)
    (inputs : List (BlindInput × InformedInput)) :
    family.DeferredSelectionState :=
  inputs.foldl family.step state

/-- A proof-side relation only at the fibre named by the informed sigma. -/
def SelectedRel
    (Rel : ∀ key, family.Blind key → family.Informed key → Prop)
    (state : family.DeferredSelectionState) : Prop :=
  Rel state.2.1 (state.1 state.2.1) state.2.2

/-- One honest homogeneous round preserves the selected relation precisely
when the corresponding member transition does. -/
theorem selectedRel_step
    (Rel : ∀ key, family.Blind key → family.Informed key → Prop)
    (hstep : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        Rel key
          (family.blindStep key blind blindInput).1
          (family.informedStep key informed informedInput blind blindInput).1)
    (state : family.DeferredSelectionState)
    (input : BlindInput × InformedInput)
    (hrel : family.SelectedRel Rel state) :
    family.SelectedRel Rel (family.step state input) := by
  rcases state with ⟨bank, ⟨key, informed⟩⟩
  exact hstep key (bank key) informed input.1 input.2 hrel

/-- Fail-fast arbitrary-prefix theorem.  No new condition appears at greater
depth: the pointwise one-round preservation law is both the induction socket
and the only semantic premise used by the product adapter. -/
theorem selectedRel_run
    (Rel : ∀ key, family.Blind key → family.Informed key → Prop)
    (hstep : ∀ key blind informed blindInput informedInput,
      Rel key blind informed →
        Rel key
          (family.blindStep key blind blindInput).1
          (family.informedStep key informed informedInput blind blindInput).1)
    (state : family.DeferredSelectionState)
    (inputs : List (BlindInput × InformedInput))
    (hrel : family.SelectedRel Rel state) :
    family.SelectedRel Rel (family.run state inputs) := by
  induction inputs generalizing state with
  | nil => exact hrel
  | cons input inputs ih =>
      exact ih (family.step state input)
        (family.selectedRel_step Rel hstep state input hrel)

@[simp] theorem run_nil (state : family.DeferredSelectionState) :
    family.run state [] = state :=
  rfl

@[simp] theorem run_cons (state : family.DeferredSelectionState)
    (input : BlindInput × InformedInput)
    (inputs : List (BlindInput × InformedInput)) :
    family.run state (input :: inputs) =
      family.run (family.step state input) inputs :=
  rfl

end FiniteDependentDeferredSelectionFamily

/-! ## Exact-closing families supply the two oriented transition systems -/

namespace FiniteExactClosingFamily

variable {Key : Type k}
variable {In₁ : Type xb} {In₂ : Type xi}
variable {Out₁ : Type yb} {Out₂ : Type yi}

variable
  (family : FiniteExactClosingFamily (In₁ := In₁) (In₂ := In₂)
    (Out₁ := Out₁) (Out₂ := Out₂) Key)

/-- Process one is blind and advances all fibres; process two stores one key
and dispatches its receives through the delivered product. -/
def strictRightDeferredSelection :
    FiniteDependentDeferredSelectionFamily Key In₁ In₂ Out₁ Out₂ where
  Blind := family.ControlOne
  Informed := family.ControlTwo
  blindFinite := family.oneFinite
  informedFinite := family.twoFinite
  blindStep := family.noRecvOne
  informedStep key two inputTwo one inputOne :=
    family.openRecvTwo key two inputTwo one inputOne

/-- Strict-left mirror. -/
def strictLeftDeferredSelection :
    FiniteDependentDeferredSelectionFamily Key In₂ In₁ Out₂ Out₁ where
  Blind := family.ControlTwo
  Informed := family.ControlOne
  blindFinite := family.twoFinite
  informedFinite := family.oneFinite
  blindStep := family.noRecvTwo
  informedStep key one inputOne two inputTwo :=
    family.openRecvOne key one inputOne two inputTwo

/-- The exact-closing relation survives an arbitrary strict-right prefix in
the selected fibre. -/
theorem strictRightDeferredSelection_rel_run
    (state : (family.strictRightDeferredSelection).DeferredSelectionState)
    (inputs : List (In₁ × In₂))
    (hrel : (family.strictRightDeferredSelection).SelectedRel family.Rel
      state) :
    (family.strictRightDeferredSelection).SelectedRel family.Rel
      ((family.strictRightDeferredSelection).run state inputs) := by
  apply (family.strictRightDeferredSelection).selectedRel_run family.Rel
  · intro key one two inputOne inputTwo hmember
    exact (family.laws key).strictRight one inputOne two inputTwo hmember
  · exact hrel

/-- Strict-left mirror. -/
theorem strictLeftDeferredSelection_rel_run
    (state : (family.strictLeftDeferredSelection).DeferredSelectionState)
    (inputs : List (In₂ × In₁))
    (hrel : (family.strictLeftDeferredSelection).SelectedRel
      (fun key two one ↦ family.Rel key one two) state) :
    (family.strictLeftDeferredSelection).SelectedRel
      (fun key two one ↦ family.Rel key one two)
      ((family.strictLeftDeferredSelection).run state inputs) := by
  apply (family.strictLeftDeferredSelection).selectedRel_run
    (fun key two one ↦ family.Rel key one two)
  · intro key two one inputTwo inputOne hmember
    exact (family.laws key).strictLeft one inputOne two inputTwo hmember
  · exact hrel

end FiniteExactClosingFamily

end FiniteAcknowledgedDelayedCarrier

end DistributedSynthesis
