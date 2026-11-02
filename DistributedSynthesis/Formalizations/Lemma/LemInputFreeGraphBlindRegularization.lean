/-
Copyright (c) 2026 The authors listed in AUTHORS.md. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Project authors: see AUTHORS.md at the repository root.
-/

import DistributedSynthesis.Formalizations.Lemma.LemBlindLibraryParitySynthesis

/-!
# Joint blind regularization for input-free, graph-insensitive automata

An accepted word supplies a unary prescription tree. Finite parity
positionalization replaces that word by one common finite generator; both
processes advance it on every round, regardless of receipt. This proves a
restricted regularization theorem, not completeness for graph-dependent
objectives or nontrivial private inputs.
-/

namespace DistributedSynthesis.InputFreeGraphBlindRegularization

open BlindControllerLibrary DetParityAutomaton

universe x y s
variable {Out₁ : Type x} {Out₂ : Type y}
variable (A : DetParityAutomaton.{max x y,s}
  (RoundRecord Unit Unit Graph Out₁ Out₂))

def letter (o : Out₁ × Out₂) : RoundRecord Unit Unit Graph Out₁ Out₂ :=
  ⟨(), (), .both, o.1, o.2⟩

/-- A sufficient syntactic condition: graph changes do not change the DPA
transition when the current state and the output pair are held fixed. -/
def GraphInsensitive : Prop :=
  ∀ q r, A.step q r = A.step q (letter (r.outputOne, r.outputTwo))

def generatorNext (q : A.State) (o : Out₁ × Out₂) (_ : Unit) : A.State :=
  A.step q (letter o)

private theorem branch_length {D : Type*} (env : Nat → D) (n : Nat) :
    (branchNode env n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [branchNode, List.length_append, List.length_singleton, ih]

variable [Fintype Out₁] [Fintype Out₂]

/-- Joint output generation uses a finite common state, without giving a
blind process any information about the graph or the other process's input. -/
theorem exists_generator (hgraph : GraphInsensitive A)
    (word : Nat → RoundRecord Unit Unit Graph Out₁ Out₂) (hword : A.Accepts word) :
    ∃ choose : A.State → Out₁ × Out₂, ∀ env : Nat → Unit,
      NatSeqMinEvenParity (fun n ↦ A.priority
        (ParityPrescription.stateAt A.initial (generatorNext A) choose (branchNode env n))) := by
  apply ParityPrescription.exists_positional
  let tree : LabeledTree Unit (Out₁ × Out₂) :=
    fun node ↦ ((word node.length).outputOne, (word node.length).outputTwo)
  let run : List Unit → A.State := fun node ↦ A.run word node.length
  refine ⟨tree, run, ⟨?_, ?_⟩, ?_⟩
  · exact A.run_zero word
  · intro node d
    change A.run word (node ++ [d]).length =
      generatorNext A (A.run word node.length) (tree node) d
    simp only [List.length_append, List.length_singleton, A.run_succ]
    exact hgraph _ _
  · intro env
    simpa only [run, branch_length] using hword

def library (choose : A.State → Out₁ × Out₂) :
    BlindControllerLibrary Unit Unit Out₁ Out₂ where
  OneControl := A.State
  TwoControl := A.State
  initialOne := A.initial
  initialTwo := A.initial
  noRecvOne := fun q _ ↦ (generatorNext A q (choose q) (), (choose q).1)
  noRecvTwo := fun q _ ↦ (generatorNext A q (choose q) (), (choose q).2)

private def generatorState (choose : A.State → Out₁ × Out₂) : Nat → A.State
  | 0 => A.initial
  | n + 1 => generatorNext A (generatorState choose n) (choose (generatorState choose n)) ()

omit [Fintype Out₁] [Fintype Out₂] in
private theorem generatorState_eq (choose : A.State → Out₁ × Out₂)
    (env : Nat → Unit) (n : Nat) :
    generatorState A choose n =
      ParityPrescription.stateAt A.initial (generatorNext A) choose (branchNode env n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [branchNode, ParityPrescription.stateAt_append, generatorState, ih]

omit [Fintype Out₁] [Fintype Out₂] in
/-- The same generator is installed on both sides. Every graph preserves
their equality, so no independent quotient of arbitrary blind streams is used. -/
theorem library_accepting (hgraph : GraphInsensitive A)
    (choose : A.State → Out₁ × Out₂)
    (hchoose : ∀ env : Nat → Unit, NatSeqMinEvenParity (fun n ↦ A.priority
      (ParityPrescription.stateAt A.initial (generatorNext A) choose (branchNode env n)))) :
    (library A choose).HasAcceptingTree A := by
  let q := generatorState A choose
  let tree : LabeledTree (EnvironmentRound Unit Unit) (library A choose).Move :=
    fun node _ _ ↦ ((q (node.length + 1), (choose (q node.length)).1),
      (q (node.length + 1), (choose (q node.length)).2))
  let run : List (EnvironmentRound Unit Unit) → (library A choose).State A :=
    fun node ↦ ((q node.length, q node.length), q node.length)
  refine ⟨tree, run, ⟨rfl, ?_⟩, ?_⟩
  · intro node e
    have hq : q (node.length + 1) = generatorNext A (q node.length)
        (choose (q node.length)) () := rfl
    have hrecord : (library A choose).record A (run node) (tree node) e =
        ⟨(), (), e.graph, (choose (q node.length)).1, (choose (q node.length)).2⟩ := by
      cases e with
      | mk i j g => cases i; cases j; cases g <;>
          simp [record, responses, library, run, tree]
    have hdpa : A.step (q node.length)
        ((library A choose).record A (run node) (tree node) e) = q (node.length + 1) := by
      rw [hgraph, hrecord, hq]
      rfl
    change ((q (node ++ [e]).length, q (node ++ [e]).length), q (node ++ [e]).length) = _
    unfold BlindControllerLibrary.next
    change _ = (_, A.step (q node.length) ((library A choose).record A (run node) (tree node) e))
    rw [hdpa]
    cases hg : e.graph <;>
      simp [responses, hg, run, tree, library, hq]
  · intro env
    have hp := hchoose (fun _ ↦ ())
    simpa only [run, branch_length, ← generatorState_eq] using hp

/-- In this restricted class, nonempty language already yields a finite
blind library with an accepting tree. Each blind control set is `A.State`. -/
theorem finite_library_of_accepted_word (hgraph : GraphInsensitive A)
    (word : Nat → RoundRecord Unit Unit Graph Out₁ Out₂) (hword : A.Accepts word) :
    ∃ choose : A.State → Out₁ × Out₂, (library A choose).HasAcceptingTree A := by
  obtain ⟨choose, hchoose⟩ := exists_generator A hgraph word hword
  exact ⟨choose, library_accepting A hgraph choose hchoose⟩

variable [Inhabited Out₁] [Inhabited Out₂]

theorem finite_winner_of_accepted_word (hgraph : GraphInsensitive A)
    (word : Nat → RoundRecord Unit Unit Graph Out₁ Out₂) (hword : A.Accepts word) :
    ∃ C : FinitePairedPhysicalController.{0,0,x,y,max s x,max s y}
      Unit Unit Out₁ Out₂, ∀ env,
      A.Accepts (C.globalMachine.globalMachineTraceWord C.globalOutputOne C.globalOutputTwo env) := by
  obtain ⟨choose, hchoose⟩ := finite_library_of_accepted_word A hgraph word hword
  letI : Fintype (library A choose).OneControl := A.stateFinite
  letI : Fintype (library A choose).TwoControl := A.stateFinite
  exact (library A choose).exists_winning_physical_controller A hchoose

end DistributedSynthesis.InputFreeGraphBlindRegularization
