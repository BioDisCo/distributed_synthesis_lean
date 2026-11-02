/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedProjectedTree
import DistributedSynthesis.Library.Automata.EncodedThreadCompiler
import DistributedSynthesis.Library.Automata.EncodedWordTree
import DistributedSynthesis.Library.Computability.FiniteFunctionCoding
import DistributedSynthesis.Library.Computability.PrimrecFunProp

/-! # Numeric rejecting-policy tables for parity tree complementation

Successor assignments and local rejecting policies are numbered using the
existing finite-function tables. Each input letter specifies the public label,
a local rejecting policy, and one direction. Invalid threads enter state zero,
an even sink; a live state carries the source priority plus one.
-/
namespace DistributedSynthesis.EncodedTreeComplement
open EncodedProjectedTree

attribute [local fun_prop] alphabetSize_primrec monitorData_primrec projection_primrec
attribute [local fun_prop] EncodedTreeNonemptiness.bound_primrec
  EncodedTreeNonemptiness.labels_primrec EncodedTreeNonemptiness.branches_primrec
  EncodedTreeNonemptiness.priorities_primrec EncodedTreeNonemptiness.initial_primrec
attribute [local fun_prop] FiniteFunctionCoding.name_primrec

@[fun_prop] theorem codes_primrec :
    Primrec (fun x : Nat × Nat => FiniteFunctionCoding.codes x.1 x.2) :=
  FiniteFunctionCoding.codes_primrec

def states (d : Data) : Nat := EncodedTreeNonemptiness.bound (monitorData d)
def branches (d : Data) : Nat := EncodedTreeNonemptiness.branches (monitorData d)
def choices (d : Data) : Nat := EncodedTreeNonemptiness.labels (monitorData d)
def vectors (d : Data) : List (List Nat) := FiniteFunctionCoding.codes (branches d) (states d)
def policies (d : Data) : List (List Nat) :=
  FiniteFunctionCoding.codes (states d * (vectors d).length) (branches d)

@[fun_prop] theorem states_primrec : Primrec states := by unfold states; fun_prop
@[fun_prop] theorem branches_primrec : Primrec branches := by unfold branches; fun_prop
@[fun_prop] theorem choices_primrec : Primrec choices := by unfold choices; fun_prop
@[fun_prop] theorem vectors_primrec : Primrec vectors := by unfold vectors; fun_prop
@[fun_prop] theorem policies_primrec : Primrec policies := by unfold policies; fun_prop

def output (d : Data) (a : Nat) : Nat := (projection d).getD a 0 % alphabetSize d

def next (d : Data) (q l b : Nat) : Nat :=
  EncodedTreeNonemptiness.rawNext (monitorData d) q l b % states d

@[fun_prop] theorem output_primrec : Primrec (fun x : Data × Nat => output x.1 x.2) := by
  unfold output; fun_prop
@[fun_prop] theorem next_primrec :
    Primrec (fun x : Data × Nat × Nat × Nat => next x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  exact Primrec.nat_mod.comp
    (EncodedTreeNonemptiness.rawNext_primrec
      (monitorData_primrec.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
    (states_primrec.comp Primrec.fst)

def legal (d : Data) (q a : Nat) (v : List Nat) : Prop :=
  ∃ l < choices d, output d l = a ∧
    (List.range (branches d)).map (fun b => next d q l b) = v
instance (d : Data) (q a : Nat) (v : List Nat) : Decidable (legal d q a v) := by
  unfold legal
  infer_instance
@[fun_prop] theorem legal_primrec :
    PrimrecPred (fun x : Data × Nat × Nat × List Nat => legal x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  unfold legal
  fun_prop

def resolve (d : Data) (q a : Nat) (p : List Nat) (b : Nat) (v : List Nat) : Nat :=
  if q = 0 then 0 else
    if legal d (q - 1) a v ∧
        p.getD ((q - 1) * (vectors d).length +
          FiniteFunctionCoding.name (branches d) (states d) v) 0 = b
    then v.getD b 0 + 1 else 0

@[fun_prop] theorem resolve_primrec :
    Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat =>
      resolve x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := by
  have hd : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.1) := Primrec.fst
  have hq : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.2.1) := by fun_prop
  have ha : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.2.2.1) := by fun_prop
  have hp : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.2.2.2.1) := by fun_prop
  have hb : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.2.2.2.2.1) := by fun_prop
  have hv : Primrec (fun x : Data × Nat × Nat × List Nat × Nat × List Nat => x.2.2.2.2.2) := by fun_prop
  have hqm := Primrec.nat_sub.comp hq (Primrec.const 1)
  have hl := legal_primrec.comp (hd.pair (hqm.pair (ha.pair hv)))
  have hi := FiniteFunctionCoding.name_primrec.comp
    (((branches_primrec.comp hd).pair (states_primrec.comp hd)).pair hv)
  have hlookup := (Primrec.list_getD 0).comp hp
    (Primrec.nat_add.comp
      (Primrec.nat_mul.comp hqm (Primrec.list_length.comp (vectors_primrec.comp hd))) hi)
  exact Primrec.ite (Primrec.eq.comp hq (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (hl.and (Primrec.eq.comp hlookup hb))
      (Primrec.succ.comp ((Primrec.list_getD 0).comp hv hb)) (Primrec.const 0))

/-- Letter indices are `(publicLabel * policyCount + policy) * branchCount + direction`. -/
def edges (d : Data) (letter : Nat) : EncodedThreadBuchi.Edges :=
  (List.range (states d + 1)).flatMap fun q => (vectors d).map fun v =>
    (q, resolve d q (letter / branches d / (policies d).length)
      ((policies d).getD (letter / branches d % (policies d).length) [])
      (letter % branches d) v)

@[fun_prop] theorem edges_primrec : Primrec (fun x : Data × Nat => edges x.1 x.2) := by
  unfold edges
  fun_prop

def priorities (d : Data) : List Nat :=
  0 :: (List.range (states d)).map
    (fun q => (EncodedTreeNonemptiness.priorities (monitorData d)).getD q 0 + 1)

@[fun_prop] theorem priorities_primrec : Primrec priorities := by
  unfold priorities
  fun_prop

/-- The existing numeric universal-thread compiler receives these tables. -/
def threadData (d : Data) : EncodedThreadBuchi.Input :=
  (states d + 1, EncodedTreeNonemptiness.initial (monitorData d) % states d + 1,
    priorities d,
    (List.range (alphabetSize d * (policies d).length * branches d)).map (edges d))

@[fun_prop] theorem threadData_primrec : Primrec threadData := by
  unfold threadData
  fun_prop

def wordAutomaton (d : Data) : EncodedParityTables.Data :=
  EncodedThreadCompiler.compile (threadData d)

@[fun_prop] theorem wordAutomaton_primrec : Primrec wordAutomaton :=
  EncodedThreadCompiler.compile_primrec.comp threadData_primrec

/-- Branchwise checking of a guessed rejecting policy, followed by projection. -/
def compile (d : Data) : Data :=
  (d.1, EncodedWordTree.compile (branches d, alphabetSize d * (policies d).length, wordAutomaton d),
    (List.range (alphabetSize d * (policies d).length)).map (fun i => i / (policies d).length))

theorem compile_primrec : Primrec compile := by
  unfold compile
  apply Primrec.pair Primrec.fst
  apply Primrec.pair
  · apply EncodedWordTree.compile_primrec.comp
    fun_prop
  · fun_prop

end DistributedSynthesis.EncodedTreeComplement
