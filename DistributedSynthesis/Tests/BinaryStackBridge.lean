/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.CounterMachines.MathlibBridge.BinaryUniversalStackMachine

/-! Public clients and executable regressions for the complete alphabet compiler.
These tests import no BSM/MM2 source model or source-undecidability premise. -/
namespace DistributedSynthesis.Tests.BinaryStackBridge
open CounterMachine.MathlibBridge Turing Turing.PartrecToTM2

example : Primrec BinaryUniversal.inputWord := BinaryUniversal.inputWord_primrec
example : (fun p : Nat.Partrec.Code => (p.eval 0).Dom) ≤₀
    BinaryUniversal.WordHalts universalCode := BinaryUniversal.halting_manyOneReducible
example : ¬ ComputablePred (BinaryUniversal.WordHalts universalCode) :=
  BinaryUniversal.wordHalting_not_computable
example : Fintype.card (BinaryStacks.Store (Option Γ')) = 15 :=
  BinaryUniversal.fifteen_store_values

#guard BinaryUniversal.encodeWord [] == []
#guard BinaryUniversal.encodeWord [0,1,2,3] ==
  [false,false,false,true,true,false,true,true]

def sourceStacks (l : List Γ') : Fin 2 → List Γ' :=
  fun k => if k = 0 then l else [Γ'.consₗ,Γ'.bit1]

def peekStmt : BinaryStacks.SourceStmt (K := Fin 2) (Γ := Γ') (Λ := Unit) (σ := Option Γ') :=
  .peek 0 (fun _ a => a) .halt

def popStmt : BinaryStacks.SourceStmt (K := Fin 2) (Γ := Γ') (Λ := Unit) (σ := Option Γ') :=
  .pop 0 (fun _ a => a) .halt

def pushStmt : BinaryStacks.SourceStmt (K := Fin 2) (Γ := Γ') (Λ := Unit) (σ := Option Γ') :=
  .push 0 (fun _ => Γ'.cons) .halt

def execute (q : BinaryStacks.SourceStmt (K := Fin 2) (Γ := Γ') (Λ := Unit) (σ := Option Γ'))
    (l : List Γ') :=
  TM2.stepAux (BinaryStacks.stmt BinaryUniversal.codec q) (none,none)
    (BinaryStacks.stacks BinaryUniversal.codec (sourceStacks l))

-- Empty peek must not push a default false bit onto the stack.
#guard (execute peekStmt []).var == (none,none)
#guard (execute peekStmt []).stk 0 == []
-- Both first-bit branches restore the complete word and clear the scratch bit.
#guard (execute peekStmt [Γ'.cons,Γ'.bit0]).var == (some Γ'.cons,none)
#guard (execute peekStmt [Γ'.cons,Γ'.bit0]).stk 0 == [false,true,true,false]
#guard (execute peekStmt [Γ'.bit1,Γ'.cons]).var == (some Γ'.bit1,none)
#guard (execute peekStmt [Γ'.bit1,Γ'.cons]).stk 0 == [true,true,false,true]
#guard (execute peekStmt [Γ'.bit1,Γ'.cons]).stk 1 == [false,false,true,true]
#guard (execute peekStmt [Γ'.bit0]).l == none
-- Pop removes exactly two bits, and push places the first bit at the top.
#guard (execute popStmt []).var == (none,none)
#guard (execute popStmt []).stk 0 == []
#guard (execute popStmt [Γ'.bit1,Γ'.cons]).var == (some Γ'.bit1,none)
#guard (execute popStmt [Γ'.bit1,Γ'.cons]).stk 0 == [false,true]
#guard (execute pushStmt [Γ'.bit0]).stk 0 == [false,true,true,false]

example (p : Nat.Partrec.Code) :
    BinaryUniversal.WordHalts universalCode (BinaryUniversal.inputWord p) ↔ (p.eval 0).Dom :=
  BinaryUniversal.inputWord_correct p

end DistributedSynthesis.Tests.BinaryStackBridge
