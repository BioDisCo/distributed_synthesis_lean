/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Distributed.EncodedChainMonitorCorrect
import DistributedSynthesis.Library.Distributed.EncodedOrdinaryCompiler
import DistributedSynthesis.Library.Distributed.EncodedThreadCompiler

/-! # Complete numeric set-started chain checker tables -/
namespace DistributedSynthesis.EncodedChainCompiler
open EncodedRoundObjectives EncodedChainThreads EncodedChainMonitor

def branches (d : Data) : List (Bool × Nat) :=
  (List.range (inputTwo d)).map (false,·) ++ (List.range (inputOne d)).map (true,·)
@[irreducible] def alphabet (d : Data) : List EncodedChainMonitor.Letter :=
  [false,true].flatMap (fun mode => (EncodedOrdinaryCompiler.labels d).flatMap
    (fun c => (branches d).map (fun b => (mode,b.1,c,b.2))))
def rows (x : Input) := (alphabet x.1).map (fun a => edges (x,a))
def threadInput (x : Input) : EncodedThreadBuchi.Input :=
  (EncodedChainMonitor.stateCount x.1,0,priorities x.1,rows x)
def compile (x : Input) := EncodedThreadCompiler.compile (threadInput x)

theorem branches_primrec : Primrec branches :=
  Primrec.list_append.comp
    (Primrec.list_map (Primrec.list_range.comp inputTwo_primrec) ((Primrec.const false).pair Primrec.snd).to₂)
    (Primrec.list_map (Primrec.list_range.comp inputOne_primrec) ((Primrec.const true).pair Primrec.snd).to₂)
theorem alphabet_primrec : Primrec alphabet := by
  unfold alphabet
  have hd : Primrec (fun y : ((Data × Bool) × EncodedJournalLabels.Code) × (Bool × Nat) => y.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have hf : Primrec (fun y : ((Data × Bool) × EncodedJournalLabels.Code) × (Bool × Nat) =>
      (y.1.1.2,y.2.1,y.1.2,y.2.2)) :=
    (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair
      ((Primrec.fst.comp Primrec.snd).pair ((Primrec.snd.comp Primrec.fst).pair (Primrec.snd.comp Primrec.snd)))
  exact Primrec.list_flatMap (Primrec.const [false,true])
    (Primrec.list_flatMap (EncodedOrdinaryCompiler.labels_primrec.comp Primrec.fst)
      (Primrec.list_map (branches_primrec.comp (Primrec.fst.comp Primrec.fst)) hf.to₂).to₂).to₂
theorem rows_primrec : Primrec rows := by
  unfold rows
  exact Primrec.list_map (alphabet_primrec.comp Primrec.fst) edges_primrec
theorem threadInput_primrec : Primrec threadInput :=
  (EncodedChainMonitor.stateCount_primrec.comp Primrec.fst).pair
    ((Primrec.const 0).pair ((priorities_primrec.comp Primrec.fst).pair rows_primrec))
theorem compile_primrec : Primrec compile := EncodedThreadCompiler.compile_primrec.comp threadInput_primrec

theorem mem_alphabet (d : Data) (a : EncodedChainMonitor.Letter) : a ∈ alphabet d ↔
    a.2.2.1 ∈ EncodedOrdinaryCompiler.labels d ∧
      (bif a.2.1 then a.2.2.2 < inputOne d else a.2.2.2 < inputTwo d) := by
  rcases a with ⟨mode,side,c,i⟩
  cases mode <;> cases side <;> simp [alphabet,branches,Prod.mk.injEq]

def decodeBranch (d : Data) (a : EncodedChainMonitor.Letter) : Fin (inputTwo d) ⊕ Fin (inputOne d) :=
  bif a.2.1 then Sum.inr ⟨a.2.2.2 % inputOne d,Nat.mod_lt _ (Nat.succ_pos _)⟩
  else Sum.inl ⟨a.2.2.2 % inputTwo d,Nat.mod_lt _ (Nat.succ_pos _)⟩
theorem context_decode (x : Input) (a : EncodedChainMonitor.Letter) (ha : a ∈ alphabet x.1) :
    context x.1 x.2 a.1 a.2.2.1 (decodeBranch x.1 a) = (x,a) := by
  have hi := ((mem_alphabet x.1 a).mp ha).2
  rcases x with ⟨d,T⟩
  rcases a with ⟨mode,side,c,i⟩
  cases side <;> dsimp only [Bool.cond_false,Bool.cond_true] at hi <;>
    simp only [context,decodeBranch,EncodedChainMonitor.side,sender,Bool.cond_true,Bool.cond_false,Nat.mod_eq_of_lt hi]

@[irreducible] def rowLetter (x : Input) (a : Fin (rows x).length) : EncodedChainMonitor.Letter :=
  (alphabet x.1)[a.val]'(by simpa only [rows,List.length_map] using a.isLt)
theorem rowLetter_mem (x : Input) (a : Fin (rows x).length) : rowLetter x a ∈ alphabet x.1 := by
  unfold rowLetter
  exact List.getElem_mem _
theorem row_get (x : Input) (a : Fin (rows x).length) :
    (rows x)[a.val]?.getD [] = edges (x,rowLetter x a) := by
  simp only [rows,List.getElem?_map,rowLetter]
  rw [List.getElem?_eq_getElem (by simpa only [rows,List.length_map] using a.isLt),Option.map_some,Option.getD_some]
end DistributedSynthesis.EncodedChainCompiler
