/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSearch
import Mathlib.Data.List.ProdSigma

/-! # Numeric bad-thread Büchi tables

A state is a monitor-state number and an optional guessed recurrent priority.
The base edge relation represents existential resolution choices for one thread
letter. Guessing an odd threshold and subsequently staying above it is the
existing bad-thread construction, not a test of an infinite execution.
-/

namespace DistributedSynthesis.EncodedThreadBuchi
abbrev State := Nat × Option Nat
abbrev Edges := List (Nat × Nat)
abbrev Context := List Nat × Edges
abbrev Args := Context × State × State

def states (n : Nat) (ps : List Nat) : List State :=
  (List.range n).product (none :: ps.map some)
def step (x : Args) : Prop :=
  (x.2.1.1, x.2.2.1) ∈ x.1.2 ∧
    ((x.2.1.2 = none ∧ (x.2.2.2 = none ∨
      ∃ p ∈ x.1.1, x.2.2.2 = some p ∧ p % 2 ≠ 0 ∧ p ≤ x.1.1.getD x.2.2.1 0)) ∨
      ∃ p ∈ x.1.1, x.2.1.2 = some p ∧ x.2.2.2 = some p ∧ p ≤ x.1.1.getD x.2.2.1 0)
instance (x : Args) : Decidable (step x) := by unfold step; infer_instance
def accepting (ps : List Nat) (s : State) : Prop :=
  ∃ p ∈ ps, s.2 = some p ∧ ps.getD s.1 0 = p
instance (ps : List Nat) (s : State) : Decidable (accepting ps s) := by unfold accepting; infer_instance

theorem states_primrec : Primrec₂ states :=
  FiniteSearch.product_primrec.comp (Primrec.list_range.comp Primrec.fst)
    (Primrec.list_cons.comp (Primrec.const none)
      (Primrec.list_map Primrec.snd (Primrec.option_some.comp Primrec.snd).to₂))

theorem step_primrec : PrimrecPred step := by
  have hps : Primrec (fun x : Args => x.1.1) := Primrec.fst.comp Primrec.fst
  have hed : Primrec (fun x : Args => x.1.2) := Primrec.snd.comp Primrec.fst
  have hs : Primrec (fun x : Args => x.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun x : Args => x.2.2) := Primrec.snd.comp Primrec.snd
  have hst := Primrec.snd.comp hs
  have htt := Primrec.snd.comp ht
  have hp := (Primrec.list_getD 0).comp hps (Primrec.fst.comp ht)
  have hm : PrimrecRel (fun (xs : Edges) e => e ∈ xs) :=
    Primrec.eq.exists_mem_list.of_eq (fun _ _ => by simp)
  have htag : PrimrecPred (fun x : Args × Nat => x.1.2.2.2 = some x.2) :=
    Primrec.eq.comp (htt.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)
  have hle : PrimrecPred (fun x : Args × Nat => x.2 ≤ x.1.1.1.getD x.1.2.2.1 0) :=
    Primrec.nat_le.comp Primrec.snd (hp.comp Primrec.fst)
  have hodd : PrimrecPred (fun x : Args × Nat => x.2 % 2 ≠ 0) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 0)).not
  have hg : PrimrecRel (fun (x : Args) p => x.2.2.2 = some p ∧ p % 2 ≠ 0 ∧ p ≤ x.1.1.getD x.2.2.1 0) :=
    htag.and (hodd.and hle)
  have hk : PrimrecRel (fun (x : Args) p => x.2.1.2 = some p ∧ x.2.2.2 = some p ∧ p ≤ x.1.1.getD x.2.2.1 0) :=
    (Primrec.eq.comp (hst.comp Primrec.fst) (Primrec.option_some.comp Primrec.snd)).and (htag.and hle)
  exact (hm.comp hed ((Primrec.fst.comp hs).pair (Primrec.fst.comp ht))).and
    (((Primrec.eq.comp hst (Primrec.const none)).and
      ((Primrec.eq.comp htt (Primrec.const none)).or
        (FiniteSearch.exists_mem hps hg))).or (FiniteSearch.exists_mem hps hk))

theorem accepting_primrec : PrimrecRel accepting :=
  FiniteSearch.exists_mem Primrec.fst
    ((Primrec.eq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.option_some.comp Primrec.snd)).and
      (Primrec.eq.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd))

def edges (n : Nat) (ctx : Context) : List (State × State) :=
  ((states n ctx.1).product (states n ctx.1)).filter (fun e => decide (step (ctx, e)))
def acceptingStates (n : Nat) (ps : List Nat) : List State :=
  (states n ps).filter (fun s => decide (accepting ps s))

theorem edges_primrec : Primrec₂ edges := by
  have hh : PrimrecRel (fun (x : Nat × Context) (e : State × State) => step (x.2, e)) :=
    step_primrec.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  have hs : Primrec (fun x : Nat × Context => states x.1 x.2.1) :=
    states_primrec.comp Primrec.fst (Primrec.fst.comp Primrec.snd)
  exact hh.swap.listFilter.comp (FiniteSearch.product_primrec.comp hs hs) Primrec.id
theorem acceptingStates_primrec : Primrec₂ acceptingStates := by
  have hh : PrimrecRel (fun (x : Nat × List Nat) s => accepting x.2 s) :=
    accepting_primrec.comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  exact hh.swap.listFilter.comp states_primrec Primrec.id

abbrev Input := Nat × Nat × List Nat × List Edges
/-- Complete finite bad-thread tables, before state numbering and determinization. -/
def compile (x : Input) :=
  (states x.1 x.2.2.1, ((x.2.1, none) : State), acceptingStates x.1 x.2.2.1,
    x.2.2.2.map (fun e => edges x.1 (x.2.2.1, e)))
theorem compile_primrec : Primrec compile := by
  have hn : Primrec (fun x : Input => x.1) := Primrec.fst
  have hi : Primrec (fun x : Input => x.2.1) := Primrec.fst.comp Primrec.snd
  have hp : Primrec (fun x : Input => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have he : Primrec (fun x : Input => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact (states_primrec.comp hn hp).pair ((hi.pair (Primrec.const none)).pair
    ((acceptingStates_primrec.comp hn hp).pair
      (Primrec.list_map he (edges_primrec.comp (hn.comp Primrec.fst)
        ((hp.comp Primrec.fst).pair Primrec.snd)).to₂)))

theorem mem_edges (n : Nat) (ctx : Context) (s t : State) :
    (s, t) ∈ edges n ctx ↔ s ∈ states n ctx.1 ∧ t ∈ states n ctx.1 ∧ step (ctx, s, t) := by
  have hm : (s, t) ∈ (states n ctx.1).product (states n ctx.1) ↔
      s ∈ states n ctx.1 ∧ t ∈ states n ctx.1 := List.mem_product
  simp only [edges, List.mem_filter, hm, decide_eq_true_eq, and_assoc]

end DistributedSynthesis.EncodedThreadBuchi
