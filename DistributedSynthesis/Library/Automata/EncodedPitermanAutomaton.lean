/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Automata.EncodedPitermanStep

/-! # Finite numeric Piterman automata

Index zero is an absorbing rejecting sink. Positive indices enumerate all raw
tree codes, without an invariant filter. The language proof embeds the existing
well-formed automaton and proves that its image is closed under transitions.
Thus no behavior of an unreachable malformed tree is used in the proof.
-/

namespace DistributedSynthesis.EncodedPitermanAutomaton
open EncodedPitermanStates
set_option synthInstance.maxSize 1024
local instance : BEq Code := instBEqOfDecidableEq

def size (n : Nat) : Nat := (allCodes n).length + 1
def locate (n : Nat) (c : Option Code) : Nat :=
  (c.map (fun c => (allCodes n).idxOf c + 1)).getD 0 % size n
def retrieve (n q : Nat) : Option Code :=
  if q = 0 then none else (allCodes n)[q - 1]?
def initialCode (n initial : Nat) : Code :=
  ((List.range (2*n)).map (fun q => if q = 0 then 1 else 0),
   (List.range (2*n)).map (fun q => if q = 0 then 0 else n),
   (List.range (2*n)).map (fun _ => 0),
   (List.range (2*n)).map (fun q => if q = 0 then FiniteSubsets.normalize n [initial] else []), n, 0)
def treePriority (c : Code) : Nat :=
  if c.2.2.2.2.2 < c.2.2.2.2.1 then 2*c.2.2.2.2.2
  else if c.2.2.2.2.1 = 0 then 1 else 2*(c.2.2.2.2.1-1)+1
def priority (n q : Nat) : Nat := ((retrieve n q).map treePriority).getD 1
abbrev Context := Nat × EncodedPitermanTransition.Edges × List Nat
def next (x : Context) (q : Nat) : Nat :=
  locate x.1 ((retrieve x.1 q).bind (fun c =>
    EncodedPitermanStep.step (x.1, x.2.1, x.2.2, c)))

theorem size_primrec : Primrec size := Primrec.succ.comp (Primrec.list_length.comp allCodes_primrec)
theorem locate_primrec : Primrec₂ locate :=
  Primrec.nat_mod.comp (Primrec.option_getD.comp
    (Primrec.option_map Primrec.snd
      (Primrec.succ.comp (Primrec.list_idxOf.comp Primrec.snd
        (allCodes_primrec.comp (Primrec.fst.comp Primrec.fst)))).to₂) (Primrec.const 0))
    (size_primrec.comp Primrec.fst)
theorem retrieve_primrec : Primrec₂ retrieve :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const none)
    (Primrec.list_getElem?.comp (allCodes_primrec.comp Primrec.fst)
      (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
theorem initialCode_primrec : Primrec₂ initialCode := by
  have hn : Primrec (fun x : Nat × Nat => 2*x.1) := Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst
  have hz : PrimrecRel (fun (_ : Nat × Nat) q => q = 0) := Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hl : Primrec (fun x : Nat × Nat => FiniteSubsets.normalize x.1 [x.2]) :=
    FiniteSubsets.normalize_primrec.comp Primrec.fst (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
  exact (Primrec.list_map (Primrec.list_range.comp hn) (Primrec.ite hz (Primrec.const 1) (Primrec.const 0)).to₂).pair
    ((Primrec.list_map (Primrec.list_range.comp hn)
      (Primrec.ite hz (Primrec.const 0) (Primrec.fst.comp Primrec.fst)).to₂).pair
      ((Primrec.list_map (Primrec.list_range.comp hn) (Primrec.const 0).to₂).pair
        ((Primrec.list_map (Primrec.list_range.comp hn)
          (Primrec.ite hz (hl.comp Primrec.fst) (Primrec.const [])).to₂).pair
          (Primrec.fst.pair (Primrec.const 0)))))
theorem treePriority_primrec : Primrec treePriority := by
  have he : Primrec (fun c : Code => c.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hf : Primrec (fun c : Code => c.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  exact Primrec.ite (Primrec.nat_lt.comp hf he) (Primrec.nat_mul.comp (Primrec.const 2) hf)
    (Primrec.ite (Primrec.eq.comp he (Primrec.const 0)) (Primrec.const 1)
      (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_sub.comp he (Primrec.const 1)))))
theorem priority_primrec : Primrec₂ priority :=
  Primrec.option_getD.comp
    (Primrec.option_map retrieve_primrec (treePriority_primrec.comp Primrec.snd).to₂) (Primrec.const 1)
theorem next_primrec : Primrec₂ next := by
  have hn : Primrec (fun x : Context × Nat => x.1.1) := Primrec.fst.comp Primrec.fst
  have hx : Primrec (fun y : (Context × Nat) × Code =>
      (y.1.1.1, y.1.1.2.1, y.1.1.2.2, y.2)) :=
    (hn.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
        ((Primrec.snd.comp (Primrec.snd.comp
          (Primrec.fst.comp Primrec.fst))).pair Primrec.snd))
  have hs := EncodedPitermanStep.step_primrec.comp hx
  exact locate_primrec.comp hn
    (Primrec.option_bind (retrieve_primrec.comp hn Primrec.snd)
      hs.to₂)

theorem locate_lt (n : Nat) (c : Option Code) : locate n c < size n := Nat.mod_lt _ (Nat.succ_pos _)
@[simp] theorem locate_none (n : Nat) : locate n none = 0 := by simp [locate]
@[simp] theorem retrieve_zero (n : Nat) : retrieve n 0 = none := by simp [retrieve]
theorem retrieve_locate (n : Nat) (c : Code) (hc : c ∈ allCodes n) :
    retrieve n (locate n (some c)) = some c := by
  have hlt := List.idxOf_lt_length_of_mem hc
  have hb : (allCodes n).idxOf c + 1 < size n := by unfold size; omega
  simp only [locate, Option.map_some, Option.getD_some, Nat.mod_eq_of_lt hb]
  simp [retrieve, List.getElem?_eq_getElem hlt]

open NondetBuchiAutomaton.Piterman
variable {L : Type*} (A : NondetBuchiAutomaton L) [DecidableEq A.State]
  (number : A.State ≃ Fin (Fintype.card A.State))

theorem initialCode_encode :
    initialCode (Fintype.card A.State) (number A.initial).val =
      encode A number (CompactTreeData.initial A) := by
  have hl : FiniteSubsets.normalize (Fintype.card A.State) [(number A.initial).val] =
      encodeLabel A number {A.initial} := by
    unfold FiniteSubsets.normalize
    apply filter_range_eq_encodeLabel
    intro q
    simp only [List.mem_singleton, decide_eq_true_eq, Finset.mem_singleton]
    exact Fin.val_injective.eq_iff.trans number.injective.eq_iff
  unfold initialCode encode
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext rfl rfl))))
  all_goals apply FiniteSearch.tabulate_eq_ofFn (n := 2 * Fintype.card A.State)
  · intro q
    simp [CompactTreeData.initial, root, Fin.ext_iff]
    split <;> simp_all
  · intro q
    simp [CompactTreeData.initial, root, Fin.ext_iff]
    split <;> rfl
  · intro q
    rfl
  · intro q
    by_cases hq : q = root A
    · subst q
      simpa [CompactTreeData.initial, root] using hl
    · have hn : q.val ≠ 0 := by simpa [root, Fin.ext_iff] using hq
      simp [CompactTreeData.initial, hq, hn, encodeLabel, FiniteSubsets.encode]

omit [DecidableEq A.State] in
theorem treePriority_encode (tree : CompactTreeData A) :
    treePriority (encode A number tree) = CompactTreeData.priority A tree := by
  simp only [treePriority, encode, CompactTreeData.priority]
  by_cases h : tree.f.val < tree.e.val
  · simp [h]
  · simp only [if_neg h]
    cases tree.e.val <;> rfl

/-- All raw codes remain in the carrier; only the image of live semantic states
is needed for language correctness. -/
def automaton (initial : Nat) (edges : L → EncodedPitermanTransition.Edges) (acc : List Nat)
    (n : Nat) : DetParityAutomaton L where
  State := Fin (size n)
  stateFinite := inferInstance
  initial := ⟨locate n (some (initialCode n initial)), locate_lt _ _⟩
  step q letter := ⟨next (n, edges letter, acc) q.val, locate_lt _ _⟩
  priority q := priority n q.val

def embed (state : CompactTreeData.DPWState A) : Fin (size (Fintype.card A.State)) :=
  ⟨locate (Fintype.card A.State) (state.map (fun t => encode A number t.val)), locate_lt _ _⟩

variable (decStep : ∀ q a r, Decidable (A.step q a r)) (decAccept : DecidablePred A.accepting)
  (edges : L → EncodedPitermanTransition.Edges) (acc : List Nat)
  (he : ∀ q a r, ((number q).val, (number r).val) ∈ edges a ↔ A.step q a r)
  (ha : ∀ q, (number q).val ∈ acc ↔ A.accepting q)
local notation "D" => automaton (Fin.val (number A.initial)) edges acc (Fintype.card A.State)
local notation "S" => Computable.automatonData A decStep decAccept

theorem embed_initial : embed A number (S).initial = (D).initial := by
  apply Fin.ext
  simp only [embed, Computable.automatonData, Option.map_some, automaton, initialCode_encode A number]

include he ha in
theorem embed_step (s : CompactTreeData.DPWState A) (a : L) :
    (D).step (embed A number s) a = embed A number ((S).step s a) := by
  apply Fin.ext
  cases s with
  | none => simp [automaton, next, embed, Computable.automatonData]
  | some t =>
    change locate _ ((retrieve _ (locate _ (some (encode A number t.val)))).bind _) = _
    rw [retrieve_locate _ _ (encode_mem_allCodes A number t.val)]
    simp only [Option.bind_some]
    rw [EncodedPitermanStep.step_correct A number decStep decAccept (edges a) acc a
      (fun q r => he q a r) ha t.val t.property]
    rfl

theorem embed_priority (s : CompactTreeData.DPWState A) : (D).priority (embed A number s) = (S).priority s := by
  cases s with
  | none => simp [automaton, priority, embed, Computable.automatonData]
  | some t =>
    change ((retrieve _ (locate _ (some (encode A number t.val)))).map treePriority).getD 1 = _
    rw [retrieve_locate _ _ (encode_mem_allCodes A number t.val)]
    exact treePriority_encode A number t.val

include he ha in
theorem run_embed (word : OmegaWord L) (t : Nat) : (D).run word t = embed A number ((S).run word t) := by
  induction t with
  | zero => exact (embed_initial A number decStep decAccept edges acc).symm
  | succ t ih =>
    rw [DetParityAutomaton.run_succ, ih, embed_step A number decStep decAccept edges acc he ha]
    rfl

include he ha decStep decAccept in
theorem accepts_iff (word : OmegaWord L) : (D).Accepts word ↔ A.Accepts word := by
  have hp (t : Nat) : (D).priority ((D).run word t) = (S).priority ((S).run word t) := by
    rw [run_embed A number decStep decAccept edges acc he ha, embed_priority A number decStep decAccept]
  have hh : (D).Accepts word ↔ (S).Accepts word := by
    unfold DetParityAutomaton.Accepts DetParityAutomaton.AcceptsFrom
      DetParityAutomaton.PrioritySeenInfinitelyOftenFrom
    change (∃ p, _ ∧ (∀ t, ∃ k, t ≤ k ∧ (D).priority ((D).run word k) = p) ∧ _) ↔ _
    simp only [DetParityAutomaton.run] at hp
    simp only [DetParityAutomaton.run, hp]
  exact hh.trans (Computable.accepts_iff A decStep decAccept word)

end DistributedSynthesis.EncodedPitermanAutomaton
