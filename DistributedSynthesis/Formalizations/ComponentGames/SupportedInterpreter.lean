/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.ComponentGames.HistoryGames

/- A strategy transformation on the existing supported public trees.
The transition witnesses are later instantiated with representation isomorphisms. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation
noncomputable section
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
variable {O A T U S : Type}

structure SupportedInterpreter (offers : A → O → Bool) (initial : O) (Legal : O → A → Prop)
    (targetOffers : U → T → Bool) (target : LabeledTree T U) where
  State : Type
  start : State
  observed : State → O
  action : State → A
  targetNode : State → List T
  start_observed : observed start = initial
  start_node : targetNode start = []
  legal : ∀ s, Legal (observed s) (action s)
  target_supported : ∀ s, publicSupport targetOffers target (targetNode s) = true
  advance : ∀ s o, offers (action s) o = true → State
  reply : ∀ s o, offers (action s) o = true → T
  advance_observed : ∀ s o h, observed (advance s o h) = o
  advance_node : ∀ s o h, targetNode (advance s o h) = targetNode s ++ [reply s o h]

namespace SupportedInterpreter
variable {offers : A → O → Bool} {initial : O} {Legal : O → A → Prop}
variable {targetOffers : U → T → Bool} {target : LabeledTree T U}
variable (I : SupportedInterpreter offers initial Legal targetOffers target)

def step (s : I.State) (o : O) : I.State := if h : offers (I.action s) o = true then I.advance s o h else s
def atState (node : List O) : I.State := node.foldl I.step I.start
def tree : LabeledTree O A := fun node => I.action (I.atState node)

@[simp] theorem at_nil : I.atState [] = I.start := rfl
@[simp] theorem at_append (node : List O) (o : O) : I.atState (node ++ [o]) = I.step (I.atState node) o := by
  simp only [atState,List.foldl_append,List.foldl_cons,List.foldl_nil]
@[simp] theorem step_offered (s : I.State) (o : O) (h : offers (I.action s) o = true) :
    I.step s o = I.advance s o h := by simp only [step,dif_pos h]

theorem observed_at (node : List O) (supported : publicSupport offers I.tree node = true) :
    I.observed (I.atState node) = observableAt initial node := by
  cases node using List.reverseRecOn with
  | nil => exact I.start_observed
  | append_singleton node o =>
    have pair : publicSupport offers I.tree node = true ∧ offers (I.tree node) o = true := by
      simpa only [publicSupport_append,Bool.and_eq_true] using supported
    rw [at_append,step_offered I _ _ pair.2,I.advance_observed]
    simp [observableAt]

theorem tree_legal : SupportedMovesValid offers initial Legal I.tree := by
  intro node supported
  rw [← I.observed_at node supported]
  exact I.legal _

/-- The entire supported branch is transformed. This does not select only
one favorable environment play. The returned equalities retain every local
state, so dependent history/run maps can be applied pointwise. -/
theorem branch (b : Nat → O) (supported : ∀ n, publicSupport offers I.tree (branchNode b n) = true) :
    ∃ c : Nat → T,
      (∀ n, publicSupport targetOffers target (branchNode c n) = true) ∧
      (∀ n, I.targetNode (I.atState (branchNode b n)) = branchNode c n) ∧
      ∀ n, ∃ h : offers (I.action (I.atState (branchNode b n))) (b n) = true,
        I.atState (branchNode b (n+1)) = I.advance (I.atState (branchNode b n)) (b n) h ∧
        c n = I.reply (I.atState (branchNode b n)) (b n) h := by
  have offered n : offers (I.action (I.atState (branchNode b n))) (b n) = true := by
    have pair := supported (n+1)
    change publicSupport offers I.tree (branchNode b n ++ [b n]) = true at pair
    simp only [publicSupport_append,Bool.and_eq_true] at pair
    exact pair.2
  let c n := I.reply (I.atState (branchNode b n)) (b n) (offered n)
  have advance n : I.atState (branchNode b (n+1)) = I.advance (I.atState (branchNode b n)) (b n) (offered n) := by
    change I.atState (branchNode b n ++ [b n]) = _
    rw [at_append,step_offered]
  have nodes n : I.targetNode (I.atState (branchNode b n)) = branchNode c n := by
    induction n with
    | zero => exact I.start_node
    | succ n ih => rw [advance,I.advance_node,ih]; rfl
  exact ⟨c,fun n => nodes n ▸ I.target_supported _,nodes,fun n => ⟨offered n,advance n,rfl⟩⟩

end SupportedInterpreter
end
end Characterisation.ComponentGames
