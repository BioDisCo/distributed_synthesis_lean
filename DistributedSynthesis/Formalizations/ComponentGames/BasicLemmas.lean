/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Formalizations.PeriodicBlocks.ComputableBounds
import DistributedSynthesis.Formalizations.PeriodicBlocks.BlockReplay
import DistributedSynthesis.Formalizations.PeriodicBlocks.LexicographicProgress

/- Exact view, counting, representative, and progress lemmas for component games. -/
namespace Characterisation.ComponentGames
open DistributedSynthesis Characterisation Characterisation.PeriodicBlocks
set_option maxHeartbeats 1200000

private theorem subtype_mk_heq {α : Type} {p q : α → Prop}
    (eq : p = q) (a : α) (hp : p a) (hq : q a) :
    HEq (⟨a,hp⟩ : Subtype p) (⟨a,hq⟩ : Subtype q) := by
  cases eq
  rfl

-- Exact paper view-extension statement, with an arbitrary domain and map.
theorem view_extension {I₁ I₂ : Type} (r : Nat)
    (H : Set (EnvHistory I₁ I₂)) (_lengths : ∀ h ∈ H, List.length h = r)
    (T : H → EnvHistory I₁ I₂) (_targetLengths : ∀ h, List.length (T h) = r)
    (preserves : ∀ (h k : H) p, currentView p h.val = currentView p k.val →
      currentView p (T h) = currentView p (T k))
    (t : Nat) (h k : H) (u v : EnvHistory I₁ I₂)
    (hu : List.length u = t) (hv : List.length v = t) (p : Proc)
    (same : currentView p (h.val ++ u) = currentView p (k.val ++ v)) :
    currentView p (T h ++ u) = currentView p (T k ++ v) :=
  append_preserves_views _ _ _ _ (preserves h k) u v (hu.trans hv.symm) p same

-- Also checks the reflection needed in finite-representation isomorphisms.
theorem extension_isomorphism {I₁ I₂ R T : Type}
    (root : R → EnvHistory I₁ I₂) (other : T → EnvHistory I₁ I₂)
    (η : R ≃ T)
    (iso : ∀ i j p, currentView p (root i) = currentView p (root j) ↔
      currentView p (other (η i)) = currentView p (other (η j)))
    (i j : R) (u v : EnvHistory I₁ I₂) (len : List.length u = List.length v) (p : Proc) :
    currentView p (root i ++ u) = currentView p (root j ++ v) ↔
      currentView p (other (η i) ++ u) = currentView p (other (η j) ++ v) := by
  constructor
  · exact append_preserves_views _ _ _ _ (fun q => (iso i j q).mp) u v len p
  · exact append_preserves_views _ _ _ _ (fun q => (iso i j q).mpr) u v len p

-- Exact number of nonempty suffixes, not the larger (|Σ|+1)^D bound.
theorem blockPrefix_card_exact (E : Type) [Fintype E] (D : Nat) :
    Nat.card (BlockPrefix E D) = ∑ t : Fin D, Nat.card E ^ (t.val + 1) := by
  classical
  let e : BlockPrefix E D ≃ (Σ t : Fin D, List.Vector E (t.val+1)) :=
    { toFun := fun u => ⟨⟨u.val.length-1, by have := u.property; omega⟩,
        ⟨u.val, by dsimp; have := u.property; omega⟩⟩
      invFun := fun x => ⟨x.2.val, by rw [x.2.property]; omega,
        by rw [x.2.property]; omega⟩
      left_inv := by intro u; rfl
      right_inv := by
        rintro ⟨⟨n,hn⟩,v,hv⟩
        have hv' : v.length = n+1 := hv
        apply Sigma.ext (Fin.ext (by dsimp; omega))
        dsimp only
        have eq : v.length - 1 = n := by omega
        apply subtype_mk_heq
        rw [eq]
    }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [card_vector, Nat.card_eq_fintype_card]

theorem blockType_card_exact (S Q E O : Type)
    [Fintype S] [Fintype Q] [Fintype E] [Fintype O] (D : Nat) :
    Nat.card (BlockType S Q (BlockPrefix E D) O (BlockWord E D)) =
      Nat.card S * Nat.card Q *
        Nat.card O ^ (∑ t : Fin D, Nat.card E ^ (t.val+1)) *
        2 ^ (Nat.card E ^ D) := by
  classical
  let e : BlockType S Q (BlockPrefix E D) O (BlockWord E D) ≃
      S × Q × (BlockPrefix E D → O) × (BlockWord E D → Bool) :=
    { toFun := fun t => (t.graphState,t.objectiveState,t.rule,t.suffixes)
      invFun := fun t => ⟨t.1,t.2.1,t.2.2.1,t.2.2.2⟩
      left_inv := by intro t; cases t; rfl
      right_inv := by intro t; rfl }
  rw [Nat.card_congr e]
  simp only [Nat.card_prod, Nat.card_fun, blockPrefix_card_exact, blockWord_card]
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [hb]
  simp only [Nat.mul_assoc]

-- The partition is the quotient by equality of the manuscript's full key.
-- Its domain can be ANY participating-history set, so no reachability or
-- winning-strategy premise is hidden in the counting result.
theorem N_bound {R S Q E O : Type}
    [Finite R] [Fintype S] [Fintype Q] [Fintype E] [Fintype O] (D : Nat)
    (key : R → BlockType S Q (BlockPrefix E D) O (BlockWord E D)) :
    Nat.card (Quotient (Setoid.ker key)) ≤
      Nat.card S * Nat.card Q *
        Nat.card O ^ (∑ t : Fin D, Nat.card E ^ (t.val+1)) *
        2 ^ (Nat.card E ^ D) := by
  let code : Quotient (Setoid.ker key) → BlockType S Q (BlockPrefix E D) O (BlockWord E D) :=
    Quotient.lift key (fun _ _ eq => eq)
  have injective : Function.Injective code := by
    intro x y
    induction x using Quotient.inductionOn with | _ x =>
      induction y using Quotient.inductionOn with | _ y =>
        intro eq
        exact Quotient.sound eq
  rw [← blockType_card_exact S Q E O D]
  exact Nat.card_le_card_of_injective code injective

-- Unique decomposition used in previous-phase-extensions, over actual words.
theorem previous_phase_unique {E : Type} (r D : Nat) (word h k u v : List E)
    (hh : h.length = r) (hk : k.length = r)
    (_hu : u.length = D) (_hv : v.length = D)
    (a : word = h ++ u) (b : word = k ++ v) : h = k ∧ u = v := by
  have heads := congrArg (List.take r) (a.symm.trans b)
  have tails := congrArg (List.drop r) (a.symm.trans b)
  have th : List.take r (h ++ u) = h := by rw [← hh, List.take_left]
  have tk : List.take r (k ++ v) = k := by rw [← hk, List.take_left]
  have heq : h = k := th.symm.trans (heads.trans tk)
  subst k
  exact ⟨rfl, List.append_cancel_left (a.symm.trans b)⟩

-- Arbitrary representatives, not just rank-minimizing representatives.
theorem arbitrary_representative_views {I₁ I₂ R T : Type}
    (root : R → EnvHistory I₁ I₂) (injective : Function.Injective root)
    (leader : Proc) (common : ∀ i j,
      currentView leader (root i) = currentView leader (root j))
    (_key : R → T) (rep : R → R)
    (i j : R) (u v : EnvHistory I₁ I₂) (len : List.length u = List.length v)
    (p : Proc) (same : currentView p (root i ++ u) = currentView p (root j ++ v)) :
    currentView p (root (rep i) ++ u) = currentView p (root (rep j) ++ v) :=
  append_preserves_views _ _ _ _
    (fun q => common_view_root_map root injective leader common rep q i j) u v len p same

theorem arbitrary_representative_idempotent {R T : Type} (key : R → T) (rep : R → R)
    (preserves : ∀ i, key (rep i) = key i)
    (classConstant : ∀ i j, key i = key j → rep i = rep j) :
    ∀ i, rep (rep i) = rep i := fun i => classConstant _ _ (preserves i)

theorem arbitrary_representative_bound {R T Z : Type} [Finite T] [Finite Z]
    (key : R → T) (rep : R → R)
    (classConstant : ∀ i j, key i = key j → rep i = rep j) :
    Finite {x : R × Z // rep x.1 = x.1} ∧
    Nat.card {x : R × Z // rep x.1 = x.1} ≤ Nat.card T * Nat.card Z := by
  let code : {x : R × Z // rep x.1 = x.1} → T × Z := fun x => (key x.val.1,x.val.2)
  have inj : Function.Injective code := by
    intro x y eq
    apply Subtype.ext
    exact Prod.ext (x.property.symm.trans
      ((classConstant _ _ (congrArg Prod.fst eq)).trans y.property))
        (congrArg (fun x : T × Z => x.2) eq)
  exact ⟨Finite.of_injective code inj, by
    simpa only [Nat.card_prod] using Nat.card_le_card_of_injective code inj⟩

-- Arithmetic in bounded-component-size uses exactly N |Σ|^(2D).
theorem bounded_component_size_step (N a D retained extensions next : Nat)
    (retainedBound : retained ≤ N * a^D)
    (extensionBound : extensions ≤ retained * a^D)
    (nextBound : next ≤ extensions) :
    extensions ≤ N * a^(2*D) ∧ next ≤ N * a^(2*D) := by
  have b : extensions ≤ N * a^(2*D) := calc
    extensions ≤ retained * a^D := extensionBound
    _ ≤ (N * a^D) * a^D := Nat.mul_le_mul_right _ retainedBound
    _ = N * a^(2*D) := by rw [two_mul, pow_add, Nat.mul_assoc]
  exact ⟨b, nextBound.trans b⟩

-- Full progress-measure assertions for arbitrary winning trees; there is no
-- finite-memory premise. Even coordinates in treeRank are fixed zeros.
theorem bounded_parity_progress {E : Type} (priority : List E → Nat)
    (winning : ∀ word : Nat → E,
      NatSeqMinEvenParity (fun n => priority (branchNode word n)))
    (d : Nat) (h k : List E) (pref : h.IsPrefix k)
    (lower : ∀ t, h.length ≤ t → t < k.length → d ≤ priority (k.take t)) :
    treeRank priority winning d k ≤ treeRank priority winning d h ∧
    (¬ DetParityAutomaton.NatEven d →
      (∃ t, h.length ≤ t ∧ t < k.length ∧ priority (k.take t) = d) →
      treeRank priority winning d k < treeRank priority winning d h) := by
  refine ⟨treeRank_le priority winning d pref lower, ?_⟩
  intro odd occurrence
  have positive : h.length < k.length := by obtain ⟨t,lo,hi,_⟩ := occurrence; omega
  exact treeRank_lt priority winning d odd ⟨pref,positive,lower,occurrence⟩


end Characterisation.ComponentGames

