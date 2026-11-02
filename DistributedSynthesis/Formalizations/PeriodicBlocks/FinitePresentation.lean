/- Project authors: see AUTHORS.md at the repository root. -/
import DistributedSynthesis.Library.Computability.FiniteTableLookup
import DistributedSynthesis.Library.Computability.FiniteCodeNumbering
import DistributedSynthesis.Library.Distributed.LeaderGame.Encoding.EncodedClosingBanksCorrect

namespace Characterisation.PeriodicBlocks
open DistributedSynthesis
noncomputable section

/-- An exact finite enumeration, together with an injective encoding. -/
structure FinitePresentation (X C : Type) where
  codes : List C
  encode : X → C
  injective : Function.Injective encode
  member : ∀ x, encode x ∈ codes
  complete : ∀ c ∈ codes, ∃ x, encode x=c

namespace FinitePresentation
variable {X Y C E : Type}

def transport (p : FinitePresentation X C) (e : Y ≃ X) : FinitePresentation Y C where
  codes := p.codes
  encode := p.encode ∘ e
  injective := p.injective.comp e.injective
  member y := p.member (e y)
  complete c hc := by
    obtain ⟨x,hx⟩ := p.complete c hc
    exact ⟨e.symm x,by simpa using hx⟩

def prod (p : FinitePresentation X C) (q : FinitePresentation Y E) :
    FinitePresentation (X × Y) (C × E) where
  codes := p.codes.product q.codes
  encode x := (p.encode x.1,q.encode x.2)
  injective := by
    intro x y eq
    exact Prod.ext (p.injective (congrArg Prod.fst eq)) (q.injective (congrArg Prod.snd eq))
  member x := List.mem_product.mpr ⟨p.member x.1,q.member x.2⟩
  complete c hc := by
    obtain ⟨a,ha⟩ := p.complete c.1 (List.mem_product.mp hc).1
    obtain ⟨b,hb⟩ := q.complete c.2 (List.mem_product.mp hc).2
    exact ⟨(a,b),Prod.ext ha hb⟩

def dedup [DecidableEq C] (p : FinitePresentation X C) : FinitePresentation X C where
  codes := FiniteCodeNumbering.unique p.codes
  encode := p.encode
  injective := p.injective
  member x := (FiniteCodeNumbering.mem_unique _ _).mpr (p.member x)
  complete c hc := p.complete c ((FiniteCodeNumbering.mem_unique _ _).mp hc)

def number [DecidableEq C] (p : FinitePresentation X C) :
    X ≃ Fin (FiniteCodeNumbering.unique p.codes).length :=
  (Equiv.ofBijective (fun x => (⟨p.encode x,(FiniteCodeNumbering.mem_unique _ _).mpr (p.member x)⟩ :
      {c // c ∈ FiniteCodeNumbering.unique p.codes}))
    ⟨fun _ _ eq => p.injective (congrArg Subtype.val eq),by
      intro c
      obtain ⟨x,hx⟩ := p.complete c.val ((FiniteCodeNumbering.mem_unique _ _).mp c.property)
      exact ⟨x,Subtype.ext hx⟩⟩).trans
    (List.Nodup.getEquiv _ (FiniteCodeNumbering.unique_nodup p.codes)).symm

theorem number_val [DecidableEq C] (p : FinitePresentation X C) (x : X) :
    (p.number x).val = FiniteCodeNumbering.name p.codes (p.encode x) := rfl

def fin (n : Nat) : FinitePresentation (Fin n) Nat where
  codes := List.range n
  encode := Fin.val
  injective := Fin.val_injective
  member i := List.mem_range.mpr i.isLt
  complete c hc := ⟨⟨c,List.mem_range.mp hc⟩,rfl⟩

def bool : FinitePresentation Bool Bool where
  codes := [false,true]
  encode := id
  injective := Function.injective_id
  member b := by cases b <;> simp
  complete c _ := ⟨c,rfl⟩

def views : FinitePresentation (Bool × Bool) (Bool × Bool) := bool.prod bool

def table {n : Nat} (domain : X ≃ Fin n) (p : FinitePresentation Y C) :
    FinitePresentation (X → Y) (List C) where
  codes := FiniteSearch.words p.codes n
  encode f := List.ofFn (fun i => p.encode (f (domain.symm i)))
  injective := by
    intro f g eq
    funext x
    apply p.injective
    have h := congrArg (fun xs : List C => xs[(domain x).val]?) eq
    simpa using h
  member f := FiniteSearch.ofFn_mem_words _ _ (fun _ => p.member _)
  complete c hc := by
    classical
    have rows := List.forall₂_iff_get.mp (List.mem_sections.mp hc)
    have len : c.length=n := by simpa using rows.1
    have mem (i : Fin n) : c[i.val]'(by omega) ∈ p.codes := by
      have h := rows.2 i.val (by omega) (by simp)
      simpa [List.get_eq_getElem] using h
    choose f hf using fun i : Fin n => p.complete _ (mem i)
    refine ⟨fun x => f (domain x),?_⟩
    apply List.ext_getElem
    · simp [len]
    · intro i hi hj
      have hit : i<n := by omega
      simpa using hf ⟨i,hit⟩

theorem table_get {n : Nat} (domain : X ≃ Fin n) (p : FinitePresentation Y C)
    (f : X → Y) (fallback : C) (x : X) :
    ((table domain p).encode f).getD (domain x).val fallback = p.encode (f x) :=
  EncodedClosingBanks.table_eval domain (p.encode ∘ f) fallback x

/-- Row-major enumeration of a rectangular table. -/
theorem flatten_ofFn {Z : Type} {n m : Nat} (f : Fin n → Fin m → Z) :
    (List.ofFn (fun i => List.ofFn (f i))).flatten =
      List.ofFn (fun k : Fin (n*m) => f (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) := by
  rw [show (List.ofFn (fun i => List.ofFn (f i))) =
    (List.ofFn (fun i : Fin n => i)).map (fun i => List.ofFn (f i)) by simp only [List.map_ofFn,Function.comp_def],
    ← List.flatMap_def]
  apply List.ext_getElem
  · rw [FiniteTableLookup.flat_length _ _ m (fun _ _ => List.length_ofFn)]
    simp
  · intro k hk hk'
    let idx : Fin (n*m) := ⟨k,by simpa using hk'⟩
    let ij := finProdFinEquiv.symm idx
    have eq : ij.1.val*m+ij.2.val=k := by
      have h := congrArg Fin.val (finProdFinEquiv.apply_symm_apply idx)
      change ij.2.val+m*ij.1.val=k at h
      calc
        ij.1.val*m+ij.2.val = ij.2.val+m*ij.1.val := by ac_rfl
        _ = k := h
    have lookup := FiniteTableLookup.flat_lookup (List.ofFn (fun i : Fin n => i))
      (fun i => List.ofFn (f i)) m (fun _ _ => List.length_ofFn)
      ij.1.val ij.2.val (by simpa using ij.1.isLt) ij.2.isLt
    rw [eq,List.getElem?_eq_getElem hk] at lookup
    simpa only [List.getElem_ofFn,List.getElem?_ofFn,dif_pos ij.2.isLt,Option.some.injEq] using lookup

theorem forall_lt_number {n : Nat} (number : X ≃ Fin n) (p : Nat → Prop) :
    (∀ i < n, p i) ↔ ∀ x, p (number x).val := by
  constructor
  · intro h x; exact h _ (number x).isLt
  · intro h i hi
    simpa only [Equiv.apply_symm_apply] using h (number.symm ⟨i,hi⟩)

theorem exists_lt_number {n : Nat} (number : X ≃ Fin n) (p : Nat → Prop) :
    (∃ i < n, p i) ↔ ∃ x, p (number x).val := by
  constructor
  · rintro ⟨i,hi,h⟩
    exact ⟨number.symm ⟨i,hi⟩,by simpa only [Equiv.apply_symm_apply] using h⟩
  · rintro ⟨x,h⟩; exact ⟨_,(number x).isLt,h⟩

theorem lookup2 {Z : Type} (xs : List X) (ys : List Y) (f : X → Y → Z)
    (i : Fin xs.length) (j : Fin ys.length) (fallback : Z) :
    (xs.flatMap (fun x => ys.map (f x))).getD (i.val*ys.length+j.val) fallback = f xs[i.val] ys[j.val] := by
  rw [List.getD_eq_getElem?_getD,
    FiniteTableLookup.flat_lookup xs (fun x => ys.map (f x)) ys.length
      (fun _ _ => List.length_map _) i.val j.val i.isLt j.isLt,
    List.getElem?_map,List.getElem?_eq_getElem j.isLt]
  rfl

end FinitePresentation
end
end Characterisation.PeriodicBlocks
