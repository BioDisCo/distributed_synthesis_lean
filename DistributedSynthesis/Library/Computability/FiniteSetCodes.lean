/- Project authors: see AUTHORS.md at the repository root. -/

import DistributedSynthesis.Library.Computability.FiniteSubsets

/-! # Canonical subset codes through an explicit finite numbering -/
namespace DistributedSynthesis.FiniteSetCodes

def imageCodes {Code : Type*} (n : Nat) (xs : List Nat) (choices : List Code)
    (step : Nat → Code → Nat) : List Nat :=
  FiniteSubsets.normalize n (xs.flatMap (fun q => choices.map (step q)))

theorem imageCodes_primrec {Param Code : Type*} [Primcodable Param] [Primcodable Code]
    {n : Param → Nat} {xs : Param → List Nat} {cs : Param → List Code}
    {step : Param → Nat → Code → Nat}
    (hn : Primrec n) (hxs : Primrec xs) (hc : Primrec cs)
    (hs : Primrec (fun x : Param × Nat × Code => step x.1 x.2.1 x.2.2)) :
    Primrec (fun x => imageCodes (n x) (xs x) (cs x) (step x)) := by
  apply FiniteSubsets.normalize_primrec.comp hn
  apply Primrec.list_flatMap hxs
  change Primrec (fun x : Param × Nat => (cs x.1).map (step x.1 x.2))
  apply Primrec.list_map (hc.comp Primrec.fst)
  exact (hs.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂

variable {X Y : Type*} {n m : Nat} [DecidableEq X] [DecidableEq Y]
  (e : X ≃ Fin n) (f : Y ≃ Fin m)

def encode (s : Finset X) := FiniteSubsets.encode (s.map e.toEmbedding)
def decode (xs : List Nat) := (FiniteSubsets.decode n xs).map e.symm.toEmbedding
section
omit [DecidableEq X]

theorem mem_encode (s : Finset X) (x : X) : (e x).val ∈ encode e s ↔ x ∈ s := by
  rw [encode,← FiniteSubsets.mem_decode,FiniteSubsets.decode_encode]
  simp only [Finset.mem_map_equiv,Equiv.symm_apply_apply]
theorem mem_decode (xs : List Nat) (x : X) : x ∈ decode e xs ↔ (e x).val ∈ xs := by
  simp only [decode,Finset.mem_map_equiv,Equiv.symm_symm,FiniteSubsets.mem_decode]
theorem decode_encode (s : Finset X) : decode e (encode e s) = s := by
  ext x
  rw [mem_decode,mem_encode]
theorem encode_mem (s : Finset X) : encode e s ∈ FiniteSubsets.codes n :=
  FiniteSubsets.encode_mem_codes _
theorem mem_encode_iff (s : Finset X) (q : Nat) :
    q ∈ encode e s ↔ ∃ x ∈ s, (e x).val = q := by
  constructor
  · intro h
    have hq : q < n := (List.mem_filter.mp h).1 |> List.mem_range.mp
    refine ⟨e.symm ⟨q,hq⟩,?_,by simp⟩
    apply (mem_encode e s _).mp
    simpa using h
  · rintro ⟨x,hx,rfl⟩
    exact (mem_encode e s x).mpr hx

end
section
omit [DecidableEq X]

theorem encode_injective : Function.Injective (encode e) := by
  intro s t h
  simpa only [decode_encode] using congrArg (decode e) h

theorem encode_singleton (x : X) : encode e {x} = [(e x).val] := by
  unfold encode
  rw [Finset.map_singleton]
  have h := FiniteSubsets.normalize_encode_eq_sort ({e x} : Finset (Fin n))
  rw [FiniteSubsets.normalize_encode] at h
  simpa using h

theorem encode_empty : encode e ∅ = [] := by simp [encode,FiniteSubsets.encode]

end

omit [DecidableEq Y] in
/-- Extensional identification of a normalized list with a finite-set image. -/
theorem normalize_eq_encode (xs : List Nat) (s : Finset Y)
    (h : ∀ y, (f y).val ∈ xs ↔ y ∈ s) : FiniteSubsets.normalize m xs = encode f s := by
  unfold encode
  rw [← FiniteSubsets.normalize_encode (s.map f.toEmbedding),FiniteSubsets.normalize_eq_iff]
  apply Finset.ext
  intro q
  rw [FiniteSubsets.mem_decode,FiniteSubsets.decode_encode,Finset.mem_map_equiv]
  simpa only [Equiv.apply_symm_apply] using h (f.symm q)

omit [DecidableEq X] in
theorem encode_decode (xs : List Nat) : encode e (decode e xs) = FiniteSubsets.normalize n xs :=
  (normalize_eq_encode e xs (decode e xs) (fun x => (mem_decode e xs x).symm)).symm

def codes (n : Nat) := (FiniteSubsets.codes n).map (FiniteSubsets.normalize n)
theorem codes_primrec : Primrec codes := Primrec.list_map FiniteSubsets.codes_primrec
  (FiniteSubsets.normalize_primrec.comp Primrec.fst Primrec.snd).to₂
section
omit [DecidableEq X]

theorem codes_complete (s : Finset X) : encode e s ∈ codes n :=
  List.mem_map.mpr ⟨encode e s,encode_mem e s,FiniteSubsets.normalize_encode _⟩
theorem codes_sound (xs : List Nat) (h : xs ∈ codes n) : ∃ s : Finset X, encode e s = xs := by
  obtain ⟨ys,_,rfl⟩ := List.mem_map.mp h
  exact ⟨decode e (FiniteSubsets.normalize n ys), by rw [encode_decode,FiniteSubsets.normalize_idem]⟩

/-- Apply a numeric transition over an encoded set and a complete finite list
of choices. The result is the canonical code of the semantic union of images. -/
theorem collect (s : Finset X) {Choice : Type*} [Fintype Choice]
    (choices : List Choice) (hc : ∀ c, c ∈ choices)
    (step : Nat → Choice → Nat) (semantic : X → Choice → Y)
    (hs : ∀ x c, step (e x).val c = (f (semantic x c)).val) :
    FiniteSubsets.normalize m ((encode e s).flatMap (fun q => choices.map (step q))) =
      encode f (s.biUnion (fun x => Finset.univ.image (semantic x))) := by
  apply normalize_eq_encode f
  intro y
  simp only [List.mem_flatMap,List.mem_map,mem_encode_iff,Finset.mem_biUnion,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,⟨x,hx,rfl⟩,c,_,he⟩
    refine ⟨x,hx,c,?_⟩
    apply f.injective
    exact Fin.ext ((hs x c).symm.trans he)
  · rintro ⟨x,hx,c,rfl⟩
    exact ⟨(e x).val,⟨x,hx,rfl⟩,c,hc c,hs x c⟩

theorem collect_raw (s : Finset X) {Choice Code : Type*} [Fintype Choice]
    (code : Choice → Code) (choices : List Code)
    (hc : ∀ c, code c ∈ choices) (hc' : ∀ v ∈ choices, ∃ c, code c = v)
    (step : Nat → Code → Nat) (semantic : X → Choice → Y)
    (hs : ∀ x c, step (e x).val (code c) = (f (semantic x c)).val) :
    FiniteSubsets.normalize m ((encode e s).flatMap (fun q => choices.map (step q))) =
      encode f (s.biUnion (fun x => Finset.univ.image (semantic x))) := by
  apply normalize_eq_encode f
  intro y
  simp only [List.mem_flatMap,List.mem_map,mem_encode_iff,Finset.mem_biUnion,Finset.mem_image,
    Finset.mem_univ,true_and]
  constructor
  · rintro ⟨q,⟨x,hx,rfl⟩,v,hv,he⟩
    obtain ⟨c,rfl⟩ := hc' v hv
    refine ⟨x,hx,c,?_⟩
    apply f.injective
    exact Fin.ext ((hs x c).symm.trans he)
  · rintro ⟨x,hx,c,rfl⟩
    exact ⟨(e x).val,⟨x,hx,rfl⟩,code c,hc c,hs x c⟩

end
end DistributedSynthesis.FiniteSetCodes
