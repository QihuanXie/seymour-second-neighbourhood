module

public import Mathlib
public import Seymour.Deletion.Hall

/-!
# Section 4.1: instances of the deletion lemma

An *instance* consists of finite types `X₁ X₂ X₃ X₄`, relations `α : X₁ → X₂ → Prop`
(written `p → i`) and `β : X₃ → X₄ → Prop` (written `s → j`), and families
`R : Finset (X₁ × X₄)` and `C : Finset (X₂ × X₃)`. Members `r = (p,j) ∈ R` and
`c = (i,s) ∈ C` *conflict* if `p → i` and `s → j`; the conflict has `Z`-point `(i,j)`
and `H`-point `(p,s)`.

This file defines `Z`, `H`, coverings, the blocks `R(h)`, `C(h)`, the matching numbers
`ν(Γ_R)`, `ν(Γ_C)`, `ν(Γ_L)`, `ν(Γ_N)`, and the symmetry `σ`, which maps the instance
`(X₁,X₂,X₃,X₄,α,β,R,C)` to `(X₃,X₄,X₁,X₂,β,α,Cᵀ,Rᵀ)`. It also defines transposes `Sᵀ` and
rows of sets of pairs, which Lemma 4.9 and Section 3 use.

Relations are arbitrary; decidability is handled classically.
-/

@[expose] public section

namespace Seymour.Deletion
open Finset

/-! ### Matching numbers -/

section Matching
variable {L A : Type*} [Fintype L]

/-- The maximum size of a matching in the bipartite graph in which `x : L` is adjacent to
the elements of `t x`. -/
noncomputable def matchingNumber (t : L → Finset A) : ℕ := by
  classical
  exact Nat.findGreatest (fun k => ∃ (s : Finset L) (f : s → A),
    Function.Injective f ∧ (∀ x : s, f x ∈ t x) ∧ s.card = k) (Fintype.card L)

/-- No matching is larger than the matching number. -/
theorem matchingNumber_bound (t : L → Finset A) : MatchingBound t (matchingNumber t) := by
  classical
  intro s f hf ht
  exact Nat.le_findGreatest (Finset.card_le_univ s) ⟨s, f, hf, ht, rfl⟩

theorem matchingNumber_le_card (t : L → Finset A) : matchingNumber t ≤ Fintype.card L := by
  classical
  exact Nat.findGreatest_le _

/-- The matching number is attained (by the empty matching if there is no edge). -/
theorem exists_matching (t : L → Finset A) : ∃ (s : Finset L) (f : s → A),
    Function.Injective f ∧ (∀ x : s, f x ∈ t x) ∧ s.card = matchingNumber t := by
  classical
  unfold matchingNumber
  apply Nat.findGreatest_spec (P := fun k => ∃ (s : Finset L) (f : s → A),
    Function.Injective f ∧ (∀ x : s, f x ∈ t x) ∧ s.card = k) (m := 0)
    (Nat.zero_le (Fintype.card L))
  refine ⟨∅, (fun x => False.elim (Finset.notMem_empty x.val x.property)), ?_, ?_, rfl⟩
  · intro x _ _
    exact False.elim (Finset.notMem_empty x.val x.property)
  · intro x
    exact False.elim (Finset.notMem_empty x.val x.property)

/-- A matching indexed by a finite type `ι`, using the left vertices `j i` and the right
vertices `f i`, has at most `ν` edges. -/
theorem card_le_matchingNumber {ι : Type*} [Fintype ι] (t : L → Finset A) (j : ι → L)
    (hj : Function.Injective j) (f : ι → A) (hf : Function.Injective f)
    (ht : ∀ i, f i ∈ t (j i)) : Fintype.card ι ≤ matchingNumber t := by
  classical
  have hs (x : (univ.image j : Finset L)) : ∃ i, j i = x := by
    obtain ⟨i, -, hi⟩ := mem_image.mp x.property
    exact ⟨i, hi⟩
  choose k hk using hs
  rw [← card_univ, ← card_image_of_injective _ hj]
  refine matchingNumber_bound t _ (f ∘ k) ?_ fun x => ?_
  · intro x y hxy
    apply Subtype.ext
    rw [← hk x, ← hk y, hf hxy]
  · rw [Function.comp_apply, ← hk x]
    exact ht (k x)

/-- A matching saturates `L` exactly when the matching number is `|L|`. -/
theorem matchingNumber_eq_card_iff (t : L → Finset A) :
    matchingNumber t = Fintype.card L ↔
      ∃ f : L → A, Function.Injective f ∧ ∀ x, f x ∈ t x := by
  classical
  constructor
  · intro h
    obtain ⟨s, f, hf, ht, hs⟩ := exists_matching t
    have hu : s = univ := eq_univ_of_card s (hs.trans h)
    refine ⟨fun x => f ⟨x, hu ▸ mem_univ x⟩, fun x y hxy => ?_, fun x => ht _⟩
    exact congrArg Subtype.val (hf hxy)
  · rintro ⟨f, hf, ht⟩
    exact le_antisymm (matchingNumber_le_card t)
      (card_le_matchingNumber t id Function.injective_id f hf ht)

/-- Matching numbers are invariant under relabelling both parts. -/
theorem matchingNumber_congr {L' A' : Type*} [Fintype L']
    (t : L → Finset A) (t' : L' → Finset A') (e : L ≃ L') (g : A ↪ A')
    (h : ∀ x, t' (e x) = (t x).map g) :
    matchingNumber t' = matchingNumber t := by
  classical
  apply le_antisymm
  · obtain ⟨s, f, hf, ht, hs⟩ := exists_matching t'
    have hpre (y : s) : ∃ a ∈ t (e.symm y), g a = f y := by
      have hy := ht y
      rw [← e.apply_symm_apply (y : L'), h] at hy
      simpa using hy
    choose a ha hga using hpre
    rw [← hs, ← Fintype.card_coe]
    refine card_le_matchingNumber t (fun y : s => e.symm y) ?_ a ?_ ha
    · intro y z hyz
      exact Subtype.ext (e.symm.injective hyz)
    · intro y z hyz
      apply hf
      rw [← hga y, ← hga z, hyz]
  · obtain ⟨s, f, hf, ht, hs⟩ := exists_matching t
    rw [← hs, ← Fintype.card_coe]
    refine card_le_matchingNumber t' (fun x : s => e x) ?_ (fun x => g (f x)) ?_ fun x => ?_
    · intro x y hxy
      exact Subtype.ext (e.injective hxy)
    · intro x y hxy
      exact hf (g.injective hxy)
    · rw [h]
      exact mem_map_of_mem g (ht x)

end Matching

/-! ### Transposition of pairs -/

section Transpose
variable {A B : Type*}

/-- The transpose `Sᵀ = {(b,a) : (a,b) ∈ S}`. -/
def tr (S : Finset (A × B)) : Finset (B × A) := S.map (Equiv.prodComm A B).toEmbedding

@[simp] theorem mem_tr (S : Finset (A × B)) (x : B × A) : x ∈ tr S ↔ (x.2, x.1) ∈ S :=
  mem_map_equiv

@[simp] theorem tr_tr (S : Finset (A × B)) : tr (tr S) = S := by
  ext x
  simp

@[simp] theorem card_tr (S : Finset (A × B)) : (tr S).card = S.card := by
  simp [tr]

@[simp] theorem tr_subset_tr {S T : Finset (A × B)} : tr S ⊆ tr T ↔ S ⊆ T :=
  map_subset_map

theorem tr_union [DecidableEq A] [DecidableEq B] (S T : Finset (A × B)) :
    tr (S ∪ T) = tr S ∪ tr T :=
  map_union S T

theorem tr_sdiff [DecidableEq A] [DecidableEq B] (S T : Finset (A × B)) :
    tr (S \ T) = tr S \ tr T :=
  map_sdiff S T

/-- Transposition identifies the members of `S` with those of `T = Sᵀ`. -/
private def trEquiv {S : Finset (A × B)} {T : Finset (B × A)} (hT : T = tr S) : S ≃ T :=
  (Equiv.prodComm A B).subtypeEquiv fun x => by simp [hT]

end Transpose

/-! ### Rows of a set of pairs -/

section Rows
variable {U V : Type*}

/-- The row `{v : (u,v) ∈ P}` of `P` at `u`. The column `{u : (u,v) ∈ P}` at `v` is the row
`row (tr P) v` of the transpose. -/
noncomputable def row (P : Finset (U × V)) (u : U) : Finset V := by
  classical
  exact (P.filter fun x => x.1 = u).image Prod.snd

@[simp] theorem mem_row (P : Finset (U × V)) (u : U) (v : V) :
    v ∈ row P u ↔ (u, v) ∈ P := by
  classical
  simp [row]

/-- `|P|` is the sum of the sizes of the rows of `P`. -/
theorem card_eq_sum_card_row [Fintype U] (P : Finset (U × V)) :
    P.card = ∑ u, (row P u).card := by
  classical
  rw [card_eq_sum_card_fiberwise (f := Prod.fst) (t := univ) fun x _ => mem_univ x.1]
  refine sum_congr rfl fun u _ => ?_
  have hinj : Set.InjOn Prod.snd (P.filter fun x => x.1 = u : Set (U × V)) := by
    intro x hx y hy h
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    exact Prod.ext (hx'.trans hy'.symm) h
  have h := card_image_of_injOn hinj
  unfold row
  convert h.symm

end Rows

/-! ### Instances -/

section Instance
variable {X₁ X₂ X₃ X₄ : Type*} (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop)

/-- The members `r = (p,j)` and `c = (i,s)` conflict: `p → i` and `s → j`. -/
def Conflict (r : X₁ × X₄) (c : X₂ × X₃) : Prop := α r.1 c.1 ∧ β c.2 r.2

variable (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃))

/-- The `Z`-points `(i,j)` of all conflicts. -/
noncomputable def Z [Fintype X₂] [Fintype X₄] : Finset (X₂ × X₄) := by
  classical
  exact univ.filter fun z => ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ α p z.1 ∧ β s z.2

/-- The `H`-points `(p,s)` of all conflicts. -/
noncomputable def H [Fintype X₁] [Fintype X₃] : Finset (X₁ × X₃) := by
  classical
  exact univ.filter fun h => ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ α h.1 i ∧ β h.2 j

@[simp] theorem mem_Z [Fintype X₂] [Fintype X₄] (z : X₂ × X₄) :
    z ∈ Z α β R C ↔ ∃ p s, (p, z.2) ∈ R ∧ (z.1, s) ∈ C ∧ α p z.1 ∧ β s z.2 := by
  classical
  simp [Z]

@[simp] theorem mem_H [Fintype X₁] [Fintype X₃] (h : X₁ × X₃) :
    h ∈ H α β R C ↔ ∃ i j, (h.1, j) ∈ R ∧ (i, h.2) ∈ C ∧ α h.1 i ∧ β h.2 j := by
  classical
  simp [H]

/-- The points `(i,j)` covered by members `(p,j)` of `R'`, that is, with `p → i`. -/
noncomputable def coveredR [Fintype X₂] [Fintype X₄] (R' : Finset (X₁ × X₄)) :
    Finset (X₂ × X₄) := by
  classical
  exact univ.filter fun z => ∃ p, (p, z.2) ∈ R' ∧ α p z.1

/-- The points `(i,j)` covered by members `(i,s)` of `C'`, that is, with `s → j`. -/
noncomputable def coveredC [Fintype X₂] [Fintype X₄] (C' : Finset (X₂ × X₃)) :
    Finset (X₂ × X₄) := by
  classical
  exact univ.filter fun z => ∃ s, (z.1, s) ∈ C' ∧ β s z.2

@[simp] theorem mem_coveredR [Fintype X₂] [Fintype X₄] (R' : Finset (X₁ × X₄))
    (z : X₂ × X₄) :
    z ∈ coveredR α R' ↔ ∃ p, (p, z.2) ∈ R' ∧ α p z.1 := by
  classical
  simp [coveredR]

@[simp] theorem mem_coveredC [Fintype X₂] [Fintype X₄] (C' : Finset (X₂ × X₃))
    (z : X₂ × X₄) :
    z ∈ coveredC β C' ↔ ∃ s, (z.1, s) ∈ C' ∧ β s z.2 := by
  classical
  simp [coveredC]

/-- No member of `R'` conflicts with a member of `C'`. -/
def NoConflict (R' : Finset (X₁ × X₄)) (C' : Finset (X₂ × X₃)) : Prop :=
  ∀ r ∈ R', ∀ c ∈ C', ¬ Conflict α β r c

/-- The block `R(h) = {(p,j) ∈ R : s → j}` of `h = (p,s)`. -/
noncomputable def blockR (h : X₁ × X₃) : Finset (X₁ × X₄) := by
  classical
  exact R.filter fun r => r.1 = h.1 ∧ β h.2 r.2

/-- The block `C(h) = {(i,s) ∈ C : p → i}` of `h = (p,s)`. -/
noncomputable def blockC (h : X₁ × X₃) : Finset (X₂ × X₃) := by
  classical
  exact C.filter fun c => c.2 = h.2 ∧ α h.1 c.1

@[simp] theorem mem_blockR (h : X₁ × X₃) (r : X₁ × X₄) :
    r ∈ blockR β R h ↔ r ∈ R ∧ r.1 = h.1 ∧ β h.2 r.2 := by
  classical
  simp [blockR]

@[simp] theorem mem_blockC (h : X₁ × X₃) (c : X₂ × X₃) :
    c ∈ blockC α C h ↔ c ∈ C ∧ c.2 = h.2 ∧ α h.1 c.1 := by
  classical
  simp [blockC]

/-- `ν(Γ_R)`: `Γ_R` joins `h ∈ H` to the members of `R(h)`. -/
noncomputable def nuR [Fintype X₁] [Fintype X₃] : ℕ :=
  matchingNumber fun h : H α β R C => blockR β R (h : X₁ × X₃)

/-- `ν(Γ_C)`: `Γ_C` joins `h ∈ H` to the members of `C(h)`. -/
noncomputable def nuC [Fintype X₁] [Fintype X₃] : ℕ :=
  matchingNumber fun h : H α β R C => blockC α C (h : X₁ × X₃)

/-- The points of `Z` covered by the member `r = (p,j)`: the `(i,j) ∈ Z` with `p → i`. -/
noncomputable def coverL [Fintype X₂] [Fintype X₄] (r : X₁ × X₄) : Finset (X₂ × X₄) := by
  classical
  exact (Z α β R C).filter fun z => z.2 = r.2 ∧ α r.1 z.1

/-- The points of `Z` covered by the member `c = (i,s)`: the `(i,j) ∈ Z` with `s → j`. -/
noncomputable def coverN [Fintype X₂] [Fintype X₄] (c : X₂ × X₃) : Finset (X₂ × X₄) := by
  classical
  exact (Z α β R C).filter fun z => z.1 = c.1 ∧ β c.2 z.2

@[simp] theorem mem_coverL [Fintype X₂] [Fintype X₄] (r : X₁ × X₄) (z : X₂ × X₄) :
    z ∈ coverL α β R C r ↔ z ∈ Z α β R C ∧ z.2 = r.2 ∧ α r.1 z.1 := by
  classical
  simp only [coverL, Finset.mem_filter]

@[simp] theorem mem_coverN [Fintype X₂] [Fintype X₄] (c : X₂ × X₃) (z : X₂ × X₄) :
    z ∈ coverN α β R C c ↔ z ∈ Z α β R C ∧ z.1 = c.1 ∧ β c.2 z.2 := by
  classical
  simp only [coverN, Finset.mem_filter]

/-- `ν(Γ_L)`: `Γ_L` joins each member of `R` to the points of `Z` it covers. -/
noncomputable def nuL [Fintype X₂] [Fintype X₄] : ℕ :=
  matchingNumber fun r : R => coverL α β R C (r : X₁ × X₄)

/-- `ν(Γ_N)`: `Γ_N` joins each member of `C` to the points of `Z` it covers. -/
noncomputable def nuN [Fintype X₂] [Fintype X₄] : ℕ :=
  matchingNumber fun c : C => coverN α β R C (c : X₂ × X₃)

theorem nuR_le_card_H [Fintype X₁] [Fintype X₃] : nuR α β R C ≤ (H α β R C).card := by
  simpa [nuR] using matchingNumber_le_card (fun h : H α β R C => blockR β R (h : X₁ × X₃))

theorem nuC_le_card_H [Fintype X₁] [Fintype X₃] : nuC α β R C ≤ (H α β R C).card := by
  simpa [nuC] using matchingNumber_le_card (fun h : H α β R C => blockC α C (h : X₁ × X₃))

/-! ### The symmetry `σ`

The instance `σ(X₁,X₂,X₃,X₄,α,β,R,C) = (X₃,X₄,X₁,X₂,β,α,Cᵀ,Rᵀ)` is written
`β α (tr C) (tr R)`. Transposition of pairs identifies its members, conflicts, coverings,
`Z` and `H` with those of the original instance, with the roles of `R` and `C` exchanged. -/

/-- The members `(s,i)` and `(j,p)` conflict in `σ` iff `(p,j)` and `(i,s)` conflict. -/
theorem conflict_sigma (r : X₁ × X₄) (c : X₂ × X₃) :
    Conflict β α (c.2, c.1) (r.2, r.1) ↔ Conflict α β r c :=
  and_comm

/-- The `Z`-points of `σ` are the transposed `Z`-points. -/
theorem Z_sigma [Fintype X₂] [Fintype X₄] : Z β α (tr C) (tr R) = tr (Z α β R C) := by
  ext z
  simp only [mem_Z, mem_tr]
  constructor <;> rintro ⟨p, s, h₁, h₂, h₃, h₄⟩ <;> exact ⟨s, p, h₂, h₁, h₄, h₃⟩

/-- The `H`-points of `σ` are the transposed `H`-points. -/
theorem H_sigma [Fintype X₁] [Fintype X₃] : H β α (tr C) (tr R) = tr (H α β R C) := by
  ext h
  simp only [mem_H, mem_tr]
  constructor <;> rintro ⟨i, j, h₁, h₂, h₃, h₄⟩ <;> exact ⟨j, i, h₂, h₁, h₄, h₃⟩

/-- In `σ`, the `R`-members `C'ᵀ` cover the transposes of the points covered by `C'`. -/
theorem coveredR_sigma [Fintype X₂] [Fintype X₄] (C' : Finset (X₂ × X₃)) :
    coveredR β (tr C') = tr (coveredC β C') := by
  ext z
  simp

/-- In `σ`, the `C`-members `R'ᵀ` cover the transposes of the points covered by `R'`. -/
theorem coveredC_sigma [Fintype X₂] [Fintype X₄] (R' : Finset (X₁ × X₄)) :
    coveredC α (tr R') = tr (coveredR α R') := by
  ext z
  simp

/-- `R'` and `C'` have no conflict iff `C'ᵀ` and `R'ᵀ` have none in `σ`. -/
theorem noConflict_sigma (R' : Finset (X₁ × X₄)) (C' : Finset (X₂ × X₃)) :
    NoConflict β α (tr C') (tr R') ↔ NoConflict α β R' C' := by
  constructor
  · intro h r hr c hc hrc
    exact h (c.2, c.1) (by simpa using hc) (r.2, r.1) (by simpa using hr)
      ((conflict_sigma α β r c).mpr hrc)
  · intro h c hc r hr hrc
    exact h (r.2, r.1) (by simpa using hr) (c.2, c.1) (by simpa using hc)
      ((conflict_sigma α β (r.2, r.1) (c.2, c.1)).mp hrc)

/-- In `σ`, the block `R(s,p)` is the transpose of the block `C(p,s)`. -/
private theorem blockR_sigma (h : X₁ × X₃) : blockR α (tr C) (h.2, h.1) = tr (blockC α C h) := by
  ext r
  simp

/-- In `σ`, the block `C(s,p)` is the transpose of the block `R(p,s)`. -/
private theorem blockC_sigma (h : X₁ × X₃) : blockC β (tr R) (h.2, h.1) = tr (blockR β R h) := by
  ext c
  simp

/-- In `σ`, the `R`-member `(s,i)` covers the transpose of what `(i,s)` covers. -/
private theorem coverL_sigma [Fintype X₂] [Fintype X₄] (c : X₂ × X₃) :
    coverL β α (tr C) (tr R) (c.2, c.1) = tr (coverN α β R C c) := by
  ext z
  simp only [mem_coverL, mem_coverN, Z_sigma, mem_tr]

/-- `ν(Γ_R)` of `σ` is `ν(Γ_C)`. -/
theorem nuR_sigma [Fintype X₁] [Fintype X₃] : nuR β α (tr C) (tr R) = nuC α β R C :=
  matchingNumber_congr _ _ (trEquiv (H_sigma α β R C)) (Equiv.prodComm X₂ X₃).toEmbedding
    fun h => blockR_sigma α C h

/-- `ν(Γ_C)` of `σ` is `ν(Γ_R)`. -/
theorem nuC_sigma [Fintype X₁] [Fintype X₃] : nuC β α (tr C) (tr R) = nuR α β R C :=
  matchingNumber_congr _ _ (trEquiv (H_sigma α β R C)) (Equiv.prodComm X₁ X₄).toEmbedding
    fun h => blockC_sigma β R h

/-- `ν(Γ_L)` of `σ` is `ν(Γ_N)`. -/
theorem nuL_sigma [Fintype X₂] [Fintype X₄] : nuL β α (tr C) (tr R) = nuN α β R C :=
  matchingNumber_congr _ _ (trEquiv rfl) (Equiv.prodComm X₂ X₄).toEmbedding
    fun c => coverL_sigma α β R C c

end Instance

end Seymour.Deletion
