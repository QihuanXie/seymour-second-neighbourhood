module

public import Seymour.Deletion.Konig

/-!
# Lemma 4.9: `ν(Γ_L) + ν(Γ_N) ≤ |Z| + ν(Γ_R)`

We follow the proof in the paper, for a fixed linear order on `X₄`. For `i ∈ X₂` let
`C_i = {s : (i,s) ∈ C}` and `Z^i = {j : (i,j) ∈ Z}`; for `p ∈ X₁` let `R_p = {j : (p,j) ∈ R}`
and `C^(p) = ⋃_{p → i} C_i`. With the greedy sets `B_i = g(C_i, Z^i)` put
`Y = {(i,j) : j ∈ B_i}`, and let `W` be the set of `(p,j) ∈ R` with `j ∈ B_i` for some `i`
with `p → i`. Observation (B) and Lemma 4.7 give `|Y| = ν(Γ_N)`; Step 1 is
`ν(Γ_L) + |Y| ≤ |W| + |Z|`; Step 2, which uses observation (A), is `|W| ≤ ν(Γ_R)`.
-/

@[expose] public section

namespace Seymour.Deletion
open Finset

/-! ### Combining matchings row by row -/

section Combine
variable {U : Type*}

/-- Matchings `M u`, one for each `u`, of the graphs joining `s` with `(u,s) ∈ P` to the `j`
with `(u,j) ∈ t (u,s)` combine into a matching of the graph `P – (U × T₂)`. -/
private theorem sum_card_le_matchingNumber {T₁ T₂ : Type*} [Fintype U] (P : Finset (U × T₁))
    (t : U × T₁ → Finset (U × T₂)) (M : U → Finset (T₁ × T₂))
    (hM : ∀ u, ∀ e ∈ M u, (u, e.1) ∈ P ∧ (u, e.2) ∈ t (u, e.1))
    (h₁ : ∀ u, Set.InjOn Prod.fst (M u : Set (T₁ × T₂)))
    (h₂ : ∀ u, Set.InjOn Prod.snd (M u : Set (T₁ × T₂))) :
    ∑ u, (M u).card ≤ matchingNumber fun x : P => t x := by
  classical
  let f : U → T₁ × T₂ → (U × T₁) × (U × T₂) := fun u e => ((u, e.1), (u, e.2))
  have hf (u : U) : Function.Injective (f u) := fun e e' h => by
    simp only [f, Prod.mk.injEq, true_and] at h
    exact Prod.ext h.1 h.2
  let E := univ.biUnion fun u => (M u).image (f u)
  have hE : E.card = ∑ u, (M u).card := by
    rw [card_biUnion]
    · exact sum_congr rfl fun u _ => card_image_of_injective _ (hf u)
    · intro u _ u' _ huu'
      rw [Function.onFun, disjoint_left]
      intro x hx hx'
      obtain ⟨e, -, rfl⟩ := mem_image.mp hx
      obtain ⟨e', -, he'⟩ := mem_image.mp hx'
      exact huu' (congrArg (fun x => x.1.1) he').symm
  have hmem (x) (hx : x ∈ E) : ∃ u, ∃ e ∈ M u, f u e = x := by
    obtain ⟨u, -, hx⟩ := mem_biUnion.mp hx
    obtain ⟨e, he, rfl⟩ := mem_image.mp hx
    exact ⟨u, e, he, rfl⟩
  rw [← hE]
  refine card_edges_le_matchingNumber P t E (fun x hx => ?_) ?_ ?_
  · obtain ⟨u, e, he, rfl⟩ := hmem x hx
    exact hM u e he
  · intro x hx y hy h
    obtain ⟨u, e, he, rfl⟩ := hmem x hx
    obtain ⟨u', e', he', rfl⟩ := hmem y hy
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [h₁ u he he' h]
  · intro x hx y hy h
    obtain ⟨u, e, he, rfl⟩ := hmem x hx
    obtain ⟨u', e', he', rfl⟩ := hmem y hy
    simp only [f, Prod.mk.injEq] at h
    obtain ⟨rfl, h⟩ := h
    rw [h₂ u he he' h]

end Combine

/-! ### The proof of Lemma 4.9 -/

section Main
variable {X₁ X₂ X₃ X₄ : Type*} (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop)
  (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃))

/-- `C^(p) = ⋃_{p → i} C_i`. -/
private noncomputable def colC (p : X₁) : Finset X₃ := by
  classical
  exact (C.filter fun c => α p c.1).image Prod.snd

@[simp] private theorem mem_colC (p : X₁) (s : X₃) :
    s ∈ colC α C p ↔ ∃ i, α p i ∧ (i, s) ∈ C := by
  classical
  simp only [colC, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨i, s⟩, ⟨hc, hp⟩, rfl⟩
    exact ⟨i, hp, hc⟩
  · rintro ⟨i, hp, hc⟩
    exact ⟨(i, s), ⟨hc, hp⟩, rfl⟩

/-- Observation (A): if `p → i`, then `R_p ∩ N(C_i) ⊆ Z^i`. -/
private theorem obsA [Fintype X₂] [Fintype X₄] {p : X₁} {i : X₂} (hpi : α p i) :
    N β (row C i) (row R p) ⊆ row (Z α β R C) i := by
  intro j hj
  obtain ⟨hjR, s, hs, hsj⟩ := (mem_N β _ _ j).mp hj
  rw [mem_row] at hjR hs ⊢
  exact (mem_Z α β R C (i, j)).mpr ⟨p, s, hjR, hs, hpi, hsj⟩

/-- Observation (B): `ν(Γ_N) = Σ_i λ(C_i, Z^i)`. -/
private theorem nuN_eq_sum [Fintype X₂] [Fintype X₄] :
    nuN α β R C = ∑ i, lam β (row C i) (row (Z α β R C) i) := by
  classical
  apply le_antisymm
  · obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges C (coverN α β R C)
    have hc' : nuN α β R C = M.card := hc.symm
    rw [hc', card_eq_sum_card_fiberwise (f := fun e => e.1.1) (t := univ) fun e _ => mem_univ _]
    refine sum_le_sum fun i _ => ?_
    have hfib (e) (he : e ∈ M.filter fun e => e.1.1 = i) :
        e.1 = (i, e.1.2) ∧ e.2 = (i, e.2.2) ∧ e.1 ∈ C ∧ e.2 ∈ Z α β R C ∧ β e.1.2 e.2.2 := by
      obtain ⟨heM, hei⟩ := mem_filter.mp he
      obtain ⟨hC, hN⟩ := hM e heM
      obtain ⟨hZ, h1, hb⟩ := (mem_coverN α β R C _ _).mp hN
      exact ⟨Prod.ext hei rfl, Prod.ext (h1.trans hei) rfl, hC, hZ, hb⟩
    have hinj : Set.InjOn (fun e => (e.1.2, e.2.2))
        (M.filter fun e => e.1.1 = i : Set ((X₂ × X₃) × (X₂ × X₄))) := by
      intro e he e' he' h
      have h' := (Prod.mk.injEq _ _ _ _).mp h
      refine h₁ (mem_filter.mp he).1 (mem_filter.mp he').1 ?_
      rw [(hfib e he).1, (hfib e' he').1, h'.1]
    rw [← card_image_of_injOn hinj]
    refine card_le_lam _ (fun e he => ?_) (fun e he e' he' h => ?_) (fun e he e' he' h => ?_)
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      obtain ⟨h1, h2, hC, hZ, hb⟩ := hfib x hx
      rw [mem_row, mem_row, ← h1, ← h2]
      exact ⟨hC, hZ, hb⟩
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      obtain ⟨x', hx', rfl⟩ := mem_image.mp he'
      have hx1 : x.1 = x'.1 := by rw [(hfib x hx).1, (hfib x' hx').1]; exact congrArg (i, ·) h
      rw [h₁ (mem_filter.mp hx).1 (mem_filter.mp hx').1 hx1]
    · obtain ⟨x, hx, rfl⟩ := mem_image.mp he
      obtain ⟨x', hx', rfl⟩ := mem_image.mp he'
      have hx2 : x.2 = x'.2 := by rw [(hfib x hx).2.1, (hfib x' hx').2.1]; exact congrArg (i, ·) h
      rw [h₂ (mem_filter.mp hx).1 (mem_filter.mp hx').1 hx2]
  · have h (i : X₂) := exists_edges_lam β (row C i) (row (Z α β R C) i)
    choose M hM h₁ h₂ hc using h
    rw [← sum_congr rfl fun i _ => hc i]
    refine sum_card_le_matchingNumber C (coverN α β R C) M (fun i e he => ?_) h₁ h₂
    obtain ⟨hC, hZ, hb⟩ := hM i e he
    rw [mem_row] at hC hZ
    exact ⟨hC, (mem_coverN α β R C _ _).mpr ⟨hZ, rfl, hb⟩⟩

variable [LinearOrder X₄]

/-- The greedy set `B_i = g(C_i, Z^i)`. -/
private noncomputable def B [Fintype X₂] [Fintype X₄] (i : X₂) : Finset X₄ :=
  greedy β (row C i) (row (Z α β R C) i)

/-- `Y = {(i,j) : j ∈ B_i}`. -/
private noncomputable def Y [Fintype X₂] [Fintype X₄] : Finset (X₂ × X₄) :=
  univ.filter fun z => z.2 ∈ B α β R C z.1

/-- `W`: the members `(p,j) ∈ R` such that `(i,j) ∈ Y` for some `i` with `p → i`. -/
private noncomputable def W [Fintype X₂] [Fintype X₄] : Finset (X₁ × X₄) := by
  classical
  exact R.filter fun r => ∃ i, α r.1 i ∧ r.2 ∈ B α β R C i

private theorem mem_Y [Fintype X₂] [Fintype X₄] (z : X₂ × X₄) :
    z ∈ Y α β R C ↔ z.2 ∈ B α β R C z.1 := by
  simp [Y]

private theorem mem_W [Fintype X₂] [Fintype X₄] (r : X₁ × X₄) :
    r ∈ W α β R C ↔ r ∈ R ∧ ∃ i, α r.1 i ∧ r.2 ∈ B α β R C i := by
  classical
  simp [W]

private theorem Y_subset_Z [Fintype X₂] [Fintype X₄] : Y α β R C ⊆ Z α β R C := by
  intro z hz
  have h := greedy_subset β _ _ ((mem_Y α β R C z).mp hz)
  rwa [mem_row] at h

/-- By observation (B) and Lemma 4.7, `|Y| = Σ_i |B_i| = ν(Γ_N)`. -/
private theorem card_Y [Fintype X₂] [Fintype X₄] : (Y α β R C).card = nuN α β R C := by
  rw [card_eq_sum_card_row, nuN_eq_sum]
  refine sum_congr rfl fun i _ => ?_
  have h : row (Y α β R C) i = B α β R C i := by
    ext j
    rw [mem_row, mem_Y]
  rw [h, B, card_greedy]

/-- Step 1: `ν(Γ_L) ≤ |W| + |Z| - |Y|`. -/
private theorem step1 [Fintype X₂] [Fintype X₄] :
    nuL α β R C + (Y α β R C).card ≤ (W α β R C).card + (Z α β R C).card := by
  classical
  obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges R (coverL α β R C)
  have hc' : nuL α β R C = M.card := hc.symm
  have hW : (M.filter fun e => e.1 ∈ W α β R C).card ≤ (W α β R C).card :=
    card_le_card_of_injOn Prod.fst (fun e he => (mem_filter.mp he).2)
      (h₁.mono (coe_subset.mpr (filter_subset _ M)))
  have hZ : (M.filter fun e => e.1 ∉ W α β R C).card ≤ (Z α β R C \ Y α β R C).card := by
    refine card_le_card_of_injOn Prod.snd (fun e he => ?_)
      (h₂.mono (coe_subset.mpr (filter_subset _ M)))
    obtain ⟨heM, heW⟩ := mem_filter.mp he
    obtain ⟨hr, hz⟩ := hM e heM
    obtain ⟨hzZ, hz2, hz1⟩ := (mem_coverL α β R C _ _).mp hz
    refine mem_sdiff.mpr ⟨hzZ, fun hY => heW ?_⟩
    have hB := (mem_Y α β R C _).mp hY
    rw [hz2] at hB
    exact (mem_W α β R C _).mpr ⟨hr, e.2.1, hz1, hB⟩
  have hsplit := card_filter_add_card_filter_not (s := M) fun e => e.1 ∈ W α β R C
  have hYZ := card_sdiff_add_card_eq_card (Y_subset_Z α β R C)
  omega

/-- The key claim of Step 2: `D_p = {j : (p,j) ∈ W} ⊆ g(C^(p), R_p)`. -/
private theorem row_W_subset [Fintype X₂] [Fintype X₄] (p : X₁) :
    row (W α β R C) p ⊆ greedy β (colC α C p) (row R p) := by
  intro j hj
  obtain ⟨hpj, i, hpi, hjB⟩ := (mem_W α β R C _).mp ((mem_row _ p j).mp hj)
  dsimp only at hpi hjB
  obtain ⟨hjZ, hinc⟩ := (mem_greedy β).mp hjB
  refine (mem_greedy β).mpr ⟨(mem_row R p j).mpr hpj, ?_⟩
  have hA : N β (row C i) ((row R p).filter (j < ·)) ⊆ (row (Z α β R C) i).filter (j < ·) := by
    intro x hx
    obtain ⟨hxX, hN⟩ := (mem_N β _ _ x).mp hx
    obtain ⟨hxR, hjx⟩ := mem_filter.mp hxX
    exact mem_filter.mpr ⟨obsA α β R C hpi ((mem_N β _ _ x).mpr ⟨hxR, hN⟩), hjx⟩
  have hjnot : j ∉ (row (Z α β R C) i).filter (j < ·) := by simp
  have ha := incr_anti β (row C i) hA hjnot
  have hjN : ∃ s ∈ row C i, β s j := by
    obtain ⟨-, s, -, hs, -, hsj⟩ := (mem_Z α β R C (i, j)).mp ((mem_row _ i j).mp hjZ)
    exact ⟨s, (mem_row C i s).mpr hs, hsj⟩
  have hd := incr_N_self β ((row R p).filter (j < ·)) hjN
  have hsub : row C i ⊆ colC α C p := fun s hs =>
    (mem_colC α C p s).mpr ⟨i, hpi, (mem_row C i s).mp hs⟩
  have hb := incr_mono β ((row R p).filter (j < ·)) j hsub
  have hle := incr_le_one β (colC α C p) ((row R p).filter (j < ·)) j
  omega

/-- Step 2: `W` can be matched into `H` in `Γ_R`, so `|W| ≤ ν(Γ_R)`. -/
private theorem step2 [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄] :
    (W α β R C).card ≤ nuR α β R C := by
  have h (p : X₁) := exists_edges_lam β (colC α C p) (row (W α β R C) p)
  choose M hM h₁ h₂ hc using h
  have hsum : ∑ p, (row (W α β R C) p).card = ∑ p, (M p).card :=
    sum_congr rfl fun p _ => by rw [hc p, lam_of_subset_greedy β _ _ (row_W_subset α β R C p)]
  rw [card_eq_sum_card_row, hsum]
  refine sum_card_le_matchingNumber (H α β R C) (blockR β R) M (fun p e he => ?_) h₁ h₂
  obtain ⟨hs, hj, hsj⟩ := hM p e he
  obtain ⟨i, hpi, hiC⟩ := (mem_colC α C p e.1).mp hs
  have hpR : (p, e.2) ∈ R := ((mem_W α β R C _).mp ((mem_row _ p e.2).mp hj)).1
  exact ⟨(mem_H α β R C _).mpr ⟨i, e.2, hpR, hiC, hpi, hsj⟩,
    (mem_blockR β R _ _).mpr ⟨hpR, rfl, hsj⟩⟩

private theorem rank_lemma_of_linearOrder [Fintype X₁] [Fintype X₂] [Fintype X₃]
    [Fintype X₄] : nuL α β R C + nuN α β R C ≤ (Z α β R C).card + nuR α β R C := by
  have h₁ := step1 α β R C
  have h₂ := step2 α β R C
  have h₃ := card_Y α β R C
  omega

end Main

variable {X₁ X₂ X₃ X₄ : Type*} [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄]
  (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃))

/-- Lemma 4.9 (rank inequality): `ν(Γ_L) + ν(Γ_N) ≤ |Z| + ν(Γ_R)`. -/
theorem rank_lemma : nuL α β R C + nuN α β R C ≤ (Z α β R C).card + nuR α β R C := by
  let _ : LinearOrder X₄ :=
    LinearOrder.lift' (Fintype.equivFin X₄) (Fintype.equivFin X₄).injective
  exact rank_lemma_of_linearOrder α β R C

end Seymour.Deletion
