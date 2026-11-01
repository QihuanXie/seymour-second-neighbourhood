module

public import Seymour.Deletion.Local

/-!
# Theorem 4.12 (the deletion lemma)

`deletion` is Theorem 4.12 for every instance. Section 3 uses the instance with one vertex
type `X` and `α = β = E`.

The proof is by induction on `|R| + |C|` over all instances at once. A member in no
conflict is kept (Case 1). If `ν(Γ_R) ≤ ν(Γ_C)` and `ν(Γ_R) < |H|`, the neighbourhood in
`Γ_R` of a Hall-deficient set of `H`-points is deleted (Case 2); the case
`ν(Γ_C) < ν(Γ_R)`, and Case 1 for members of `C`, follow by applying these arguments to
`σ(I)`. Otherwise both `Γ_R` and `Γ_C` saturate `H` and Lemma 4.11 applies (Case 3).
-/

@[expose] public section

namespace Seymour.Deletion
open Finset

universe u

/-! ### Auxiliary facts about instances -/

section Aux

variable {X₁ X₂ X₃ X₄ : Type*} {α : X₁ → X₂ → Prop} {β : X₃ → X₄ → Prop}

private theorem card_tr_sdiff {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset (A × B)) (T : Finset (B × A)) : (tr S \ T).card = (S \ tr T).card := by
  rw [← card_tr (S \ tr T), tr_sdiff, tr_tr]

private theorem H_mono [Fintype X₁] [Fintype X₃] {R₁ R₂ : Finset (X₁ × X₄)}
    {C₁ C₂ : Finset (X₂ × X₃)} (hR : R₁ ⊆ R₂) (hC : C₁ ⊆ C₂) :
    H α β R₁ C₁ ⊆ H α β R₂ C₂ := by
  intro h
  simp only [mem_H]
  rintro ⟨i, j, h1, h2, h3, h4⟩
  exact ⟨i, j, hR h1, hC h2, h3, h4⟩

private theorem Z_mono [Fintype X₂] [Fintype X₄] {R₁ R₂ : Finset (X₁ × X₄)}
    {C₁ C₂ : Finset (X₂ × X₃)} (hR : R₁ ⊆ R₂) (hC : C₁ ⊆ C₂) :
    Z α β R₁ C₁ ⊆ Z α β R₂ C₂ := by
  intro z
  simp only [mem_Z]
  rintro ⟨p, s, h1, h2, h3, h4⟩
  exact ⟨p, s, hR h1, hC h2, h3, h4⟩

/-- A member of a block `R(h)` with `h ∈ H` is in a conflict (Remark 4.2). -/
private theorem exists_conflict_of_mem_blockR [Fintype X₁] [Fintype X₃]
    {R : Finset (X₁ × X₄)} {C : Finset (X₂ × X₃)} {h : X₁ × X₃} (hh : h ∈ H α β R C)
    {r : X₁ × X₄} (hr : r ∈ blockR β R h) : ∃ c ∈ C, Conflict α β r c := by
  obtain ⟨i, -, -, hc, hi, -⟩ := (mem_H α β R C h).1 hh
  obtain ⟨-, h1, h2⟩ := (mem_blockR β R h r).1 hr
  exact ⟨(i, h.2), hc, h1 ▸ hi, h2⟩

private theorem nuR_congr [Fintype X₁] [Fintype X₃] {R₁ R₂ : Finset (X₁ × X₄)}
    {C₁ C₂ : Finset (X₂ × X₃)} (hH : H α β R₁ C₁ = H α β R₂ C₂)
    (hb : ∀ h ∈ H α β R₁ C₁, blockR β R₁ h = blockR β R₂ h) :
    nuR α β R₁ C₁ = nuR α β R₂ C₂ :=
  (matchingNumber_congr (fun h : H α β R₁ C₁ => blockR β R₁ h)
    (fun h : H α β R₂ C₂ => blockR β R₂ h) (Equiv.subtypeEquivRight fun x => by rw [hH])
    (Function.Embedding.refl _) fun x => by simp [hb x x.2]).symm

private theorem nuC_congr [Fintype X₁] [Fintype X₃] {R₁ R₂ : Finset (X₁ × X₄)}
    {C₁ C₂ : Finset (X₂ × X₃)} (hH : H α β R₁ C₁ = H α β R₂ C₂)
    (hb : ∀ h ∈ H α β R₁ C₁, blockC α C₁ h = blockC α C₂ h) :
    nuC α β R₁ C₁ = nuC α β R₂ C₂ :=
  (matchingNumber_congr (fun h : H α β R₁ C₁ => blockC α C₁ h)
    (fun h : H α β R₂ C₂ => blockC α C₂ h) (Equiv.subtypeEquivRight fun x => by rw [hH])
    (Function.Embedding.refl _) fun x => by simp [hb x x.2]).symm

end Aux

/-! ### Solutions -/

/-- `(R', C')` as in Theorem 4.12 exists for the instance `(α, β, R, C)`. -/
private def Solvable {X₁ X₂ X₃ X₄ : Type*} [Fintype X₁] [Fintype X₂] [Fintype X₃]
    [Fintype X₄] [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq X₄]
    (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄))
    (C : Finset (X₂ × X₃)) : Prop :=
  ∃ R' ⊆ R, ∃ C' ⊆ C, NoConflict α β R' C' ∧
    (∀ r ∈ R, (∀ c ∈ C, ¬ Conflict α β r c) → r ∈ R') ∧
    (∀ c ∈ C, (∀ r ∈ R, ¬ Conflict α β r c) → c ∈ C') ∧
    (R \ R').card + (C \ C').card ≤
      min (nuR α β R C) (nuC α β R C) + (Z α β R C \ (coveredR α R' ∪ coveredC β C')).card

/-- Theorem 4.12 holds for every instance in `Type u` with fewer than `n` members. -/
private def Smaller (n : ℕ) : Prop :=
  ∀ {X₁ X₂ X₃ X₄ : Type u} [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄]
    [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq X₄]
    (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃)),
    R.card + C.card < n → Solvable α β R C

section Cases

variable {X₁ X₂ X₃ X₄ : Type u} [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄]
  [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq X₄]
  (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃))

/-- A solution `(R'', C'')` for `σ(I)` gives the solution `((C'')ᵀ, (R'')ᵀ)` for `I`. -/
private theorem solvable_of_sigma (h : Solvable β α (tr C) (tr R)) : Solvable α β R C := by
  obtain ⟨R'', hR'', C'', hC'', hnc, hkR, hkC, hcount⟩ := h
  refine ⟨tr C'', by simpa using tr_subset_tr.2 hC'', tr R'', by simpa using tr_subset_tr.2 hR'',
    ?_, ?_, ?_, ?_⟩
  · rw [← noConflict_sigma, tr_tr, tr_tr]
    exact hnc
  · intro r hr hf
    rw [mem_tr]
    refine hkC _ (by simpa using hr) fun c hc hcon => hf _ ((mem_tr _ _).1 hc) ?_
    exact (conflict_sigma α β r _).1 hcon
  · intro c hc hf
    rw [mem_tr]
    refine hkR _ (by simpa using hc) fun r hr hcon => hf _ ((mem_tr _ _).1 hr) ?_
    exact (conflict_sigma α β _ c).1 hcon
  · have h1 : coveredR β R'' = tr (coveredC β (tr R'')) := by rw [← coveredR_sigma, tr_tr]
    have h2 : coveredC α C'' = tr (coveredR α (tr C'')) := by rw [← coveredC_sigma, tr_tr]
    simp only [nuR_sigma, nuC_sigma, Z_sigma, card_tr_sdiff, h1, h2, ← tr_union, tr_tr]
      at hcount
    rw [min_comm, union_comm]
    omega

/-- Case 1 of Theorem 4.12: a member `r₀ ∈ R` in no conflict is kept. -/
private theorem solvable_of_free (ih : Smaller.{u} (R.card + C.card)) {r₀ : X₁ × X₄}
    (hr₀ : r₀ ∈ R) (hfree : ∀ c ∈ C, ¬ Conflict α β r₀ c) : Solvable α β R C := by
  have hlt : (R.erase r₀).card + C.card < R.card + C.card := by
    have := card_erase_lt_of_mem hr₀
    omega
  obtain ⟨R'', hR'', C'', hC'', hnc, hkR, hkC, hcount⟩ := ih α β (R.erase r₀) C hlt
  have hH : H α β (R.erase r₀) C = H α β R C := by
    refine (H_mono (erase_subset _ _) subset_rfl).antisymm fun h hh => ?_
    obtain ⟨i, j, h1, h2, h3, h4⟩ := (mem_H α β R C h).1 hh
    refine (mem_H α β _ C h).2 ⟨i, j, mem_erase.2 ⟨?_, h1⟩, h2, h3, h4⟩
    rintro rfl
    exact hfree _ h2 ⟨h3, h4⟩
  have hnuR : nuR α β (R.erase r₀) C = nuR α β R C := by
    refine nuR_congr hH fun h hh => ?_
    ext r
    refine ⟨fun hr => ?_, fun hr => ?_⟩
    · rw [mem_blockR] at hr ⊢
      exact ⟨mem_of_mem_erase hr.1, hr.2⟩
    · obtain ⟨c, hc, hcon⟩ := exists_conflict_of_mem_blockR (hH ▸ hh) hr
      rw [mem_blockR] at hr ⊢
      refine ⟨mem_erase.2 ⟨?_, hr.1⟩, hr.2⟩
      rintro rfl
      exact hfree c hc hcon
  have hnuC : nuC α β (R.erase r₀) C = nuC α β R C := nuC_congr hH fun _ _ => rfl
  have hnot : r₀ ∉ R'' := fun h => by simpa using hR'' h
  have hq : (Z α β (R.erase r₀) C \ (coveredR α R'' ∪ coveredC β C'')).card ≤
      (Z α β R C \ (coveredR α (insert r₀ R'') ∪ coveredC β C'')).card := by
    refine card_le_card fun z hz => ?_
    rw [mem_sdiff, mem_union, not_or] at hz ⊢
    refine ⟨Z_mono (erase_subset _ _) subset_rfl hz.1, ?_, hz.2.2⟩
    rw [mem_coveredR]
    rintro ⟨p, hp, hpi⟩
    rcases mem_insert.1 hp with rfl | hp
    · obtain ⟨-, s, -, hs, -, hsj⟩ := (mem_Z α β _ C z).1 hz.1
      exact hfree (z.1, s) hs ⟨hpi, hsj⟩
    · exact hz.2.1 ((mem_coveredR α R'' z).2 ⟨p, hp, hpi⟩)
  refine ⟨insert r₀ R'', insert_subset hr₀ (hR''.trans (erase_subset _ _)), C'', hC'', ?_,
    ?_, ?_, ?_⟩
  · intro r hr c hc
    rcases mem_insert.1 hr with rfl | hr
    · exact hfree c (hC'' hc)
    · exact hnc r hr c hc
  · intro r hr hf
    by_cases he : r = r₀
    · exact he ▸ mem_insert_self _ _
    · exact mem_insert_of_mem (hkR r (mem_erase.2 ⟨he, hr⟩) hf)
  · exact fun c hc hf => hkC c hc fun r hr => hf r (mem_of_mem_erase hr)
  · rw [sdiff_insert, ← erase_sdiff_comm, ← hnuR, ← hnuC]
    omega

/-- Case 2 of Theorem 4.12 when `ν(Γ_R) ≤ ν(Γ_C)`: by Lemma 4.3 some nonempty `H' ⊆ H`
has few neighbours `W` in `Γ_R`; delete `W` and apply the induction hypothesis. -/
private theorem solvable_of_deficient (ih : Smaller.{u} (R.card + C.card))
    (hle : nuR α β R C ≤ nuC α β R C) (hlt : nuR α β R C < (H α β R C).card) :
    Solvable α β R C := by
  obtain ⟨K, hKne, hK⟩ := hall_defect (fun h : H α β R C => blockR β R h) (nuR α β R C)
    (matchingNumber_bound _) (by rwa [Fintype.card_coe])
  rw [Fintype.card_coe] at hK
  set W := K.biUnion fun h : H α β R C => blockR β R h with hW
  have hWR : W ⊆ R := fun r hr => by
    obtain ⟨h, -, hr⟩ := mem_biUnion.1 hr
    exact ((mem_blockR β R h r).1 hr).1
  have hWne : W.Nonempty := by
    obtain ⟨h, hhK⟩ := hKne
    obtain ⟨i, j, h1, -, -, h4⟩ := (mem_H α β R C h).1 h.2
    exact ⟨((h : X₁ × X₃).1, j), mem_biUnion.2 ⟨h, hhK, (mem_blockR β R h _).2 ⟨h1, rfl, h4⟩⟩⟩
  have hcardW := card_sdiff_add_card_eq_card hWR
  have hWpos := hWne.card_pos
  obtain ⟨R', hR', C', hC', hnc, hkR, hkC, hcount⟩ := ih α β (R \ W) C (by omega)
  have hHK : (H α β (R \ W) C).card + K.card ≤ (H α β R C).card := by
    rw [← card_map (Function.Embedding.subtype _), ← card_union_of_disjoint]
    · refine card_le_card (union_subset (H_mono sdiff_subset subset_rfl) fun x hx => ?_)
      obtain ⟨y, -, rfl⟩ := mem_map.1 hx
      exact y.2
    · rw [disjoint_left]
      intro x hx hxK
      obtain ⟨y, hyK, rfl⟩ := mem_map.1 hxK
      obtain ⟨i, j, h1, -, -, h4⟩ := (mem_H α β _ C _).1 hx
      exact (mem_sdiff.1 h1).2 (mem_biUnion.2
        ⟨y, hyK, (mem_blockR β R y _).2 ⟨(mem_sdiff.1 h1).1, rfl, h4⟩⟩)
  have hq : (Z α β (R \ W) C \ (coveredR α R' ∪ coveredC β C')).card ≤
      (Z α β R C \ (coveredR α R' ∪ coveredC β C')).card :=
    card_le_card (sdiff_subset_sdiff (Z_mono sdiff_subset subset_rfl) subset_rfl)
  have h1 := card_sdiff_add_card_eq_card hR'
  have h2 := card_sdiff_add_card_eq_card (hR'.trans sdiff_subset)
  have h3 := min_le_left (nuR α β (R \ W) C) (nuC α β (R \ W) C)
  have h4 := nuR_le_card_H α β (R \ W) C
  refine ⟨R', hR'.trans sdiff_subset, C', hC', hnc, ?_, ?_, ?_⟩
  · intro r hr hf
    refine hkR r (mem_sdiff.2 ⟨hr, fun hrW => ?_⟩) hf
    obtain ⟨h, -, hrh⟩ := mem_biUnion.1 hrW
    obtain ⟨c, hc, hcon⟩ := exists_conflict_of_mem_blockR h.2 hrh
    exact hf c hc hcon
  · exact fun c hc hf => hkC c hc fun r hr => hf r (mem_sdiff.1 hr).1
  · rw [min_eq_left hle]
    omega

/-- Case 3 of Theorem 4.12: every member is in a conflict and both `Γ_R` and `Γ_C`
saturate `H`. Take `R' = C' = ∅` and apply Lemma 4.11. -/
private theorem solvable_of_saturated (hR : ∀ r ∈ R, ∃ c ∈ C, Conflict α β r c)
    (hC : ∀ c ∈ C, ∃ r ∈ R, Conflict α β r c)
    (hHR : nuR α β R C = (H α β R C).card) (hHC : nuC α β R C = (H α β R C).card) :
    Solvable α β R C := by
  have hcount := count_lemma α β R C hR hC hHR hHC
  refine ⟨∅, empty_subset _, ∅, empty_subset _, fun r hr => absurd hr (notMem_empty r),
    fun r hr hf => ?_, fun c hc hf => ?_, ?_⟩
  · obtain ⟨c, hc, hcon⟩ := hR r hr
    exact absurd hcon (hf c hc)
  · obtain ⟨r, hr, hcon⟩ := hC c hc
    exact absurd hcon (hf r hr)
  · have h0 : coveredR α (∅ : Finset (X₁ × X₄)) ∪ coveredC β (∅ : Finset (X₂ × X₃)) = ∅ := by
      ext z
      simp
    rw [h0, sdiff_empty, sdiff_empty, sdiff_empty, hHR, hHC, min_self]
    omega

/-- The induction step of Theorem 4.12. -/
private theorem solvable_step (ih : Smaller.{u} (R.card + C.card)) : Solvable α β R C := by
  have ihσ : Smaller.{u} ((tr C).card + (tr R).card) := by
    rw [card_tr, card_tr, add_comm]
    exact ih
  by_cases hfR : ∃ r ∈ R, ∀ c ∈ C, ¬ Conflict α β r c
  · obtain ⟨r, hr, hf⟩ := hfR
    exact solvable_of_free α β R C ih hr hf
  by_cases hfC : ∃ c ∈ C, ∀ r ∈ R, ¬ Conflict α β r c
  · obtain ⟨c, hc, hf⟩ := hfC
    refine solvable_of_sigma α β R C (solvable_of_free β α (tr C) (tr R) ihσ
      (r₀ := (c.2, c.1)) (by simpa using hc) fun r hr hcon => hf _ ((mem_tr _ _).1 hr) ?_)
    exact (conflict_sigma α β _ c).1 hcon
  push Not at hfR hfC
  by_cases hlt : min (nuR α β R C) (nuC α β R C) < (H α β R C).card
  · rcases le_total (nuR α β R C) (nuC α β R C) with hle | hle
    · exact solvable_of_deficient α β R C ih hle (by rwa [min_eq_left hle] at hlt)
    · refine solvable_of_sigma α β R C (solvable_of_deficient β α (tr C) (tr R) ihσ ?_ ?_)
      · rwa [nuR_sigma, nuC_sigma]
      · rwa [nuR_sigma, H_sigma, card_tr, ← min_eq_right hle]
  · have hR := nuR_le_card_H α β R C
    have hC := nuC_le_card_H α β R C
    exact solvable_of_saturated α β R C hfR hfC (by omega) (by omega)

end Cases

private theorem smaller (n : ℕ) : Smaller.{u} n := by
  induction n with
  | zero => exact fun _ _ _ _ h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro X₁ X₂ X₃ X₄ _ _ _ _ _ _ _ _ α β R C h
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | h
    · exact ih α β R C h
    · exact solvable_step α β R C (h ▸ ih)

/-- Theorem 4.12. -/
theorem deletion {X₁ X₂ X₃ X₄ : Type u} [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄]
    [DecidableEq X₁] [DecidableEq X₂] [DecidableEq X₃] [DecidableEq X₄]
    (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃)) :
    ∃ R' ⊆ R, ∃ C' ⊆ C, NoConflict α β R' C' ∧
      (∀ r ∈ R, (∀ c ∈ C, ¬ Conflict α β r c) → r ∈ R') ∧
      (∀ c ∈ C, (∀ r ∈ R, ¬ Conflict α β r c) → c ∈ C') ∧
      (R \ R').card + (C \ C').card ≤
        min (nuR α β R C) (nuC α β R C) +
          (Z α β R C \ (coveredR α R' ∪ coveredC β C')).card :=
  smaller _ α β R C (Nat.lt_succ_self _)

end Seymour.Deletion
