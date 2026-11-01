module

public import Seymour.Defs
public import Seymour.Deletion.Theorem

/-!
# Section 3: the extremal argument and Theorem 1.2

`set_version` is Theorem 1.2 (the set version). It is proved by the extremal argument of
Section 3, which applies the deletion lemma (Theorem 4.12, `Deletion.deletion`) to the
instance of Section 4 with `X₁ = X₂ = X₃ = X₄ = X` and `α = β = E`: members `(p,j) ∈ R` and
`(i,s) ∈ C` conflict if `p → i` and `s → j`.

For `Ω ⊆ X × X`, the set `F₁Ω = {(i,j) : (p,j) ∈ Ω, p → i}` of the paper is
`Deletion.coveredR E Ω` and `F₂Ω = {(i,j) : (i,s) ∈ Ω, s → j}` is `Deletion.coveredC E Ω`.
So `F₁` acts by `F` on every column `Ω_{∗j}`, which is the row `row (tr Ω) j` of the
transpose (`col_coveredR`), and `F₂` acts by `F` on every row `Ω_{i∗} = row Ω i`
(`row_coveredC`). A pair `(P, Q)` is compatible if `F₁P` and `F₂Q` are disjoint;
`holes E P Q` is the set of the `d` points outside `F₁P ∪ F₂Q`, and
`score E P Q = |P| + |Q| + d` is the potential `Φ(P, Q)`.

The proof follows Section 3. Among compatible pairs `(P, Q)` with `Δ ⊆ P ∩ Q` choose one
maximising `Φ`. Every column of `P` and every row of `Q` is nonempty and proper
(`column_nonempty_proper`, `row_nonempty_proper`), so summing the strict concavity (3) over
them gives `|P| + |F₁²P| < 2|F₁P|` and `|Q| + |F₂²Q| < 2|F₂Q|` (`strict_fiber_sums`).
The deletion lemma applied to `R = X² \ F₂²Q` and `C = X² \ F₁²P` then yields a compatible
pair containing `Δ` with larger `Φ`.
-/

@[expose] public section

namespace Seymour

open Finset Deletion

section Extremal

variable {X : Type*} [Fintype X]

/-- `F₁` acts by `F` on columns: the column of `F₁P` at `j` is `F` of the column of `P`. -/
private theorem col_coveredR (E : X → X → Prop) (P : Finset (X × X)) (j : X) :
    row (tr (coveredR E P)) j = image E (row (tr P) j) := by
  ext i
  simp

/-- `F₂` acts by `F` on rows: the row of `F₂Q` at `i` is `F` of the row of `Q`. -/
private theorem row_coveredC (E : X → X → Prop) (Q : Finset (X × X)) (i : X) :
    row (coveredC E Q) i = image E (row Q i) := by
  ext j
  simp

/-- `|P|` is the sum of the sizes of the columns of `P`. -/
private theorem card_eq_sum_card_col (P : Finset (X × X)) :
    P.card = ∑ j, (row (tr P) j).card := by
  rw [← card_tr P]
  exact card_eq_sum_card_row (tr P)

/-- The diagonal `Δ`. -/
private noncomputable def diagonal : Finset (X × X) := by
  classical
  exact univ.filter (fun z => z.1 = z.2)

@[simp] private theorem mem_diagonal (i j : X) :
    (i,j) ∈ (diagonal : Finset (X × X)) ↔ i = j := by
  classical
  simp [diagonal]

/-- `(Δ, Δ)` is compatible: `(i,j) ∈ F₁Δ` means `j → i`, and `(i,j) ∈ F₂Δ` means `i → j`. -/
private theorem diagonal_compatible (E : X → X → Prop) (ho : Oriented E) :
    Disjoint (coveredR E diagonal) (coveredC E diagonal) := by
  rw [disjoint_left]
  rintro ⟨i, j⟩ h₁ h₂
  obtain ⟨p, hp, hpi⟩ := (mem_coveredR E _ _).mp h₁
  obtain ⟨s, hs, hsj⟩ := (mem_coveredC E _ _).mp h₂
  obtain rfl := (mem_diagonal p j).mp hp
  obtain rfl := (mem_diagonal i s).mp hs
  exact ho p i hpi hsj

/-- The points outside `F₁P ∪ F₂Q`. -/
private noncomputable def holes (E : X → X → Prop) (P Q : Finset (X × X)) :
    Finset (X × X) := by
  classical
  exact (coveredR E P ∪ coveredC E Q)ᶜ

/-- The potential `Φ(P, Q) = |P| + |Q| + d`, where `d = |holes E P Q|`. -/
private noncomputable def score (E : X → X → Prop) (P Q : Finset (X × X)) : ℕ :=
  P.card + Q.card + (holes E P Q).card

/-- If `(P, Q)` is compatible and `Δ ⊆ P ∩ Q`, then every column of `P` is nonempty and
proper. -/
private theorem column_nonempty_proper (E : X → X → Prop)
    (hi : ∀ y, ∃ x, E x y) (P Q : Finset (X × X))
    (hc : Disjoint (coveredR E P) (coveredC E Q)) (hp : diagonal ⊆ P) (hq : diagonal ⊆ Q)
    (j : X) : (row (tr P) j).Nonempty ∧ row (tr P) j ≠ univ := by
  classical
  refine ⟨⟨j, by simpa using hp ((mem_diagonal j j).mpr rfl)⟩, ?_⟩
  intro hall
  obtain ⟨w, hw⟩ := hi j
  obtain ⟨p, hpw⟩ := hi w
  have hpj : (p,j) ∈ P := by simpa using (hall ▸ mem_univ p : p ∈ row (tr P) j)
  exact disjoint_left.mp hc
    ((mem_coveredR E P (w, j)).mpr ⟨p, hpj, hpw⟩)
    ((mem_coveredC E Q (w, j)).mpr ⟨w, hq (by simp), hw⟩)

/-- If `(P, Q)` is compatible and `Δ ⊆ P ∩ Q`, then every row of `Q` is nonempty and
proper. -/
private theorem row_nonempty_proper (E : X → X → Prop)
    (hi : ∀ y, ∃ x, E x y) (P Q : Finset (X × X))
    (hc : Disjoint (coveredR E P) (coveredC E Q)) (hp : diagonal ⊆ P) (hq : diagonal ⊆ Q)
    (i : X) : (row Q i).Nonempty ∧ row Q i ≠ univ := by
  classical
  refine ⟨⟨i, (mem_row Q i i).mpr (hq (by simp))⟩, ?_⟩
  intro hall
  obtain ⟨w, hw⟩ := hi i
  obtain ⟨s, hsw⟩ := hi w
  have his : (i,s) ∈ Q := (mem_row Q i s).mp (by rw [hall]; exact mem_univ s)
  exact disjoint_left.mp hc
    ((mem_coveredR E P (i, w)).mpr ⟨w, hp (by simp), hw⟩)
    ((mem_coveredC E Q (i, w)).mpr ⟨s, his, hsw⟩)

/-- The strict concavity (3) on every nonempty proper vertex set, summed over the columns of
`P` and the rows of `Q`: `|P| + |F₁²P| < 2|F₁P|` and `|Q| + |F₂²Q| < 2|F₂Q|`. -/
private theorem strict_fiber_sums [Nonempty X] (E : X → X → Prop)
    (hi : ∀ y, ∃ x, E x y)
    (hs : ∀ S : Finset X, S.Nonempty → S ≠ univ →
      S.card + (image E (image E S)).card < 2 * (image E S).card)
    (P Q : Finset (X × X)) (hc : Disjoint (coveredR E P) (coveredC E Q))
    (hp : diagonal ⊆ P) (hq : diagonal ⊆ Q) :
    P.card + (coveredR E (coveredR E P)).card < 2 * (coveredR E P).card ∧
    Q.card + (coveredC E (coveredC E Q)).card < 2 * (coveredC E Q).card := by
  classical
  have hp' (j : X) := hs (row (tr P) j) (column_nonempty_proper E hi P Q hc hp hq j).1
    (column_nonempty_proper E hi P Q hc hp hq j).2
  have hq' (i : X) := hs (row Q i) (row_nonempty_proper E hi P Q hc hp hq i).1
    (row_nonempty_proper E hi P Q hc hp hq i).2
  have hpc := sum_lt_sum (s := (univ : Finset X)) (fun j _ => (hp' j).le)
    ⟨Classical.arbitrary X, mem_univ _, hp' _⟩
  have hqc := sum_lt_sum (s := (univ : Finset X)) (fun i _ => (hq' i).le)
    ⟨Classical.arbitrary X, mem_univ _, hq' _⟩
  constructor
  · simpa only [card_eq_sum_card_col, col_coveredR, sum_add_distrib, mul_sum] using hpc
  · simpa only [card_eq_sum_card_row, row_coveredC, sum_add_distrib, mul_sum] using hqc

/-- For a compatible pair, `d + |F₁P| + |F₂Q| = |X|²`. -/
private theorem holes_card (E : X → X → Prop) (P Q : Finset (X × X))
    (hc : Disjoint (coveredR E P) (coveredC E Q)) :
    (holes E P Q).card + (coveredR E P).card + (coveredC E Q).card =
      Fintype.card (X × X) := by
  classical
  have hu : (coveredR E P ∪ coveredC E Q).card = (coveredR E P).card + (coveredC E Q).card :=
    card_union_of_disjoint hc
  have hle := card_le_univ (coveredR E P ∪ coveredC E Q)
  simp only [holes, card_compl]
  omega

end Extremal

/-- Theorem 1.2 (set version). Every nonempty finite oriented graph in which every vertex has
an in-neighbour has a nonempty proper vertex set `U` with `|U| + |F²(U)| ≥ 2|F(U)|`. -/
theorem set_version (X : Type*) [Fintype X] [Nonempty X] (E : X → X → Prop)
    (hE : Oriented E) (hin : ∀ y, ∃ x, E x y) :
    ∃ U : Finset X, U.Nonempty ∧ U ≠ Finset.univ ∧
      2 * (image E U).card ≤ U.card + (image E (image E U)).card := by
  classical
  by_contra hn
  have hs (S : Finset X) (hne : S.Nonempty) (hneq : S ≠ univ) :
      S.card + (image E (image E S)).card < 2 * (image E S).card := by
    by_contra hnot
    exact hn ⟨S, hne, hneq, Nat.le_of_not_gt hnot⟩
  let choices : Finset (Finset (X × X) × Finset (X × X)) :=
    univ.filter fun pq => diagonal ⊆ pq.1 ∧ diagonal ⊆ pq.2 ∧
      Disjoint (coveredR E pq.1) (coveredC E pq.2)
  have hchoices : choices.Nonempty := by
    refine ⟨(diagonal, diagonal), ?_⟩
    simp only [choices, mem_filter, mem_univ, true_and]
    exact ⟨Subset.refl _, Subset.refl _, diagonal_compatible E hE⟩
  obtain ⟨⟨P, Q⟩, hpq, hmax⟩ := exists_max_image choices (fun pq => score E pq.1 pq.2) hchoices
  obtain ⟨hP, hQ, hc⟩ := (mem_filter.mp hpq).2
  obtain ⟨hpstrict, hqstrict⟩ := strict_fiber_sums E hin hs P Q hc hP hQ
  let R : Finset (X × X) := (coveredC E (coveredC E Q))ᶜ
  let C : Finset (X × X) := (coveredR E (coveredR E P))ᶜ
  -- the diagonal survives and has no conflicts
  have hRd (v : X) : (v,v) ∈ R := by
    refine mem_compl.mpr fun hm => ?_
    obtain ⟨s, hvs, hsv⟩ := (mem_coveredC E _ (v, v)).mp hm
    exact disjoint_left.mp hc ((mem_coveredR E P (v, s)).mpr ⟨s, hP (by simp), hsv⟩) hvs
  have hCd (v : X) : (v,v) ∈ C := by
    refine mem_compl.mpr fun hm => ?_
    obtain ⟨p, hpv, hpv'⟩ := (mem_coveredR E _ (v, v)).mp hm
    exact disjoint_left.mp hc hpv ((mem_coveredC E Q (p, v)).mpr ⟨p, hQ (by simp), hpv'⟩)
  have hRfree (v : X) (c : X × X) (hcC : c ∈ C) : ¬ Conflict E E (v, v) c := by
    rintro ⟨hvi, hsv⟩
    exact mem_compl.mp hcC ((mem_coveredR E _ c).mpr
      ⟨v, (mem_coveredR E P (v, c.2)).mpr ⟨c.2, hP (by simp), hsv⟩, hvi⟩)
  have hCfree (v : X) (r : X × X) (hrR : r ∈ R) : ¬ Conflict E E r (v, v) := by
    rintro ⟨hpv, hvj⟩
    exact mem_compl.mp hrR ((mem_coveredC E _ r).mpr
      ⟨v, (mem_coveredC E Q (r.1, v)).mpr ⟨r.1, hQ (by simp), hpv⟩, hvj⟩)
  -- `H`-points are uncovered
  have hH : H E E R C ⊆ holes E P Q := by
    rintro ⟨p, s⟩ hh
    obtain ⟨i, j, hr, hc', hpi, hsj⟩ := (mem_H E E R C (p, s)).mp hh
    refine mem_compl.mpr fun hm => ?_
    rcases mem_union.mp hm with hm | hm
    · exact mem_compl.mp hc' ((mem_coveredR E _ (i, s)).mpr ⟨p, hm, hpi⟩)
    · exact mem_compl.mp hr ((mem_coveredC E _ (p, j)).mpr ⟨s, hm, hsj⟩)
  obtain ⟨R', hR', C', hC', hnc, hkR, hkC, hcost⟩ := deletion E E R C
  -- `(R', C')` is compatible and contains `Δ`
  have hc' : Disjoint (coveredR E R') (coveredC E C') := by
    rw [disjoint_left]
    rintro ⟨i, j⟩ h₁ h₂
    obtain ⟨p, hp, hpi⟩ := (mem_coveredR E R' (i, j)).mp h₁
    obtain ⟨s, hs, hsj⟩ := (mem_coveredC E C' (i, j)).mp h₂
    exact hnc _ hp _ hs ⟨hpi, hsj⟩
  have hR'd : diagonal ⊆ R' := by
    rintro ⟨p, j⟩ h
    obtain rfl := (mem_diagonal p j).mp h
    exact hkR _ (hRd p) (hRfree p)
  have hC'd : diagonal ⊆ C' := by
    rintro ⟨i, s⟩ h
    obtain rfl := (mem_diagonal i s).mp h
    exact hkC _ (hCd i) (hCfree i)
  have hnewmax : score E R' C' ≤ score E P Q := by
    apply hmax (R', C')
    simp only [choices, mem_filter, mem_univ, true_and]
    exact ⟨hR'd, hC'd, hc'⟩
  -- counting
  have hq : (Z E E R C \ (coveredR E R' ∪ coveredC E C')).card ≤ (holes E R' C').card :=
    card_le_card fun z hz => mem_compl.mpr (mem_sdiff.mp hz).2
  have hHcard := card_le_card hH
  have holdcard := holes_card E P Q hc
  have hRcard : R.card + (coveredC E (coveredC E Q)).card = Fintype.card (X × X) := by
    have hle := card_le_univ (coveredC E (coveredC E Q))
    simp only [R, card_compl]
    omega
  have hCcard : C.card + (coveredR E (coveredR E P)).card = Fintype.card (X × X) := by
    have hle := card_le_univ (coveredR E (coveredR E P))
    simp only [C, card_compl]
    omega
  have h₁ := card_sdiff_add_card_eq_card hR'
  have h₂ := card_sdiff_add_card_eq_card hC'
  have h₃ := min_le_left (nuR E E R C) (nuC E E R C)
  have h₄ := nuR_le_card_H E E R C
  unfold score at hnewmax
  omega

end Seymour
