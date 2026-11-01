module

public import Seymour.Deletion.Basic

/-!
# Section 4.2: matching numbers into `X₄`

For `S : Finset X₃` and `X : Finset X₄`, `λ(S,X)` is the maximum size of a matching in the
bipartite graph with parts `S` and `X` in which `s` is adjacent to `j` when `s → j`, that is,
when `β s j`. This file proves the König formula (Lemma 4.4), bisubmodularity (Lemma 4.5),
the properties of the increments `∂_j` (Corollary 4.6), and the properties of the greedy sets
(Lemma 4.7).

Matchings are also described by their edge sets: a finset `M` of pairs whose two projections
are injective on `M`. This is the form in which Lemma 4.9 uses them.
-/

@[expose] public section

namespace Seymour.Deletion
open Finset

/-! ### Matchings as edge sets -/

section Edges
variable {T A : Type*} (P : Finset T) (t : T → Finset A)

/-- A set of edges of the graph `P – A` (with `x` adjacent to `t x`) whose two projections
are injective is no larger than the matching number. -/
theorem card_edges_le_matchingNumber (M : Finset (T × A))
    (hM : ∀ e ∈ M, e.1 ∈ P ∧ e.2 ∈ t e.1)
    (h₁ : Set.InjOn Prod.fst (M : Set (T × A))) (h₂ : Set.InjOn Prod.snd (M : Set (T × A))) :
    M.card ≤ matchingNumber fun x : P => t x := by
  rw [← Fintype.card_coe M]
  refine card_le_matchingNumber _ (fun e : M => (⟨e.1.1, (hM e.1 e.2).1⟩ : P)) ?_
    (fun e : M => e.1.2) ?_ fun e => (hM e.1 e.2).2
  · intro e e' h
    exact Subtype.ext (h₁ e.2 e'.2 (congrArg Subtype.val h))
  · intro e e' h
    exact Subtype.ext (h₂ e.2 e'.2 h)

/-- The matching number is attained by a set of edges with injective projections. -/
theorem exists_edges : ∃ M : Finset (T × A), (∀ e ∈ M, e.1 ∈ P ∧ e.2 ∈ t e.1) ∧
    Set.InjOn Prod.fst (M : Set (T × A)) ∧ Set.InjOn Prod.snd (M : Set (T × A)) ∧
    M.card = matchingNumber fun x : P => t x := by
  classical
  obtain ⟨s, f, hf, ht, hs⟩ := exists_matching fun x : P => t x
  have hinj : Function.Injective fun x : s => (((x : P) : T), f x) := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg Prod.fst h))
  refine ⟨univ.image fun x : s => (((x : P) : T), f x), ?_, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨x, -, rfl⟩ := mem_image.mp he
    exact ⟨(x : P).2, ht x⟩
  · intro e he e' he' h
    obtain ⟨x, -, rfl⟩ := mem_image.mp he
    obtain ⟨y, -, rfl⟩ := mem_image.mp he'
    rw [Subtype.ext (Subtype.ext h)]
  · intro e he e' he' h
    obtain ⟨x, -, rfl⟩ := mem_image.mp he
    obtain ⟨y, -, rfl⟩ := mem_image.mp he'
    rw [hf h]
  · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_coe, hs]

end Edges

/-! ### The function `λ` -/

section Lambda
variable {X₃ X₄ : Type*} (β : X₃ → X₄ → Prop)

/-- The points of `X` adjacent to `s`. -/
noncomputable def nbrs (X : Finset X₄) (s : X₃) : Finset X₄ := by
  classical
  exact X.filter (β s)

@[simp] theorem mem_nbrs (X : Finset X₄) (s : X₃) (j : X₄) : j ∈ nbrs β X s ↔ j ∈ X ∧ β s j := by
  classical
  simp [nbrs]

/-- `λ(S,X)`: the maximum size of a matching in the bipartite graph with parts `S` and `X`
in which `s` is adjacent to `j` when `s → j`. -/
noncomputable def lam (S : Finset X₃) (X : Finset X₄) : ℕ :=
  matchingNumber fun s : S => nbrs β X s

/-- `N(A) ∩ X`: the points of `X` adjacent to some point of `A`. For `X = univ` this is
`N(A) = {j : s → j for some s ∈ A}`. -/
noncomputable def N (A : Finset X₃) (X : Finset X₄) : Finset X₄ := by
  classical
  exact X.filter fun j => ∃ s ∈ A, β s j

@[simp] theorem mem_N (A : Finset X₃) (X : Finset X₄) (j : X₄) :
    j ∈ N β A X ↔ j ∈ X ∧ ∃ s ∈ A, β s j := by
  classical
  simp [N]

private theorem N_subset (A : Finset X₃) (X : Finset X₄) : N β A X ⊆ X := fun j hj =>
  ((mem_N β A X j).mp hj).1

variable {β}

/-- A set of edges with injective projections is no larger than `λ`. -/
theorem card_le_lam {S : Finset X₃} {X : Finset X₄} (M : Finset (X₃ × X₄))
    (hM : ∀ e ∈ M, e.1 ∈ S ∧ e.2 ∈ X ∧ β e.1 e.2)
    (h₁ : Set.InjOn Prod.fst (M : Set (X₃ × X₄)))
    (h₂ : Set.InjOn Prod.snd (M : Set (X₃ × X₄))) : M.card ≤ lam β S X :=
  card_edges_le_matchingNumber S (nbrs β X) M
    (fun e he => ⟨(hM e he).1, (mem_nbrs β X e.1 e.2).mpr (hM e he).2⟩) h₁ h₂

variable (β)

/-- `λ(S,X)` is attained by a set of edges with injective projections. -/
theorem exists_edges_lam (S : Finset X₃) (X : Finset X₄) :
    ∃ M : Finset (X₃ × X₄), (∀ e ∈ M, e.1 ∈ S ∧ e.2 ∈ X ∧ β e.1 e.2) ∧
      Set.InjOn Prod.fst (M : Set (X₃ × X₄)) ∧ Set.InjOn Prod.snd (M : Set (X₃ × X₄)) ∧
      M.card = lam β S X := by
  obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges S (nbrs β X)
  refine ⟨M, fun e he => ?_, h₁, h₂, hc⟩
  obtain ⟨h, h'⟩ := hM e he
  exact ⟨h, (mem_nbrs β X e.1 e.2).mp h'⟩

/-- The easy half of König's formula: `λ(S,X) ≤ |S ∖ A| + |N(A) ∩ X|` for `A ⊆ S`. -/
private theorem lam_add_card_le {S A : Finset X₃} (X : Finset X₄) (hA : A ⊆ S) :
    lam β S X + A.card ≤ S.card + (N β A X).card := by
  classical
  obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges_lam β S X
  have hin : (M.filter fun e => e.1 ∈ A).card ≤ (N β A X).card := by
    refine card_le_card_of_injOn Prod.snd (fun e he => ?_)
      (h₂.mono (coe_subset.mpr (filter_subset _ M)))
    have he' := mem_filter.mp he
    exact (mem_N β A X e.2).mpr ⟨(hM e he'.1).2.1, e.1, he'.2, (hM e he'.1).2.2⟩
  have hout : (M.filter fun e => e.1 ∉ A).card ≤ (S \ A).card := by
    refine card_le_card_of_injOn Prod.fst (fun e he => ?_)
      (h₁.mono (coe_subset.mpr (filter_subset _ M)))
    have he' := mem_filter.mp he
    exact mem_sdiff.mpr ⟨(hM e he'.1).1, he'.2⟩
  have hsplit := card_filter_add_card_filter_not (s := M) fun e => e.1 ∈ A
  have hS := card_sdiff_add_card_eq_card hA
  omega

/-- The hard half of König's formula, from the defect form of Hall's theorem. -/
private theorem exists_lam_add_card_eq (S : Finset X₃) (X : Finset X₄) :
    ∃ A ⊆ S, lam β S X + A.card = S.card + (N β A X).card := by
  classical
  by_cases hlt : lam β S X < S.card
  · obtain ⟨s, -, hs⟩ := hall_defect (fun x : S => nbrs β X x) (lam β S X)
      (matchingNumber_bound _) (by rwa [Fintype.card_coe])
    have hA : s.map (Function.Embedding.subtype _) ⊆ S := by
      intro a ha
      obtain ⟨x, -, rfl⟩ := mem_map.mp ha
      exact x.2
    refine ⟨_, hA, le_antisymm (lam_add_card_le β X hA) ?_⟩
    have hN : N β (s.map (Function.Embedding.subtype _)) X = s.biUnion fun x => nbrs β X x := by
      ext j
      simp only [mem_N, mem_map, Function.Embedding.coe_subtype, mem_biUnion, mem_nbrs]
      constructor
      · rintro ⟨hj, _, ⟨x, hx, rfl⟩, h⟩
        exact ⟨x, hx, hj, h⟩
      · rintro ⟨x, hx, hj, h⟩
        exact ⟨hj, x, ⟨x, hx, rfl⟩, h⟩
    rw [hN, card_map]
    rw [Fintype.card_coe] at hs
    omega
  · refine ⟨∅, empty_subset S, ?_⟩
    have hle : lam β S X ≤ S.card := by
      simpa [lam] using matchingNumber_le_card fun x : S => nbrs β X x
    have hN : N β ∅ X = ∅ := by
      ext j
      simp
    rw [hN]
    simp only [card_empty]
    omega

/-- Lemma 4.4 (König): `λ(S,X) = min_{A ⊆ S} (|S ∖ A| + |N(A) ∩ X|)`. -/
theorem konig [DecidableEq X₃] (S : Finset X₃) (X : Finset X₄) :
    lam β S X = S.powerset.inf' S.powerset_nonempty fun A => (S \ A).card + (N β A X).card := by
  apply le_antisymm
  · refine (le_inf'_iff _ _).mpr fun A hA => ?_
    have h := lam_add_card_le β X (mem_powerset.mp hA)
    have hS := card_sdiff_add_card_eq_card (mem_powerset.mp hA)
    omega
  · obtain ⟨A, hA, h⟩ := exists_lam_add_card_eq β S X
    refine (inf'_le _ (mem_powerset.mpr hA)).trans ?_
    have hS := card_sdiff_add_card_eq_card hA
    omega

private theorem lam_le_card_right (S : Finset X₃) (X : Finset X₄) : lam β S X ≤ X.card := by
  have h := lam_add_card_le β X (subset_refl S)
  have := card_le_card (N_subset β S X)
  omega

private theorem lam_mono (S : Finset X₃) {X X' : Finset X₄} (h : X ⊆ X') :
    lam β S X ≤ lam β S X' := by
  obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges_lam β S X
  rw [← hc]
  exact card_le_lam M (fun e he => ⟨(hM e he).1, h (hM e he).2.1, (hM e he).2.2⟩) h₁ h₂

private theorem lam_insert_le [DecidableEq X₄] (S : Finset X₃) (X : Finset X₄) (j : X₄) :
    lam β S (insert j X) ≤ lam β S X + 1 := by
  obtain ⟨A, hA, h⟩ := exists_lam_add_card_eq β S X
  have h' := lam_add_card_le β (insert j X) hA
  have hN : N β A (insert j X) ⊆ insert j (N β A X) := by
    intro x hx
    rw [mem_N, mem_insert] at hx
    rw [mem_insert, mem_N]
    rcases hx with ⟨rfl | hx, h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, h⟩
  have := (card_le_card hN).trans (card_insert_le _ _)
  omega

/-- Two sets whose union and intersection lie in the union and intersection of two others. -/
private theorem card_add_card_le {Y : Type*} [DecidableEq Y] {P P' U V : Finset Y}
    (h₁ : P ∪ P' ⊆ U ∪ V) (h₂ : P ∩ P' ⊆ U ∩ V) : P.card + P'.card ≤ U.card + V.card := by
  rw [← card_union_add_card_inter P P', ← card_union_add_card_inter U V]
  exact add_le_add (card_le_card h₁) (card_le_card h₂)

/-- Lemma 4.5 (bisubmodularity). -/
theorem lam_bisub [DecidableEq X₃] [DecidableEq X₄] (S₁ S₂ : Finset X₃) (Q₁ Q₂ : Finset X₄) :
    lam β (S₁ ∪ S₂) (Q₁ ∩ Q₂) + lam β (S₁ ∩ S₂) (Q₁ ∪ Q₂) ≤ lam β S₁ Q₁ + lam β S₂ Q₂ := by
  obtain ⟨A₁, hA₁, e₁⟩ := exists_lam_add_card_eq β S₁ Q₁
  obtain ⟨A₂, hA₂, e₂⟩ := exists_lam_add_card_eq β S₂ Q₂
  have h₁ := lam_add_card_le β (Q₁ ∩ Q₂) (union_subset_union hA₁ hA₂)
  have h₂ := lam_add_card_le β (Q₁ ∪ Q₂) (inter_subset_inter hA₁ hA₂)
  have hS := card_union_add_card_inter S₁ S₂
  have hA := card_union_add_card_inter A₁ A₂
  have hN : (N β (A₁ ∪ A₂) (Q₁ ∩ Q₂)).card + (N β (A₁ ∩ A₂) (Q₁ ∪ Q₂)).card ≤
      (N β A₁ Q₁).card + (N β A₂ Q₂).card := by
    apply card_add_card_le
    · intro x hx
      simp only [mem_union, mem_inter, mem_N] at hx ⊢
      rcases hx with ⟨⟨hq₁, hq₂⟩, s, hs | hs, h⟩ | ⟨hq₁ | hq₂, s, ⟨hs₁, hs₂⟩, h⟩
      · exact Or.inl ⟨hq₁, s, hs, h⟩
      · exact Or.inr ⟨hq₂, s, hs, h⟩
      · exact Or.inl ⟨hq₁, s, hs₁, h⟩
      · exact Or.inr ⟨hq₂, s, hs₂, h⟩
    · intro x hx
      simp only [mem_union, mem_inter, mem_N] at hx ⊢
      obtain ⟨⟨⟨hq₁, hq₂⟩, -⟩, -, s, ⟨hs₁, hs₂⟩, h⟩ := hx
      exact ⟨⟨hq₁, s, hs₁, h⟩, hq₂, s, hs₂, h⟩
  omega

/-- The increment `∂_j(S,X) = λ(S, X ∪ {j}) - λ(S,X)`. -/
noncomputable def incr [DecidableEq X₄] (S : Finset X₃) (X : Finset X₄) (j : X₄) : ℕ :=
  lam β S (insert j X) - lam β S X

/-- Corollary 4.6(a): increments decrease as `X` grows. -/
theorem incr_anti [DecidableEq X₄] (S : Finset X₃) {X X' : Finset X₄} {j : X₄} (hX : X ⊆ X')
    (hj : j ∉ X') : incr β S X' j ≤ incr β S X j := by
  classical
  have h := lam_bisub β S S (insert j X) X'
  have e₁ : insert j X ∩ X' = X := by
    ext x
    simp only [mem_inter, mem_insert]
    constructor
    · rintro ⟨rfl | hx, hx'⟩
      · exact absurd hx' hj
      · exact hx
    · exact fun hx => ⟨Or.inr hx, hX hx⟩
  have e₂ : insert j X ∪ X' = insert j X' := by
    ext x
    simp only [mem_union, mem_insert]
    constructor
    · rintro ((rfl | hx) | hx)
      · exact Or.inl rfl
      · exact Or.inr (hX hx)
      · exact Or.inr hx
    · rintro (rfl | hx)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hx
  rw [e₁, e₂, union_self, inter_self] at h
  have m₁ := lam_mono β S (subset_insert j X)
  have m₂ := lam_mono β S (subset_insert j X')
  unfold incr
  omega

/-- Corollary 4.6(b): increments increase as `S` grows. -/
theorem incr_mono [DecidableEq X₄] {S S' : Finset X₃} (X : Finset X₄) (j : X₄) (hS : S ⊆ S') :
    incr β S X j ≤ incr β S' X j := by
  classical
  have h := lam_bisub β S' S (insert j X) X
  rw [inter_eq_right.mpr (subset_insert j X), union_eq_left.mpr (subset_insert j X),
    union_eq_left.mpr hS, inter_eq_right.mpr hS] at h
  have m₁ := lam_mono β S (subset_insert j X)
  have m₂ := lam_mono β S' (subset_insert j X)
  unfold incr
  omega

/-- Corollary 4.6(c): every increment is `0` or `1`. -/
theorem incr_le_one [DecidableEq X₄] (S : Finset X₃) (X : Finset X₄) (j : X₄) :
    incr β S X j ≤ 1 := by
  have := lam_insert_le β S X j
  unfold incr
  omega

/-- Corollary 4.6(d): `λ(S,X) = λ(S, X ∩ N(S))`. -/
theorem lam_N_self (S : Finset X₃) (X : Finset X₄) : lam β S (N β S X) = lam β S X := by
  apply le_antisymm (lam_mono β S (N_subset β S X))
  obtain ⟨M, hM, h₁, h₂, hc⟩ := exists_edges_lam β S X
  rw [← hc]
  refine card_le_lam M (fun e he => ⟨(hM e he).1, ?_, (hM e he).2.2⟩) h₁ h₂
  exact (mem_N β S X e.2).mpr ⟨(hM e he).2.1, e.1, (hM e he).1, (hM e he).2.2⟩

private theorem N_insert [DecidableEq X₄] {A : Finset X₃} (X : Finset X₄) {j : X₄}
    (hj : ∃ s ∈ A, β s j) : N β A (insert j X) = insert j (N β A X) := by
  ext x
  simp only [mem_N, mem_insert]
  constructor
  · rintro ⟨rfl | hx, h⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, h⟩
  · rintro (rfl | ⟨hx, h⟩)
    · exact ⟨Or.inl rfl, hj⟩
    · exact ⟨Or.inr hx, h⟩

/-- By Corollary 4.6(d), if `j ∈ N(S)` then `∂_j(S,X) = ∂_j(S, X ∩ N(S))`. -/
theorem incr_N_self [DecidableEq X₄] {S : Finset X₃} (X : Finset X₄) {j : X₄}
    (hj : ∃ s ∈ S, β s j) : incr β S (N β S X) j = incr β S X j := by
  unfold incr
  rw [← N_insert β X hj, lam_N_self, lam_N_self]

end Lambda

/-! ### Greedy sets -/

section Greedy
variable {X₃ X₄ : Type*} [LinearOrder X₄] (β : X₃ → X₄ → Prop)

/-- The greedy set `g(S,Q) = {j ∈ Q : ∂_j(S, Q_{≻j}) = 1}`, where `Q_{≻j} = {x ∈ Q : j < x}`
for the linear order `<` on `X₄`. -/
noncomputable def greedy (S : Finset X₃) (Q : Finset X₄) : Finset X₄ :=
  Q.filter fun j => incr β S (Q.filter (j < ·)) j = 1

theorem mem_greedy {S : Finset X₃} {Q : Finset X₄} {j : X₄} :
    j ∈ greedy β S Q ↔ j ∈ Q ∧ incr β S (Q.filter (j < ·)) j = 1 :=
  mem_filter

theorem greedy_subset (S : Finset X₃) (Q : Finset X₄) : greedy β S Q ⊆ Q :=
  filter_subset _ _

/-- Lemma 4.7, first part: `|g(S,Q)| = λ(S,Q)`. -/
theorem card_greedy (S : Finset X₃) (Q : Finset X₄) : (greedy β S Q).card = lam β S Q := by
  induction Q using Finset.induction_on_min with
  | empty =>
    have := lam_le_card_right β S ∅
    simp only [card_empty, nonpos_iff_eq_zero] at this
    simp [greedy, this]
  | insert a s has ih =>
    have hfa : (insert a s).filter (a < ·) = s := by
      ext x
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | h, h'⟩
        · exact absurd h' (lt_irrefl _)
        · exact h
      · exact fun h => ⟨Or.inr h, has x h⟩
    have hfx : ∀ x ∈ s, (insert a s).filter (x < ·) = s.filter (x < ·) := by
      intro x hx
      ext y
      simp only [mem_filter, mem_insert]
      constructor
      · rintro ⟨rfl | h, h'⟩
        · exact absurd (h'.trans (has x hx)) (lt_irrefl _)
        · exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩
        exact ⟨Or.inr h, h'⟩
    have hg : greedy β S (insert a s) =
        if incr β S s a = 1 then insert a (greedy β S s) else greedy β S s := by
      unfold greedy
      rw [filter_insert, hfa, filter_congr fun x hx => by rw [hfx x hx]]
    have ha : a ∉ greedy β S s := fun h => lt_irrefl a (has a (greedy_subset β S s h))
    have hle := incr_le_one β S s a
    have hm := lam_mono β S (subset_insert a s)
    rw [hg]
    unfold incr at hle ⊢
    split_ifs with h
    · rw [card_insert_of_notMem ha]
      omega
    · omega

/-- Lemma 4.7, second part: every `D ⊆ g(S,Q)` satisfies `λ(S,D) = |D|`. -/
theorem lam_of_subset_greedy (S : Finset X₃) (Q : Finset X₄) {D : Finset X₄}
    (hD : D ⊆ greedy β S Q) : lam β S D = D.card := by
  refine le_antisymm (lam_le_card_right β S D) ?_
  induction D using Finset.induction_on_min with
  | empty => simp
  | insert a s has ih =>
    have hs : s ⊆ greedy β S Q := (subset_insert _ _).trans hD
    obtain ⟨-, hinc⟩ := (mem_greedy β).mp (hD (mem_insert_self a s))
    have hsQ : s ⊆ Q.filter (a < ·) := fun x hx =>
      mem_filter.mpr ⟨greedy_subset β S Q (hs hx), has x hx⟩
    have hnot : a ∉ Q.filter (a < ·) := by simp
    have h := incr_anti β S hsQ hnot
    have has' : a ∉ s := fun h => lt_irrefl a (has a h)
    rw [card_insert_of_notMem has']
    have := ih hs
    unfold incr at h hinc
    omega

end Greedy

end Seymour.Deletion
