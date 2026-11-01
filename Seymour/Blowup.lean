module

public import Seymour.Defs

/-!
# Lemma 2.2: the lexicographic blow-up

`blowup E m` has vertex set `X × Fin m`, with `(v,a) → (w,b)` if `v → w`, or `v = w` and
`a < b`: every vertex of `E` is replaced by a transitive tournament on `Fin m`.
`blowup_lemma` (Lemma 2.2) states that if `E` is oriented, every vertex has an in-neighbour,
the strict subset deficit (1) holds, and `m > |X|`, then the blow-up is oriented, every vertex
has an in-neighbour, and `|U| + |F²(U)| < 2|F(U)|` for every nonempty proper vertex set `U`
(the strict concavity (3)).

The proof of (3) counts fibre by fibre. Let `S` be the projection of `U`, and for a
vertex `v` let `Θ_v`, `P_v`, `Q_v ⊆ Fin m` be the fibres of `U`, `F(U)`, `F²(U)` over `v`.
With `A = F(S)` and `B = F²(S) \ F(S)`:
* `Θ_v = ∅` if `v ∉ S`, and `|Θ_v| ≤ |P_v| + 1` if `v ∈ S`, since everything above the
  minimum of `Θ_v` lies in `P_v`;
* `P_v = Fin m` if `v ∈ A`;
* `Q_v ⊆ P_v` if `v ∉ A ∪ F²(S)`.
Hence `|Θ_v| + |Q_v| - 2|P_v| ≤ m[v ∈ B] + [v ∈ S \ A] - m[v ∈ A \ S]`, and summing over
`v` gives `|U| + |F²(U)| - 2|F(U)| ≤ m(|B| - |A \ S|) + |S \ A|`. If `S ≠ X` this is
negative by the strict subset deficit (1) and `|S \ A| ≤ |X| < m`; if `S = X`, then
`F(U) = F²(U) = X × Fin m`.
-/

@[expose] public section

namespace Seymour
open Finset

/-- The lexicographic blow-up of `E` by transitive tournaments on `Fin m`. -/
def blowup {X : Type*} (E : X → X → Prop) (m : ℕ) : X × Fin m → X × Fin m → Prop :=
  fun a b => E a.1 b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

/-- The fibre of a set of blow-up vertices over the vertex `v`. -/
private def blowupFib {X : Type*} [DecidableEq X] {m : ℕ} (W : Finset (X × Fin m)) (v : X) :
    Finset (Fin m) :=
  univ.filter (fun a => (v, a) ∈ W)

@[simp] private theorem mem_blowupFib {X : Type*} [DecidableEq X] {m : ℕ} (W : Finset (X × Fin m))
    (v : X) (a : Fin m) : a ∈ blowupFib W v ↔ (v, a) ∈ W := by
  simp [blowupFib]

/-- A set of blow-up vertices is the disjoint union of its fibres. -/
private theorem card_eq_sum_blowupFib {X : Type*} [Fintype X] [DecidableEq X] {m : ℕ}
    (W : Finset (X × Fin m)) : W.card = ∑ v, (blowupFib W v).card := by
  have h1 : W.card = ∑ p : X × Fin m, if p ∈ W then 1 else 0 := by
    rw [Finset.sum_boole]; simp
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [blowupFib, Finset.card_filter]

/-- The blow-up of an oriented graph is oriented. -/
private theorem blowup_oriented {X : Type*} (E : X → X → Prop) (hE : Oriented E) (m : ℕ) :
    Oriented (blowup E m) := by
  rintro ⟨x, a⟩ ⟨y, b⟩ h1 h2
  simp only [blowup] at h1 h2
  rcases h1 with h1 | ⟨h1', h1⟩ <;> rcases h2 with h2 | ⟨h2', h2⟩
  · exact hE _ _ h1 h2
  · subst h2'; exact hE _ _ h1 h1
  · subst h1'; exact hE _ _ h2 h2
  · exact lt_asymm h1 h2

/-- If every vertex of `E` has an in-neighbour, so does every vertex of the blow-up. -/
private theorem blowup_indeg {X : Type*} (E : X → X → Prop) (hpos : ∀ y, ∃ x, E x y) (m : ℕ) :
    ∀ y, ∃ x, blowup E m x y := by
  rintro ⟨w, b⟩
  obtain ⟨u, hu⟩ := hpos w
  exact ⟨(u, b), Or.inl hu⟩

/-- The strict concavity (3) for the blow-up: `|U| + |F²(U)| < 2|F(U)|` for every nonempty
proper vertex set `U`, provided `E` has positive indegrees, satisfies the strict subset
deficit (1), and `m > |X|`. -/
private theorem blowup_concave {X : Type*} [Fintype X] [DecidableEq X]
    (E : X → X → Prop) (hpos : ∀ y, ∃ x, E x y)
    (hdef : ∀ S : Finset X, S.Nonempty → S ≠ univ →
      (image E (image E S) \ image E S).card < (image E S \ S).card)
    (m : ℕ) (hm : Fintype.card X < m) (U : Finset (X × Fin m)) (hU : U.Nonempty)
    (hU' : U ≠ univ) :
    U.card + (image (blowup E m) (image (blowup E m) U)).card <
      2 * (image (blowup E m) U).card := by
  set G := blowup E m with hG
  set F1 := image G U with hF1def
  set F2 := image G F1 with hF2def
  set S : Finset X := univ.filter (fun v => ∃ a, (v, a) ∈ U) with hS
  have memS : ∀ v, v ∈ S ↔ ∃ a, (v, a) ∈ U := by simp [S]
  by_cases hSu : S = univ
  · -- every vertex carries a point of `U`, so `F U = F² U = univ`
    have hF1 : F1 = univ := by
      apply eq_univ_of_forall
      rintro ⟨w, b⟩
      obtain ⟨u, hu⟩ := hpos w
      obtain ⟨a, ha⟩ := (memS u).1 (hSu ▸ mem_univ u)
      exact (mem_image _ _ _).2 ⟨(u, a), ha, Or.inl hu⟩
    have hF2 : F2 = univ := by
      rw [hF2def, hF1]
      exact image_univ_of_positive_indegree _ (blowup_indeg E hpos m)
    rw [hF2, hF1]
    have : U.card < (univ : Finset (X × Fin m)).card := card_lt_card (ssubset_univ_iff.2 hU')
    omega
  · set A := image E S with hA
    set B := image E A \ A with hB
    have hSne : S.Nonempty := by
      obtain ⟨⟨v, a⟩, h⟩ := hU
      exact ⟨v, (memS v).2 ⟨a, h⟩⟩
    have hd : B.card < (A \ S).card := hdef S hSne hSu
    have hSA : (S \ A).card < m := lt_of_le_of_lt (card_le_univ _) hm
    -- per-vertex facts
    have fe : ∀ v, v ∉ S → (blowupFib U v).card = 0 := by
      intro v hv
      rw [card_eq_zero, eq_empty_iff_forall_notMem]
      intro a ha
      exact hv ((memS v).2 ⟨a, (mem_blowupFib _ _ _).1 ha⟩)
    have fa : ∀ v, (blowupFib U v).card ≤
        (blowupFib F1 v).card + (if v ∈ S then 1 else 0) := by
      intro v
      by_cases hv : v ∈ S
      · have hne : (blowupFib U v).Nonempty := by
          obtain ⟨a, ha⟩ := (memS v).1 hv
          exact ⟨a, (mem_blowupFib _ _ _).2 ha⟩
        set a1 := (blowupFib U v).min' hne
        have ha1 : (v, a1) ∈ U := (mem_blowupFib _ _ _).1 (min'_mem _ _)
        have hsub : blowupFib U v ⊆ insert a1 (blowupFib F1 v) := by
          intro a ha
          by_cases h : a = a1
          · rw [h]; exact mem_insert_self _ _
          · apply mem_insert_of_mem
            have hlt : a1 < a := lt_of_le_of_ne (min'_le _ _ ha) (Ne.symm h)
            exact (mem_blowupFib _ _ _).2
              ((mem_image _ _ _).2 ⟨(v, a1), ha1, Or.inr ⟨rfl, hlt⟩⟩)
        have := (card_le_card hsub).trans (card_insert_le _ _)
        simpa [hv] using this
      · rw [fe v hv]
        exact Nat.zero_le _
    have fb : ∀ v, v ∈ A → (blowupFib F1 v).card = m := by
      intro v hv
      have : blowupFib F1 v = univ := by
        apply eq_univ_of_forall
        intro b
        obtain ⟨u, hu, huv⟩ := (mem_image _ _ _).1 hv
        obtain ⟨a, ha⟩ := (memS u).1 hu
        exact (mem_blowupFib _ _ _).2 ((mem_image _ _ _).2 ⟨(u, a), ha, Or.inl huv⟩)
      rw [this, card_univ, Fintype.card_fin]
    have fd : ∀ v, v ∉ A → v ∉ image E A →
        (blowupFib F2 v).card ≤ (blowupFib F1 v).card := by
      intro v hvA hvA2
      apply card_le_card
      intro c hc
      obtain ⟨⟨w, b⟩, hwb, hG2⟩ := (mem_image _ _ _).1 ((mem_blowupFib _ _ _).1 hc)
      obtain ⟨⟨u, a⟩, hua, hG1⟩ := (mem_image _ _ _).1 hwb
      have huS : u ∈ S := (memS u).2 ⟨a, hua⟩
      rcases hG2 with h2 | ⟨h2', h2⟩ <;> rcases hG1 with h1 | ⟨h1', h1⟩
      · exact absurd ((mem_image _ _ _).2 ⟨w, (mem_image _ _ _).2 ⟨u, huS, h1⟩, h2⟩) hvA2
      · simp only at h1' h2; subst h1'
        exact absurd ((mem_image _ _ _).2 ⟨u, huS, h2⟩) hvA
      · simp only at h2' h1; subst h2'
        exact absurd ((mem_image _ _ _).2 ⟨u, huS, h1⟩) hvA
      · simp only at h1' h2' h1 h2; subst h1'; subst h2'
        exact (mem_blowupFib _ _ _).2
          ((mem_image _ _ _).2 ⟨(u, a), hua, Or.inr ⟨rfl, h1.trans h2⟩⟩)
    have fm : ∀ (W : Finset (X × Fin m)) v, (blowupFib W v).card ≤ m := by
      intro W v
      simpa using card_le_univ (blowupFib W v)
    -- the per-vertex inequality
    have key : ∀ v, ((blowupFib U v).card : ℤ) + (blowupFib F2 v).card
          - 2 * (blowupFib F1 v).card ≤
        m * (if v ∈ B then 1 else 0) + (if v ∈ S \ A then 1 else 0)
          - m * (if v ∈ A \ S then 1 else 0) := by
      intro v
      have h1 := fa v
      have h2 : ((blowupFib U v).card : ℤ) ≤ m := by exact_mod_cast fm U v
      have h3 : ((blowupFib F2 v).card : ℤ) ≤ m := by exact_mod_cast fm F2 v
      have h1' : ((blowupFib U v).card : ℤ) ≤
          (blowupFib F1 v).card + (if v ∈ S then 1 else 0) := by
        split_ifs at h1 ⊢ <;> omega
      by_cases hvA : v ∈ A
      · have h5 : ((blowupFib F1 v).card : ℤ) = m := by exact_mod_cast fb v hvA
        have nB : v ∉ B := fun h => (mem_sdiff.1 h).2 hvA
        have nSA : v ∉ S \ A := fun h => (mem_sdiff.1 h).2 hvA
        rw [ite_eq_right nB, ite_eq_right nSA]
        by_cases hvS : v ∈ S
        · have nAS : v ∉ A \ S := fun h => (mem_sdiff.1 h).2 hvS
          rw [ite_eq_right nAS]
          linarith
        · have yAS : v ∈ A \ S := mem_sdiff.2 ⟨hvA, hvS⟩
          rw [ite_eq_left yAS]
          have h0 : ((blowupFib U v).card : ℤ) = 0 := by exact_mod_cast fe v hvS
          linarith
      · have nAS : v ∉ A \ S := fun h => hvA (mem_sdiff.1 h).1
        rw [ite_eq_right nAS]
        have hSA' : (if v ∈ S \ A then (1 : ℤ) else 0) = if v ∈ S then 1 else 0 := by
          by_cases hvS : v ∈ S
          · rw [ite_eq_left (mem_sdiff.2 ⟨hvS, hvA⟩), ite_eq_left hvS]
          · rw [ite_eq_right (fun h => hvS (mem_sdiff.1 h).1), ite_eq_right hvS]
        rw [hSA']
        by_cases hvA2 : v ∈ image E A
        · have yB : v ∈ B := mem_sdiff.2 ⟨hvA2, hvA⟩
          rw [ite_eq_left yB]
          have h0 : (0 : ℤ) ≤ (blowupFib F1 v).card := by positivity
          linarith
        · have h5 : ((blowupFib F2 v).card : ℤ) ≤ (blowupFib F1 v).card := by
            exact_mod_cast fd v hvA hvA2
          have nB : v ∉ B := fun h => hvA2 (mem_sdiff.1 h).1
          rw [ite_eq_right nB]
          linarith
    -- sum over all vertices
    have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset X)) => key v)
    have eL : (∑ v, (((blowupFib U v).card : ℤ) + (blowupFib F2 v).card
          - 2 * (blowupFib F1 v).card)) = (U.card : ℤ) + F2.card - 2 * F1.card := by
      rw [card_eq_sum_blowupFib U, card_eq_sum_blowupFib F1, card_eq_sum_blowupFib F2]
      push_cast
      rw [sum_sub_distrib, sum_add_distrib, mul_sum]
    have hind : ∀ T : Finset X, (∑ v, (if v ∈ T then (1 : ℤ) else 0)) = T.card := by
      intro T
      rw [sum_boole]
      simp
    have eR : (∑ v, ((m : ℤ) * (if v ∈ B then 1 else 0) + (if v ∈ S \ A then 1 else 0)
          - m * (if v ∈ A \ S then 1 else 0))) =
          m * B.card + (S \ A).card - m * (A \ S).card := by
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, hind, hind, hind]
    rw [eL, eR] at hsum
    have hmul : m * B.card + m ≤ m * (A \ S).card := by
      have := Nat.mul_le_mul_left m hd
      rw [Nat.mul_succ] at this
      exact this
    have hmulZ : (m : ℤ) * B.card + m ≤ m * (A \ S).card := by exact_mod_cast hmul
    have hSAZ : ((S \ A).card : ℤ) < m := by exact_mod_cast hSA
    have : (U.card : ℤ) + F2.card < 2 * F1.card := by linarith
    exact_mod_cast this

/-- Lemma 2.2. Let `E` be an oriented graph on `X` in which every vertex has an in-neighbour
and `|F²(S) \ F(S)| < |F(S) \ S|` for every nonempty proper `S` (the strict subset
deficit (1)), and let `m > |X|`. Then `blowup E m` is oriented, every vertex of it has an
in-neighbour, and `|U| + |F²(U)| < 2|F(U)|` for every nonempty proper vertex set `U` (the
strict concavity (3)). -/
theorem blowup_lemma {X : Type*} [Fintype X] [DecidableEq X] (E : X → X → Prop)
    (hE : Oriented E) (hpos : ∀ y, ∃ x, E x y)
    (hdef : ∀ S : Finset X, S.Nonempty → S ≠ univ →
      (image E (image E S) \ image E S).card < (image E S \ S).card)
    (m : ℕ) (hm : Fintype.card X < m) :
    Oriented (blowup E m) ∧ (∀ y, ∃ x, blowup E m x y) ∧
      ∀ U : Finset (X × Fin m), U.Nonempty → U ≠ univ →
        U.card + (image (blowup E m) (image (blowup E m) U)).card <
          2 * (image (blowup E m) U).card :=
  ⟨blowup_oriented E hE m, blowup_indeg E hpos m,
    fun U hU hU' => blowup_concave E hpos hdef m hm U hU hU'⟩

end Seymour
