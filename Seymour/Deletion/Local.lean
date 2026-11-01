module

public import Seymour.Deletion.Rank

/-!
# Lemma 4.10 (local lemma) and Lemma 4.11 (counting lemma)

The local lemma is proved by a weighted form of Hall's theorem, applied to all of `R` at
once. The member `r = (p,j)` gets weight `#{s : s → j, ∃ (i,s) ∈ C, p → i}` and the point
`z = (i,j)` gets weight `#{s : s → j, (i,s) ∈ C}`; the weight inequality comes from the
matching of `Γ_C` saturating `H`. The counting lemma applies the local lemma to the instance
and to its image under the symmetry `σ`, and then uses Lemma 4.9.
-/

@[expose] public section

namespace Seymour.Deletion
open Finset

/-! ### A weighted form of Hall's theorem -/

/-- Hall's theorem for a finset of left vertices. -/
private theorem hall_finset {A B : Type*} [DecidableEq B] (t : A → Finset B) (S : Finset A)
    (h : ∀ W ⊆ S, W.card ≤ (W.biUnion t).card) :
    ∃ f : ↥S → B, Function.Injective f ∧ ∀ x : ↥S, f x ∈ t (x : A) := by
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' (fun x : ↥S => t x)).mp
  intro s
  have hs := h (s.map (Function.Embedding.subtype _)) (by
    intro a ha
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ha
    exact x.2)
  rw [Finset.card_map] at hs
  have heq : (s.map (Function.Embedding.subtype _)).biUnion t =
      s.biUnion (fun x : ↥S => t x) := by
    ext b
    simp
  rwa [heq] at hs

/-- Weighted Hall: if every left vertex has weight at least `1`, weights do not increase
along edges, and every left set has at most the total weight of its neighbourhood, then
Hall's condition holds. -/
private theorem weighted_hall {A B : Type*} [DecidableEq B] (t : A → Finset B)
    (S : Finset A) (m : A → ℕ) (n : B → ℕ)
    (h1 : ∀ a ∈ S, 1 ≤ m a)
    (h2 : ∀ a ∈ S, ∀ b ∈ t a, n b ≤ m a)
    (h3 : ∀ W ⊆ S, ∑ a ∈ W, m a ≤ ∑ b ∈ W.biUnion t, n b) :
    ∀ W ⊆ S, W.card ≤ (W.biUnion t).card := by
  classical
  intro W
  induction W using Finset.strongInduction with
  | H W ih =>
    intro hWS
    by_contra hlt
    push Not at hlt
    obtain ⟨w, hw⟩ : W.Nonempty := by
      rcases W.eq_empty_or_nonempty with h | h
      · subst h; simp at hlt
      · exact h
    have hW'S : W.erase w ⊆ S := (Finset.erase_subset w W).trans hWS
    obtain ⟨μ, hμi, hμt⟩ := hall_finset t (W.erase w) (fun V hV =>
      ih V (lt_of_le_of_lt hV (Finset.erase_ssubset hw)) (hV.trans hW'S))
    have himg_sub : (univ : Finset ↥(W.erase w)).image μ ⊆ W.biUnion t := by
      intro b hb
      obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hb
      exact Finset.mem_biUnion.mpr ⟨x, Finset.mem_of_mem_erase x.2, hμt x⟩
    have himg_card : ((univ : Finset ↥(W.erase w)).image μ).card = (W.erase w).card := by
      rw [Finset.card_image_of_injective _ hμi, Finset.card_univ, Fintype.card_coe]
    have hWc : (W.erase w).card + 1 = W.card := Finset.card_erase_add_one hw
    have himg_eq : (univ : Finset ↥(W.erase w)).image μ = W.biUnion t :=
      Finset.eq_of_subset_of_card_le himg_sub (by omega)
    have hs1 : ∑ b ∈ W.biUnion t, n b = ∑ x : ↥(W.erase w), n (μ x) := by
      rw [← himg_eq, Finset.sum_image (fun x _ y _ hxy => hμi hxy)]
    have hs2 : ∑ x : ↥(W.erase w), n (μ x) ≤ ∑ x : ↥(W.erase w), m x :=
      Finset.sum_le_sum (fun x _ => h2 x (hW'S x.2) (μ x) (hμt x))
    have hs3 : ∑ x : ↥(W.erase w), m x = ∑ a ∈ W.erase w, m a :=
      Finset.sum_coe_sort (W.erase w) m
    have hs4 : m w + ∑ a ∈ W.erase w, m a = ∑ a ∈ W, m a :=
      Finset.add_sum_erase W m hw
    have h3W := h3 W hWS
    have h1w := h1 w (hWS hw)
    omega

/-! ### The local lemma and the counting lemma -/

variable {X₁ X₂ X₃ X₄ : Type*} [Fintype X₁] [Fintype X₂] [Fintype X₃] [Fintype X₄]
  (α : X₁ → X₂ → Prop) (β : X₃ → X₄ → Prop) (R : Finset (X₁ × X₄)) (C : Finset (X₂ × X₃))

/-- Lemma 4.10: if every member of `R` is in a conflict and `Γ_C` has a matching
saturating `H`, then `Γ_L` has a matching saturating `R`. -/
theorem local_lemma (hR : ∀ r ∈ R, ∃ c ∈ C, Conflict α β r c)
    (hC : nuC α β R C = (H α β R C).card) : nuL α β R C = R.card := by
  classical
  obtain ⟨g, hgi, hg⟩ := (matchingNumber_eq_card_iff _).mp
    (show nuC α β R C = Fintype.card ↥(H α β R C) by rw [Fintype.card_coe]; exact hC)
  let S : X₁ × X₄ → Finset X₃ := fun r =>
    univ.filter fun s => β s r.2 ∧ ∃ i, (i, s) ∈ C ∧ α r.1 i
  let T : X₂ × X₄ → Finset X₃ := fun z =>
    univ.filter fun s => β s z.2 ∧ (z.1, s) ∈ C
  have hS (r : X₁ × X₄) (s : X₃) : s ∈ S r ↔ β s r.2 ∧ ∃ i, (i, s) ∈ C ∧ α r.1 i := by
    simp [S]
  have hT (z : X₂ × X₄) (s : X₃) : s ∈ T z ↔ β s z.2 ∧ (z.1, s) ∈ C := by
    simp [T]
  have hH : ∀ r ∈ R, ∀ s ∈ S r, (r.1, s) ∈ H α β R C := by
    intro r hr s hs
    obtain ⟨hsj, i, his, hpi⟩ := (hS r s).mp hs
    exact (mem_H α β R C _).mpr ⟨i, r.2, hr, his, hpi, hsj⟩
  have h1 : ∀ r ∈ R, 1 ≤ (S r).card := by
    intro r hr
    obtain ⟨c, hc, hpi, hsj⟩ := hR r hr
    exact Finset.card_pos.mpr ⟨c.2, (hS r c.2).mpr ⟨hsj, c.1, hc, hpi⟩⟩
  have h2 : ∀ r ∈ R, ∀ z ∈ coverL α β R C r, (T z).card ≤ (S r).card := by
    intro r _ z hz
    obtain ⟨-, hzr, hpz⟩ := (mem_coverL α β R C r z).mp hz
    apply Finset.card_le_card
    intro s hs
    obtain ⟨hsz, hzs⟩ := (hT z s).mp hs
    exact (hS r s).mpr ⟨hzr ▸ hsz, z.1, hzs, hpz⟩
  have h3 : ∀ W ⊆ R,
      ∑ r ∈ W, (S r).card ≤ ∑ z ∈ W.biUnion (coverL α β R C), (T z).card := by
    intro W hW
    rw [← Finset.card_sigma, ← Finset.card_sigma]
    refine Finset.card_le_card_of_forall_subsingleton
      (fun x y => y.1.2 = x.1.2 ∧
        ∃ hx : (x.1.1, x.2) ∈ H α β R C, g ⟨_, hx⟩ = (y.1.1, y.2)) ?_ ?_
    · rintro ⟨⟨p, j⟩, s⟩ hx
      obtain ⟨hr, hs⟩ := Finset.mem_sigma.mp hx
      have hps := hH _ (hW hr) s hs
      obtain ⟨hgC, hg2, hgα⟩ := (mem_blockC α C _ _).mp (hg ⟨_, hps⟩)
      have hc : ((g ⟨_, hps⟩).1, s) ∈ C := by
        have e : ((g ⟨_, hps⟩).1, s) = g ⟨_, hps⟩ := Prod.ext rfl hg2.symm
        rw [e]
        exact hgC
      have hsj : β s j := ((hS _ s).mp hs).1
      refine ⟨⟨((g ⟨_, hps⟩).1, j), s⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, rfl, hps,
        Prod.ext rfl hg2⟩
      · refine Finset.mem_biUnion.mpr ⟨(p, j), hr, (mem_coverL α β R C _ _).mpr ⟨?_, rfl, hgα⟩⟩
        exact (mem_Z α β R C _).mpr ⟨p, s, hW hr, hc, hgα, hsj⟩
      · exact (hT _ s).mpr ⟨hsj, hc⟩
    · rintro y - ⟨⟨p, j⟩, s⟩ ⟨-, hj, hx, hxy⟩ ⟨⟨p', j'⟩, s'⟩ ⟨-, hj', hx', hxy'⟩
      have e := congrArg Subtype.val (hgi (hxy.trans hxy'.symm))
      simp only [Prod.mk.injEq] at e hj hj'
      obtain ⟨rfl, rfl⟩ := e
      rw [← hj, ← hj']
  obtain ⟨f, hfi, hft⟩ := hall_finset (coverL α β R C) R
    (weighted_hall _ R (fun r => (S r).card) (fun z => (T z).card) h1 h2 h3)
  have hL : nuL α β R C = Fintype.card ↥R :=
    (matchingNumber_eq_card_iff _).mpr ⟨f, hfi, hft⟩
  rwa [Fintype.card_coe] at hL

/-- Lemma 4.11: if every member is in a conflict and both `Γ_R` and `Γ_C` have
matchings saturating `H`, then `|R| + |C| ≤ |Z| + |H|`. -/
theorem count_lemma (hR : ∀ r ∈ R, ∃ c ∈ C, Conflict α β r c)
    (hC : ∀ c ∈ C, ∃ r ∈ R, Conflict α β r c)
    (hHR : nuR α β R C = (H α β R C).card) (hHC : nuC α β R C = (H α β R C).card) :
    R.card + C.card ≤ (Z α β R C).card + (H α β R C).card := by
  have hL : nuL α β R C = R.card := local_lemma α β R C hR hHC
  have hσ : nuL β α (tr C) (tr R) = (tr C).card := by
    refine local_lemma β α (tr C) (tr R) ?_ ?_
    · intro c' hc'
      obtain ⟨r, hr, hrc⟩ := hC _ ((mem_tr C c').mp hc')
      exact ⟨(r.2, r.1), (mem_tr R _).mpr hr, (conflict_sigma α β r _).mpr hrc⟩
    · rw [nuC_sigma, H_sigma, card_tr]
      exact hHR
  have hN : nuN α β R C = C.card := by
    rw [← nuL_sigma, hσ, card_tr]
  have hrank := rank_lemma α β R C
  have hRH := nuR_le_card_H α β R C
  omega

end Seymour.Deletion
