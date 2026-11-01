module

public import Seymour.Main

/-!
# Section 5: two consequences

* Corollary 5.1 (weighted form, `weighted_real`): for every nonempty finite oriented graph
  and all weights `w : X → ℝ` with `w ≥ 0`, some vertex `v` has `w(N₁⁺(v)) ≤ w(N₂⁺(v))`.
  For positive integer weights (`weighted_nat`) Theorem 1.1 is applied to the graph in which
  every vertex `x` is replaced by `w(x)` copies; general weights follow by approximation,
  since for each `v` the set of weight vectors satisfying the inequality is closed.
* Corollary 5.2 (directed triangles): an oriented graph on `n ≥ 1` vertices without a
  directed triangle has a vertex with `2|N₁⁺(v)| + |N₁⁻(v)| ≤ n - 1`
  (`triangle_free_degree_bound`); hence an oriented graph in which every vertex has at least
  `n/3` out-neighbours and at least `n/3` in-neighbours contains a directed triangle
  (`directed_triangle_of_semidegree`).
-/

@[expose] public section

namespace Seymour

/-- `E` has no directed triangle `a → b → c → a`. -/
def TriangleFree {X : Type*} (E : X → X → Prop) : Prop :=
  ∀ a b c, E a b → E b c → ¬ E c a

/-- Corollary 5.2, first part: a nonempty finite oriented graph without directed triangles
has a vertex `v` with `2|N₁⁺(v)| + |N₁⁻(v)| ≤ n - 1`, where `n = |X|`. -/
theorem triangle_free_degree_bound (X : Type) [Fintype X] [Nonempty X]
    (E : X → X → Prop) (ho : Oriented E) (ht : TriangleFree E) :
    ∃ v, 2 * (outNeighbors E v).card + (inNeighbors E v).card + 1 ≤ Fintype.card X := by
  classical
  obtain ⟨v, hv⟩ := seymour X E ho
  refine ⟨v, ?_⟩
  have doi : Disjoint (outNeighbors E v) (inNeighbors E v) := by
    simp only [Finset.disjoint_left, mem_outNeighbors, mem_inNeighbors]
    exact fun x h1 h2 => ho v x h1 h2
  have dos : Disjoint (outNeighbors E v) (secondNeighbors E v) := by
    simp only [Finset.disjoint_left, mem_outNeighbors, mem_secondNeighbors]
    exact fun x hx hs => hs.2 hx
  have dis : Disjoint (inNeighbors E v) (secondNeighbors E v) := by
    simp only [Finset.disjoint_left, mem_inNeighbors, mem_secondNeighbors]
    rintro x hx ⟨⟨w, hvw, hwx⟩, _⟩
    exact ht v w x hvw hwx hx
  have hself : v ∉ outNeighbors E v ∪ inNeighbors E v ∪ secondNeighbors E v := by
    simp only [Finset.mem_union, mem_outNeighbors, mem_inNeighbors, not_or]
    exact ⟨⟨fun h => ho v v h h, fun h => ho v v h h⟩, notMem_secondNeighbors_self ho v⟩
  have hc := Finset.card_le_univ
    (insert v (outNeighbors E v ∪ inNeighbors E v ∪ secondNeighbors E v))
  rw [Finset.card_insert_of_notMem hself, Finset.card_union_of_disjoint
    (Finset.disjoint_union_left.mpr ⟨dos, dis⟩), Finset.card_union_of_disjoint doi] at hc
  unfold Good at hv
  omega

/-- Corollary 5.2, second part: a nonempty finite oriented graph on `n` vertices in which every
vertex has at least `n/3` out-neighbours and at least `n/3` in-neighbours contains a directed
triangle. -/
theorem directed_triangle_of_semidegree (X : Type) [Fintype X] [Nonempty X]
    (E : X → X → Prop) (ho : Oriented E)
    (hout : ∀ v, Fintype.card X ≤ 3 * (outNeighbors E v).card)
    (hin : ∀ v, Fintype.card X ≤ 3 * (inNeighbors E v).card) :
    ∃ a b c, E a b ∧ E b c ∧ E c a := by
  by_contra hn
  have ht : TriangleFree E := by
    intro a b c hab hbc hca
    exact hn ⟨a, b, c, hab, hbc, hca⟩
  obtain ⟨v, hv⟩ := triangle_free_degree_bound X E ho ht
  have := hout v
  have := hin v
  omega

/-- Corollary 5.1 for positive integer weights: apply Theorem 1.1 to the graph with `w(x)`
copies of every vertex `x`, and an arc between copies of `x` and `y` whenever `x → y`. -/
private theorem weighted_nat (X : Type) [Fintype X] [Nonempty X]
    (E : X → X → Prop) (ho : Oriented E) (w : X → ℕ) (hw : ∀ x, 0 < w x) :
    ∃ v, ∑ x ∈ outNeighbors E v, w x ≤ ∑ x ∈ secondNeighbors E v, w x := by
  classical
  let EY : ((x : X) × Fin (w x)) → ((x : X) × Fin (w x)) → Prop := fun a b => E a.1 b.1
  have : Nonempty ((x : X) × Fin (w x)) := ⟨⟨Classical.arbitrary X, ⟨0, hw _⟩⟩⟩
  have hEY : Oriented EY := fun a b hab hba => ho a.1 b.1 hab hba
  obtain ⟨v, hv⟩ := seymour ((x : X) × Fin (w x)) EY hEY
  refine ⟨v.1, ?_⟩
  have hfirst : outNeighbors EY v =
      (outNeighbors E v.1).sigma (fun x => (Finset.univ : Finset (Fin (w x)))) := by
    ext ⟨y, k⟩
    simp [EY]
  have hsecond : secondNeighbors EY v =
      (secondNeighbors E v.1).sigma (fun x => (Finset.univ : Finset (Fin (w x)))) := by
    ext ⟨y, k⟩
    simp only [mem_secondNeighbors, Finset.mem_sigma, Finset.mem_univ, and_true]
    constructor
    · rintro ⟨⟨z, hz1, hz2⟩, hn⟩
      exact ⟨⟨z.1, hz1, hz2⟩, hn⟩
    · rintro ⟨⟨z, hz1, hz2⟩, hn⟩
      exact ⟨⟨⟨z, ⟨0, hw z⟩⟩, hz1, hz2⟩, hn⟩
  unfold Good at hv
  rw [hfirst, hsecond] at hv
  simp only [Finset.card_sigma, Finset.card_univ, Fintype.card_fin] at hv
  exact hv

/-- Corollary 5.1 (weighted form). For every nonempty finite oriented graph and all weights
`w : X → ℝ` with `w ≥ 0`, some vertex `v` has `w(N₁⁺(v)) ≤ w(N₂⁺(v))`. The weights
`(⌊(n+1) w(x)⌋ + 1)/(n+1)` are positive rationals converging to `w`, and for each `v` the set
of weight vectors satisfying the inequality is closed. -/
theorem weighted_real (X : Type) [Fintype X] [Nonempty X]
    (E : X → X → Prop) (ho : Oriented E) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    ∃ v, ∑ x ∈ outNeighbors E v, w x ≤ ∑ x ∈ secondNeighbors E v, w x := by
  classical
  let A : X → Set (X → ℝ) := fun v =>
    {u | ∑ x ∈ outNeighbors E v, u x ≤ ∑ x ∈ secondNeighbors E v, u x}
  have hclosed : IsClosed (⋃ v, A v) := by
    apply isClosed_iUnion_of_finite
    intro v
    apply isClosed_le
    · fun_prop
    · fun_prop
  let W : ℕ → X → ℝ := fun n x => ((⌊w x * (n + 1 : ℝ)⌋₊ + 1 : ℕ) : ℝ) / (n + 1)
  have hmem : ∀ n, W n ∈ ⋃ v, A v := by
    intro n
    obtain ⟨v, hv⟩ :=
      weighted_nat X E ho (fun x => ⌊w x * (n + 1 : ℝ)⌋₊ + 1) (fun _ => Nat.succ_pos _)
    apply Set.mem_iUnion.mpr
    refine ⟨v, ?_⟩
    change ∑ x ∈ outNeighbors E v, W n x ≤ ∑ x ∈ secondNeighbors E v, W n x
    dsimp [W]
    rw [← Finset.sum_div, ← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hv
  have ht : Filter.Tendsto W Filter.atTop (nhds w) := by
    apply tendsto_pi_nhds.mpr
    intro x
    have hn : Filter.Tendsto (fun n : ℕ => (n + 1 : ℝ)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have h1 := (tendsto_nat_floor_mul_div_atTop (hw x)).comp hn
    have h2 := tendsto_inv_atTop_zero.comp hn
    have h := h1.add h2
    simpa [W, Nat.cast_add, Nat.cast_one, add_div, one_div] using h
  have hfinal : w ∈ ⋃ v, A v := hclosed.mem_of_tendsto ht (Filter.Eventually.of_forall hmem)
  simpa only [Set.mem_iUnion, Set.mem_ofPred_eq, A] using hfinal

end Seymour
