module

public import Seymour.Reduction
public import Seymour.Blowup
public import Seymour.Extremal

/-!
# Theorem 1.1

`seymour` (Theorem 1.1) is proved as at the end of Section 3. If it failed, it would have a
counterexample with the fewest vertices and, among those, the fewest arcs
(`exists_minimal_counterexample`). By Lemma 2.1 (`deficit_lemma`) every vertex of it has an
in-neighbour and it satisfies the strict subset deficit (1). By Lemma 2.2 (`blowup_lemma`) its
blow-up by `Fin (n + 1)`, where `n` is the number of vertices, would be an oriented graph with
positive indegrees satisfying the strict concavity (3) on every nonempty proper vertex set,
contradicting Theorem 1.2 (`set_version`).

`seymour_second_neighbourhood` restates Theorem 1.1 without the definitions of
`Seymour.Defs`.
-/

@[expose] public section

namespace Seymour

/-- Theorem 1.1 (Seymour's second-neighbourhood conjecture). Every nonempty finite oriented
graph has a vertex `v` with `|N₁⁺(v)| ≤ |N₂⁺(v)|`. -/
theorem seymour : SeymourStatement := by
  classical
  by_contra h
  obtain ⟨X, _, _, E, hE, hbad, hvert, harcs⟩ := exists_minimal_counterexample h
  obtain ⟨-, hin, hdef⟩ := deficit_lemma E hE hbad hvert harcs
  obtain ⟨hO, hI, hconc⟩ :=
    blowup_lemma E hE hin hdef (Fintype.card X + 1) (Nat.lt_succ_self _)
  obtain ⟨U, hU, hUu, hineq⟩ := set_version _ (blowup E (Fintype.card X + 1)) hO hI
  have := hconc U hU hUu
  omega

/-- Theorem 1.1, stated with no auxiliary definitions: if `E` is a relation on a nonempty
finite type with no `x, y` such that `E x y` and `E y x`, then some `v` has at most as many
out-neighbours `u` (`E v u`) as vertices `u` at directed distance exactly two (`¬ E v u`,
and `E v w`, `E w u` for some `w`). -/
theorem seymour_second_neighbourhood (X : Type) [Finite X] [Nonempty X] (E : X → X → Prop)
    (hE : ∀ x y, E x y → ¬ E y x) :
    ∃ v, Nat.card {u // E v u} ≤ Nat.card {u // ¬ E v u ∧ ∃ w, E v w ∧ E w u} := by
  have := Fintype.ofFinite X
  obtain ⟨v, hv⟩ := seymour X E hE
  refine ⟨v, ?_⟩
  have h1 : Nat.card {u // E v u} = (outNeighbors E v).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => (mem_outNeighbors E v u).symm)
  have h2 : Nat.card {u // ¬ E v u ∧ ∃ w, E v w ∧ E w u} = (secondNeighbors E v).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun u => by rw [mem_secondNeighbors, and_comm])
  rw [h1, h2]
  exact hv

end Seymour
