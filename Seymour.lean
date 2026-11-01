module

public import Seymour.Defs
public import Seymour.Reduction
public import Seymour.Blowup
public import Seymour.Extremal
public import Seymour.Deletion.Hall
public import Seymour.Deletion.Basic
public import Seymour.Deletion.Konig
public import Seymour.Deletion.Rank
public import Seymour.Deletion.Local
public import Seymour.Deletion.Theorem
public import Seymour.Main
public import Seymour.Consequences

/-!
# A short proof of Seymour's second-neighbourhood conjecture

Formal proof of the results of the paper, by section.

* §1 `Seymour.Defs`: oriented graphs, `F(S)`, `N₁⁺(v)`, `N₂⁺(v)`, and the statement of
  Theorem 1.1 (`SeymourStatement`).
* §2 `Seymour.Reduction`: Lemma 2.1 (`Seymour.deficit_lemma`: the strict subset deficit of a
  minimal counterexample); `Seymour.Blowup`: Lemma 2.2 (`Seymour.blowup_lemma`: the
  lexicographic blow-up).
* §3 `Seymour.Extremal`: the extremal argument, which proves Theorem 1.2
  (`Seymour.set_version`); `Seymour.Main`: Theorem 1.1 (`Seymour.seymour`, and
  `Seymour.seymour_second_neighbourhood` without auxiliary definitions).
* §4 `Seymour.Deletion.*`: the deletion lemma for general instances. `Hall`: Lemma 4.3;
  `Basic`: §4.1; `Konig`: §4.2, Lemmas 4.4–4.7; `Rank`: Lemma 4.9; `Local`: Lemmas 4.10 and
  4.11; `Theorem`: Theorem 4.12 (`Seymour.Deletion.deletion`).
* §5 `Seymour.Consequences`: Corollary 5.1 (`Seymour.weighted_real`) and Corollary 5.2
  (`Seymour.triangle_free_degree_bound`, `Seymour.directed_triangle_of_semidegree`).
-/

#print axioms Seymour.seymour
#print axioms Seymour.seymour_second_neighbourhood
#print axioms Seymour.set_version
#print axioms Seymour.Deletion.deletion
#print axioms Seymour.weighted_real
#print axioms Seymour.triangle_free_degree_bound
#print axioms Seymour.directed_triangle_of_semidegree
