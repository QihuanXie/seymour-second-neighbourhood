# A short combinatorial proof of Seymour's second neighbourhood conjecture

[![Lean build](https://github.com/QihuanXie/seymour-second-neighbourhood/actions/workflows/ci.yml/badge.svg)](https://github.com/QihuanXie/seymour-second-neighbourhood/actions/workflows/ci.yml)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23852411.svg)](https://doi.org/10.5281/zenodo.23852411)

This repository contains the paper and its Lean 4 formalization.

> **Theorem (Seymour's second neighbourhood conjecture).** Every nonempty finite oriented graph
> has a vertex with at least as many vertices at directed distance exactly two as at directed
> distance one.

- **Paper:** [`paper/seymour_simplified_proof.pdf`](paper/seymour_simplified_proof.pdf)
  (LaTeX source: [`paper/seymour_simplified_proof.tex`](paper/seymour_simplified_proof.tex)).
- **Formalization:** the Lean library `Seymour` (Lean 4 `v4.36.0-rc2`, Mathlib `v4.36.0-rc2`).
  It checks every numbered lemma, theorem and corollary of the paper (Theorem 1.3 is an informal
  version of Theorem 3.1). The deletion lemma, Theorem 3.1, is checked for general instances.
  The docstrings in the Lean sources use the numbering of version 1.0.0 of the paper; the table
  below gives both numberings. The Lean code is unchanged since version 1.0.0.

The proof is purely combinatorial; its only external ingredient is Hall's theorem. The main
ingredient is a deletion lemma for two families of ordered pairs. It is proved by an induction
driven by Hall's defect theorem, with greedy matchings and double counting in the saturated case.
The overall reduction follows the first proof of the conjecture, released by OpenAI in 2026
([openai/math](https://github.com/openai/math)).

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
lake exe cache get    # download the precompiled Mathlib
lake build            # build the library Seymour
```

- The build produces no warnings and contains no `sorry`.
- `Seymour.lean` prints the axioms of the main results. Each depends only on `propext`,
  `Classical.choice` and `Quot.sound`.
- `lake env lean scripts/DepCheck.lean` traverses the proof terms of the main results. It confirms
  that none of them uses a constant from Mathlib's linear algebra (matrices, linear maps,
  submodules, ranks, polynomial rings, fraction fields).
- [`verification.log`](verification.log) records a clean build, the axioms, the traversal and the
  SHA-256 checksums of the sources.

The statement of Theorem 1.1 that is checked, `Seymour.seymour_second_neighbourhood`, uses no
definitions from the development:

```lean
theorem seymour_second_neighbourhood (X : Type) [Finite X] [Nonempty X] (E : X → X → Prop)
    (hE : ∀ x y, E x y → ¬ E y x) :
    ∃ v, Nat.card {u // E v u} ≤ Nat.card {u // ¬ E v u ∧ ∃ w, E v w ∧ E w u}
```

## Results of the paper and their Lean names

| Paper (v1.1.0) | Paper (v1.0.0) | Lean |
|---|---|---|
| Theorem 1.1 | Theorem 1.1 | `Seymour.seymour : SeymourStatement`; unfolded: `Seymour.seymour_second_neighbourhood` |
| Theorem 1.2 | Theorem 1.2 | `Seymour.set_version` |
| Lemma 2.1 | Lemma 2.1 | `Seymour.deficit_lemma`; `Seymour.exists_minimal_counterexample` |
| Lemma 2.2 | Lemma 2.2 | `Seymour.blowup_lemma` |
| Theorem 3.1 (informal version: Theorem 1.3) | Theorem 4.12 | `Seymour.Deletion.deletion` (general instances) |
| Lemma 5.1 | Lemma 4.11 | `Seymour.Deletion.count_lemma` |
| defect form of Hall's theorem (Section 5.1) | Lemma 4.3 | `Seymour.Deletion.hall_defect` |
| min-cut formula for λ (Section 5.2) | Lemma 4.4 | `Seymour.Deletion.konig` |
| inequality (7) | Lemma 4.5 | `Seymour.Deletion.lam_bisub` |
| inequalities (8) and the facts around them | Corollary 4.6 (a)–(d) | `Seymour.Deletion.incr_anti`, `incr_mono`, `incr_le_one`, `lam_N_self` |
| Lemma 5.2 | Lemma 4.7 | `Seymour.Deletion.card_greedy`, `Seymour.Deletion.lam_of_subset_greedy` |
| Lemma 5.3 | Lemma 4.10 | `Seymour.Deletion.local_lemma` |
| Lemma 5.4 | Lemma 4.9 | `Seymour.Deletion.rank_lemma` |
| Corollary 6.1 | Corollary 5.1 | `Seymour.weighted_real` |
| Corollary 6.2 | Corollary 5.2 | `Seymour.triangle_free_degree_bound`, `Seymour.directed_triangle_of_semidegree` |

## Repository layout

```
paper/                        the paper (LaTeX source and PDF) and its licence
Seymour.lean                  root of the library; prints the axioms of the main results
Seymour/Defs.lean             oriented graphs, F(S), N₁⁺, N₂⁺, statement of Theorem 1.1
Seymour/Reduction.lean        Lemma 2.1
Seymour/Blowup.lean           Lemma 2.2
Seymour/Extremal.lean         Section 4: extremal compatible pairs, Theorem 1.2
Seymour/Main.lean             Theorem 1.1
Seymour/Deletion/Hall.lean    defect form of Hall's theorem (Section 5.1)
Seymour/Deletion/Basic.lean   Section 3: instances, Z, H, blocks, matching numbers, the symmetry σ
Seymour/Deletion/Konig.lean   Section 5.2: λ, (7), (8), Lemma 5.2
Seymour/Deletion/Rank.lean    Lemma 5.4
Seymour/Deletion/Local.lean   Lemmas 5.3 and 5.1
Seymour/Deletion/Theorem.lean Theorem 3.1
Seymour/Consequences.lean     Corollaries 6.1 and 6.2
scripts/DepCheck.lean         proof-term traversal
verification.log              record of a clean build
```

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff). The repository is archived on Zenodo:

- all versions: [10.5281/zenodo.23852411](https://doi.org/10.5281/zenodo.23852411)
- version 1.0.0: [10.5281/zenodo.23852412](https://doi.org/10.5281/zenodo.23852412)

```bibtex
@software{xie_seymour_2026,
  author    = {Xie, Qihuan},
  title     = {A short combinatorial proof of {Seymour}'s second neighbourhood conjecture},
  year      = {2026},
  publisher = {Zenodo},
  version   = {1.1.0},
  doi       = {10.5281/zenodo.23852411},
  url       = {https://doi.org/10.5281/zenodo.23852411}
}
```

## Licence

- The Lean code and scripts are licensed under the Apache License 2.0 ([`LICENSE`](LICENSE)).
- The paper in [`paper/`](paper/) is licensed under the Creative Commons Attribution 4.0
  International licence ([`paper/LICENSE`](paper/LICENSE)).

Copyright © 2026 Qihuan Xie.

## Acknowledgements

Parts of the proofs, and the Lean formalization, were developed with the assistance of the AI
model Claude Opus 5.5 (Anthropic). The author takes full responsibility for the content.
