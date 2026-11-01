module

public import Mathlib

/-!
# Oriented graphs and second out-neighbourhoods

A digraph on a finite type `X` is a relation `E : X → X → Prop`; `E x y` means that there
is an arc `x → y`. It is *oriented* (`Oriented E`) if it has no pair of opposite arcs, which
also excludes loops.

For a vertex set `S`, `image E S` is `F(S) = {y : x → y for some x ∈ S}`; it may meet `S`.
`outNeighbors E v` is `N₁⁺(v) = F({v})` and `secondNeighbors E v` is
`F(N₁⁺(v)) \ N₁⁺(v) = F²({v}) \ F({v})`, the vertices reached from `v` by a walk of length
two that are not out-neighbours of `v`. In an oriented graph `v` itself is not of this kind
(`notMem_secondNeighbors_self`), so this is the set `N₂⁺(v)` of vertices at directed
distance exactly two from `v`. A vertex `v` is *good* if `|N₁⁺(v)| ≤ |N₂⁺(v)|`, and
`SeymourStatement` is Theorem 1.1.
-/

@[expose] public section

namespace Seymour

/-- `E` is oriented: there are no opposite arcs `x → y` and `y → x` (in particular no
loops). -/
def Oriented {X : Type*} (E : X → X → Prop) : Prop := ∀ x y, E x y → ¬ E y x

/-- The image `F(S)` of a vertex set `S`: all heads of arcs with tail in `S`. -/
noncomputable def image {X : Type*} [Fintype X] (E : X → X → Prop)
    (S : Finset X) : Finset X := by
  classical
  exact Finset.univ.filter (fun y => ∃ x ∈ S, E x y)

/-- The out-neighbourhood `N₁⁺(v)`. -/
noncomputable def outNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v : X) : Finset X := by
  classical
  exact Finset.univ.filter (E v)

/-- The in-neighbourhood `N₁⁻(v)`. -/
noncomputable def inNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v : X) : Finset X := by
  classical
  exact Finset.univ.filter (fun u => E u v)

/-- The second out-neighbourhood `N₂⁺(v) = F(N₁⁺(v)) \ N₁⁺(v)`. -/
noncomputable def secondNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v : X) : Finset X := by
  classical
  exact image E (outNeighbors E v) \ outNeighbors E v

/-- A vertex is good if it has at most as many out-neighbours as second
out-neighbours. -/
def Good {X : Type*} [Fintype X] (E : X → X → Prop) (v : X) : Prop :=
  (outNeighbors E v).card ≤ (secondNeighbors E v).card

/-- Theorem 1.1 (Seymour's second-neighbourhood conjecture): every nonempty finite oriented
graph has a good vertex. -/
def SeymourStatement : Prop := ∀ (X : Type) [Fintype X] [Nonempty X]
  (E : X → X → Prop), Oriented E → ∃ v, Good E v

@[simp] theorem mem_image {X : Type*} [Fintype X] (E : X → X → Prop)
    (S : Finset X) (y : X) : y ∈ image E S ↔ ∃ x ∈ S, E x y := by
  simp [image]

@[simp] theorem mem_outNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v u : X) : u ∈ outNeighbors E v ↔ E v u := by
  simp [outNeighbors]

@[simp] theorem mem_inNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v u : X) : u ∈ inNeighbors E v ↔ E u v := by
  simp [inNeighbors]

@[simp] theorem mem_secondNeighbors {X : Type*} [Fintype X] (E : X → X → Prop)
    (v u : X) : u ∈ secondNeighbors E v ↔ (∃ w, E v w ∧ E w u) ∧ ¬ E v u := by
  simp [secondNeighbors]

/-- In an oriented graph no vertex is its own second out-neighbour. -/
theorem notMem_secondNeighbors_self {X : Type*} [Fintype X] {E : X → X → Prop}
    (hE : Oriented E) (v : X) : v ∉ secondNeighbors E v := by
  simp only [mem_secondNeighbors]
  rintro ⟨⟨w, hvw, hwv⟩, _⟩
  exact hE v w hvw hwv

theorem image_mono {X : Type*} [Fintype X] (E : X → X → Prop)
    {S T : Finset X} (h : S ⊆ T) : image E S ⊆ image E T := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := (mem_image E S y).mp hy
  exact (mem_image E T y).mpr ⟨x, h hx, hxy⟩

@[simp] theorem image_empty {X : Type*} [Fintype X] (E : X → X → Prop) :
    image E ∅ = ∅ := by
  ext y
  simp

theorem image_union {X : Type*} [Fintype X] [DecidableEq X] (E : X → X → Prop)
    (S T : Finset X) : image E (S ∪ T) = image E S ∪ image E T := by
  ext y
  simp only [mem_image, Finset.mem_union]
  aesop

/-- If every vertex has an in-neighbour, then `F(X) = X`. -/
theorem image_univ_of_positive_indegree {X : Type*} [Fintype X]
    (E : X → X → Prop) (h : ∀ y, ∃ x, E x y) : image E Finset.univ = Finset.univ := by
  ext y
  simp [h y]

end Seymour
