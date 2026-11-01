module

public import Mathlib.Combinatorics.Hall.Finite
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

/-!
# Lemma 4.3: the defect form of Hall's theorem

A bipartite graph with parts `L` and `R` is given by the neighbourhoods `t x ⊆ R` of the
vertices `x : L`. If no matching has more than `ν < |L|` edges, then some nonempty `V ⊆ L`
has at most `|V| - |L| + ν` neighbours.

The proof follows the paper: add `|L| - ν - 1` new vertices adjacent to every vertex of `L`.
The enlarged graph has no matching saturating `L`, so Hall's theorem gives a set `V` with
fewer than `|V|` neighbours in it, and `V` is nonempty.
-/

@[expose] public section

namespace Seymour.Deletion

/-- Every matching from a subset of the left part has at most `ν` edges. -/
def MatchingBound {L R : Type*} (t : L → Finset R) (ν : ℕ) : Prop :=
  ∀ (s : Finset L) (f : s → R), Function.Injective f → (∀ x : s, f x ∈ t (x : L)) → s.card ≤ ν

/-- After adding `k` new vertices adjacent to all of `L`, a matching saturating `L` has at
most `ν` edges at old vertices and at most `k` at new ones, so `|L| ≤ ν + k`. -/
private theorem card_le_add_of_saturating {L R : Type*} [Fintype L] [DecidableEq R]
    (t : L → Finset R) (ν k : ℕ) (hb : MatchingBound t ν)
    (f : L → R ⊕ Fin k) (hf : Function.Injective f)
    (ht : ∀ x, f x ∈ (t x).image Sum.inl ∪ Finset.univ.image Sum.inr) :
    Fintype.card L ≤ ν + k := by
  classical
  let s := Finset.univ.filter fun x => (f x).isLeft
  let u := Finset.univ.filter fun x => ¬ (f x).isLeft
  have hs : s.card ≤ ν := by
    have hl (x : s) : (f x).isLeft := (Finset.mem_filter.mp x.property).2
    refine hb s (fun x => (f x).getLeft (hl x)) (fun x y hxy => ?_) fun x => ?_
    · rw [Sum.getLeft_eq_iff, Sum.inl_getLeft] at hxy
      exact Subtype.ext (hf hxy)
    · obtain ⟨a, ha⟩ := Sum.isLeft_iff.mp (hl x)
      have h := ht x
      rw [ha] at h
      simpa [ha] using h
  have hu : u.card ≤ k := by
    have hr (x : u) : (f x).isRight := Sum.not_isLeft.mp (Finset.mem_filter.mp x.property).2
    have h := Fintype.card_le_of_injective (fun x : u => (f x).getRight (hr x)) fun x y hxy => by
      rw [Sum.getRight_eq_iff, Sum.inr_getRight] at hxy
      exact Subtype.ext (hf hxy)
    simpa using h
  have hsu : s.card + u.card = Fintype.card L := by
    simpa [s, u] using Finset.card_filter_add_card_filter_not (s := Finset.univ)
      fun x => (f x).isLeft
  omega

/-- Lemma 4.3 (defect form of Hall's theorem). If every matching of `t` has at most
`ν < |L|` edges, then some nonempty `s ⊆ L` has at most `|s| - |L| + ν` neighbours. -/
theorem hall_defect {L R : Type*} [Fintype L] [DecidableEq R]
    (t : L → Finset R) (ν : ℕ) (hb : MatchingBound t ν) (hν : ν < Fintype.card L) :
    ∃ s : Finset L, s.Nonempty ∧
      (s.biUnion t).card + Fintype.card L ≤ s.card + ν := by
  classical
  let k := Fintype.card L - ν - 1
  let t' : L → Finset (R ⊕ Fin k) := fun x =>
    (t x).image Sum.inl ∪ Finset.univ.image Sum.inr
  have hno : ¬ ∃ f : L → R ⊕ Fin k, Function.Injective f ∧ ∀ x, f x ∈ t' x := by
    rintro ⟨f, hf, ht⟩
    have h := card_le_add_of_saturating t ν k hb f hf ht
    omega
  have hbad : ¬ ∀ s : Finset L, s.card ≤ (s.biUnion t').card := fun h =>
    hno ((Finset.all_card_le_biUnion_card_iff_existsInjective' t').mp h)
  push Not at hbad
  obtain ⟨s, hs⟩ := hbad
  have hsne : s.Nonempty := by
    by_contra h
    simp [Finset.not_nonempty_iff_eq_empty.mp h] at hs
  have heq : s.biUnion t' = (s.biUnion t).image Sum.inl ∪ Finset.univ.image Sum.inr := by
    ext x
    cases x with
    | inl r => simp [t']
    | inr j => simpa [t'] using (show ∃ a, a ∈ s from hsne)
  have hdis : Disjoint ((s.biUnion t).image (Sum.inl : R → R ⊕ Fin k))
      (Finset.univ.image (Sum.inr : Fin k → R ⊕ Fin k)) := by
    simp [Finset.disjoint_left]
  have hcard : (s.biUnion t').card = (s.biUnion t).card + k := by
    rw [heq, Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ Sum.inl_injective,
      Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, Fintype.card_fin]
  refine ⟨s, hsne, ?_⟩
  rw [hcard] at hs
  omega

end Seymour.Deletion
