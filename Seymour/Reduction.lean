module

public import Seymour.Defs

/-!
# Lemma 2.1: the strict subset deficit of a minimal counterexample

`deficit_lemma` is Lemma 2.1. Let `D` be a counterexample to Theorem 1.1 with the fewest
vertices and, among those, the fewest arcs. Then `F(S) ⊄ S` for every nonempty proper vertex
set `S`; in particular every vertex has an in-neighbour. Moreover `|F²(S) \ F(S)| < |F(S) \ S|`
for every nonempty proper `S`; this is the strict subset deficit (1).
`exists_minimal_counterexample` provides such a `D` if Theorem 1.1 fails.

The proof follows the paper.
* `good_of_closed_subtype`: if `F(S) ⊆ S`, a good vertex of the subgraph induced on `S` is
  good in the whole graph.
* `arcDeletion_step` is the Claim in the proof of Lemma 2.1. With `I = F(S) ∩ S`,
  `B = F(S) \ S` (the set `E` of the paper) and `g(T) = |F(T) \ (I ∪ T)|`, every `T ⊊ B`
  admits a nonempty `Q ⊆ B \ T` with `g(T ∪ Q) < g(T) + |Q|`. The proof deletes the arcs
  from `S` to `B \ T` and uses a good vertex of the smaller graph (`ArcMinimal`).
* `subsetDeficit_of_arcMinimal` iterates the Claim from `T = ∅` to `T = B` and obtains the
  strict subset deficit (1).
-/

@[expose] public section

namespace Seymour

universe u

/-- Iterating the Claim of Lemma 2.1: if `g ∅ = 0` and every `T ⊊ B` can be enlarged by a
nonempty `Q ⊆ B \ T` with `g (T ∪ Q) < g T + |Q|`, then `g B < |B|`. -/
private theorem strict_growth_finset {X : Type*} [DecidableEq X] (B : Finset X)
    (hB : B.Nonempty) (g : Finset X → ℕ) (g0 : g ∅ = 0)
    (step : ∀ T ⊆ B, T ≠ B → ∃ Q : Finset X,
      Q.Nonempty ∧ Q ⊆ B \ T ∧ g (T ∪ Q) < g T + Q.card) :
    g B < B.card := by
  let f : Finset X → ℤ := fun T => (T.card : ℤ) - g T
  obtain ⟨T, hT, hmax⟩ := B.powerset.exists_max_image f ⟨∅, by simp⟩
  have hTB : T ⊆ B := Finset.mem_powerset.mp hT
  have hT_eq : T = B := by
    by_contra hne
    obtain ⟨Q, _, hQ, hg⟩ := step T hTB hne
    have hd : Disjoint T Q := by
      apply Finset.disjoint_left.mpr
      intro x hx hxQ
      exact (Finset.mem_sdiff.mp (hQ hxQ)).2 hx
    have hU : T ∪ Q ⊆ B := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hTB hx
      · exact (Finset.mem_sdiff.mp (hQ hx)).1
    have hc := Finset.card_union_of_disjoint hd
    have hh := hmax (T ∪ Q) (Finset.mem_powerset.mpr hU)
    dsimp [f] at hh
    omega
  subst T
  obtain ⟨Q, _, hQ, hg⟩ := step ∅ (Finset.empty_subset B) (by simpa using hB.ne_empty.symm)
  have hQB : Q ⊆ B := by simpa using hQ
  have hh := hmax Q (Finset.mem_powerset.mpr hQB)
  simp only [Finset.empty_union, g0, zero_add] at hg
  dsimp [f] at hh
  omega

/-- Counting identity behind `g(T ∪ Q) - g(T) = |Λ| - |Q ∩ F(T)|` in the Claim of
Lemma 2.1, with `A = F(T)` and `B = F(Q)`. -/
private theorem image_increment_card {X : Type*} [DecidableEq X] (I T Q A B : Finset X)
    (hQT : Disjoint Q (I ∪ T)) :
    ((A ∪ B) \ (I ∪ T ∪ Q)).card + (Q ∩ A).card =
      (A \ (I ∪ T)).card + (B \ (I ∪ T ∪ Q ∪ A)).card := by
  let O := A \ (I ∪ T)
  let L := B \ (I ∪ T ∪ Q ∪ A)
  have heq : (A ∪ B) \ (I ∪ T ∪ Q) = (O \ Q) ∪ L := by
    ext x
    simp only [O, L, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hd : Disjoint (O \ Q) L := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [O, L, Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  have hi : O ∩ Q = Q ∩ A := by
    ext x
    have hh : x ∈ Q → x ∉ I ∪ T := fun hx => Finset.disjoint_left.mp hQT hx
    simp only [O, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · tauto
    · rintro ⟨hq, ha⟩
      exact ⟨⟨ha, hh hq⟩, hq⟩
  rw [heq, Finset.card_union_of_disjoint hd]
  have hc := Finset.card_sdiff_add_card_inter O Q
  rw [hi] at hc
  dsimp [O, L] at *
  omega

/-- If `F(S) ⊆ S`, then out-neighbourhoods and second out-neighbourhoods of vertices of `S`
are the same in the subgraph induced on `S` as in the whole graph; so a good vertex of the
induced subgraph is good. -/
private theorem good_of_closed_subtype {X : Type*} [Fintype X] (E : X → X → Prop)
    (S : Finset X) (hS : image E S ⊆ S) (v : S)
    (hv : Good (fun a b : S => E a b) v) : Good E v := by
  classical
  have hout : (outNeighbors (fun a b : S => E a b) v).map (Function.Embedding.subtype _) =
      outNeighbors E v := by
    ext y
    simp only [Finset.mem_map, mem_outNeighbors, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact hu
    · intro hy
      exact ⟨⟨y, hS ((mem_image E S y).mpr ⟨v, v.2, hy⟩)⟩, hy, rfl⟩
  have hsec : (secondNeighbors (fun a b : S => E a b) v).map
      (Function.Embedding.subtype _) = secondNeighbors E v := by
    ext y
    simp only [Finset.mem_map, mem_secondNeighbors, Function.Embedding.coe_subtype]
    constructor
    · rintro ⟨u, ⟨⟨w, hvw, hwu⟩, hn⟩, rfl⟩
      exact ⟨⟨w, hvw, hwu⟩, hn⟩
    · rintro ⟨⟨w, hvw, hwy⟩, hn⟩
      have hw : w ∈ S := hS ((mem_image E S w).mpr ⟨v, v.2, hvw⟩)
      have hy : y ∈ S := hS ((mem_image E S y).mpr ⟨w, hw, hwy⟩)
      exact ⟨⟨y, hy⟩, ⟨⟨⟨w, hw⟩, hvw, hwy⟩, hn⟩, rfl⟩
  unfold Good at hv ⊢
  rw [← hout, ← hsec, Finset.card_map, Finset.card_map]
  exact hv

/-- Every graph obtained from `E` by deleting at least one arc has a good vertex. This holds
for a counterexample with the fewest arcs among those on its vertex set. -/
private def ArcMinimal {X : Type*} [Fintype X] (E : X → X → Prop) : Prop :=
  ∀ E' : X → X → Prop, (∀ x y, E' x y → E x y) →
    (∃ x y, E x y ∧ ¬ E' x y) → ∃ v, Good E' v

/-- The graph `D_T` of the Claim: delete the arcs from `S` to `B \ T`. -/
private def deleteAcross {X : Type*} (E : X → X → Prop) (S B T : Finset X) :
    X → X → Prop :=
  fun x y => E x y ∧ ¬ (x ∈ S ∧ y ∈ B ∧ y ∉ T)

/-- Deleting arcs without changing `N₁⁺(v)` can only shrink `N₂⁺(v)`. -/
private theorem second_sub_of_out_eq {X : Type*} [Fintype X] {E E' : X → X → Prop}
    (h : ∀ x y, E' x y → E x y) (v : X)
    (heq : outNeighbors E' v = outNeighbors E v) :
    secondNeighbors E' v ⊆ secondNeighbors E v := by
  intro w hw
  obtain ⟨⟨u, hvu, huw⟩, hn⟩ := (mem_secondNeighbors E' v w).mp hw
  refine (mem_secondNeighbors E v w).mpr ⟨⟨u, h v u hvu, h u w huw⟩, ?_⟩
  intro hvw
  have hm : w ∈ outNeighbors E' v := by rw [heq]; exact (mem_outNeighbors E v w).mpr hvw
  exact hn ((mem_outNeighbors E' v w).mp hm)

/-- The Claim in the proof of Lemma 2.1. Let `E` be arc-minimal with no good vertex, and put
`I = F(S) ∩ S`, `B = F(S) \ S` and `g(T) = |F(T) \ (I ∪ T)|`. For every `T ⊊ B` there is a
nonempty `Q ⊆ B \ T` with `g(T ∪ Q) < g(T) + |Q|`. -/
private theorem arcDeletion_step {X : Type*} [Fintype X] [DecidableEq X] (E : X → X → Prop)
    (hmin : ArcMinimal E)
    (hbad : ∀ v, ¬ Good E v) (S T : Finset X)
    (hT : T ⊆ image E S \ S) (hne : T ≠ image E S \ S) :
    ∃ Q : Finset X, Q.Nonempty ∧ Q ⊆ (image E S \ S) \ T ∧
      (image E (T ∪ Q) \ ((image E S ∩ S) ∪ (T ∪ Q))).card <
        (image E T \ ((image E S ∩ S) ∪ T)).card + Q.card := by
  classical
  let B := image E S \ S
  let I := image E S ∩ S
  let E' := deleteAcross E S B T
  have hsub : ∀ x y, E' x y → E x y := fun _ _ h => h.1
  have hproper : ∃ x y, E x y ∧ ¬ E' x y := by
    have hBT : (B \ T).Nonempty := Finset.sdiff_nonempty.mpr (by
      intro h
      exact hne (Finset.Subset.antisymm hT h))
    obtain ⟨y, hy⟩ := hBT
    obtain ⟨hyB, hyT⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨x, hxS, hxy⟩ := (mem_image E S y).mp (Finset.mem_sdiff.mp hyB).1
    refine ⟨x, y, hxy, ?_⟩
    simp only [E', deleteAcross]
    tauto
  obtain ⟨v, hgood⟩ := hmin E' hsub hproper
  have hlost : ∃ q, E v q ∧ ¬ E' v q := by
    by_contra hn
    have hback : ∀ q, E v q → E' v q := by simpa only [not_exists, not_and, not_not] using hn
    have hout : outNeighbors E' v = outNeighbors E v := by
      ext q
      simp only [mem_outNeighbors]
      exact ⟨hsub v q, hback q⟩
    have hsecond := Finset.card_le_card (second_sub_of_out_eq hsub v hout)
    exact hbad v (by dsimp [Good] at hgood ⊢; rw [hout] at hgood; omega)
  obtain ⟨q, hvq, hnq⟩ := hlost
  have hremove : v ∈ S ∧ q ∈ B ∧ q ∉ T := by
    simpa only [E', deleteAcross, hvq, true_and, not_not] using hnq
  have hvS : v ∈ S := hremove.1
  let Q := outNeighbors E v ∩ (B \ T)
  let L := image E Q \ (I ∪ T ∪ Q ∪ image E T)
  have hQne : Q.Nonempty := ⟨q, Finset.mem_inter.mpr
    ⟨(mem_outNeighbors E v q).mpr hvq, Finset.mem_sdiff.mpr hremove.2⟩⟩
  have hQB : Q ⊆ B \ T := Finset.inter_subset_right
  have hQI : Disjoint Q (I ∪ T) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxIT
    obtain ⟨hxB, hxT⟩ := Finset.mem_sdiff.mp (hQB hx)
    obtain ⟨_, hxS⟩ := Finset.mem_sdiff.mp hxB
    rcases Finset.mem_union.mp hxIT with hi | ht
    · exact hxS (Finset.mem_inter.mp hi).2
    · exact hxT ht
  have hFS : image E S = I ∪ B := by
    ext x
    simp only [I, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hout_bound : outNeighbors E v ⊆ I ∪ T ∪ Q := by
    intro x hx
    have hxf : x ∈ image E S := (mem_image E S x).mpr ⟨v, hvS, (mem_outNeighbors E v x).mp hx⟩
    rw [hFS] at hxf
    rcases Finset.mem_union.mp hxf with hi | hb
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    · by_cases ht : x ∈ T
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ ht)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hx, Finset.mem_sdiff.mpr ⟨hb, ht⟩⟩)
  have hout_eq : outNeighbors E' v = outNeighbors E v \ Q := by
    ext x
    simp only [mem_outNeighbors, E', deleteAcross, hvS, true_and, Q,
      Finset.mem_sdiff, Finset.mem_inter, mem_outNeighbors]
    tauto
  have hnew_out : outNeighbors E' v ⊆ I ∪ T := by
    intro x hx
    rw [hout_eq] at hx
    obtain ⟨hxold, hxQ⟩ := Finset.mem_sdiff.mp hx
    have hb := hout_bound hxold
    exact (Finset.mem_union.mp hb).resolve_right hxQ
  have hwalk : image E' (outNeighbors E' v) ⊆ I ∪ T ∪ image E T := by
    intro w hw
    obtain ⟨u, hu, huw⟩ := (mem_image E' _ w).mp hw
    rcases Finset.mem_union.mp (hnew_out hu) with huI | huT
    · have huS : u ∈ S := (Finset.mem_inter.mp huI).2
      have hwF : w ∈ image E S := (mem_image E S w).mpr ⟨u, huS, huw.1⟩
      rw [hFS] at hwF
      rcases Finset.mem_union.mp hwF with hwI | hwB
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hwI)
      · have hwT : w ∈ T := by
          by_contra hn
          exact huw.2 ⟨huS, hwB, hn⟩
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hwT)
    · exact Finset.mem_union_right _ ((mem_image E T w).mpr ⟨u, huT, huw.1⟩)
  have hgain : secondNeighbors E' v \ secondNeighbors E v ⊆ Q ∩ image E T := by
    intro w hw
    obtain ⟨hwnew, hwold⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨⟨u, hvu, huw⟩, hnnew⟩ := (mem_secondNeighbors E' v w).mp hwnew
    have hvw : E v w := by
      by_contra hn
      exact hwold ((mem_secondNeighbors E v w).mpr ⟨⟨u, hsub v u hvu, hsub u w huw⟩, hn⟩)
    have hwQ : w ∈ Q := by
      have hnmem : w ∉ outNeighbors E' v := by simpa only [mem_outNeighbors] using hnnew
      rw [hout_eq] at hnmem
      simpa only [Finset.mem_sdiff, mem_outNeighbors, hvw, true_and, not_not] using hnmem
    have hwFT : w ∈ image E T := by
      have hww : w ∈ image E' (outNeighbors E' v) := (mem_image E' _ w).mpr
        ⟨u, (mem_outNeighbors E' v u).mpr hvu, huw⟩
      rcases Finset.mem_union.mp (hwalk hww) with hit | hft
      · exact False.elim (Finset.disjoint_left.mp hQI hwQ hit)
      · exact hft
    exact Finset.mem_inter.mpr ⟨hwQ, hwFT⟩
  have hLold : L ⊆ secondNeighbors E v := by
    intro w hw
    obtain ⟨hwFQ, hn⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨q', hqQ, hqw⟩ := (mem_image E Q w).mp hwFQ
    have hvq' := (mem_outNeighbors E v q').mp (Finset.mem_inter.mp hqQ).1
    refine (mem_secondNeighbors E v w).mpr ⟨⟨q', hvq', hqw⟩, ?_⟩
    intro hvw
    exact hn (Finset.mem_union_left _ (hout_bound ((mem_outNeighbors E v w).mpr hvw)))
  have hLnew : Disjoint L (secondNeighbors E' v) := by
    apply Finset.disjoint_left.mpr
    intro w hwL hwnew
    have hn := (Finset.mem_sdiff.mp hwL).2
    obtain ⟨⟨u, hvu, huw⟩, _⟩ := (mem_secondNeighbors E' v w).mp hwnew
    have hi : w ∈ image E' (outNeighbors E' v) :=
      (mem_image E' _ w).mpr ⟨u, (mem_outNeighbors E' v u).mpr hvu, huw⟩
    have hh := hwalk hi
    simp only [Finset.mem_union] at hn hh
    tauto
  have hsecond_bound : secondNeighbors E' v ⊆
      (secondNeighbors E v \ L) ∪ (Q ∩ image E T) := by
    intro w hw
    by_cases ho : w ∈ secondNeighbors E v
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
        ⟨ho, fun hL => Finset.disjoint_left.mp hLnew hL hw⟩)
    · exact Finset.mem_union_right _ (hgain (Finset.mem_sdiff.mpr ⟨hw, ho⟩))
  have hcard_second := (Finset.card_le_card hsecond_bound).trans (Finset.card_union_le _ _)
  have hcard_L := Finset.card_sdiff_add_card_eq_card hLold
  have hcard_Q := Finset.card_sdiff_add_card_eq_card
    (show Q ⊆ outNeighbors E v from Finset.inter_subset_left)
  rw [← hout_eq] at hcard_Q
  have hbadcard : (secondNeighbors E v).card < (outNeighbors E v).card := Nat.lt_of_not_ge (hbad v)
  have hgoodcard : (outNeighbors E' v).card ≤ (secondNeighbors E' v).card := hgood
  have hinc := image_increment_card I T Q (image E T) (image E Q) hQI
  rw [← image_union E T Q] at hinc
  have hassoc : I ∪ T ∪ Q = I ∪ (T ∪ Q) := Finset.union_assoc _ _ _
  rw [hassoc] at hinc
  refine ⟨Q, hQne, hQB, ?_⟩
  change (image E (T ∪ Q) \ (I ∪ (T ∪ Q))).card <
    (image E T \ (I ∪ T)).card + Q.card
  have hLc : (image E Q \ (I ∪ (T ∪ Q) ∪ image E T)).card = L.card := by
    simp only [L, Finset.union_assoc]
  rw [hLc] at hinc
  omega

/-- The strict subset deficit (1) for an arc-minimal graph with no good vertex: if
`F(S) ⊄ S`, then `|F²(S) \ F(S)| < |F(S) \ S|`. -/
private theorem subsetDeficit_of_arcMinimal {X : Type*} [Fintype X] [DecidableEq X]
    (E : X → X → Prop) (hmin : ArcMinimal E)
    (hbad : ∀ v, ¬ Good E v) (S : Finset X)
    (hboundary : (image E S \ S).Nonempty) :
    (image E (image E S) \ image E S).card < (image E S \ S).card := by
  classical
  let I := image E S ∩ S
  let B := image E S \ S
  let g : Finset X → ℕ := fun T => (image E T \ (I ∪ T)).card
  have hg : g B < B.card := strict_growth_finset B hboundary g (by simp [g]) (by
    intro T hT hne
    exact arcDeletion_step E hmin hbad S T hT hne)
  have hFS : image E S = I ∪ B := by
    ext x
    simp only [I, B, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hFI : image E I ⊆ image E S := image_mono E Finset.inter_subset_right
  have heq : image E (image E S) \ image E S = image E B \ (I ∪ B) := by
    conv_lhs => rw [hFS, image_union]
    ext x
    have hh : x ∈ image E I → x ∈ I ∪ B := by simpa only [← hFS] using @hFI x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    simp only [Finset.mem_union] at hh
    tauto
  rw [heq]
  exact hg

/-- The number of arcs of `E`. -/
noncomputable def numArcs {X : Type*} [Fintype X] (E : X → X → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter fun a : X × X => E a.1 a.2).card

/-- Lemma 2.1. Let `E` be a counterexample to Theorem 1.1 with the fewest vertices and, among
those, the fewest arcs: `E` is oriented and has no good vertex, every nonempty oriented graph
with fewer vertices has a good vertex, and every oriented graph on `X` with fewer arcs has a
good vertex. Then `F(S) ⊄ S` for every nonempty proper vertex set `S`; in particular every
vertex has an in-neighbour. Moreover `|F²(S) \ F(S)| < |F(S) \ S|` for every nonempty proper
`S` (the strict subset deficit (1)). -/
theorem deficit_lemma {X : Type u} [Fintype X] [DecidableEq X] [Nonempty X] (E : X → X → Prop)
    (hE : Oriented E) (hbad : ∀ v, ¬ Good E v)
    (hvert : ∀ (Y : Type u) [Fintype Y] [Nonempty Y] (E' : Y → Y → Prop),
      Fintype.card Y < Fintype.card X → Oriented E' → ∃ v, Good E' v)
    (harcs : ∀ E' : X → X → Prop, Oriented E' → numArcs E' < numArcs E → ∃ v, Good E' v) :
    (∀ S : Finset X, S.Nonempty → S ≠ Finset.univ → ¬ image E S ⊆ S) ∧
      (∀ y, ∃ x, E x y) ∧
      ∀ S : Finset X, S.Nonempty → S ≠ Finset.univ →
        (image E (image E S) \ image E S).card < (image E S \ S).card := by
  classical
  -- deleting an arc creates a good vertex
  have hmin : ArcMinimal E := by
    rintro E' hsub ⟨x, y, hxy, hnxy⟩
    refine harcs E' (fun a b hab hba => hE a b (hsub a b hab) (hsub b a hba)) ?_
    unfold numArcs
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨(x, y), by simp [hxy], by simp [hnxy]⟩
    · intro p hp'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp' ⊢
      exact hsub _ _ hp'
  -- a nonempty proper `S` with `F(S) ⊆ S` would give a counterexample with fewer vertices
  have hclosed : ∀ S : Finset X, S.Nonempty → S ≠ Finset.univ → ¬ image E S ⊆ S := by
    intro S hS hSu hcl
    have : Nonempty S := hS.to_subtype
    obtain ⟨v, hv⟩ := hvert S (fun a b : S => E a b)
      (by rw [Fintype.card_coe]; exact (Finset.card_lt_iff_ne_univ S).mpr hSu)
      (fun a b hab hba => hE a b hab hba)
    exact hbad v (good_of_closed_subtype E S hcl v hv)
  -- apply this to `S = X \ {y}`
  have hin : ∀ y, ∃ x, E x y := by
    intro y
    have hy : y ∉ Finset.univ.erase y := Finset.notMem_erase y _
    rcases (Finset.univ.erase y).eq_empty_or_nonempty with he | hne
    · -- `y` is the only vertex, so it has no out-neighbour and is good
      refine absurd ?_ (hbad y)
      have hout : outNeighbors E y = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun u hu => ?_
        have hu' : u = y := by
          by_contra hne'
          have hmem : u ∈ Finset.univ.erase y := Finset.mem_erase.2 ⟨hne', Finset.mem_univ u⟩
          simp [he] at hmem
        rw [mem_outNeighbors, hu'] at hu
        exact hE y y hu hu
      simp [Good, hout]
    · have hSu : Finset.univ.erase y ≠ Finset.univ := by
        intro hu
        rw [hu] at hy
        exact hy (Finset.mem_univ y)
      obtain ⟨z, hz, hzn⟩ := Finset.not_subset.1 (hclosed _ hne hSu)
      obtain ⟨x, -, hxz⟩ := (mem_image E _ z).1 hz
      have hzy : z = y := by
        by_contra hzy
        exact hzn (Finset.mem_erase.2 ⟨hzy, Finset.mem_univ z⟩)
      exact ⟨x, hzy ▸ hxz⟩
  exact ⟨hclosed, hin, fun S hS hSu => subsetDeficit_of_arcMinimal E hmin hbad S
    (Finset.sdiff_nonempty.2 (hclosed S hS hSu))⟩

/-- If Theorem 1.1 fails, it has a counterexample `E` on a nonempty finite type `X` with the
fewest vertices and, among those, the fewest arcs, as in Lemma 2.1. -/
theorem exists_minimal_counterexample (h : ¬ SeymourStatement) :
    ∃ (X : Type) (_ : Fintype X) (_ : Nonempty X) (E : X → X → Prop),
      Oriented E ∧ (∀ v, ¬ Good E v) ∧
      (∀ (Y : Type) [Fintype Y] [Nonempty Y] (E' : Y → Y → Prop),
        Fintype.card Y < Fintype.card X → Oriented E' → ∃ v, Good E' v) ∧
      ∀ E' : X → X → Prop, Oriented E' → numArcs E' < numArcs E → ∃ v, Good E' v := by
  by_contra hno
  apply h
  suffices key : ∀ n (X : Type) [Fintype X] [Nonempty X] (E : X → X → Prop),
      Fintype.card X = n → Oriented E → ∃ v, Good E v from
    fun X _ _ E hE => key _ X E rfl hE
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro X _ _ E0 hcard hE0
  suffices key : ∀ k (E : X → X → Prop), numArcs E = k → Oriented E → ∃ v, Good E v from
    key _ E0 rfl hE0
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ihk =>
  intro E hk hE
  by_contra hgood
  exact hno ⟨X, inferInstance, inferInstance, E, hE, fun v hv => hgood ⟨v, hv⟩,
    fun Y _ _ E' hY hE' => ih (Fintype.card Y) (hcard ▸ hY) Y E' rfl hE',
    fun E' hE' hlt => ihk (numArcs E') (hk ▸ hlt) E' rfl hE'⟩

end Seymour
