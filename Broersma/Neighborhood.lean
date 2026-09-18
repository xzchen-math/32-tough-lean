import Broersma.TwoK2Free

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The set equality `S = T ∪ T'` near the end of Section 4.
`M` and `K` are the portions of the neighborhoods in the two maximum
independent sets.  The reverse inclusion is proved by the two disjoint edges. -/
theorem neighborhood_eq_union (hG : TwoK2Free G)
    {I₀ M K : Finset V} {u v : V} (huv : G.Adj u v)
    (hu : u ∉ neighborhood G I₀) (hv : v ∉ neighborhood G I₀)
    (hM : Anticomplete G M I₀) (hK : Anticomplete G K I₀)
    (hT : neighborsIn G univ u \ M ⊆ neighborhood G I₀)
    (hT' : neighborsIn G univ v \ K ⊆ neighborhood G I₀) :
    neighborhood G I₀ = (neighborsIn G univ u \ M) ∪ (neighborsIn G univ v \ K) := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨y, hy, hzy⟩ := mem_neighborhood.mp hz
    have huy : ¬ G.Adj y u := fun e => hu (mem_neighborhood.mpr ⟨y, hy, e.symm⟩)
    have hvy : ¬ G.Adj y v := fun e => hv (mem_neighborhood.mpr ⟨y, hy, e.symm⟩)
    have hzM : z ∉ M := fun hzM => hM hzM hy hzy
    have hzK : z ∉ K := fun hzK => hK hzK hy hzy
    rcases hG.cross_edge hzy.symm huv with e | e | e | e
    · exact (huy e).elim
    · exact (hvy e).elim
    · exact mem_union_left _ (mem_sdiff.mpr
        ⟨mem_neighborsIn.mpr ⟨mem_univ _, e.symm⟩, hzM⟩)
    · exact mem_union_right _ (mem_sdiff.mpr
        ⟨mem_neighborsIn.mpr ⟨mem_univ _, e.symm⟩, hzK⟩)
  · exact union_subset hT hT'

/-- If two forbidden sets leave at most one exceptional vertex each,
at most two of their union can belong to `S`. -/
theorem card_inter_union_le_two {S A B : Finset V}
    (hA : (S ∩ A).card ≤ 1) (hB : (S ∩ B).card ≤ 1) :
    (S ∩ (A ∪ B)).card ≤ 2 := by
  rw [inter_union_distrib_left]
  have := card_union_le (S ∩ A) (S ∩ B)
  omega

/-- The complement count used to bound `|N(I₀)|` from the predecessor
and successor sets. Its formulation avoids truncated subtraction. -/
theorem neighborhood_union_count {S A B X : Finset V}
    (hS : S ⊆ X) (hA : A ⊆ X) (hB : B ⊆ X)
    (hSA : (S ∩ A).card ≤ 1) (hSB : (S ∩ B).card ≤ 1) :
    S.card + A.card + B.card ≤ X.card + (A ∩ B).card + 2 := by
  have hsub : S ∪ (A ∪ B) ⊆ X := union_subset hS (union_subset hA hB)
  have hle := card_le_card hsub
  have hinter := card_inter_union_le_two hSA hSB
  have hun := card_union_add_card_inter S (A ∪ B)
  have hab := card_union_add_card_inter A B
  omega

/-- A common independent part and `W \ I` form an independent set.
The maximum-cardinality comparison forces equality with the known `K₀`. -/
theorem endpoint_set_exchange {I I₀ K W : Finset V}
    (hI : MaximumIndependent G I) (hI₀ : I₀ ⊆ I)
    (hW : Independent G W) (hanti : Anticomplete G I₀ (W \ I))
    (hK : K ⊆ W \ I) (hsize : I₀.card + K.card = I.card) : W \ I = K := by
  have hmax := hI.2 (I₀ ∪ (W \ I))
    ((hI.1.mono hI₀).union (hW.mono sdiff_subset) hanti)
  have hd : Disjoint I₀ (W \ I) := by
    rw [disjoint_left]
    intro x hx hxd
    exact (mem_sdiff.mp hxd).2 (hI₀ hx)
  rw [card_union_of_disjoint hd] at hmax
  exact (eq_of_subset_of_card_le hK (by omega)).symm

/-- Independent vertices anticomplete to the ends of a fixed edge,
used to prove that the rotation endpoint set `W` is independent. -/
theorem TwoK2Free.independent_common_nonneighbors (hG : TwoK2Free G)
    {W : Finset V} {a x : V} (hax : G.Adj a x)
    (hWa : ∀ w ∈ W, ¬ G.Adj w a) (hWx : ∀ w ∈ W, ¬ G.Adj w x) :
    Independent G W := by
  intro w hw z hz hwz
  rcases hG.cross_edge hwz hax with h | h | h | h
  · exact hWa w hw h
  · exact hWx w hw h
  · exact hWa z hz h
  · exact hWx z hz h

end Broersma
