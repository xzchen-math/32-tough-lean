import Broersma.TwoK2Free
import Broersma.Cycles

/-! The two successive finite maximizations in Section 3. -/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

structure ExtremalPair (G : SimpleGraph V) (D I : Finset V) (u : V) : Prop where
  maximum : MaximumIndependent G I
  mem_D : u ∈ D
  outside : u ∉ I
  first_max : ∀ J : Finset V, MaximumIndependent G J →
    ∀ z ∈ D, z ∉ J → (J ∩ D).card ≤ (I ∩ D).card
  second_max : ∀ J : Finset V, MaximumIndependent G J →
    ∀ z ∈ D, z ∉ J → (J ∩ D).card = (I ∩ D).card →
      (neighborsIn G J z).card ≤ (neighborsIn G I u).card

theorem exists_extremalPair (D : Finset V)
    (hD : ∀ I, MaximumIndependent G I → ∃ u ∈ D, u ∉ I) :
    ∃ I u, ExtremalPair G D I u := by
  classical
  let Q : Finset (Finset V × V) :=
    univ.filter (fun q => MaximumIndependent G q.1 ∧ q.2 ∈ D ∧ q.2 ∉ q.1)
  have hQ : Q.Nonempty := by
    obtain ⟨I, hI⟩ := exists_maximumIndependent G
    obtain ⟨u, huD, huI⟩ := hD I hI
    exact ⟨(I, u), by simp [Q, hI, huD, huI]⟩
  obtain ⟨q₀, hq₀, hmax₀⟩ := Q.exists_max_image (fun q => (q.1 ∩ D).card) hQ
  let R := Q.filter (fun q => (q.1 ∩ D).card = (q₀.1 ∩ D).card)
  have hR : R.Nonempty := ⟨q₀, by simp [R, hq₀]⟩
  obtain ⟨q, hq, hmax⟩ := R.exists_max_image
    (fun q => (neighborsIn G q.1 q.2).card) hR
  have hqQ := (mem_filter.mp hq).1
  have heq := (mem_filter.mp hq).2
  have hprops : MaximumIndependent G q.1 ∧ q.2 ∈ D ∧ q.2 ∉ q.1 :=
    (mem_filter.mp hqQ).2
  refine ⟨q.1, q.2, hprops.1, hprops.2.1, hprops.2.2, ?_, ?_⟩
  · intro J hJ z hzD hzJ
    rw [heq]
    exact hmax₀ (J, z) (by simp [Q, hJ, hzD, hzJ])
  · intro J hJ z hzD hzJ he
    exact hmax (J, z) (by simp [R, Q, hJ, hzD, hzJ, he, heq])

theorem Independent.neighborsIn_eq_empty {I : Finset V} (hI : Independent G I)
    {z : V} (hz : z ∈ I) : neighborsIn G I z = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact hI hz (mem_neighborsIn.mp hx).1 (mem_neighborsIn.mp hx).2

theorem ExtremalPair.degree_bound {D I : Finset V} {u : V}
    (h : ExtremalPair G D I u) {z : V} (hz : z ∈ D) :
    (neighborsIn G I z).card ≤ (neighborsIn G I u).card := by
  by_cases hzI : z ∈ I
  · simp [h.maximum.1.neighborsIn_eq_empty hzI]
  · exact h.second_max I h.maximum z hz hzI rfl

theorem ExtremalPair.neighbors_nonempty {D I : Finset V} {u : V}
    (h : ExtremalPair G D I u) : (neighborsIn G I u).Nonempty := by
  obtain ⟨y, hy, huy⟩ := h.maximum.neighbor_of_not_mem h.outside
  exact ⟨y, mem_neighborsIn.mpr ⟨hy, huy⟩⟩

theorem ExtremalPair.not_mem_D_of_large_neighborhood {D I : Finset V} {u x : V}
    (h : ExtremalPair G D I u)
    (hx : (neighborsIn G I u).card < (neighborsIn G I x).card) : x ∉ D := by
  intro hxD
  have := h.degree_bound hxD
  omega

/-- Pure finite-set calculation underlying the first maximum in Lemma 3.4. -/
theorem exchange_card_inter {I M K D : Finset V}
    (hMI : M ⊆ I) (hKI : Disjoint K I) (hKD : K ⊆ D)
    (hcard : K.card = M.card) :
    ((I \ M ∪ K) ∩ D).card + (M ∩ D).card = (I ∩ D).card + M.card := by
  have hdis : Disjoint (I \ M) K :=
    (hKI.symm.mono_left sdiff_subset)
  have hdisD : Disjoint ((I \ M) ∩ D) K := hdis.mono_left inter_subset_left
  have hEq : (I \ M ∪ K) ∩ D = ((I ∩ D) \ (M ∩ D)) ∪ K := by
    ext x
    have hm : x ∈ M → x ∈ I := fun hx => hMI hx
    have hk : x ∈ K → x ∈ D := fun hx => hKD hx
    simp only [mem_inter, mem_union, mem_sdiff]
    tauto
  have hsub : M ∩ D ⊆ I ∩ D := by
    intro x hx
    exact mem_inter.mpr ⟨hMI (mem_inter.mp hx).1, (mem_inter.mp hx).2⟩
  have hd : Disjoint ((I ∩ D) \ (M ∩ D)) K := by
    apply hKI.symm.mono_left
    exact fun x hx => (mem_inter.mp (mem_sdiff.mp hx).1).1
  rw [hEq, card_union_of_disjoint hd, card_sdiff_of_subset hsub, hcard]
  have := card_le_card hsub
  omega

/-- The exchange of `N_I(u)` with `K₀` preserves maximum cardinality. -/
theorem maximumIndependent_exchange {I M K : Finset V}
    (hI : MaximumIndependent G I) (hMI : M ⊆ I)
    (hK : Independent G K) (hKI : Disjoint K I)
    (hanti : Anticomplete G (I \ M) K) (hcard : K.card = M.card) :
    MaximumIndependent G ((I \ M) ∪ K) := by
  have hi : Independent G (I \ M ∪ K) :=
    (hI.1.mono sdiff_subset).union hK hanti
  have hc : (I \ M ∪ K).card = I.card := by
    rw [card_union_of_disjoint (hKI.symm.mono_left sdiff_subset),
      card_sdiff_of_subset hMI, hcard]
    exact Nat.sub_add_cancel (card_le_card hMI)
  exact ⟨hi, fun J hJ => hc ▸ hI.2 J hJ⟩

/-- First-half conclusion of Lemma 3.4. This has explicit hypotheses for
the predecessor-set properties proved earlier in the paper. -/
theorem ExtremalPair.exchange_subset_D {D I K : Finset V} {u : V}
    (h : ExtremalPair G D I u)
    (hD : ∀ J, MaximumIndependent G J → ∃ z ∈ D, z ∉ J)
    (hK : Independent G K) (hKI : Disjoint K I) (hKD : K ⊆ D)
    (hanti : Anticomplete G (I \ neighborsIn G I u) K)
    (hcard : K.card = (neighborsIn G I u).card) :
    neighborsIn G I u ⊆ D ∧
      (((I \ neighborsIn G I u) ∪ K) ∩ D).card = (I ∩ D).card := by
  let M := neighborsIn G I u
  have hMI : M ⊆ I := neighborsIn_subset I u
  have hmax := maximumIndependent_exchange h.maximum hMI hK hKI hanti hcard
  obtain ⟨z, hzD, hzJ⟩ := hD _ hmax
  have hle := h.first_max _ hmax z hzD hzJ
  have he := exchange_card_inter hMI hKI hKD hcard
  have hmle : (M ∩ D).card ≤ M.card := card_le_card inter_subset_left
  have hmeq : (M ∩ D).card = M.card := by omega
  have hsets : M ∩ D = M := eq_of_subset_of_card_le inter_subset_left (by omega)
  refine ⟨?_, ?_⟩
  · intro x hx
    change x ∈ M at hx
    rw [← hsets] at hx
    exact (mem_inter.mp hx).2
  · change ((I \ M ∪ K) ∩ D).card = (I ∩ D).card
    omega

/-- The remaining set-theoretic content of Lemma 3.4: nested neighborhoods
produce `v`, and the exchanged pair attains exactly the same two maxima. -/
theorem ExtremalPair.exchange (hG : TwoK2Free G) {D I K : Finset V} {u : V}
    (h : ExtremalPair G D I u)
    (hD : ∀ J, MaximumIndependent G J → ∃ z ∈ D, z ∉ J)
    (hK : Independent G K) (hKI : Disjoint K I) (hKD : K ⊆ D)
    (hanti : Anticomplete G (I \ neighborsIn G I u) K)
    (hcard : K.card = (neighborsIn G I u).card)
    (hcover : ∀ k ∈ K, ∃ z ∈ neighborsIn G I u, G.Adj z k) :
    MaximumIndependent G ((I \ neighborsIn G I u) ∪ K) ∧
    neighborsIn G I u ⊆ D ∧
    ∃ v ∈ neighborsIn G I u,
      neighborsIn G ((I \ neighborsIn G I u) ∪ K) v = K ∧
      ExtremalPair G D ((I \ neighborsIn G I u) ∪ K) v := by
  classical
  let M := neighborsIn G I u
  let J := (I \ M) ∪ K
  have hMI : M ⊆ I := neighborsIn_subset I u
  have hJ : MaximumIndependent G J :=
    maximumIndependent_exchange h.maximum hMI hK hKI hanti hcard
  obtain ⟨hMD, hfirst⟩ := h.exchange_subset_D hD hK hKI hKD hanti hcard
  obtain ⟨v, hvM, hv⟩ := hG.union_neighborhood_realized hK
    (h.maximum.1.mono hMI) h.neighbors_nonempty
  have hKM : neighborsOfSetIn G K M = K := by
    ext k
    simp only [neighborsOfSetIn, mem_inter, mem_neighborhood]
    constructor
    · exact And.left
    · intro hk
      obtain ⟨z, hz, hzk⟩ := hcover k hk
      exact ⟨hk, z, hz, hzk.symm⟩
  have hvK : neighborsIn G K v = K := hv.trans hKM
  have hnv : neighborsIn G J v = K := by
    ext k
    constructor
    · intro hk
      obtain ⟨hkJ, hvk⟩ := mem_neighborsIn.mp hk
      rcases mem_union.mp hkJ with hk | hk
      · exact (h.maximum.1 (hMI hvM) (mem_sdiff.mp hk).1 hvk).elim
      · exact hk
    · intro hk
      have hadj := (mem_neighborsIn.mp (hvK ▸ hk)).2
      exact mem_neighborsIn.mpr ⟨mem_union_right _ hk, hadj⟩
  have hvJ : v ∉ J := by
    intro hvJ
    rcases mem_union.mp hvJ with hv' | hv'
    · exact (mem_sdiff.mp hv').2 hvM
    · exact disjoint_left.mp hKI hv' (hMI hvM)
  refine ⟨hJ, hMD, v, hvM, hnv, hJ, hMD hvM, hvJ, ?_, ?_⟩
  · intro L hL z hzD hzL
    rw [hfirst]
    exact h.first_max L hL z hzD hzL
  · intro L hL z hzD hzL heq
    rw [hnv, hcard]
    apply h.second_max L hL z hzD hzL
    exact heq.trans hfirst

end Broersma
