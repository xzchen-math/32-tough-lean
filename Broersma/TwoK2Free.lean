import Broersma.Basic

/-! Fully proved versions of Fact 2.1 and its elementary consequences. -/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The fourth cross-edge is forced if the other three are absent.
The hypotheses themselves ensure that the four ends are distinct. -/
theorem TwoK2Free.force_edge (hG : TwoK2Free G) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (had : ¬ G.Adj a d) (hbc : ¬ G.Adj b c) :
    G.Adj b d := by
  have hac' : a ≠ c := by intro h; subst c; exact hbc hab.symm
  have had' : a ≠ d := by intro h; subst d; exact hac hcd.symm
  have hbc' : b ≠ c := by intro h; subst c; exact hac hab
  have hbd' : b ≠ d := by intro h; subst d; exact had hab
  rcases hG hab hcd hac' had' hbc' hbd' with h | h | h | h
  · exact (hac h).elim
  · exact (had h).elim
  · exact (hbc h).elim
  · exact h

/-- The cross-edge conclusion also holds for overlapping edges. -/
theorem TwoK2Free.cross_edge (hG : TwoK2Free G) {a b c d : V}
    (hab : G.Adj a b) (hcd : G.Adj c d) :
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d := by
  by_cases hac : G.Adj a c
  · exact Or.inl hac
  by_cases had : G.Adj a d
  · exact Or.inr (Or.inl had)
  by_cases hbc : G.Adj b c
  · exact Or.inr (Or.inr (Or.inl hbc))
  exact Or.inr (Or.inr (Or.inr (hG.force_edge hab hcd hac had hbc)))

/-- Fact 2.1(ii), first assertion; nonemptiness is unnecessary. -/
theorem TwoK2Free.neighbors_comparable (hG : TwoK2Free G)
    {I : Finset V} (hI : Independent G I) {x y : V} (hxy : ¬ G.Adj x y) :
    neighborsIn G I x ⊆ neighborsIn G I y ∨
      neighborsIn G I y ⊆ neighborsIn G I x := by
  classical
  by_contra! h
  obtain ⟨a, ha, hay⟩ := Finset.not_subset.mp h.1
  obtain ⟨b, hb, hbx⟩ := Finset.not_subset.mp h.2
  obtain ⟨haI, hxa⟩ := mem_neighborsIn.mp ha
  obtain ⟨hbI, hyb⟩ := mem_neighborsIn.mp hb
  have hyan : ¬ G.Adj y a := fun e => hay (mem_neighborsIn.mpr ⟨haI, e⟩)
  have hxbn : ¬ G.Adj x b := fun e => hbx (mem_neighborsIn.mpr ⟨hbI, e⟩)
  have hab := hG.force_edge hxa hyb hxy hxbn (fun e => hyan e.symm)
  exact hI haI hbI hab

/-- Fact 2.1(ii), second assertion, with the union written explicitly. -/
theorem TwoK2Free.union_neighborhood_realized (hG : TwoK2Free G)
    {I U : Finset V} (hI : Independent G I) (hU : Independent G U)
    (hne : U.Nonempty) :
    ∃ u ∈ U, neighborsIn G I u = neighborsOfSetIn G I U := by
  classical
  obtain ⟨u, hu, hmax⟩ := U.exists_max_image (fun v => (neighborsIn G I v).card) hne
  refine ⟨u, hu, ?_⟩
  ext x
  simp only [mem_neighborsIn, neighborsOfSetIn, mem_inter, mem_neighborhood]
  constructor
  · rintro ⟨hxI, hux⟩
    exact ⟨hxI, u, hu, hux.symm⟩
  · rintro ⟨hxI, v, hv, hxv⟩
    have hsub : neighborsIn G I v ⊆ neighborsIn G I u := by
      rcases hG.neighbors_comparable hI (hU hu hv) with h | h
      · have heq := Finset.eq_of_subset_of_card_le h (hmax v hv)
        exact heq ▸ Finset.Subset.refl _
      · exact h
    exact mem_neighborsIn.mp (hsub (mem_neighborsIn.mpr ⟨hxI, hxv.symm⟩))

/-- Fact 2.1(iii), as an equality of genuine connected components:
any two components of an induced graph that contain edges coincide. -/
theorem TwoK2Free.edge_components_equal (hG : TwoK2Free G)
    (S : Finset V) {a b c d : {v // v ∉ S}}
    (hab : (Deleted G S).Adj a b) (hcd : (Deleted G S).Adj c d) :
    (Deleted G S).connectedComponentMk a = (Deleted G S).connectedComponentMk c := by
  apply SimpleGraph.ConnectedComponent.sound
  rcases hG.cross_edge hab hcd with h | h | h | h
  · exact (show (Deleted G S).Adj a c from h).reachable
  · exact (show (Deleted G S).Adj a d from h).reachable.trans hcd.symm.reachable
  · exact hab.reachable.trans (show (Deleted G S).Adj b c from h).reachable
  · exact (hab.reachable.trans (show (Deleted G S).Adj b d from h).reachable).trans
      hcd.symm.reachable

/-- Every split graph is 2K₂-free, as asserted in the introduction. -/
theorem Split.twoK2Free (hG : Split G) : TwoK2Free G := by
  classical
  obtain ⟨I, hI, hclique⟩ := hG
  intro a b c d hab hcd hac had hbc hbd
  have h1 : a ∉ I ∨ b ∉ I := by
    by_contra! h
    exact hI h.1 h.2 hab
  have h2 : c ∉ I ∨ d ∉ I := by
    by_contra! h
    exact hI h.1 h.2 hcd
  rcases h1 with ha | hb <;> rcases h2 with hc | hd
  · exact Or.inl (hclique ha hc hac)
  · exact Or.inr (Or.inl (hclique ha hd had))
  · exact Or.inr (Or.inr (Or.inl (hclique hb hc hbc)))
  · exact Or.inr (Or.inr (Or.inr (hclique hb hd hbd)))

/-- A nonneighbor of `u` which sees `I \ N_I(u)` sees every member of `N_I(u)`.
This is the repeatedly used cross-edge inference in Sections 3 and 4. -/
theorem TwoK2Free.neighborhood_extension (hG : TwoK2Free G)
    {I : Finset V} (hI : Independent G I) {u x y : V}
    (hy : y ∈ I) (huy : ¬ G.Adj u y) (hux : ¬ G.Adj u x)
    (hxy : G.Adj x y) : neighborsIn G I u ⊂ neighborsIn G I x := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro t ht
    obtain ⟨htI, hut⟩ := mem_neighborsIn.mp ht
    have hxt : G.Adj x t := by
      have e := hG.force_edge hxy.symm hut (fun e => huy e.symm)
        (hI hy htI) (fun e => hux e.symm)
      exact e
    exact mem_neighborsIn.mpr ⟨htI, hxt⟩
  · intro heq
    have hmem : y ∈ neighborsIn G I x := mem_neighborsIn.mpr ⟨hy, hxy⟩
    rw [← heq] at hmem
    exact huy (mem_neighborsIn.mp hmem).2

end Broersma
