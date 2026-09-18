import Broersma.Definitions

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

@[simp] theorem mem_neighborhood {A : Finset V} {x : V} :
    x ∈ neighborhood G A ↔ ∃ a ∈ A, G.Adj x a := by
  classical
  simp [neighborhood]

@[simp] theorem mem_neighborsIn {I : Finset V} {x y : V} :
    y ∈ neighborsIn G I x ↔ y ∈ I ∧ G.Adj x y := by
  classical
  simp [neighborsIn]

theorem neighborsIn_subset (I : Finset V) (x : V) : neighborsIn G I x ⊆ I := by
  classical
  exact filter_subset _ _

theorem independent_iff_mathlib {I : Finset V} :
    Independent G I ↔ G.IsIndepSet (I : Set V) := by
  rw [SimpleGraph.isIndepSet_iff]
  constructor
  · intro h x hx y hy _
    exact h hx hy
  · intro h x hx y hy
    by_cases hxy : x = y
    · subst y; exact G.loopless.irrefl x
    · exact h hx hy hxy

theorem Independent.mono {A B : Finset V} (h : Independent G B) (hAB : A ⊆ B) :
    Independent G A := fun _ hx _ hy => h (hAB hx) (hAB hy)

theorem Independent.disjoint_neighborhood {I : Finset V} (hI : Independent G I) :
    Disjoint I (neighborhood G I) := by
  rw [Finset.disjoint_left]
  intro x hx hxn
  obtain ⟨y, hy, hxy⟩ := mem_neighborhood.mp hxn
  exact hI hx hy hxy

theorem Independent.union {A B : Finset V} (hA : Independent G A)
    (hB : Independent G B) (hAB : Anticomplete G A B) : Independent G (A ∪ B) := by
  intro x hx y hy hxy
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · exact hA hx hy hxy
  · exact hAB hx hy hxy
  · exact hAB hy hx hxy.symm
  · exact hB hx hy hxy

theorem Independent.insert {I : Finset V} {x : V} (hI : Independent G I)
    (hx : x ∉ neighborhood G I) : Independent G (insert x I) := by
  intro a ha b hb hab
  rcases mem_insert.mp ha with ha | ha
  · subst a
    rcases mem_insert.mp hb with hb | hb
    · subst b; exact G.loopless.irrefl _ hab
    · exact hx (mem_neighborhood.mpr ⟨_, hb, hab⟩)
  · rcases mem_insert.mp hb with hb | hb
    · subst b; exact hx (mem_neighborhood.mpr ⟨_, ha, hab.symm⟩)
    · exact hI ha hb hab

theorem independent_card_le {I : Finset V} (hI : Independent G I) :
    I.card ≤ independenceNumber G := by
  classical
  exact Finset.le_sup (f := Finset.card) (by simp [hI])

theorem exists_maximumIndependent (G : SimpleGraph V) :
    ∃ I : Finset V, MaximumIndependent G I := by
  classical
  have hne : (univ.filter (Independent G)).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [Independent]
  obtain ⟨I, hI, hmax⟩ := (univ.filter (Independent G)).exists_max_image Finset.card hne
  exact ⟨I, (mem_filter.mp hI).2, fun J hJ => hmax J (by simp [hJ])⟩

theorem MaximumIndependent.card_eq {I : Finset V} (hI : MaximumIndependent G I) :
    I.card = independenceNumber G := by
  classical
  apply le_antisymm (independent_card_le hI.1)
  exact Finset.sup_le fun J hJ => hI.2 J (mem_filter.mp hJ).2

theorem MaximumIndependent.neighbor_of_not_mem {I : Finset V}
    (hI : MaximumIndependent G I) {x : V} (hx : x ∉ I) :
    ∃ y ∈ I, G.Adj x y := by
  by_contra h
  have hind := hI.1.insert (show x ∉ neighborhood G I by simpa using h)
  have hcard := hI.2 _ hind
  rw [card_insert_of_notMem hx] at hcard
  omega

theorem toughThreeHalves_iff (G : SimpleGraph V) :
    ToughThreeHalves G ↔ Tough G (3 / 2) := by
  constructor
  · intro h S hS
    have hh := h S hS
    have hh' : (3 : ℚ) * components G S ≤ 2 * (S.card : ℚ) := by exact_mod_cast hh
    linarith
  · intro h S hS
    have hh := h S hS
    have hh' : (3 : ℚ) * components G S ≤ 2 * (S.card : ℚ) := by linarith
    exact_mod_cast hh'

/-- Adding edges cannot destroy 3/2-toughness. -/
theorem ToughThreeHalves.mono {H : SimpleGraph V} (hG : ToughThreeHalves G)
    (hGH : G ≤ H) : ToughThreeHalves H := by
  intro S hS
  have hle : components H S ≤ components G S :=
    SimpleGraph.ConnectedComponent.card_le_card_of_le
      (show Deleted G S ≤ Deleted H S from fun _ _ h => hGH h)
  have ht := hG S (lt_of_lt_of_le hS hle)
  omega

end Broersma
