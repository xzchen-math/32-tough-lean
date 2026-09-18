import Broersma.TwoK2Free
import Broersma.Cycles

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem Path.order_eq_length_add_one (P : Path G) : P.order = P.walk.length + 1 := by
  rw [Path.order, Path.vertices, List.toFinset_card_of_nodup P.simple.support_nodup,
    SimpleGraph.Walk.length_support]

def Path.prepend (P : Path G) {x : V} (hx : x ∉ P.vertices)
    (h : G.Adj x P.first) : Path G where
  first := x
  last := P.last
  walk := P.walk.cons h
  simple := P.simple.cons (by simpa [Path.vertices] using hx)

@[simp] theorem Path.prepend_vertices (P : Path G) {x : V} (hx : x ∉ P.vertices)
    (h : G.Adj x P.first) : (P.prepend hx h).vertices = insert x P.vertices := by
  simp [Path.prepend, Path.vertices]

@[simp] theorem Path.prepend_order (P : Path G) {x : V} (hx : x ∉ P.vertices)
    (h : G.Adj x P.first) : (P.prepend hx h).order = P.order + 1 := by
  simp [Path.order, hx]

theorem Path.prepend_admits (P : Path G) {J : Finset V} (hP : P.Admits J)
    {x : V} (hx : x ∉ P.vertices) (h : G.Adj x P.first) :
    (P.prepend hx h).Admits J := by
  refine ⟨?_, ?_, hP.2.2⟩
  · rw [Path.prepend_vertices]
    exact subset_insert _ _ |>.trans' hP.1
  · exact fun hxJ => hx (hP.1 hxJ)

def Path.dropFirst (P : Path G) : Path G where
  first := P.walk.snd
  last := P.last
  walk := P.walk.tail
  simple := P.simple.tail

theorem Path.dropFirst_vertices_subset (P : Path G) (hne : ¬ P.walk.Nil) :
    P.dropFirst.vertices ⊆ P.vertices := by
  intro x hx
  simp only [Path.vertices, Path.dropFirst, List.mem_toFinset] at hx ⊢
  rw [← P.walk.cons_support_tail hne]
  exact List.mem_cons_of_mem _ hx

theorem Path.dropFirst_contains (P : Path G) (hne : ¬ P.walk.Nil)
    {J : Finset V} (hP : P.Admits J) : J ⊆ P.dropFirst.vertices := by
  intro x hx
  have hm := hP.1 hx
  simp only [Path.vertices, List.mem_toFinset] at hm
  rw [← P.walk.cons_support_tail hne] at hm
  rcases List.mem_cons.mp hm with h | h
  · exact (hP.2.1 (h ▸ hx)).elim
  · exact List.mem_toFinset.mpr h

theorem Path.dropFirst_order (P : Path G) (hne : ¬ P.walk.Nil) :
    P.dropFirst.order + 1 = P.order := by
  rw [Path.order_eq_length_add_one, Path.order_eq_length_add_one]
  have := P.walk.length_tail_add_one hne
  change P.walk.tail.length + 1 + 1 = P.walk.length + 1
  omega

/-- A longest admissible path cannot be extended at its first vertex. -/
theorem Path.no_outside_neighbor_first {J : Finset V} (P : Path G)
    (hP : P.Admits J)
    (hmax : ∀ Q : Path G, Q.Admits J → Q.order ≤ P.order)
    {x : V} (hx : x ∉ P.vertices) : ¬ G.Adj P.first x := by
  intro he
  have hb := hmax (P.prepend hx he.symm) (P.prepend_admits hP hx he.symm)
  rw [Path.prepend_order] at hb
  omega

/-- Claim 2.1 (`claim:U-independent`): every longest path containing `J`
and with both ends outside `J` is dominating.  Both extension constructions
are explicit `SimpleGraph.Walk.cons` terms checked by Lean. -/
theorem longest_admissible_path_dominating (hG : TwoK2Free G)
    {J : Finset V} (P : Path G) (hP : P.Admits J)
    (hmax : ∀ Q : Path G, Q.Admits J → Q.order ≤ P.order) : P.Dominating := by
  intro x hx y hy hxy
  have hxout : x ∉ P.vertices := (mem_sdiff.mp hx).2
  have hyout : y ∉ P.vertices := (mem_sdiff.mp hy).2
  have hxJ : x ∉ J := fun hxJ => hxout (hP.1 hxJ)
  have hyJ : y ∉ J := fun hyJ => hyout (hP.1 hyJ)
  by_cases hnil : P.walk.Nil
  · have hJe : J = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      have hm := hP.1 hz
      have hs : P.walk.support = [P.first] := SimpleGraph.Walk.nil_iff_support_eq.mp hnil
      have hzf : z = P.first := by simpa [Path.vertices, hs] using hm
      exact hP.2.1 (hzf ▸ hz)
    let Q : Path G := ⟨x, y, .cons hxy .nil, by simp [hxy.ne]⟩
    have hadm : Q.Admits J := by simp [Path.Admits, hJe]
    have hb := hmax Q hadm
    have hℓ : P.order = 1 := by
      rw [P.order_eq_length_add_one, SimpleGraph.Walk.length_eq_zero_iff.mpr hnil]
    have hq : Q.order = 2 := by
      rw [Q.order_eq_length_add_one]
      rfl
    omega
  · have hfx := P.no_outside_neighbor_first hP hmax hxout
    have hfy := P.no_outside_neighbor_first hP hmax hyout
    have hf : G.Adj P.first P.walk.snd := P.walk.adj_snd hnil
    have hbranch : G.Adj P.walk.snd x ∨ G.Adj P.walk.snd y := by
      rcases hG.cross_edge hf hxy with h | h | h | h
      · exact (hfx h).elim
      · exact (hfy h).elim
      · exact Or.inl h
      · exact Or.inr h
    have grow (a b : V) (ha : a ∉ P.vertices) (hb : b ∉ P.vertices)
        (hab : G.Adj a b) (hsa : G.Adj P.walk.snd a) : False := by
      have hat : a ∉ P.dropFirst.vertices := fun h => ha (P.dropFirst_vertices_subset hnil h)
      let Q := P.dropFirst.prepend hat hsa.symm
      have hbq : b ∉ Q.vertices := by
        change b ∉ (a :: P.walk.tail.support).toFinset
        simp only [List.mem_toFinset, List.mem_cons, not_or]
        exact ⟨hab.ne.symm, fun h => hb
          (P.dropFirst_vertices_subset hnil (List.mem_toFinset.mpr h))⟩
      let R := Q.prepend hbq hab.symm
      have hRa : R.Admits J := by
        refine ⟨?_, fun h => hb (hP.1 h), hP.2.2⟩
        intro z hz
        have hzt := P.dropFirst_contains hnil hP hz
        change z ∈ (b :: a :: P.walk.tail.support).toFinset
        simp only [List.mem_toFinset, List.mem_cons]
        exact Or.inr (Or.inr (List.mem_toFinset.mp hzt))
      have hbound := hmax R hRa
      have horder : R.order = P.dropFirst.order + 2 := by
        rw [R.order_eq_length_add_one, P.dropFirst.order_eq_length_add_one]
        simp [R, Q, Path.prepend, Path.dropFirst]
      have hdrop := P.dropFirst_order hnil
      omega
    rcases hbranch with h | h
    · exact grow x y hxout hyout hxy h
    · exact grow y x hyout hxout hxy.symm h

end Broersma
