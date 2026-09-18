import Broersma.Basic

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem Path.first_mem (P : Path G) : P.first ∈ P.vertices := by
  exact List.mem_toFinset.mpr P.walk.start_mem_support

theorem Path.last_mem (P : Path G) : P.last ∈ P.vertices := by
  exact List.mem_toFinset.mpr P.walk.end_mem_support

theorem Cycle.order_eq_length (C : Cycle G) : C.order = C.walk.length := by
  have hs : C.walk.support.toFinset = C.walk.tail.support.toFinset := by
    rw [← C.walk.cons_support_tail C.simple.not_nil, List.toFinset_cons]
    exact Finset.insert_eq_of_mem (List.mem_toFinset.mpr C.walk.tail.end_mem_support)
  rw [Cycle.order, Cycle.vertices, hs,
    List.toFinset_card_of_nodup C.simple.isPath_tail.support_nodup,
    SimpleGraph.Walk.length_support]
  exact C.walk.length_tail_add_one C.simple.not_nil

theorem Cycle.three_le_order (C : Cycle G) : 3 ≤ C.order := by
  rw [C.order_eq_length]
  exact C.simple.three_le_length

theorem Cycle.order_le_card (C : Cycle G) : C.order ≤ Fintype.card V :=
  Finset.card_le_univ _

theorem Cycle.hamiltonian_of_order_eq (C : Cycle G)
    (h : C.order = Fintype.card V) : Hamiltonian G := by
  refine ⟨C, ?_⟩
  exact Finset.eq_univ_of_card _ h

theorem Hamiltonian.mathlib (h : Hamiltonian G) : G.IsHamiltonian := by
  obtain ⟨C, hC⟩ := h
  intro _
  refine ⟨C.base, C.walk, ?_⟩
  apply SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
  refine ⟨C.simple, ?_⟩
  rw [← C.order_eq_length, Cycle.order, hC, Finset.card_univ]

theorem hamiltonian_of_mathlib (hn : 3 ≤ Fintype.card V) (h : G.IsHamiltonian) :
    Hamiltonian G := by
  obtain ⟨a, p, hp⟩ := h (by omega)
  refine ⟨⟨a, p, hp.isCycle⟩, ?_⟩
  ext v
  simp only [Cycle.vertices, List.mem_toFinset, Finset.mem_univ, iff_true]
  exact hp.mem_support v

theorem hamiltonian_iff_mathlib (hn : 3 ≤ Fintype.card V) :
    Hamiltonian G ↔ G.IsHamiltonian :=
  ⟨Hamiltonian.mathlib, hamiltonian_of_mathlib hn⟩

theorem Hamiltonian.three_le_card (h : Hamiltonian G) : 3 ≤ Fintype.card V := by
  obtain ⟨C, hC⟩ := h
  have := C.three_le_order
  simpa [Cycle.order, hC] using this

theorem Cycle.order_lt_card_of_nonhamiltonian (C : Cycle G)
    (hG : ¬ Hamiltonian G) : C.order < Fintype.card V := by
  have := C.order_le_card
  have hne : C.order ≠ Fintype.card V := fun h => hG (C.hamiltonian_of_order_eq h)
  omega

/-- The complement of a cycle of order `n-1` is a singleton. -/
theorem Cycle.exists_omitted_of_order (C : Cycle G)
    (h : C.order + 1 = Fintype.card V) :
    ∃ u : V, C.vertices = univ.erase u := by
  have hcard : (univ \ C.vertices).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ]
    change Fintype.card V - C.order = 1
    omega
  obtain ⟨u, hu⟩ := card_eq_one.mp hcard
  refine ⟨u, ?_⟩
  ext x
  have hm := congrArg (fun A : Finset V => x ∈ A) hu
  simp only [mem_sdiff, mem_univ, true_and, mem_singleton] at hm
  simp only [mem_erase, mem_univ, and_true]
  tauto

theorem mem_deletable {u : V} :
    u ∈ deletable G ↔ HasCycleOn G (univ.erase u) := by
  classical
  simp [deletable]

/-- Position of a vertex in the oriented support with the repeated base removed.
Only vertices on the cycle are used in predecessor/successor statements. -/
noncomputable def Cycle.position (C : Cycle G) (v : V) : ℕ :=
  C.walk.support.dropLast.idxOf v

noncomputable def Cycle.succ (C : Cycle G) (v : V) : V :=
  C.walk.getVert ((C.position v + 1) % C.walk.length)

noncomputable def Cycle.pred (C : Cycle G) (v : V) : V :=
  C.walk.getVert ((C.position v + C.walk.length - 1) % C.walk.length)

noncomputable def Cycle.successors (C : Cycle G) (A : Finset V) : Finset V :=
  (A ∩ C.vertices).image C.succ

noncomputable def Cycle.predecessors (C : Cycle G) (A : Finset V) : Finset V :=
  (A ∩ C.vertices).image C.pred

noncomputable def Path.pred (P : Path G) (v : V) : V :=
  P.walk.getVert (P.walk.support.idxOf v - 1)

noncomputable def Path.predecessors (P : Path G) (A : Finset V) : Finset V :=
  ((A ∩ P.vertices).erase P.first).image P.pred

/-- Lemma 3.1's conclusion implies that every maximum independent set
misses at least one member of `D`. -/
theorem deletable_outside_of_near_cycle {I : Finset V} (C : Cycle G)
    (hIC : I ⊆ C.vertices) (hcard : C.order + 1 = Fintype.card V) :
    ∃ u ∈ deletable G, u ∉ I := by
  obtain ⟨u, hu⟩ := C.exists_omitted_of_order hcard
  refine ⟨u, mem_deletable.mpr ⟨C, hu⟩, ?_⟩
  intro huI
  have hh := hIC huI
  simp [hu] at hh

end Broersma
