import Broersma.External
import Broersma.Extremal

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Lemma 3.3(i), using only the two authorized Ota–Sanka black boxes.
This applies to any specified oriented cycle spanning `G-u`. -/
theorem near_cycle_external_structure
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G)
    (hf : TwoK2Free G) (hnh : ¬ Hamiltonian G)
    (u : V) (C : Cycle G) (hC : C.vertices = univ.erase u) :
    Independent G (insert u (C.successors (neighborsIn G univ u))) ∧
      (neighborsIn G univ u).card + 1 ≤ independenceNumber G := by
  exact External.coabsorbable_successors G (External.two_factor G hn ht hf) hnh u C hC

theorem deletable_degree_bound
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G)
    (hf : TwoK2Free G) (hnh : ¬ Hamiltonian G)
    {u : V} (hu : u ∈ deletable G) :
    (neighborsIn G univ u).card + 1 ≤ independenceNumber G := by
  obtain ⟨C, hC⟩ := mem_deletable.mp hu
  exact (near_cycle_external_structure hn ht hf hnh u C hC).2

/-- The degree subtraction `|T'| ≤ k-1` in Sections 3 and 4,
with no truncated subtraction in the conclusion. -/
theorem excess_neighbors_bound {J K I₀ : Finset V} {v : V}
    (hJ : MaximumIndependent G J)
    (hdegree : (neighborsIn G univ v).card + 1 ≤ independenceNumber G)
    (hK : neighborsIn G J v = K) (hcard : J.card = K.card + I₀.card) :
    (neighborsIn G univ v \ K).card + 1 ≤ I₀.card := by
  have hsub : K ⊆ neighborsIn G univ v := by
    intro z hz
    rw [← hK] at hz
    exact mem_neighborsIn.mpr ⟨mem_univ _, (mem_neighborsIn.mp hz).2⟩
  have heq := card_sdiff_add_card_eq_card hsub
  have hc := hJ.card_eq
  omega

end Broersma
