import Broersma.External
import Broersma.TwoK2Free

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Complete the complement of `I` to a clique, as in Lemma 3.1. -/
def splitCompletion (G : SimpleGraph V) (I : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x ∉ I ∧ y ∉ I ∧ x ≠ y)
  symm := ⟨by
    intro x y h
    rcases h with h | ⟨hx, hy, hxy⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨hy, hx, hxy.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | ⟨_, _, h⟩
    · exact G.irrefl h
    · exact h rfl⟩

theorem le_splitCompletion (G : SimpleGraph V) (I : Finset V) :
    G ≤ splitCompletion G I := fun _ _ h => Or.inl h

theorem splitCompletion_split {G : SimpleGraph V} {I : Finset V}
    (hI : Independent G I) : Split (splitCompletion G I) := by
  refine ⟨I, ?_, ?_⟩
  · intro x hx y hy hxy
    rcases hxy with h | ⟨h, _, _⟩
    · exact hI hx hy h
    · exact h hx
  · intro x y hx hy hxy
    exact Or.inr ⟨hx, hy, hxy⟩

/-- No new edge of the completion is incident with the independent set. -/
theorem splitCompletion_adj_of_mem {G : SimpleGraph V} {I : Finset V}
    {x y : V} (hx : x ∈ I) : (splitCompletion G I).Adj x y ↔ G.Adj x y := by
  constructor
  · rintro (h | ⟨h, _, _⟩)
    · exact h
    · exact (h hx).elim
  · exact Or.inl

/-- The use of the authorized KLM black box in Lemma 3.1.
The preservation of toughness and the completion itself are proved. -/
theorem split_completion_hamiltonian (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G)
    {I : Finset V} (hI : Independent G I) : Hamiltonian (splitCompletion G I) := by
  exact External.split_hamiltonian _ hn (ht.mono (le_splitCompletion G I))
    (splitCompletion_split hI)

end Broersma
