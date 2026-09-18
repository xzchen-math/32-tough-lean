import Broersma.Cycles
import Broersma.Constructions

/-!
# Authorized external black boxes

Only previously published results appear as axioms in this file.
No assertion proved in Sections 2–4 of `v4.tex` is made an axiom.

Sources:
* Kratsch–Lehel–Müller (1996), Discrete Mathematics 150, 231–245,
  https://doi.org/10.1016/0012-365X(95)00190-8
* Ota–Sanka (2022), Journal of Graph Theory 101, 769–781,
  https://doi.org/10.1002/jgt.22852
  Author manuscript: https://arxiv.org/pdf/2103.06760
* Chvátal (1973), Discrete Mathematics 5, 215–228,
  https://doi.org/10.1016/0012-365X(73)90138-6
  The split examples are also recalled in Ota–Sanka, Introduction, p. 2,
  and in the user-supplied manuscript, Introduction.

The third axiom is the near-spanning-cycle specialization of Lemma 3.3
AND ITS PROOF: a non-Hamiltonian graph with a 2-factor has at least two
cycles in any minimum 2-factor, while the displayed cycle has one.
This specialization does not assume the main theorem of `v4.tex`.
-/

namespace Broersma.External

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- KLM (1996), the split-graph Hamiltonicity theorem. -/
axiom split_hamiltonian (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G) (hs : Split G) :
    Hamiltonian G

/-- Ota–Sanka, Proposition 1.6. -/
axiom two_factor (G : SimpleGraph V)
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G) (hf : TwoK2Free G) :
    HasTwoFactor G

/-- Ota–Sanka, Lemma 3.3 and its proof, specialized to a cycle of G-u. -/
axiom coabsorbable_successors (G : SimpleGraph V)
    (hF : HasTwoFactor G) (hnh : ¬ Hamiltonian G)
    (u : V) (C : Cycle G) (hC : C.vertices = univ.erase u) :
    Independent G (insert u (C.successors (neighborsIn G univ u))) ∧
      (neighborsIn G univ u).card + 1 ≤ independenceNumber G

/-- Chvátal's published sharp examples, instantiated with the explicitly
defined three-part graph in Constructions.lean. The exact toughness is
expressed by both its universal lower bound and an attaining vertex cut.
This axiom is used only for sharpness, never for the main reduction. -/
axiom chvatal_properties (h : ℕ) (hh : 0 < h) :
    RealTough (chvatalGraph h) (3 * (h : ℝ) / (2 * h + 1)) ∧
    ¬ Hamiltonian (chvatalGraph h) ∧
    ¬ HasTwoFactor (chvatalGraph h) ∧
    ∃ S : Finset (ChvatalVertex h), 1 < components (chvatalGraph h) S ∧
      (S.card : ℝ) = 3 * (h : ℝ) / (2 * h + 1) * components (chvatalGraph h) S

end Broersma.External
