import Broersma.Cut
import Broersma.Neighborhood
import Broersma.Extremal

/-!
# Verified reduction of the main theorem

`FinalConfiguration` records exactly the outstanding graph construction and
Claims 4.1–4.3. Its *existence is not asserted in this module*.
`main_of_configuration` is deliberately a CONDITIONAL theorem.  Supplying
`construct` requires the remaining proofs from Sections 2–4; it is not an
external black box and has not been discharged.
-/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def Path.neighborsIn (G : SimpleGraph V) (P : Path G)
    (W : Finset V) (z : V) : Finset V := by
  classical
  exact W.filter (fun w => s(z, w) ∈ P.walk.edges)

noncomputable def Path.doubleNeighborVertices (G : SimpleGraph V)
    (P : Path G) (W : Finset V) : Finset V := by
  classical
  exact P.vertices.filter (fun z => (P.neighborsIn G W z).card = 2)

/-- Concrete graph data needed in the last part of the proof.
The three claims are about cardinalities of actual finite vertex sets. -/
structure FinalConfiguration (G : SimpleGraph V) where
  I : Finset V
  I₀ : Finset V
  K : Finset V
  W : Finset V
  H : Finset V
  u : V
  v : V
  C : Cycle G
  P : Path G
  I_maximum : MaximumIndependent G I
  I₀_subset : I₀ ⊆ I
  I₀_nonempty : I₀.Nonempty
  cardinal_split : I.card = K.card + I₀.card
  u_outside : u ∉ I₀
  u_no_neighbor : u ∉ neighborhood G I₀
  v_no_neighbor : v ∉ neighborhood G I₀
  uv_edge : G.Adj u v
  cycle_vertices : C.vertices = univ.erase u
  I_on_cycle : I ⊆ C.vertices
  predecessors_outside : C.predecessors (neighborsIn G I u) ⊆ C.vertices \ I
  successors_outside : C.successors (neighborsIn G I u) ⊆ C.vertices \ I
  predecessors_card : (C.predecessors (neighborsIn G I u)).card = K.card
  successors_card : (C.successors (neighborsIn G I u)).card = K.card
  predecessor_exception :
    (neighborhood G I₀ ∩ C.predecessors (neighborsIn G I u)).card ≤ 1
  successor_exception :
    (neighborhood G I₀ ∩ C.successors (neighborsIn G I u)).card ≤ 1
  M_anticomplete : Anticomplete G (neighborsIn G I u) I₀
  K_anticomplete : Anticomplete G K I₀
  T_subset : neighborsIn G univ u \ neighborsIn G I u ⊆ neighborhood G I₀
  T'_subset : neighborsIn G univ v \ K ⊆ neighborhood G I₀
  T'_card : (neighborsIn G univ v \ K).card + 1 ≤ I₀.card
  /-- Claim `claim:n`. -/
  claim_n : (Fintype.card V : ℤ) =
    2 * (W.card : ℤ) - 1 - (P.doubleNeighborVertices G W).card + I.card + (H \ I).card
  /-- Claim `claim:h`. -/
  claim_h :
    ((C.predecessors (neighborsIn G I u) ∩ C.successors (neighborsIn G I u)).card : ℤ) +
      (neighborsIn G univ u \ neighborsIn G I u).card + W.card - I.card ≤
        (P.doubleNeighborVertices G W).card
  /-- Claim `claim:|W|+|V(H)setminus I|`. -/
  claim_WH : (W.card : ℤ) + (H \ I).card ≤ (I.card : ℤ) - 1

namespace FinalConfiguration

variable {G : SimpleGraph V}

theorem neighborhood_on_cycle (F : FinalConfiguration G) :
    neighborhood G F.I₀ ⊆ F.C.vertices \ F.I := by
  intro z hz
  have hzu : z ≠ F.u := by intro h; subst z; exact F.u_no_neighbor hz
  have hzI : z ∉ F.I := by
    intro hzI
    obtain ⟨y, hy, hzy⟩ := mem_neighborhood.mp hz
    exact F.I_maximum.1 hzI (F.I₀_subset hy) hzy
  apply mem_sdiff.mpr
  exact ⟨by simp [F.cycle_vertices, hzu], hzI⟩

theorem complement_card (F : FinalConfiguration G) :
    (F.C.vertices \ F.I).card + F.I.card + 1 = Fintype.card V := by
  have hu : F.u ∈ (univ : Finset V) := mem_univ _
  have hc : F.C.vertices.card + 1 = Fintype.card V := by
    rw [F.cycle_vertices, card_erase_of_mem hu, card_univ]
    have hpos := Fintype.card_pos_iff.mpr ⟨F.u⟩
    omega
  rw [card_sdiff_of_subset F.I_on_cycle]
  have := card_le_card F.I_on_cycle
  omega

theorem first_bound (F : FinalConfiguration G) :
    (neighborhood G F.I₀).card +
      (neighborsIn G univ F.u \ neighborsIn G F.I F.u).card + 1 ≤ 2 * F.I₀.card := by
  have hc := neighborhood_union_count F.neighborhood_on_cycle
    F.predecessors_outside F.successors_outside
    F.predecessor_exception F.successor_exception
  rw [F.predecessors_card, F.successors_card] at hc
  have hcomp := F.complement_card
  have hci : ((neighborhood G F.I₀).card : ℤ) + (F.K.card : ℤ) + F.K.card ≤
      ((F.C.vertices \ F.I).card : ℤ) +
      (F.C.predecessors (neighborsIn G F.I F.u) ∩
        F.C.successors (neighborsIn G F.I F.u)).card + 2 := by exact_mod_cast hc
  have hco : ((F.C.vertices \ F.I).card : ℤ) + F.I.card + 1 = Fintype.card V :=
    by exact_mod_cast hcomp
  have hα : (F.I.card : ℤ) = (F.K.card : ℤ) + F.I₀.card :=
    by exact_mod_cast F.cardinal_split
  have hs : ((neighborhood G F.I₀).card : ℤ) ≤
      (Fintype.card V : ℤ) - F.I.card - 2 * F.K.card +
      (F.C.predecessors (neighborsIn G F.I F.u) ∩
        F.C.successors (neighborsIn G F.I F.u)).card + 1 := by omega
  have hb := first_neighborhood_bound _ _ _ _ _ _ _ _ _ _ hα F.claim_n
    F.claim_h F.claim_WH hs
  exact_mod_cast hb

theorem second_bound (hf : TwoK2Free G) (F : FinalConfiguration G) :
    (neighborhood G F.I₀).card + 1 ≤
      (neighborsIn G univ F.u \ neighborsIn G F.I F.u).card + F.I₀.card := by
  have heq := neighborhood_eq_union hf F.uv_edge F.u_no_neighbor F.v_no_neighbor
    F.M_anticomplete F.K_anticomplete F.T_subset F.T'_subset
  have hcard := card_union_le (neighborsIn G univ F.u \ neighborsIn G F.I F.u)
    (neighborsIn G univ F.v \ F.K)
  rw [← heq] at hcard
  have hh := F.T'_card
  omega

/-- The last part of the paper is verified from a concrete configuration. -/
theorem impossible (ht : ToughThreeHalves G) (hf : TwoK2Free G)
    (F : FinalConfiguration G) : False := by
  exact cut_contradiction ht (F.I_maximum.1.mono F.I₀_subset) F.I₀_nonempty
    F.u_outside F.u_no_neighbor _ F.first_bound (F.second_bound hf)

end FinalConfiguration

/-- Exact statement of Theorem 1.4 in `v4.tex`; no proof is asserted here. -/
def MainTheoremStatement (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ToughThreeHalves G → TwoK2Free G → Hamiltonian G

/-- The missing internal construction. This is a proposition, not an axiom. -/
def InternalConstruction (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ToughThreeHalves G → TwoK2Free G →
    ¬ Hamiltonian G → Nonempty (FinalConfiguration G)

/-- CONDITIONAL reduction, not an unconditional proof of the main theorem.
The `construct` argument remains an internal proof obligation. -/
theorem main_of_configuration (G : SimpleGraph V) (construct : InternalConstruction G) :
    MainTheoremStatement G := by
  intro hn ht hf
  by_contra hnh
  obtain ⟨F⟩ := construct hn ht hf hnh
  exact F.impossible ht hf

end Broersma
