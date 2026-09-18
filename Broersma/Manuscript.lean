import Broersma.MainReduction
import Broersma.Paths
import Broersma.Descent
import Broersma.External

/-!
# Explicit internal proof obligations from `v4.tex`

IMPORTANT: the declarations named `...Statement` below are DEFINITIONS OF
PROPOSITIONS, not theorems and not axioms. Their presence in a successful
build does not prove them. This file records the still-unproved mathematical
content without introducing `sorryAx` or disguising internal lemmas as
external results. See `STATUS.md` for the verified/open distinction.

Natural-number inequalities are written without subtraction, to preserve
the integer inequalities in the paper even at boundary values.
-/

namespace Broersma.Manuscript

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

noncomputable def exceptional (G : SimpleGraph V) (D U J M : Finset V) : Finset V := by
  classical
  exact D.filter (fun x => neighborsIn G U x = ∅ ∧ (neighborsIn G J x \ M).Nonempty)

def PredecessorConclusion (G : SimpleGraph V) (J U M D T : Finset V)
    (u : V) (pred : V → V) : Prop :=
  Disjoint D J ∧ Independent G D ∧
  (∀ x ∈ D, ¬ G.Adj u x) ∧
  (∀ y ∈ U, (neighborsIn G D y).card ≤ 1) ∧
  (D ∩ neighborhood G U).card ≤ 1 ∧
  ∀ x ∈ T,
    M ⊂ neighborsIn G J x ∧ ¬ G.Adj u (pred x) ∧
      pred x ∉ M ∪ D ∧ neighborsIn G D (pred x) = {x}

/-- `lem:predecessor-structure`, path case. OPEN. -/
def PathPredecessorStatement (G : SimpleGraph V) : Prop :=
  ∀ (J : Finset V) (P : Path G) (u : V),
    let U := univ \ P.vertices
    let M := neighborsOfSetIn G J U
    let D := insert P.last (P.predecessors M)
    let T := exceptional G D U J M
    TwoK2Free G → Independent G J → P.Admits J → P.Dominating →
    M.Nonempty → u ∈ U → neighborsIn G J u = M →
    (∀ (Q : Path G), Q.Admits J →
      ∀ X : Finset V, X.Nonempty → X ⊆ U → Q.vertices ≠ P.vertices ∪ X) →
    (∀ (Q : Path G), Q.Admits J →
      ∀ x ∈ T, Q.vertices ≠ insert u (P.vertices.erase x)) →
    PredecessorConclusion G J U M D T u P.pred ∧
    D.card = M.card + 1 ∧
    (∀ y ∈ U, ¬ G.Adj P.first y ∧ ¬ G.Adj P.last y) ∧
    ∀ x ∈ T, x ≠ P.first

/-- `lem:predecessor-structure`, cycle case. OPEN. -/
def CyclePredecessorStatement (G : SimpleGraph V) : Prop :=
  ∀ (J : Finset V) (C : Cycle G) (u : V),
    let U := univ \ C.vertices
    let M := neighborsOfSetIn G J U
    let D := C.predecessors M
    let T := exceptional G D U J M
    TwoK2Free G → Independent G J → J ⊆ C.vertices → C.Dominating →
    M.Nonempty → u ∈ U → neighborsIn G J u = M →
    (∀ (Q : Cycle G), J ⊆ Q.vertices →
      ∀ X : Finset V, X.Nonempty → X ⊆ U → Q.vertices ≠ C.vertices ∪ X) →
    (∀ (Q : Cycle G), J ⊆ Q.vertices →
      ∀ x ∈ T, Q.vertices ≠ insert u (C.vertices.erase x)) →
    PredecessorConclusion G J U M D T u C.pred ∧ D.card = M.card

/-- `lem:path` (i). OPEN. -/
def PathExistenceStatement (G : SimpleGraph V) : Prop :=
  ∀ J : Finset V, TwoK2Free G → Independent G J → PathCover G J →
    Nonempty V → ∃ P : Path G, P.Admits J

/-- `lem:path` (ii). OPEN; its dominating-path subclaim is proved in Paths.lean. -/
def PathBoundStatement (G : SimpleGraph V) : Prop :=
  ∀ (J : Finset V) (P : Path G), TwoK2Free G → Independent G J →
    P.Admits J → (∀ Q : Path G, Q.Admits J → Q.order ≤ P.order) →
    J.card + Fintype.card V ≤ independenceNumber G + P.order

/-- `lem:path` (iii). OPEN. -/
def PathCoverBoundStatement (G : SimpleGraph V) : Prop :=
  ∀ J : Finset V, TwoK2Free G → Independent G J → PathCover G J →
    ∃ (k : ℕ) (P : Fin k → Path G),
      k + J.card ≤ independenceNumber G + 1 ∧
      (∀ i, (P i).first ∉ J ∧ (P i).last ∉ J) ∧
      (∀ i j, i ≠ j → Disjoint (P i).vertices (P j).vertices) ∧
      ∀ v : V, ∃ i, v ∈ (P i).vertices

/-- `lem:cycle`. OPEN. -/
def CycleBoundStatement (G : SimpleGraph V) : Prop :=
  ∀ (J : Finset V) (C : Cycle G), TwoK2Free G → Independent G J →
    J ⊆ C.vertices → C.Dominating →
    (∀ Q : Cycle G, J ⊆ Q.vertices → Q.Dominating → Q.order ≤ C.order) →
    J.card + Fintype.card V ≤ independenceNumber G + C.order + 1

/-- `lem:n-1cycle`. OPEN. -/
def NearSpanningCycleStatement (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ToughThreeHalves G → TwoK2Free G → ¬ Hamiltonian G →
    ∀ I : Finset V, MaximumIndependent G I →
      ∃ C : Cycle G, I ⊆ C.vertices ∧ C.order + 1 = Fintype.card V

/-- The fixed-I maximum used before `prop:s3-omitted-vertices`. -/
def FixedPair (G : SimpleGraph V) (I : Finset V) (u : V) : Prop :=
  MaximumIndependent G I ∧ u ∈ deletable G ∧ u ∉ I ∧
    ∀ z ∈ deletable G, (neighborsIn G I z).card ≤ (neighborsIn G I u).card

/-- `prop:s3-omitted-vertices`. OPEN. -/
def OmittedVerticesStatement (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ToughThreeHalves G → TwoK2Free G → ¬ Hamiltonian G →
    ∀ (I : Finset V) (u : V), FixedPair G I u →
      ∀ (Q : Cycle G) (r s : V), Q.Dominating → I ⊆ Q.vertices →
        Q.order + 2 = Fintype.card V → univ \ Q.vertices = {r, s} →
        (neighborsIn G I u).card < (neighborsIn G I r).card → s ∈ deletable G

/-- The conclusions of `lem:s3-structure` for a specified oriented cycle. -/
def CycleStructure (G : SimpleGraph V) (I : Finset V) (u : V) (C : Cycle G) : Prop :=
  let N := neighborsIn G univ u
  let M := neighborsIn G I u
  let I₀ := I \ M
  Independent G (insert u (C.successors N)) ∧
  N.card + 1 ≤ independenceNumber G ∧
  ∃ a,
    a ∈ C.predecessors M ∧ a ∈ neighborhood G I₀ ∧
    (∀ x ∈ C.predecessors M, x ∈ neighborhood G I₀ → x = a) ∧
    M ⊂ neighborsIn G I a ∧
    C.predecessors N \ I = C.predecessors M ∧
    C.predecessors M \ deletable G = {a} ∧
    ¬ G.Adj u (C.pred a) ∧
    (∃! b, b ∈ C.successors M ∧ b ∈ neighborhood G I₀) ∧
    ∀ x ∈ N \ I, C.pred x ∈ I₀ ∧ C.succ x ∈ I₀

/-- `lem:s3-structure`. OPEN; part (i) is available as an external black box. -/
def StructureStatement (G : SimpleGraph V) : Prop :=
  3 ≤ Fintype.card V → ToughThreeHalves G → TwoK2Free G → ¬ Hamiltonian G →
    ∀ (I : Finset V) (u : V), FixedPair G I u →
      ∀ C : Cycle G, C.vertices = univ.erase u → CycleStructure G I u C

/-- A checked implication from the near-spanning-cycle lemma to the exact
extremal choice used later. The near-spanning lemma itself remains a premise. -/
theorem extremal_pair_of_near_cycles (G : SimpleGraph V)
    (hnear : NearSpanningCycleStatement G)
    (hn : 3 ≤ Fintype.card V) (ht : ToughThreeHalves G) (hf : TwoK2Free G)
    (hnh : ¬ Hamiltonian G) : ∃ I u, ExtremalPair G (deletable G) I u := by
  apply exists_extremalPair
  intro I hI
  obtain ⟨C, hIC, hcard⟩ := hnear hn ht hf hnh I hI
  exact deletable_outside_of_near_cycle C hIC hcard

end Broersma.Manuscript
