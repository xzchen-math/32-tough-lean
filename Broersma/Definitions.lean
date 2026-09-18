import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Tactic

/-!
# Definitions for Chen–Ning, `v4.tex`

All graphs use mathlib's `SimpleGraph`.  Vertex sets are finite sets; the
number of components is the cardinality of the actual reachability quotient
of the induced graph after deletion.  No graph property is a free predicate.
-/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- A finite independent set, including the empty set. -/
def Independent (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ ⦃x⦄, x ∈ I → ∀ ⦃y⦄, y ∈ I → ¬ G.Adj x y

def Anticomplete (G : SimpleGraph V) (A B : Finset V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ¬ G.Adj a b

/-- Absence of an induced pair of disjoint edges.  The four cross
inequalities, together with the two edges, assert four distinct vertices. -/
def TwoK2Free (G : SimpleGraph V) : Prop :=
  ∀ ⦃a b c d⦄, G.Adj a b → G.Adj c d →
    a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    G.Adj a c ∨ G.Adj a d ∨ G.Adj b c ∨ G.Adj b d

noncomputable def neighborhood (G : SimpleGraph V) (A : Finset V) : Finset V :=
  by classical exact univ.filter (fun x => ∃ a ∈ A, G.Adj x a)

noncomputable def neighborsIn (G : SimpleGraph V) (I : Finset V) (x : V) : Finset V :=
  by classical exact I.filter (G.Adj x)

noncomputable def neighborsOfSetIn (G : SimpleGraph V) (I A : Finset V) : Finset V :=
  I ∩ neighborhood G A

abbrev Deleted (G : SimpleGraph V) (S : Finset V) := G.induce {v | v ∉ S}

noncomputable def components (G : SimpleGraph V) (S : Finset V) : ℕ :=
  Nat.card (Deleted G S).ConnectedComponent

/-- The denominator-free, exact definition of 3/2-toughness. -/
def ToughThreeHalves (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, 1 < components G S → 3 * components G S ≤ 2 * S.card

def Tough (G : SimpleGraph V) (t : ℚ) : Prop :=
  ∀ S : Finset V, 1 < components G S → t * (components G S : ℚ) ≤ S.card

noncomputable def independenceNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (univ.filter (Independent G)).sup Finset.card

def MaximumIndependent (G : SimpleGraph V) (I : Finset V) : Prop :=
  Independent G I ∧ ∀ J : Finset V, Independent G J → J.card ≤ I.card

def Split (G : SimpleGraph V) : Prop :=
  ∃ I : Finset V, Independent G I ∧
    ∀ ⦃x y⦄, x ∉ I → y ∉ I → x ≠ y → G.Adj x y

/-- A nonempty simple path. Single-vertex paths are permitted. -/
structure Path (G : SimpleGraph V) where
  first : V
  last : V
  walk : G.Walk first last
  simple : walk.IsPath

noncomputable def Path.vertices {G : SimpleGraph V} (P : Path G) : Finset V :=
  P.walk.support.toFinset

noncomputable def Path.order {G : SimpleGraph V} (P : Path G) : ℕ := P.vertices.card

def Path.Admits {G : SimpleGraph V} (P : Path G) (J : Finset V) : Prop :=
  J ⊆ P.vertices ∧ P.first ∉ J ∧ P.last ∉ J

def Path.Dominating {G : SimpleGraph V} (P : Path G) : Prop :=
  Independent G (univ \ P.vertices)

/-- A genuine simple cycle, using mathlib's `Walk.IsCycle` (length ≥ 3). -/
structure Cycle (G : SimpleGraph V) where
  base : V
  walk : G.Walk base base
  simple : walk.IsCycle

noncomputable def Cycle.vertices {G : SimpleGraph V} (C : Cycle G) : Finset V :=
  C.walk.support.toFinset

noncomputable def Cycle.order {G : SimpleGraph V} (C : Cycle G) : ℕ := C.vertices.card

def Cycle.Dominating {G : SimpleGraph V} (C : Cycle G) : Prop :=
  Independent G (univ \ C.vertices)

def HasCycleOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∃ C : Cycle G, C.vertices = A

/-- The paper's Hamiltonicity convention requires a genuine spanning cycle. -/
def Hamiltonian (G : SimpleGraph V) : Prop := HasCycleOn G univ

noncomputable def deletable (G : SimpleGraph V) : Finset V := by
  classical
  exact univ.filter (fun x => HasCycleOn G (univ.erase x))

def PathCover (G : SimpleGraph V) (J : Finset V) : Prop :=
  ∃ (k : ℕ) (P : Fin k → Path G),
    (∀ i, (P i).first ∉ J ∧ (P i).last ∉ J) ∧
    (∀ i j, i ≠ j → Disjoint (P i).vertices (P j).vertices) ∧
    ∀ v : V, ∃ i, v ∈ (P i).vertices

def HasTwoFactor (G : SimpleGraph V) : Prop :=
  ∃ F : SimpleGraph V, F ≤ G ∧ ∀ v : V, (F.neighborSet v).ncard = 2

end Broersma
