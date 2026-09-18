import Broersma.TwoK2Free
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Broersma

open Finset

universe u

/-- Toughness for arbitrary real thresholds, used in the sharpness statement. -/
def RealTough {V : Type u} [Fintype V] (G : SimpleGraph V) (t : ℝ) : Prop :=
  ∀ S : Finset V, 1 < components G S → t * (components G S : ℝ) ≤ S.card

theorem RealTough.mono {V : Type u} [Fintype V] {G : SimpleGraph V} {s t : ℝ}
    (h : RealTough G t) (hst : s ≤ t) : RealTough G s := by
  intro S hS
  exact (mul_le_mul_of_nonneg_right hst (Nat.cast_nonneg _)).trans (h S hS)

/-- Vertices of Chvátal's example: `S`, `R`, and `T`, with cardinalities
`h`, `2h+1`, and `2h+1`. -/
abbrev ChvatalVertex (h : ℕ) := Fin h ⊕ (Fin (2 * h + 1) ⊕ Fin (2 * h + 1))

def chvatalRelation {h : ℕ} : ChvatalVertex h → ChvatalVertex h → Prop
  | .inl _, _ => True
  | _, .inl _ => True
  | .inr (.inl _), .inr (.inl _) => True
  | .inr (.inl i), .inr (.inr j) => i = j
  | .inr (.inr i), .inr (.inl j) => i = j
  | .inr (.inr _), .inr (.inr _) => False

def chvatalGraph (h : ℕ) : SimpleGraph (ChvatalVertex h) :=
  SimpleGraph.fromRel chvatalRelation

def chvatalT (h : ℕ) : Finset (ChvatalVertex h) :=
  univ.image (fun i : Fin (2 * h + 1) => Sum.inr (Sum.inr i))

@[simp] theorem mem_chvatalT {h : ℕ} {x : ChvatalVertex h} :
    x ∈ chvatalT h ↔ ∃ i, x = Sum.inr (Sum.inr i) := by
  simp [chvatalT, eq_comm]

theorem chvatal_order (h : ℕ) : Fintype.card (ChvatalVertex h) = 5 * h + 2 := by
  simp [ChvatalVertex, Fintype.card_sum]
  omega

theorem chvatal_split (h : ℕ) : Split (chvatalGraph h) := by
  refine ⟨chvatalT h, ?_, ?_⟩
  · intro x hx y hy hxy
    obtain ⟨i, rfl⟩ := mem_chvatalT.mp hx
    obtain ⟨j, rfl⟩ := mem_chvatalT.mp hy
    simp [chvatalGraph, SimpleGraph.fromRel, chvatalRelation] at hxy
  · intro x y hx hy hxy
    rcases x with x | (x | x) <;> rcases y with y | (y | y) <;>
      simp_all [chvatalGraph, SimpleGraph.fromRel, chvatalRelation, mem_chvatalT]

theorem chvatal_twoK2Free (h : ℕ) : TwoK2Free (chvatalGraph h) :=
  (chvatal_split h).twoK2Free

/-- Exact distance of the toughness ratio from 3/2. -/
theorem chvatal_ratio (h : ℕ) :
    (3 : ℝ) * h / (2 * h + 1) = 3 / 2 - 3 / (4 * h + 2) := by
  have hp : (0 : ℝ) < 2 * h + 1 := by positivity
  have hq : (0 : ℝ) < 4 * h + 2 := by positivity
  field_simp
  ring

theorem chvatal_ratio_lt (h : ℕ) : (3 : ℝ) * h / (2 * h + 1) < 3 / 2 := by
  rw [chvatal_ratio]
  have : (0 : ℝ) < 3 / (4 * h + 2) := by positivity
  linarith

/-- The explicit sequence approaches the threshold from below. -/
theorem exists_chvatal_ratio_above {t : ℝ} (ht : t < 3 / 2) :
    ∃ h : ℕ, 0 < h ∧ t < 3 * (h : ℝ) / (2 * h + 1) := by
  have he : 0 < (3 : ℝ) / 2 - t := by linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (3 / (((3 : ℝ) / 2 - t) * 4))
  refine ⟨n + 1, by omega, ?_⟩
  rw [chvatal_ratio]
  have hpos : (0 : ℝ) < ((3 : ℝ) / 2 - t) * 4 := by positivity
  have hmul := (div_lt_iff₀ hpos).mp hn
  have hd : (0 : ℝ) < 4 * (n + 1 : ℕ) + 2 := by positivity
  have hdiv : 3 / (4 * (n + 1 : ℕ) + 2 : ℝ) < 3 / 2 - t := by
    apply (div_lt_iff₀ hd).mpr
    push_cast
    nlinarith
  linarith

end Broersma
