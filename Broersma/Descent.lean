import Broersma.Definitions

/-! The finite arithmetic behind the threshold descent in Lemmas 2.3 and 2.4.
The construction of the next path/cycle is a separate proof obligation. -/

namespace Broersma

open Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

def aboveThreshold (weight : V → ℕ) (U : Finset V) (m : ℕ) : Finset V :=
  U.filter (fun v => m < weight v)

theorem threshold_removal_bound (weight : V → ℕ) (U X : Finset V) (m : ℕ) :
    (aboveThreshold weight U m).card ≤
      (aboveThreshold weight (U \ X) m).card + X.card := by
  have hsub : aboveThreshold weight U m ⊆ aboveThreshold weight (U \ X) m ∪ X := by
    intro v hv
    by_cases hvX : v ∈ X
    · exact mem_union_right _ hvX
    · simp only [aboveThreshold, mem_filter] at hv
      exact mem_union_left _ (by simp [aboveThreshold, hv.1, hv.2, hvX])
  have hh := card_le_card hsub
  have hh' := card_union_le (aboveThreshold weight (U \ X) m) X
  omega

theorem threshold_swap (weight : V → ℕ) {U : Finset V} {u x : V} {m : ℕ}
    (hu : u ∈ U) (hx : x ∉ U) (hwu : m < weight u) (hwx : m < weight x) :
    (aboveThreshold weight (insert x (U.erase u)) m).card =
      (aboveThreshold weight U m).card := by
  have hset : aboveThreshold weight (insert x (U.erase u)) m =
      insert x ((aboveThreshold weight U m).erase u) := by
    ext v
    simp only [aboveThreshold, mem_filter, mem_insert, mem_erase]
    by_cases hvx : v = x
    · subst v; simp [hwx]
    · tauto
  have hxout : x ∉ (aboveThreshold weight U m).erase u := by
    simp only [mem_erase, aboveThreshold, mem_filter]
    tauto
  have huin : u ∈ aboveThreshold weight U m := by simp [aboveThreshold, hu, hwu]
  rw [hset, card_insert_of_notMem hxout, card_erase_of_mem huin]
  have := card_pos.mpr ⟨u, huin⟩
  omega

theorem threshold_two_for_one (weight : V → ℕ) {U : Finset V} {u x z : V} {m : ℕ}
    (hu : u ∈ U) (hx : x ∉ U) (hz : z ∉ U) (hxz : x ≠ z)
    (hwu : m < weight u) (hwx : m < weight x) (hwz : m < weight z) :
    (aboveThreshold weight (insert z (insert x (U.erase u))) m).card =
      (aboveThreshold weight U m).card + 1 := by
  have hs : aboveThreshold weight (insert z (insert x (U.erase u))) m =
      insert z (aboveThreshold weight (insert x (U.erase u)) m) := by
    ext v
    simp only [aboveThreshold, mem_filter, mem_insert]
    by_cases hvz : v = z
    · subst v; simp [hwz]
    · tauto
  have hzout : z ∉ aboveThreshold weight (insert x (U.erase u)) m := by
    simp only [aboveThreshold, mem_filter, mem_insert, mem_erase]
    have hzx := hxz.symm
    tauto
  rw [hs, card_insert_of_notMem hzout, threshold_swap weight hu hx hwu hwx]

/-- A bounded strictly increasing sequence of natural-number thresholds
cannot continue indefinitely. -/
theorem bounded_growth_impossible (m : ℕ → ℕ) (B : ℕ)
    (hstep : ∀ r, m r < m (r + 1)) (hbound : ∀ r, m r ≤ B) : False := by
  have hge : ∀ r, r ≤ m r := by
    intro r
    induction r with
    | zero => omega
    | succ r ih => have := hstep r; omega
  have := hge (B + 1)
  have := hbound (B + 1)
  omega

/-- An alternative finite form: if every nonterminal stage has a larger
threshold, some terminal stage must exist. -/
theorem exists_terminal_of_growth {State : Type u} [Fintype State]
    (valid terminal : State → Prop) (weight : State → ℕ)
    (hne : ∃ s, valid s)
    (step : ∀ s, valid s → ¬ terminal s → ∃ t, valid t ∧ weight s < weight t) :
    ∃ s, valid s ∧ terminal s := by
  classical
  let S := Finset.univ.filter valid
  have hs : S.Nonempty := by
    obtain ⟨s, hs⟩ := hne
    exact ⟨s, by simp [S, hs]⟩
  obtain ⟨s, hs, hmax⟩ := S.exists_max_image weight hs
  have hvalid : valid s := (mem_filter.mp hs).2
  refine ⟨s, hvalid, ?_⟩
  by_contra hnot
  obtain ⟨t, ht, hlt⟩ := step s hvalid hnot
  have hle := hmax t (by simp [S, ht])
  omega

end Broersma
