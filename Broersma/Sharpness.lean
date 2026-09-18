import Broersma.External

namespace Broersma

/-- Sharpness for every real `t < 3/2`, with an explicit family of vertex
types and graphs. Only Chvátal's published example properties are black boxes;
splitness, 2K₂-freeness, size, and the threshold limit are proved in Lean. -/
theorem sharpness (t : ℝ) (ht : t < 3 / 2) :
    ∃ h : ℕ, 0 < h ∧ 3 ≤ Fintype.card (ChvatalVertex h) ∧
      Split (chvatalGraph h) ∧ TwoK2Free (chvatalGraph h) ∧
      RealTough (chvatalGraph h) t ∧ ¬ Hamiltonian (chvatalGraph h) ∧
      ¬ HasTwoFactor (chvatalGraph h) := by
  obtain ⟨h, hh, hratio⟩ := exists_chvatal_ratio_above ht
  obtain ⟨htough, hnh, hnf, _⟩ := External.chvatal_properties h hh
  refine ⟨h, hh, ?_, chvatal_split h, chvatal_twoK2Free h,
    htough.mono hratio.le, hnh, hnf⟩
  rw [chvatal_order]
  omega

end Broersma
