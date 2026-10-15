import Mathlib

/-! Finite-prefix and finite-index packaging for actual geometric bounds.
These helpers retain the same positive rate and do not introduce a new
growth rate or discard any generation. -/

namespace EIGS
noncomputable section
open Filter Topology
open scoped Classical

theorem geometric_bounds_all_generations_of_eventually
    (sequence : ℕ → ℝ) (rate : ℝ) (ratePositive : 0 < rate)
    (positive : ∀ level, 0 < sequence level)
    (eventualBounds : ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ᶠ level in atTop, lower * rate ^ level ≤ sequence level ∧ sequence level ≤ upper * rate ^ level) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ level, lower * rate ^ level ≤ sequence level ∧ sequence level ≤ upper * rate ^ level := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, bounds⟩ := eventualBounds
  obtain ⟨threshold, after⟩ := eventually_atTop.mp bounds
  have prefixNonempty : (Finset.range (threshold + 1)).Nonempty := by simp
  let prefixLower := (Finset.range (threshold + 1)).inf' prefixNonempty
    (fun level => sequence level / rate ^ level)
  let prefixUpper := (Finset.range (threshold + 1)).sup' prefixNonempty
    (fun level => sequence level / rate ^ level)
  have prefixLowerPositive : 0 < prefixLower :=
    (Finset.lt_inf'_iff _).2 (fun level _ => div_pos (positive level) (pow_pos ratePositive level))
  refine ⟨min lower prefixLower, max upper prefixUpper,
    lt_min lowerPositive prefixLowerPositive, upperPositive.trans_le (le_max_left _ _), ?_⟩
  intro level
  by_cases large : threshold ≤ level
  · exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_pos ratePositive level).le).trans
      (after level large).1,
      (after level large).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_pos ratePositive level).le)⟩
  · have inPrefix : level ∈ Finset.range (threshold + 1) := Finset.mem_range.mpr (by omega)
    have lowerComparison : prefixLower ≤ sequence level / rate ^ level := Finset.inf'_le _ inPrefix
    have upperComparison : sequence level / rate ^ level ≤ prefixUpper :=
      Finset.le_sup' (fun level => sequence level / rate ^ level) inPrefix
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) (pow_pos ratePositive level).le).trans
      ((le_div_iff₀ (pow_pos ratePositive level)).1 lowerComparison),
      ((div_le_iff₀ (pow_pos ratePositive level)).1 upperComparison).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_pos ratePositive level).le)⟩

theorem finite_family_uniform_geometric_bounds {Index : Type*} [Fintype Index] [Nonempty Index]
    (sequence : Index → ℕ → ℝ) (rate : ℝ) (ratePositive : 0 < rate)
    (bounds : ∀ index, ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ level, lower * rate ^ level ≤ sequence index level ∧ sequence index level ≤ upper * rate ^ level) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ index level, lower * rate ^ level ≤ sequence index level ∧ sequence index level ≤ upper * rate ^ level := by
  choose lower upper lowerPositive upperPositive bound using bounds
  let uniformLower := Finset.univ.inf' Finset.univ_nonempty lower
  let uniformUpper := Finset.univ.sup' Finset.univ_nonempty upper
  refine ⟨uniformLower, uniformUpper,
    (Finset.lt_inf'_iff _).2 (fun index _ => lowerPositive index),
    (upperPositive (Classical.arbitrary Index)).trans_le
      (Finset.le_sup' _ (Finset.mem_univ _)), ?_⟩
  intro index level
  exact ⟨(mul_le_mul_of_nonneg_right (Finset.inf'_le _ (Finset.mem_univ index))
      (pow_pos ratePositive level).le).trans (bound index level).1,
    (bound index level).2.trans (mul_le_mul_of_nonneg_right
      (Finset.le_sup' _ (Finset.mem_univ index)) (pow_pos ratePositive level).le)⟩

end
end EIGS

#print axioms EIGS.geometric_bounds_all_generations_of_eventually
#print axioms EIGS.finite_family_uniform_geometric_bounds
