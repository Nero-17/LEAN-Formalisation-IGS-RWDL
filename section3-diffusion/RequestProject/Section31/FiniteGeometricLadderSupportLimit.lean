import RequestProject.Section31.FiniteMarkovVectorRange
import Mathlib.Analysis.SpecificLimits.Basic

/-! Ordinary limits on a finite union of positive geometric ladders,
with finitely many positive exceptional values. Each ladder may overlap
the others. Candidate source. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem finite_geometric_ladder_support_limit {Kind Initial : Type*}
    [Fintype Kind] [Nonempty Kind] [Fintype Initial] [Nonempty Initial]
    (coefficients : Kind → ℝ) (coefficientsPositive : ∀ kind, 0 < coefficients kind)
    (initialValues : Initial → ℝ) (initialPositive : ∀ initial, 0 < initialValues initial)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate) (support : Set ℝ)
    (supportContained : support ⊆ Set.range initialValues ∪
      Set.range (fun code : Kind × ℕ => coefficients code.1 / rate ^ code.2))
    (function : ℝ → ℝ) (limit : ℝ)
    (ladderLimits : ∀ kind, Tendsto (fun level : ℕ => function (coefficients kind / rate ^ level))
      atTop (𝓝 limit)) :
    Tendsto function (𝓝[support] (0 : ℝ)) (𝓝 limit) := by
  classical
  apply Metric.tendsto_nhdsWithin_nhds.2
  intro epsilon epsilonPositive
  have eventual : ∀ kind, ∃ threshold : ℕ, ∀ level ≥ threshold,
      dist (function (coefficients kind / rate ^ level)) limit < epsilon :=
    fun kind => Metric.tendsto_atTop.1 (ladderLimits kind) epsilon epsilonPositive
  choose thresholds largeEnough using eventual
  let threshold := Finset.univ.sup thresholds
  have thresholdsBounded : ∀ kind, thresholds kind ≤ threshold :=
    fun kind => Finset.le_sup (Finset.mem_univ kind)
  have coefficientMinimumPositive : 0 < finiteVectorMinimum coefficients :=
    (Finset.lt_inf'_iff _).2 (fun kind _ => coefficientsPositive kind)
  have initialMinimumPositive : 0 < finiteVectorMinimum initialValues :=
    (Finset.lt_inf'_iff _).2 (fun initial _ => initialPositive initial)
  let radius := min (finiteVectorMinimum initialValues) (finiteVectorMinimum coefficients / rate ^ threshold)
  have radiusPositive : 0 < radius := lt_min initialMinimumPositive
    (div_pos coefficientMinimumPositive (pow_pos (zero_lt_one.trans rateGreaterThanOne) _))
  refine ⟨radius, radiusPositive, ?_⟩
  intro value inSupport nearZero
  rcases supportContained inSupport with ⟨initial, rfl⟩ | ⟨⟨kind, level⟩, rfl⟩
  · have valueSmall : initialValues initial < radius := by
      simpa only [Real.dist_eq, sub_zero, abs_of_pos (initialPositive initial)] using nearZero
    have valueLarge : radius ≤ initialValues initial :=
      (min_le_left _ _).trans (finiteVector_range_bounds initialValues initial).1
    exact ((not_lt_of_ge valueLarge) valueSmall).elim
  · have valuePositive : 0 < coefficients kind / rate ^ level :=
      div_pos (coefficientsPositive kind) (pow_pos (zero_lt_one.trans rateGreaterThanOne) _)
    have levelLarge : threshold ≤ level := by
      by_contra notLarge
      have powerBound : rate ^ level ≤ rate ^ threshold :=
        pow_le_pow_right₀ rateGreaterThanOne.le (Nat.lt_of_not_ge notLarge).le
      have valueLarge : radius ≤ coefficients kind / rate ^ level :=
        (min_le_right _ _).trans ((div_le_div_of_nonneg_left coefficientMinimumPositive.le
          (pow_pos (zero_lt_one.trans rateGreaterThanOne) _) powerBound).trans
          (div_le_div_of_nonneg_right (finiteVector_range_bounds coefficients kind).1
            (pow_pos (zero_lt_one.trans rateGreaterThanOne) _).le))
      have valueSmall : coefficients kind / rate ^ level < radius := by
        simpa only [Real.dist_eq, sub_zero, abs_of_pos valuePositive] using nearZero
      exact (not_lt_of_ge valueLarge) valueSmall
    exact largeEnough kind level ((thresholdsBounded kind).trans levelLarge)

theorem geometric_ladder_occupied_support_accumulates (coefficient rate : ℝ)
    (coefficientPositive : 0 < coefficient) (rateGreaterThanOne : 1 < rate)
    (support : Set ℝ) (occupied : ∀ level : ℕ, coefficient / rate ^ (level + 1) ∈ support) :
    NeBot (𝓝[support] (0 : ℝ)) := by
  have powerGrowth : Tendsto (fun level : ℕ => rate ^ (level + 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt rateGreaterThanOne).comp (tendsto_add_atTop_nat 1)
  have approachZero : Tendsto (fun level : ℕ => coefficient / rate ^ (level + 1))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.comp powerGrowth).const_mul coefficient
  exact (tendsto_nhdsWithin_iff.2 ⟨approachZero, Eventually.of_forall occupied⟩).neBot

end
end EIGS

#print axioms EIGS.finite_geometric_ladder_support_limit
#print axioms EIGS.geometric_ladder_occupied_support_accumulates
