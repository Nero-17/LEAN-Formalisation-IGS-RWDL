import RequestProject.Section2SpectralScaleInequality
import RequestProject.Section31.EIGSEdgeAddressMeasure

/-! The actual time rate for any admissible positive eigenpair exceeds one.
It is not an extra input to subsequent analytic tail estimates. -/

namespace EIGS

open Filter Topology

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : (system.ruleFamily connected).Psi resistanceVector = resistanceRate • resistanceVector)

theorem XiMassParameters.rate_eq_spectralRadius :
    mass.rate = realMatrixSpectralRadius (massMatrixR system.toRuleData) := by
  symm
  exact realMatrixSpectralRadius_eq_positive_eigenvalue
    (lt_of_le_of_lt (Nat.zero_le system.initCol.val) system.initCol.isLt)
    (massMatrixR system.toRuleData)
    (massMatrixR_nonneg system.toRuleData)
    mass.amplitude mass.rate mass.amplitude_positive mass.rate_positive.le mass.eigenpair

include connected loopless unique distancePositive resistanceRatePositive
  resistanceVectorPositive renormalizationEigenpair in
theorem xiAnalyticTimeRate_distance_square_lower :
    system.distanceSpectralRadius connected ^ 2 ≤ mass.rate * resistanceRate := by
  rw [XiMassParameters.rate_eq_spectralRadius system mass,
    system.resistanceSpectralRadius_eq_of_positive_eigenpair connected distancePositive
      resistanceRatePositive resistanceVectorPositive renormalizationEigenpair]
  exact system.distanceSpectralRadius_sq_le_mass_mul_resistance connected loopless unique distancePositive

include connected loopless unique plantingNonadjacent distancePositive resistanceRatePositive
  resistanceVectorPositive renormalizationEigenpair

theorem xiAnalyticTimeRate_ge_four : 4 ≤ mass.rate * resistanceRate := by
  have distanceBound := system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive
  have scaleBound := xiAnalyticTimeRate_distance_square_lower system connected loopless unique distancePositive
    mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
  nlinarith

theorem xiAnalyticTimeRate_gt_one : 1 < mass.rate * resistanceRate :=
  (by norm_num : (1 : ℝ) < 4).trans_le
    (xiAnalyticTimeRate_ge_four system connected loopless unique plantingNonadjacent distancePositive
      mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair)

theorem xiAnalyticTailRate_tendsto_zero :
    Tendsto (fun level : ℕ => (mass.rate * resistanceRate)⁻¹ ^ level) atTop (nhds 0) := by
  have rateGreaterThanOne := xiAnalyticTimeRate_gt_one system connected loopless unique plantingNonadjacent
    distancePositive mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (inv_nonneg.mpr (zero_lt_one.trans rateGreaterThanOne).le)
    ((inv_lt_one₀ (zero_lt_one.trans rateGreaterThanOne)).mpr rateGreaterThanOne)

theorem xiAnalyticWalkExponent_ge_two :
    2 ≤ Real.log (mass.rate * resistanceRate) / Real.log (system.distanceSpectralRadius connected) := by
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  have logarithmBound := Real.log_le_log (sq_pos_of_pos (zero_lt_one.trans distanceGreaterThanOne))
    (xiAnalyticTimeRate_distance_square_lower system connected loopless unique distancePositive
      mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair)
  rw [Real.log_pow] at logarithmBound
  apply (le_div_iff₀ (Real.log_pos distanceGreaterThanOne)).mpr
  simpa only [Nat.cast_ofNat] using logarithmBound

end EIGS

#print axioms EIGS.XiMassParameters.rate_eq_spectralRadius
#print axioms EIGS.xiAnalyticTimeRate_distance_square_lower
#print axioms EIGS.xiAnalyticTimeRate_ge_four
#print axioms EIGS.xiAnalyticTimeRate_gt_one
#print axioms EIGS.xiAnalyticTailRate_tendsto_zero
#print axioms EIGS.xiAnalyticWalkExponent_ge_two
