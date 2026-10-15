import RequestProject.Section31.EIGSSameNativeJointFullHeatEstimatesOfRules
import RequestProject.Section3.SpectralDimension

/-! All-point spectral dimension from a single kernel's pure-power bounds. -/
namespace IGS.Sec31
open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

theorem positiveKernelRealDiagonal_spectral_dimension_of_power_bounds
    {Space : Type*}
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ)
    (heatExponent cutoffTime lowerConstant upperConstant : ℝ)
    (cutoffPositive : 0 < cutoffTime) (lowerPositive : 0 < lowerConstant)
    (upperPositive : 0 < upperConstant)
    (bounds : ∀ time : {time : ℝ≥0 // 0 < time}, (time.val : ℝ) ≤ cutoffTime →
      ∀ point : Space, lowerConstant / (time.val : ℝ) ^ heatExponent ≤ kernel time point point ∧
        kernel time point point ≤ upperConstant / (time.val : ℝ) ^ heatExponent) :
    ∀ point : Space, Tendsto (fun time : ℝ =>
      -2 * Real.log (positiveKernelRealDiagonal kernel time point) / Real.log time)
      (𝓝[>] (0 : ℝ)) (𝓝 (2 * heatExponent)) := by
  intro point
  apply IGS.tendsto_spectral_dimension_of_pure_bounds _ heatExponent lowerConstant upperConstant cutoffTime
    lowerPositive upperPositive cutoffPositive
  · intro time timeInRange
    have bound := (bounds ⟨⟨time, timeInRange.1.le⟩, timeInRange.1⟩ timeInRange.2.le point).1
    simpa only [positiveKernelRealDiagonal, dif_pos timeInRange.1,
      Real.rpow_neg timeInRange.1.le, div_eq_mul_inv] using bound
  · intro time timeInRange
    have bound := (bounds ⟨⟨time, timeInRange.1.le⟩, timeInRange.1⟩ timeInRange.2.le point).2
    simpa only [positiveKernelRealDiagonal, dif_pos timeInRange.1,
      Real.rpow_neg timeInRange.1.le, div_eq_mul_inv] using bound

end
end IGS.Sec31

#print axioms IGS.Sec31.positiveKernelRealDiagonal_spectral_dimension_of_power_bounds
