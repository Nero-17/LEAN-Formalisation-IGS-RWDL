import RequestProject.Section31.PoissonizedWalkTimeRounding

/-! The extra endpoint rounding error in differences of absolute floor
clocks vanishes at diverging jump rate. This is a scalar estimate; actual
models must supply their native jump-rate divergence internally. -/

namespace IGS.Sec31.PoissonizedWalk

open Filter Topology

theorem rounding_coefficient_additive_tendsto_zero
    {Index : Type*} {filter : Filter Index} (rate : Index → ℝ)
    (rateLimit : Tendsto rate filter atTop) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (offset : ℝ) :
    Tendsto (fun index => (Real.sqrt (Nat.floor (time * rate index)) + offset) / rate index)
      filter (𝓝 0) := by
  have inverseLimit : Tendsto (fun index => (rate index)⁻¹) filter (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp rateLimit
  have correctionLimit : Tendsto (fun index => (offset - 1) / rate index) filter (𝓝 (0 : ℝ)) := by
    simpa only [div_eq_mul_inv, mul_zero] using inverseLimit.const_mul (offset - 1)
  have combined := (rounding_coefficient_tendsto_zero rate rateLimit time timeNonnegative).add correctionLimit
  have identity (index : Index) :
      (Real.sqrt (Nat.floor (time * rate index)) + 1) / rate index + (offset - 1) / rate index =
        (Real.sqrt (Nat.floor (time * rate index)) + offset) / rate index := by ring
  simpa only [identity, zero_add] using combined

theorem absolute_clock_coefficient_tendsto_zero
    {Index : Type*} {filter : Filter Index} (rate : Index → ℝ)
    (rateLimit : Tendsto rate filter atTop) (first second : ℝ) (ordered : first ≤ second) :
    Tendsto (fun index => (Real.sqrt (Nat.floor ((second - first) * rate index)) + 2) / rate index)
      filter (𝓝 0) :=
  rounding_coefficient_additive_tendsto_zero rate rateLimit (second - first) (sub_nonneg.mpr ordered) 2

end IGS.Sec31.PoissonizedWalk

#print axioms IGS.Sec31.PoissonizedWalk.rounding_coefficient_additive_tendsto_zero
#print axioms IGS.Sec31.PoissonizedWalk.absolute_clock_coefficient_tendsto_zero
