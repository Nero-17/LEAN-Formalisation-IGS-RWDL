import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! Self-adjoint strongly continuous semigroups are injective. Repeated
halving of a zero orbit approaches time zero. No irreducibility, order,
analyticity, compactness, or positivity improvement is assumed.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open Filter Topology
open scoped NNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem selfAdjoint_semigroup_norm_sq_pairing
    (semigroup : ℝ≥0 → H →L[ℝ] H)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time)) (time : ℝ≥0) (values : H) :
    ‖semigroup time values‖ ^ 2 = inner ℝ values (semigroup (time + time) values) := by
  rw [← real_inner_self_eq_norm_sq]
  have pairing := (symmetric time).isSymmetric values (semigroup time values)
  rw [addition time time]
  exact pairing

theorem selfAdjoint_semigroup_zero_of_double
    (semigroup : ℝ≥0 → H →L[ℝ] H)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (time : ℝ≥0) (values : H) (zero : semigroup (time + time) values = 0) :
    semigroup time values = 0 := by
  have square := selfAdjoint_semigroup_norm_sq_pairing semigroup addition symmetric time values
  rw [zero, inner_zero_right] at square
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp square)

theorem selfAdjoint_continuous_semigroup_eq_zero_of_image_zero
    (semigroup : ℝ≥0 → H →L[ℝ] H)
    (zeroTime : semigroup 0 = ContinuousLinearMap.id ℝ H)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (continuousOrbit : ∀ values, Continuous (fun time => semigroup time values))
    (time : ℝ≥0) (values : H) (zero : semigroup time values = 0) : values = 0 := by
  let halfTimes : ℕ → ℝ≥0 := fun index => time * (1 / 2 : ℝ≥0) ^ index
  have orbitZero (index : ℕ) : semigroup (halfTimes index) values = 0 := by
    induction index with
    | zero => simpa only [halfTimes, pow_zero, mul_one] using zero
    | succ index induction =>
        have doubleTime : halfTimes (index + 1) + halfTimes (index + 1) = halfTimes index := by
          dsimp only [halfTimes]
          rw [pow_succ]
          ring
        apply selfAdjoint_semigroup_zero_of_double semigroup addition symmetric
          (halfTimes (index + 1)) values
        rw [doubleTime]
        exact induction
  have halfTimesLimit : Tendsto halfTimes atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.mp
    have geometric := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (time : ℝ)
    simpa only [halfTimes, NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_div,
      NNReal.coe_one, NNReal.coe_ofNat, NNReal.coe_zero, mul_zero] using geometric
  have orbitLimit := ((continuousOrbit values).tendsto 0).comp halfTimesLimit
  have zeroLimit : Tendsto (fun index => semigroup (halfTimes index) values) atTop (𝓝 0) := by
    simpa only [orbitZero] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : H)) atTop (𝓝 0))
  have same := tendsto_nhds_unique orbitLimit zeroLimit
  simpa only [zeroTime, ContinuousLinearMap.id_apply] using same

theorem selfAdjoint_continuous_semigroup_injective
    (semigroup : ℝ≥0 → H →L[ℝ] H)
    (zeroTime : semigroup 0 = ContinuousLinearMap.id ℝ H)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (continuousOrbit : ∀ values, Continuous (fun time => semigroup time values)) (time : ℝ≥0) :
    Function.Injective (semigroup time) := by
  intro first second equal
  apply sub_eq_zero.mp
  apply selfAdjoint_continuous_semigroup_eq_zero_of_image_zero semigroup zeroTime addition symmetric continuousOrbit time
  rw [map_sub, equal, sub_self]

theorem selfAdjoint_continuous_semigroup_pairing_pos
    (semigroup : ℝ≥0 → H →L[ℝ] H)
    (zeroTime : semigroup 0 = ContinuousLinearMap.id ℝ H)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (continuousOrbit : ∀ values, Continuous (fun time => semigroup time values))
    (time : ℝ≥0) (values : H) (nonzero : values ≠ 0) :
    0 < inner ℝ values (semigroup time values) := by
  have halfTimeIdentity : time / 2 + time / 2 = time := by ring
  have pairing := selfAdjoint_semigroup_norm_sq_pairing semigroup addition symmetric (time / 2) values
  rw [halfTimeIdentity] at pairing
  rw [← pairing]
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro zero
  exact nonzero (selfAdjoint_continuous_semigroup_eq_zero_of_image_zero semigroup zeroTime addition
    symmetric continuousOrbit (time / 2) values zero)

end IGS.Sec31

#print axioms IGS.Sec31.selfAdjoint_semigroup_norm_sq_pairing
#print axioms IGS.Sec31.selfAdjoint_semigroup_zero_of_double
#print axioms IGS.Sec31.selfAdjoint_continuous_semigroup_eq_zero_of_image_zero
#print axioms IGS.Sec31.selfAdjoint_continuous_semigroup_injective
#print axioms IGS.Sec31.selfAdjoint_continuous_semigroup_pairing_pos
