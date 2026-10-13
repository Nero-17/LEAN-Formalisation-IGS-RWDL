import RequestProject.Section31.EIGSStationaryPairWeakLimit
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! The genuine kernel pair probabilities tend weakly to the diagonal from
actual strong L² convergence to the identity. Compact-product
Stone--Weierstrass is the already proved product-test bridge. Portmanteau
then proves the probability of a positive metric displacement tends to zero.
This is not a sample-path continuity or Hunt theorem. -/

namespace IGS.Sec31.StationaryPair

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ProbabilityTheory BoundedContinuousFunction NNReal
noncomputable section
set_option maxHeartbeats 3000000

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

variable {Index : Type*} {indexFilter : Filter Index}

def diagonalProbability (measure : ProbabilityMeasure Space) : ProbabilityMeasure (Space × Space) :=
  probability measure Kernel.id inferInstance

theorem identity_kernel_represents_L2 (measure : ProbabilityMeasure Space)
    (function : Space →ᵇ ℝ) :
    ∀ᵐ source ∂(measure : Measure Space),
      (∫ target, function target ∂(Kernel.id : Kernel Space Space) source) =
        (ContinuousLinearMap.id ℝ (Lp ℝ 2 (measure : Measure Space)))
          (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) source := by
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (measure : Measure Space) ℝ function]
    with source equality
  simp only [Kernel.id_apply, integral_dirac, ContinuousLinearMap.id_apply]
  exact equality.symm

theorem kernel_pair_tendsto_diagonal (measure : ProbabilityMeasure Space)
    (kernels : Index → Kernel Space Space) (markov : ∀ time, IsMarkovKernel (kernels time))
    (operators : Index → Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space))
    (representation : ∀ time (function : Space →ᵇ ℝ),
      ∀ᵐ source ∂(measure : Measure Space),
        (∫ target, function target ∂kernels time source) =
          operators time (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) source)
    (strongToIdentity : ∀ values : Lp ℝ 2 (measure : Measure Space),
      Tendsto (fun time => operators time values) indexFilter (nhds values)) :
    Tendsto (fun time => probability measure (kernels time) (markov time)) indexFilter
      (nhds (diagonalProbability measure)) := by
  apply weak_tendsto_of_product_integrals
  intro first second
  have pairIdentity : ∀ time,
      (∫ pair : Space × Space, first pair.1 * second pair.2
        ∂(probability measure (kernels time) (markov time) : Measure _)) =
      inner ℝ (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ first)
        (operators time (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ second)) := by
    intro time
    exact (inner_eq_integral_product measure (kernels time) (markov time)
      (operators time) (representation time) first second).symm
  have diagonalIdentity := inner_eq_integral_product measure Kernel.id inferInstance
    (ContinuousLinearMap.id ℝ (Lp ℝ 2 (measure : Measure Space)))
    (identity_kernel_represents_L2 measure) first second
  simp only [ContinuousLinearMap.id_apply] at diagonalIdentity
  simp_rw [pairIdentity]
  change Tendsto _ indexFilter
    (nhds (∫ pair : Space × Space, first pair.1 * second pair.2
      ∂(probability measure Kernel.id inferInstance : Measure _)))
  rw [← diagonalIdentity]
  exact tendsto_const_nhds.inner (strongToIdentity _)

theorem diagonal_distance_event_null (measure : ProbabilityMeasure Space)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    (diagonalProbability measure : Measure (Space × Space))
      {pair | epsilon < dist pair.1 pair.2} = 0 := by
  change ((measure : Measure Space) ⊗ₘ (Kernel.id : Kernel Space Space)) _ = 0
  rw [Measure.compProd_id, Measure.map_apply (f := fun source : Space => (source, source))
    (measurable_id.prodMk measurable_id)
    (isOpen_lt continuous_const (continuous_fst.dist continuous_snd)).measurableSet]
  have emptyPreimage : (fun source : Space => (source, source)) ⁻¹'
      {pair | epsilon < dist pair.1 pair.2} = ∅ := by
    ext source
    simp [not_lt.mpr positive.le]
  rw [emptyPreimage, measure_empty]

theorem diagonal_distance_frontier_null (measure : ProbabilityMeasure Space)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    (diagonalProbability measure : Measure (Space × Space))
      (frontier {pair | epsilon < dist pair.1 pair.2}) = 0 := by
  have boundary : frontier {pair : Space × Space | epsilon < dist pair.1 pair.2} ⊆
      {pair | epsilon = dist pair.1 pair.2} :=
    frontier_lt_subset_eq continuous_const (continuous_fst.dist continuous_snd)
  have equalityNull : (diagonalProbability measure : Measure (Space × Space))
      {pair | epsilon = dist pair.1 pair.2} = 0 := by
    change ((measure : Measure Space) ⊗ₘ (Kernel.id : Kernel Space Space)) _ = 0
    rw [Measure.compProd_id, Measure.map_apply (f := fun source : Space => (source, source))
      (measurable_id.prodMk measurable_id)
      (isClosed_eq continuous_const (continuous_fst.dist continuous_snd)).measurableSet]
    have emptyPreimage : (fun source : Space => (source, source)) ⁻¹'
        {pair | epsilon = dist pair.1 pair.2} = ∅ := by
      ext source
      simp [ne_of_gt positive]
    rw [emptyPreimage, measure_empty]
  exact measure_mono_null boundary equalityNull

theorem kernel_pair_distance_probability_tendsto_zero (measure : ProbabilityMeasure Space)
    (kernels : Index → Kernel Space Space) (markov : ∀ time, IsMarkovKernel (kernels time))
    (operators : Index → Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space))
    (representation : ∀ time (function : Space →ᵇ ℝ),
      ∀ᵐ source ∂(measure : Measure Space),
        (∫ target, function target ∂kernels time source) =
          operators time (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ function) source)
    (strongToIdentity : ∀ values : Lp ℝ 2 (measure : Measure Space),
      Tendsto (fun time => operators time values) indexFilter (nhds values))
    (epsilon : ℝ) (positive : 0 < epsilon) :
    Tendsto (fun time => (probability measure (kernels time) (markov time) : Measure (Space × Space))
      {pair | epsilon < dist pair.1 pair.2}) indexFilter (nhds 0) := by
  have weakConvergence := kernel_pair_tendsto_diagonal measure kernels markov operators
    representation strongToIdentity
  have eventConvergence := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    weakConvergence (diagonal_distance_frontier_null measure epsilon positive)
  simpa only [diagonal_distance_event_null measure epsilon positive] using eventConvergence

end
end IGS.Sec31.StationaryPair

#print axioms IGS.Sec31.StationaryPair.kernel_pair_tendsto_diagonal
#print axioms IGS.Sec31.StationaryPair.diagonal_distance_frontier_null
#print axioms IGS.Sec31.StationaryPair.kernel_pair_distance_probability_tendsto_zero
