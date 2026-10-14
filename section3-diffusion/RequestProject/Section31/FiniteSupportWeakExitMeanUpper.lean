import RequestProject.Section31.FiniteSupportWeakExitTail
import RequestProject.Section31.FiniteStepRadiusExitTail

/-! Transfer a whole finite floor-clock exit expectation through the
proved finite-horizon weak laws. Open prefix radii give the tail comparison
at every positive time; Tonelli and Fatou give the full expected exit.
The finite expectation assumption is an input for actual finite graph
consumers, not an assumption about the continuous target exit. -/

namespace IGS.Sec31.DiscreteMarkov
open Set Filter Topology MeasureTheory ProbabilityTheory
open IGS.Sec31
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
set_option maxHeartbeats 5000000
variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable [MeasurableSpace C(ℝ≥0, State)] [BorelSpace C(ℝ≥0, State)]
variable {Vertex : ℕ → Type} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]
variable [∀ level, DecidableEq (Vertex level)]

local instance weakExitMeanStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteSupport_weak_global_exit_mean_upper
    (rates : ℕ → ℝ≥0) (ratesPositive : ∀ level, 0 < rates level)
    (embedding : ∀ level, Vertex level → State)
    (kernels : ∀ level, Kernel (Vertex level) (Vertex level))
    [∀ level, IsMarkovKernel (kernels level)]
    (initial : ∀ level, ProbabilityMeasure (Vertex level))
    (levels : ℕ → ℕ)
    (laws : (horizon : ℝ≥0) → ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (convergence : ∀ horizon, Tendsto (fun index =>
      finiteHorizonStepLaw horizon rates embedding kernels initial (levels index)) atTop (𝓝 (laws horizon)))
    (limitContinuous : ∀ horizon, ∀ᵐ path ∂(laws horizon : Measure
      (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))),
        Continuous (UniformFun.toFun path.val))
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (restriction : ∀ horizon,
      (laws horizon : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
        (fun path => UniformFun.toFun path.val) =
      (globalLaw : Measure C(ℝ≥0, State)).map
        (fun path => fun observed : Icc (0 : ℝ) (horizon : ℝ) => path ⟨observed.val, observed.property.1⟩))
    (center : State) (discreteCenters : ∀ level, Vertex level)
    (radius outerRadius : ℝ)
    (centerNear : ∀ᶠ index in atTop,
      dist (embedding (levels index) (discreteCenters (levels index))) center ≤ outerRadius - radius)
    (upper : ℝ≥0∞)
    (finiteMeanUpper : ∀ index,
      (∫⁻ path, EIGS.graphFloorExitTime
        (Finset.univ.filter fun vertex => dist
          (embedding (levels index) (discreteCenters (levels index)))
          (embedding (levels index) vertex) < outerRadius) (rates (levels index)) path
        ∂pathLaw (kernels (levels index)) (initial (levels index))) ≤ upper) :
    (∫⁻ path, continuousPathBallExit path center radius ∂(globalLaw : Measure C(ℝ≥0, State))) ≤ upper := by
  let finiteTails : ℕ → ℝ → ℝ≥0∞ := fun index time =>
    pathLaw (kernels (levels index)) (initial (levels index))
      {path | ENNReal.ofReal time < EIGS.graphFloorExitTime
        (Finset.univ.filter fun vertex => dist
          (embedding (levels index) (discreteCenters (levels index)))
          (embedding (levels index) vertex) < outerRadius) (rates (levels index)) path}
  have finiteTailsMeasurable : ∀ index, Measurable (finiteTails index) := by
    intro index
    apply Antitone.measurable
    intro first second ordered
    apply measure_mono
    intro path survives
    exact (ENNReal.ofReal_le_ofReal ordered).trans_lt survives
  apply positive_tail_mean_upper_of_liminf (globalLaw : Measure C(ℝ≥0, State))
    (fun path => continuousPathBallExit path center radius)
    (continuousPathBallExit_measurable center radius) finiteTails finiteTailsMeasurable ?_ upper ?_
  · intro time timePositive
    let horizon : ℝ≥0 := ⟨time, timePositive.le⟩
    letI : Nonempty (Icc (0 : ℝ) (horizon : ℝ)) := ⟨⟨0, le_rfl, horizon.property⟩⟩
    obtain ⟨times, timesDense⟩ := exists_dense_seq (α := Icc (0 : ℝ) (horizon : ℝ))
    have timeEquality : ENNReal.ofReal time = (horizon : ℝ≥0∞) := by
      change ENNReal.ofReal (horizon : ℝ) = (horizon : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    have weakTail := finiteSupport_weak_global_exit_tail horizon
      (finiteHorizonStepPaths horizon rates embedding) times timesDense center radius
      (fun index => finiteHorizonStepLaw horizon rates embedding kernels initial (levels index))
      (laws horizon) (convergence horizon) (limitContinuous horizon) globalLaw (restriction horizon)
    have finiteComparison : ∀ᶠ index in atTop,
        (finiteHorizonStepLaw horizon rates embedding kernels initial (levels index) :
          Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
          {path | dist path.val (UniformFun.ofFun
            (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < radius} ≤ finiteTails index time := by
      filter_upwards [centerNear] with index near
      dsimp only [finiteTails]
      rw [timeEquality]
      exact finiteHorizonStepLaw_radius_le_floorExitTail horizon rates embedding kernels initial
        (levels index) (ratesPositive _) center (discreteCenters _) radius outerRadius near
    rw [timeEquality]
    exact weakTail.trans (liminf_le_liminf finiteComparison)
  · intro index
    dsimp only [finiteTails]
    rw [← lintegral_exit_eq_positive_tail
      (pathLaw (kernels (levels index)) (initial (levels index)))
      (EIGS.graphFloorExitTime _ (rates (levels index)))
      (EIGS.graphFloorExitTime_measurable _ _)]
    exact finiteMeanUpper index

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupport_weak_global_exit_mean_upper
