import RequestProject.Section31.EIGSL2QuadraticEnergy
import RequestProject.Section31.EIGSHarmonicDensity
import RequestProject.Section31.EnergyOrthogonality
import Mathlib.Topology.MetricSpace.Thickening

/-! Strong locality on the actual continuous finite-energy core. Compact
support and an open constant neighborhood give a metric buffer; the actual
edge mesh tends to zero. No locality claim for the whole closed domain is
made here. -/

namespace IGS.Sec31

open Filter Topology

theorem exists_cross_difference_zero_near_support {Space : Type*} [MetricSpace Space]
    (first second : Space → ℝ) (supportCompact : IsCompact (tsupport second))
    (neighborhood : Set Space) (neighborhoodOpen : IsOpen neighborhood)
    (supportSubset : tsupport second ⊆ neighborhood) (constant : ℝ)
    (constantOn : ∀ point ∈ neighborhood, first point = constant) :
    ∃ buffer : ℝ, 0 < buffer ∧ ∀ source sink : Space, dist source sink < buffer →
      (first source - first sink) * (second source - second sink) = 0 := by
  obtain ⟨buffer, bufferPositive, bufferInside⟩ :=
    supportCompact.exists_thickening_subset_open neighborhoodOpen supportSubset
  refine ⟨buffer, bufferPositive, ?_⟩
  intro source sink close
  by_cases sourceZero : second source = 0
  · by_cases sinkZero : second sink = 0
    · simp [sourceZero, sinkZero]
    · have sinkSupport : sink ∈ tsupport second := subset_tsupport second sinkZero
      have sourceInside : source ∈ neighborhood := bufferInside
        (Metric.ball_subset_thickening sinkSupport buffer close)
      rw [constantOn source sourceInside, constantOn sink (supportSubset sinkSupport)]
      simp
  · have sourceSupport : source ∈ tsupport second := subset_tsupport second sourceZero
    have sinkInside : sink ∈ neighborhood := bufferInside
      (Metric.ball_subset_thickening sourceSupport buffer (by simpa only [Metric.mem_ball, dist_comm] using close))
    rw [constantOn source (supportSubset sourceSupport), constantOn sink sinkInside]
    simp

theorem traceEnergyValue_add_of_eventually_energyInner_zero {Vertex : Type*}
    (networks : ℕ → FiniteNetwork Vertex)
    (energyIncreasing : ∀ values : Vertex → ℝ, Monotone (fun level => (networks level).energy values))
    (first second : traceEnergyDomain networks)
    (orthogonal : ∀ᶠ level in atTop, (networks level).energyInner first second = 0) :
    traceEnergyValue networks (first + second) = traceEnergyValue networks first + traceEnergyValue networks second := by
  have eventuallyAdd : ∀ᶠ level in atTop,
      (networks level).energy (first + second) = (networks level).energy first + (networks level).energy second := by
    filter_upwards [orthogonal] with level zero
    simpa only [one_mul, one_pow, zero, mul_zero, add_zero] using
      (networks level).energy_line first second 1
  exact tendsto_nhds_unique (finite_energy_tendsto_traceEnergyValue networks energyIncreasing (first + second))
    (((finite_energy_tendsto_traceEnergyValue networks energyIncreasing first).add
      (finite_energy_tendsto_traceEnergyValue networks energyIncreasing second)).congr'
        (eventuallyAdd.mono (fun _ equality => equality.symm)))

end IGS.Sec31

namespace EIGS

open Filter Topology IGS.Sec31
open scoped BigOperators

set_option maxHeartbeats 2400000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)

theorem xiContinuous_eventually_edge_cross_zero
    (first second : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (neighborhood : Set (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair))
    (neighborhoodOpen : IsOpen neighborhood) (supportSubset : tsupport second ⊆ neighborhood)
    (constant : ℝ) (constantOn : ∀ point ∈ neighborhood, first point = constant) :
    ∀ᶠ level in atTop, ∀ edge : XiEdge system.toRuleData level,
      (first (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiTail system level edge)) -
        first (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiHead system level edge))) *
      (second (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiTail system level edge)) -
        second (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiHead system level edge))) = 0 := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  obtain ⟨buffer, bufferPositive, differencesZero⟩ := exists_cross_difference_zero_near_support
    first second (isClosed_tsupport second).isCompact neighborhood neighborhoodOpen supportSubset constant constantOn
  have meshZero : Tendsto (fun level : ℕ => distanceRate⁻¹ ^ level * ∑ colour, lengths colour)
      atTop (nhds 0) := by
    have decay := tendsto_pow_atTop_nhds_zero_of_lt_one
      (inv_pos.mpr (zero_lt_one.trans distanceRateGreaterThanOne)).le
      ((inv_lt_one₀ (zero_lt_one.trans distanceRateGreaterThanOne)).mpr distanceRateGreaterThanOne)
    simpa only [zero_mul] using decay.mul_const (∑ colour, lengths colour)
  filter_upwards [(tendsto_order.1 meshZero).2 buffer bufferPositive] with level meshSmall
  intro edge
  exact differencesZero _ _ ((xiCompletionEmbedding_edge_distance_le system rulesConnected lengths lengthsPositive
    distanceRate (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level edge).trans_lt meshSmall)

variable (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)

theorem xiContinuous_eventually_energyInner_zero
    (first second : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (neighborhood : Set (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair))
    (neighborhoodOpen : IsOpen neighborhood) (supportSubset : tsupport second ⊆ neighborhood)
    (constant : ℝ) (constantOn : ∀ point ∈ neighborhood, first point = constant) :
    ∀ᶠ level in atTop,
      (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energyInner
        (first ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
        (second ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) = 0 := by
  filter_upwards [xiContinuous_eventually_edge_cross_zero system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair first second neighborhood neighborhoodOpen supportSubset constant constantOn]
      with level differencesZero
  unfold FiniteNetwork.energyInner
  apply Finset.sum_eq_zero
  intro edge _
  have zero := differencesZero edge
  change _ *
      (first (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiTail system level edge)) -
        first (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiHead system level edge))) *
      (second (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiTail system level edge)) -
        second (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (XiHead system level edge))) = 0
  rw [mul_assoc, zero, mul_zero]

theorem xiContinuousLpEnergy_associated_eq_zero_on_core
    (mass : XiMassParameters system)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (first second : xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive)
    (neighborhood : Set (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair))
    (neighborhoodOpen : IsOpen neighborhood) (supportSubset : tsupport second.val ⊆ neighborhood)
    (constant : ℝ) (constantOn : ∀ point ∈ neighborhood, first.val point = constant) :
    (xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair).associated
      (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive first)
      (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive second) = 0 := by
  have orthogonal := xiContinuous_eventually_energyInner_zero system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
    first.val second.val neighborhood neighborhoodOpen supportSubset constant constantOn
  have energyAdd := traceEnergyValue_add_of_eventually_energyInner_zero
    (xiUnionWeightedNetwork system resistanceRate ratePositive resistanceVector vectorPositive)
    (xiUnionWeightedNetwork_energy_increasing_of_eigenpair system rulesConnected resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair)
    (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive first)
    (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive second) orthogonal
  rw [QuadraticMap.associated_apply, ← map_add]
  rw [xiContinuousLpEnergyQuadraticForm_of_continuous, xiContinuousLpEnergyQuadraticForm_of_continuous,
    xiContinuousLpEnergyQuadraticForm_of_continuous]
  change _ • (traceEnergyValue _
    ((xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive first) +
     (xiContinuousEnergyToUnionDomain system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive second)) - _ - _) = 0
  rw [energyAdd]
  simp only [traceEnergyValue, xiExtendedWeightedEnergy, xiContinuousEnergyToUnionDomain,
    xiContinuousUnionRestriction, LinearMap.coe_mk, AddHom.coe_mk]
  simp

end EIGS

#print axioms IGS.Sec31.exists_cross_difference_zero_near_support
#print axioms IGS.Sec31.traceEnergyValue_add_of_eventually_energyInner_zero
#print axioms EIGS.xiContinuous_eventually_edge_cross_zero
#print axioms EIGS.xiContinuous_eventually_energyInner_zero
#print axioms EIGS.xiContinuousLpEnergy_associated_eq_zero_on_core
