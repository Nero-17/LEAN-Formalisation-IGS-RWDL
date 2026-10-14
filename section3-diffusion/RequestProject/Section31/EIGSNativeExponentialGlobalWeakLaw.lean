import RequestProject.Section31.FiniteGraphExponentialJ1WeakLimit
import RequestProject.Section31.FiniteSupportUnitGlobalLawIdentification
import RequestProject.Section31.EIGSNativeExponentialClockCouplingOfRules
import RequestProject.Section31.EIGSContinuousBallGeometricMeanOfRules

/-! Upgrade an already fixed global continuous family to actual holding
J1 weak convergence. The floor restrictions and sample coupling are supplied
internally; no new global-law witness is selected. -/

namespace EIGS
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Classical NNReal
set_option maxHeartbeats 7000000
variable {K : ℕ}
local instance nativeWeakGlobalPathMeasurable {State : Type*} [TopologicalSpace State] :
    MeasurableSpace C(ℝ≥0, State) := borel _
local instance nativeWeakGlobalPathBorel {State : Type*} [TopologicalSpace State] :
    BorelSpace C(ℝ≥0, State) := ⟨rfl⟩

def XiNativeExponentialGlobalWeakFamilyProperties (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :=
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
      distanceGreaterThanOne parameters.eigenpair
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx system level,
      Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
      ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
        Tendsto (fun level => finiteGraphExponentialJ1Law (XiSimpleGraph system level)
          (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
          (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
          (parameters.vertexEmbedding level) ((rates level : ℝ) * horizon)
          (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
            (by exact_mod_cast horizonPositive))) atTop
          (𝓝 (ProbabilityMeasure.map (globalLaws start)
            (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable))

theorem xiNativeExponentialGlobalWeakFamilyProperties_of_continuous_restriction
    (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (globalLaws : (xiPathMetricDataOfRules system connected loopless unique distancePositive).LimitSpace →
      ProbabilityMeasure C(ℝ≥0, (xiPathMetricDataOfRules system connected loopless unique distancePositive).LimitSpace))
    (restrictions : XiNativeGlobalContinuousRestrictionFamilyProperties system connected loopless unique
      plantingNonadjacent distancePositive normalization normalizationPositive globalLaws) :
    XiNativeExponentialGlobalWeakFamilyProperties system connected loopless unique plantingNonadjacent
      distancePositive normalization normalizationPositive globalLaws := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system connected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius connected)
      distanceGreaterThanOne parameters.eigenpair
  letI : BoundedSpace parameters.LimitSpace := ⟨Metric.isBounded_of_compactSpace⟩
  letI : MeasurableSpace parameters.LimitSpace := borel _
  letI : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  dsimp only [XiNativeExponentialGlobalWeakFamilyProperties]
  intro start starts startConverges horizon horizonPositive
  dsimp only [XiNativeGlobalContinuousRestrictionFamilyProperties] at restrictions
  obtain ⟨laws, convergence, limitContinuous, functionRestriction⟩ := restrictions start
  let initial := fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
  have floorConverges := convergence starts startConverges horizon
  have result := finiteGraphExponentialJ1Laws_tendsto_of_floor_coupling (fun level => XiVtx system level)
    (fun level => XiSimpleGraph system level)
    (fun level vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
    initial parameters.vertexEmbedding rates
    (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive)
    horizon horizonPositive (laws horizon)
    (by simpa only [initial, xiNativeDiscreteKernel] using floorConverges)
    (by
      intro radius error radiusPositive errorPositive
      have coupling := xiNativeExponentialClock_uniform_coupling_of_rules system connected loopless unique
        plantingNonadjacent distancePositive normalization normalizationPositive initial ⌈(horizon : ℝ)⌉₊
          radius error radiusPositive errorPositive
      filter_upwards [coupling] with level witness
      obtain ⟨bad, badMeasurable, bound, close⟩ := witness
      refine ⟨bad, badMeasurable, bound, ?_⟩
      intro sample outside time timeNonnegative timeBound
      exact close sample outside time timeNonnegative (timeBound.trans (Nat.le_ceil (horizon : ℝ))))
  rw [finiteSupportPathToUnitCadlagJ1_law_eq_globalRestriction horizon horizonPositive rates parameters.vertexEmbedding
    (laws horizon) (limitContinuous horizon) (globalLaws start) (functionRestriction horizon)] at result
  exact result

end
end EIGS

#print axioms EIGS.xiNativeExponentialGlobalWeakFamilyProperties_of_continuous_restriction
