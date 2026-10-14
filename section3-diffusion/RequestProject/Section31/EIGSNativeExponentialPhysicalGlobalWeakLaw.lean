import RequestProject.Section31.EIGSNativeExponentialGlobalWeakLaw
import RequestProject.Section31.ExponentialPhysicalJ1GlobalLawIdentification

/-! Literal [0,H] genuine J1 weak convergence for the same already fixed
actual native global continuous family. -/

namespace EIGS
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Classical NNReal
set_option maxHeartbeats 6000000
variable {K : ℕ}
local instance nativePhysicalMapMeasurable {Time State : Type*}
    [TopologicalSpace Time] [TopologicalSpace State] : MeasurableSpace C(Time, State) := borel _
local instance nativePhysicalMapBorel {Time State : Type*}
    [TopologicalSpace Time] [TopologicalSpace State] : BorelSpace C(Time, State) := ⟨rfl⟩
local instance nativePhysicalIntervalBounded (horizon : ℝ≥0) : BoundedSpace (Set.Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance nativePhysicalCadlagMeasurable {State : Type*} [MetricSpace State] [BoundedSpace State]
    (horizon : ℝ≥0) : MeasurableSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance nativePhysicalCadlagBorel {State : Type*} [MetricSpace State] [BoundedSpace State]
    (horizon : ℝ≥0) : BorelSpace (CadlagJ1Path (Set.Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩

def XiNativeExponentialPhysicalGlobalWeakFamilyProperties (system : EIGSData K)
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
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  fun globalLaws : parameters.LimitSpace → ProbabilityMeasure C(ℝ≥0, parameters.LimitSpace) =>
    ∀ start : parameters.LimitSpace, ∀ starts : ∀ level, XiVtx system level,
      Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
      ∀ horizon : ℝ≥0, ∀ horizonPositive : 0 < horizon,
        Tendsto (fun level => finiteGraphExponentialPhysicalJ1Law (XiSimpleGraph system level)
          (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
          (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level))
          (parameters.vertexEmbedding level) (rates level : ℝ)
          (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
          horizon horizonPositive) atTop
          (𝓝 (ProbabilityMeasure.map
            (ProbabilityMeasure.map (globalLaws start)
              (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
            compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable))

theorem xiNativeExponentialPhysicalGlobalWeakFamilyProperties_of_unit
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
    (unitWeak : XiNativeExponentialGlobalWeakFamilyProperties system connected loopless unique
      plantingNonadjacent distancePositive normalization normalizationPositive globalLaws) :
    XiNativeExponentialPhysicalGlobalWeakFamilyProperties system connected loopless unique plantingNonadjacent
      distancePositive normalization normalizationPositive globalLaws := by
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
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  dsimp only [XiNativeExponentialPhysicalGlobalWeakFamilyProperties]
  intro start starts startConverges horizon horizonPositive
  exact finiteGraphExponentialPhysicalJ1Laws_tendsto_global_restriction (fun level => XiVtx system level)
    (fun level => XiSimpleGraph system level)
    (fun level vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
    (fun level => (⟨Measure.dirac (starts level), inferInstance⟩ : ProbabilityMeasure (XiVtx system level)))
    parameters.vertexEmbedding (fun level => (rates level : ℝ))
    (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive)
    horizon horizonPositive (globalLaws start) (unitWeak start starts startConverges horizon horizonPositive)

end
end EIGS

#print axioms EIGS.xiNativeExponentialPhysicalGlobalWeakFamilyProperties_of_unit
