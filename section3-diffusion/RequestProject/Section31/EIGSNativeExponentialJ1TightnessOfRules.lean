import RequestProject.Section31.FiniteGraphExponentialUniformJ1Tightness
import RequestProject.Section31.EIGSNativeExponentialClockCouplingOfRules
import RequestProject.Section31.EIGSFiniteHorizonPathTightnessOfRules

/-! Actual native finite graph exponential-clock path laws are uniformly
tight on every positive finite horizon, in the genuine J1 Borel carrier.
The sample coupling, native clocks, and floor-law tightness are all supplied
by the original rules. Identification of renewal counts as the Poisson
process is a separate distributional theorem. -/

namespace EIGS
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Classical NNReal
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem xiNativeExponentialJ1Laws_isTight_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (initial : ∀ level, ProbabilityMeasure (XiVtx system level))
    (horizon : ℝ≥0) (horizonPositive : 0 < horizon) :
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
    IsTightMeasureSet (Set.range (fun level =>
      (finiteGraphExponentialJ1Law (XiSimpleGraph system level)
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
        (initial level) (parameters.vertexEmbedding level) ((rates level : ℝ) * horizon)
        (mul_pos (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive level)
          (by exact_mod_cast horizonPositive)) : Measure (UnitCadlagJ1Path parameters.LimitSpace)))) := by
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
  let rates := xiNativeFiniteJumpRateNNReal system connected distancePositive normalization normalizationPositive
  dsimp only
  apply finiteGraphExponentialJ1Laws_isTight_of_floor_coupling (fun level => XiVtx system level)
    (fun level => XiSimpleGraph system level)
    (fun level vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex)) initial
    parameters.vertexEmbedding rates
    (xiNativeFiniteJumpRateNNReal_positive system connected distancePositive normalization normalizationPositive)
      horizon horizonPositive
  · have tight := xiFiniteHorizonNativeStepLaw_isTight_of_rules system connected loopless unique
      plantingNonadjacent distancePositive normalization normalizationPositive (horizon : ℝ≥0) initial
    simpa only [parameters, rates, xiNativeDiscreteKernel] using tight
  · intro radius error radiusPositive errorPositive
    have coupling := xiNativeExponentialClock_uniform_coupling_of_rules system connected loopless unique
      plantingNonadjacent distancePositive normalization normalizationPositive initial ⌈(horizon : ℝ)⌉₊ radius error
        radiusPositive errorPositive
    filter_upwards [coupling] with level witness
    obtain ⟨bad, badMeasurable, bound, close⟩ := witness
    refine ⟨bad, bound, ?_⟩
    intro sample outside time timeNonnegative timeBound
    exact close sample outside time timeNonnegative (timeBound.trans (Nat.le_ceil (horizon : ℝ)))

end
end EIGS

#print axioms EIGS.xiNativeExponentialJ1Laws_isTight_of_rules
