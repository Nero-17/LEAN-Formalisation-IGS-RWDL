import RequestProject.Section31.ExponentialClockCouplingProbability
import RequestProject.Section31.EIGSAsymptoticPathModulus
import RequestProject.Section31.EIGSNativeDiscreteContraction

/-! The actual rule walk and its independent exponential-clock version are
uniformly close in probability on every bounded horizon, on their explicitly
constructed common sample space. The actual chain modulus and divergence of
its native jump rates are proved internally. This is not yet a theorem about
Poisson counting distributions or tightness of J1 laws. -/

namespace EIGS
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open IGS.Sec31.DiscreteMarkov IGS.Sec31.PoissonClock
open scoped Topology Classical
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiNativeExponentialClock_uniform_coupling_of_rules (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)]
    (initial : ∀ level, ProbabilityMeasure (XiVtx system level))
    (horizon : ℕ) (tolerance probabilityTolerance : ℝ)
    (tolerancePositive : 0 < tolerance) (probabilityPositive : 0 < probabilityTolerance) :
    let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
    let rate := fun level => xiNativeFiniteJumpRate system level
      (system.resistanceSpectralRadius connected distancePositive) normalization
    ∀ᶠ level in atTop,
      ∃ bad : Set ((ℕ → XiVtx system level) × (ℕ → ℝ)), MeasurableSet bad ∧
        ((pathLaw (finiteGraphTransitionKernel (XiSimpleGraph system level)
          (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex)))
            (initial level : Measure _)).prod exponentialHoldingTimeLaw).real bad ≤ probabilityTolerance ∧
        ∀ sample ∉ bad, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
          dist (parameters.vertexEmbedding level
            (holdingTimePath sample.1 sample.2 (rate level * time)))
            (parameters.vertexEmbedding level (sample.1 ⌊rate level * time⌋₊)) ≤ tolerance := by
  classical
  let parameters := xiPathMetricDataOfRules system connected loopless unique distancePositive
  let mass := xiMassParametersOfRules system connected distancePositive
  let rate := fun level => xiNativeFiniteJumpRate system level
    (system.resistanceSpectralRadius connected distancePositive) normalization
  let transition := fun level => finiteGraphTransitionKernel (XiSimpleGraph system level)
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system connected level vertex))
  let laws := fun level => pathLaw (transition level) (initial level : Measure _)
  obtain ⟨resistancePositive, vector, vectorPositive, eigenpair⟩ :=
    system.resistanceSpectralRadius_positive_eigenpair connected distancePositive
  have ratePositive : ∀ level, 0 < rate level := fun level =>
    xiNativeFiniteJumpRate_positive system mass level _ normalization resistancePositive normalizationPositive
  have rateDiverges : Tendsto rate atTop atTop :=
    xiNativeFiniteJumpRate_tendsto_atTop system connected loopless unique plantingNonadjacent mass
      distancePositive _ normalization resistancePositive normalizationPositive vector vectorPositive eigenpair
  have chainModulus : ∀ windowHorizon : ℕ, ∀ error probabilityError : ℝ,
      0 < error → 0 < probabilityError → ∃ window : ℝ, 0 < window ∧
        ∀ᶠ level in atTop, (laws level).real
          (floorClockBadModulus (parameters.vertexEmbedding level) (rate level)
            windowHorizon window error) ≤ probabilityError := by
    intro windowHorizon error probabilityError errorPositive probabilityErrorPositive
    obtain ⟨coarse, window, windowPositive, _, bounds⟩ :=
      exists_xiAsymptoticPathModulus_of_rules system connected loopless unique plantingNonadjacent
        distancePositive normalization normalizationPositive (windowHorizon : ℝ) error probabilityError 1
        (Nat.cast_nonneg _) errorPositive probabilityErrorPositive zero_lt_one
    refine ⟨window, windowPositive, ?_⟩
    filter_upwards [eventually_ge_atTop coarse] with level afterCoarse
    obtain ⟨steps, rfl⟩ := Nat.exists_eq_add_of_le afterCoarse
    have bound := bounds steps (initial (coarse + steps))
    simpa only [laws, transition, parameters, rate, xiActualPathModulusEvent, floorClockBadModulus]
      using bound.le
  exact continuousClock_uniform_coupling_probability (fun level => XiVtx system level) laws
    parameters.vertexEmbedding rate ratePositive rateDiverges chainModulus horizon tolerance probabilityTolerance
      tolerancePositive probabilityPositive

end
end EIGS

#print axioms EIGS.xiNativeExponentialClock_uniform_coupling_of_rules
