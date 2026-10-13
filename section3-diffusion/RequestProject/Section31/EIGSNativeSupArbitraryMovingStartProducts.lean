import RequestProject.Section31.EIGSNativeSupMovingStartProducts
import RequestProject.Section31.FiniteObservationTimeReindexing

/-! Every finite tuple of nonnegative observation times has a genuine
moving-start product-moment limit for the actual walk. Times need not be
ordered or distinct and may start strictly above zero; the empty tuple is
included. A pointwise finite-grid identity supplies the reindexing. The final
consumer preserves the coherent semigroup data from the original rules. -/

namespace EIGS

open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

def XiNativeSupArbitraryProductProperties (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) : Prop :=
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  ∀ (starts : ∀ level, XiVtx system level) (start : parameters.LimitSpace),
    Tendsto (fun level => parameters.vertexEmbedding level (starts level)) atTop (𝓝 start) →
    ∀ (dimension : ℕ) (times : Fin dimension → ℝ≥0)
      (tests : Fin dimension → C(parameters.LimitSpace, ℝ)),
      ∃ value : ℝ, Tendsto (fun level => ∫ path,
        ∏ index : Fin dimension, tests index (parameters.vertexEmbedding level
          (path (Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))
          ∂pathLaw
            (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
            (Measure.dirac (starts level))) atTop (𝓝 value)

theorem xiNativeSupArbitraryProductProperties_of_movingStartProducts (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (movingProperties : XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair normalization normalizationPositive) :
    XiNativeSupArbitraryProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive resistanceRate normalization := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
  letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  dsimp only [XiNativeSupMovingStartProductProperties] at movingProperties
  obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
    semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, semigroupIntertwining,
    canonicalLimit, supLimit, floorLimit, absoluteUniform, orderedProducts⟩ := movingProperties
  dsimp only [XiNativeSupArbitraryProductProperties]
  intro starts start startsConverge dimension times tests
  refine FiniteObservationTimeReindexing.arbitrary_products_have_limit_of_ordered_products
    (fun level => pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (Measure.dirac (starts level)))
    (fun level time path => parameters.vertexEmbedding level
      (path (Nat.floor ((time : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))
    ?_ dimension times tests
  intro orderedTimes timesMonotone startsAtZero orderedTests count terminal
  refine ⟨BanachBackwardObservations.backwardProduct
    (fun index : ℕ => semigroup (orderedTimes (index + 1) - orderedTimes index))
    (fun index : ℕ => ContinuousLinearMap.mul ℝ C(parameters.LimitSpace, ℝ) (orderedTests index))
    ((List.range count).map (fun index => (index, index))) terminal start, ?_⟩
  exact orderedProducts orderedTimes timesMonotone startsAtZero orderedTests count terminal
    starts start startsConverge

theorem exists_xiNativeSupArbitraryMovingStartProducts_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ resistanceRate : ℝ, ∃ ratePositive : 0 < resistanceRate,
      ∃ resistanceVector : Fin K → ℝ, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (𝓝 (normalization • resistanceVector)) ∧
      XiNativeSupMovingStartProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive ∧
      XiNativeSupArbitraryProductProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive resistanceRate normalization := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, movingProperties⟩ :=
    exists_xiNativeSupMovingStartProducts_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, movingProperties, ?_⟩
  exact xiNativeSupArbitraryProductProperties_of_movingStartProducts system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive movingProperties

end
end EIGS

#print axioms EIGS.xiNativeSupArbitraryProductProperties_of_movingStartProducts
#print axioms EIGS.exists_xiNativeSupArbitraryMovingStartProducts_of_rules
