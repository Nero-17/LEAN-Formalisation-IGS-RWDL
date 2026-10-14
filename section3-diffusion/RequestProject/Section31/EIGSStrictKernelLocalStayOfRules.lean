import RequestProject.Section31.EIGSContinuousSemigroupLocalStayOfRules
import RequestProject.Section31.EIGSStrictPositiveJointContinuousHeatKernelDensityOfRules

/-! Joint strict-positive kernel and local stay-test estimates built from
one actual native-discrete witness, retaining the identical resistance
vector and normalization. Their continuous lifts both intertwine the same
closed L2 semigroup, so subsequent pointwise consumers can identify them
by the already proved continuous-embedding injectivity. No target stay,
analyticity, irreducibility, or heat bound is an assumption.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter IGS.Sec31
open scoped Topology Classical NNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem xiStrictKernelLocalStay_of_discreteConvergence (system : EIGSData K)
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
    (discreteProperties : XiNativeSupDiscreteConvergenceProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    XiStrictPositiveJointContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair ∧
      XiContinuousSemigroupLocalStayProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  have stay := xiContinuousSemigroupLocalStayProperties_of_discreteConvergence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive discreteProperties
  have continuousProperties : XiContinuousSemigroupProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair := by
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    letI : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
      parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
      distanceGreaterThanOne parameters.eigenpair
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    dsimp only [XiNativeSupDiscreteConvergenceProperties, XiContinuousSemigroupProperties]
      at discreteProperties ⊢
    obtain ⟨originalDense, resolvers, resolverProperties, approximateIdentity, fullStepLimit,
      semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, intertwining,
      canonicalLimit, supLimit, floorLimit, absoluteUniform⟩ := discreteProperties
    exact ⟨originalDense, semigroup, semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, intertwining⟩
  have smoothing := xiContinuousSemigroupSmoothingProperties_of_continuousSemigroup system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair continuousProperties
  have compactSmoothing := xiContinuousSemigroupCompactSmoothingProperties_of_smoothing system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair smoothing
  have allTimeCompact := xiContinuousAllTimeCompactSmoothingProperties_of_compactSmoothing system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair compactSmoothing
  have jointKernel := xiJointContinuousHeatKernelDensityProperties_of_compactSmoothing system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair allTimeCompact
  have strictKernel := xiStrictPositiveJointContinuousHeatKernelDensityProperties_of_density system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair jointKernel
  exact ⟨strictKernel, stay⟩

theorem exists_xiStrictKernelLocalStay_of_rules (system : EIGSData K)
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
      (XiStrictPositiveJointContinuousHeatKernelDensityProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair ∧
        XiContinuousSemigroupLocalStayProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
          resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive) := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
      normalization, normalizationPositive, normalizedConvergence, discreteProperties⟩ :=
    exists_xiNativeSupDiscreteConvergence_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, ?_⟩
  exact xiStrictKernelLocalStay_of_discreteConvergence system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive discreteProperties

end
end EIGS

#print axioms EIGS.xiStrictKernelLocalStay_of_discreteConvergence
#print axioms EIGS.exists_xiStrictKernelLocalStay_of_rules
