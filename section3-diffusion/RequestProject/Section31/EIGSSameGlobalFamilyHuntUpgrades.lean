import RequestProject.Section31.EIGSFullFutureStoppingClosedIdentification
import RequestProject.Section31.EIGSExtendedFullFutureStoppingClosedIdentification
import RequestProject.Section31.EIGSConservativeHuntClosedIdentification

/-! Explicit upgrades of an already chosen same-closed-semigroup/global-family
witness. The finite-future family from the preceding construction is retained
verbatim when adding the extended finite-event law, and that extended family
is retained when collecting the full conservative Hunt criteria. The original
L² intertwining, all finite laws and all FDD are preserved by construction.
The old future property is not used as a hypothesis for the new future proof:
the latter is derived again from the very same retained ordered FDD. -/

namespace EIGS
open IGS.Sec31 MeasureTheory ProbabilityTheory Filter Topology
open IGS.Sec31.DiscreteMarkov
open scoped Classical BigOperators NNReal UniformConvergence BoundedContinuousFunction
noncomputable section
set_option maxHeartbeats 7000000
variable {K : ℕ}

theorem xiExtendedFullFutureContinuousPathSemigroupProperties_of_priorFamily (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (semigroup : ℝ≥0 → C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace, ℝ) →L[ℝ]
      C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace, ℝ))
    (properties : XiFullFutureContinuousPathSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup) :
    XiExtendedFullFutureContinuousPathSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI xiSameFamilyExtendedBridgeUpgradeLimitCompact : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI xiSameFamilyExtendedBridgeUpgradeLimitMeasurable : MeasurableSpace parameters.LimitSpace := borel _
  letI xiSameFamilyExtendedBridgeUpgradeLimitBorel : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI xiSameFamilyExtendedBridgeUpgradePathMeasurable : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI xiSameFamilyExtendedBridgeUpgradePathBorel : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiFullFutureContinuousPathSemigroupProperties, XiExtendedFullFutureContinuousPathSemigroupProperties]
    at properties ⊢
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, priorFutureProperty, startingData⟩ := properties
  refine ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, ?_, startingData⟩
  apply continuousPath_usualExtendedFutureLawProperties_of_ordered_observations
    globalLaws familyMeasurable semigroup positive preservesOne
  intro start times timesMonotone startsAtZero tests count terminal
  obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
    initialDirac, finiteEvaluations, observations, deterministicIdentity, naturalStoppingIdentity⟩ := startingData start
  exact observations times timesMonotone startsAtZero tests count terminal

theorem xiIdentifiedExtendedFullFutureContinuousPathProperties_of_identifiedPriorFamily (system : EIGSData K)
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
    (properties : XiIdentifiedFullFutureContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    XiIdentifiedExtendedFullFutureContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  dsimp only [XiIdentifiedFullFutureContinuousPathProperties, XiIdentifiedExtendedFullFutureContinuousPathProperties]
    at properties ⊢
  obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := properties
  exact ⟨originalDense, semigroup,
    xiExtendedFullFutureContinuousPathSemigroupProperties_of_priorFamily system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup semigroupProperties,
    intertwining⟩
theorem exists_xiIdentifiedExtendedFullFutureContinuousPath_of_priorFamily_rules (system : EIGSData K)
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
      XiIdentifiedExtendedFullFutureContinuousPathProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, properties⟩ :=
    exists_xiIdentifiedFullFutureContinuousPath_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiIdentifiedExtendedFullFutureContinuousPathProperties_of_identifiedPriorFamily system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive properties⟩

theorem xiConservativeHuntContinuousPathSemigroupProperties_of_priorFamily (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ) (normalizationPositive : 0 < normalization)
    (semigroup : ℝ≥0 → C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace, ℝ) →L[ℝ]
      C((xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace, ℝ))
    (properties : XiExtendedFullFutureContinuousPathSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup) :
    XiConservativeHuntContinuousPathSemigroupProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  letI xiSameFamilyHuntBridgeUpgradeLimitCompact : CompactSpace parameters.LimitSpace := xiCompletion_compactSpace system rulesConnected
    parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
    distanceGreaterThanOne parameters.eigenpair
  letI xiSameFamilyHuntBridgeUpgradeLimitMeasurable : MeasurableSpace parameters.LimitSpace := borel _
  letI xiSameFamilyHuntBridgeUpgradeLimitBorel : BorelSpace parameters.LimitSpace := ⟨rfl⟩
  letI xiSameFamilyHuntBridgeUpgradePathMeasurable : MeasurableSpace C(ℝ≥0, parameters.LimitSpace) := borel _
  letI xiSameFamilyHuntBridgeUpgradePathBorel : BorelSpace C(ℝ≥0, parameters.LimitSpace) := ⟨rfl⟩
  dsimp only [XiExtendedFullFutureContinuousPathSemigroupProperties, XiConservativeHuntContinuousPathSemigroupProperties]
    at properties ⊢
  obtain ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, priorFutureProperty, startingData⟩ := properties
  refine ⟨semigroupNorm, semigroupZero, semigroupAdd, semigroupContinuous, supLimit,
    positive, preservesOne, globalLaws, familyMeasurable, probabilityFamilyMeasurable,
    probabilityKernel, ?_, startingData⟩
  apply continuousPath_conservativeHuntFamilyData_of_ordered_observations
    globalLaws familyMeasurable probabilityFamilyMeasurable semigroup positive preservesOne
  · intro start
    obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
      initialDirac, finiteEvaluations, observations, deterministicIdentity, naturalStoppingIdentity⟩ := startingData start
    exact initialDirac
  · intro start times timesMonotone startsAtZero tests count terminal
    obtain ⟨starts, startsConverge, laws, lawsConverge, lawsContinuous, lawsCompatible,
      initialDirac, finiteEvaluations, observations, deterministicIdentity, naturalStoppingIdentity⟩ := startingData start
    exact observations times timesMonotone startsAtZero tests count terminal

theorem xiIdentifiedConservativeHuntContinuousPathProperties_of_identifiedPriorFamily (system : EIGSData K)
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
    (properties : XiIdentifiedExtendedFullFutureContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive) :
    XiIdentifiedConservativeHuntContinuousPathProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive := by
  dsimp only [XiIdentifiedExtendedFullFutureContinuousPathProperties, XiIdentifiedConservativeHuntContinuousPathProperties]
    at properties ⊢
  obtain ⟨originalDense, semigroup, semigroupProperties, intertwining⟩ := properties
  exact ⟨originalDense, semigroup,
    xiConservativeHuntContinuousPathSemigroupProperties_of_priorFamily system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate normalization normalizationPositive semigroup semigroupProperties,
    intertwining⟩
theorem exists_xiIdentifiedConservativeHuntContinuousPath_of_priorFamily_rules (system : EIGSData K)
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
      XiIdentifiedConservativeHuntContinuousPathProperties system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
  obtain ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, properties⟩ :=
    exists_xiIdentifiedExtendedFullFutureContinuousPath_of_priorFamily_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  exact ⟨resistanceRate, ratePositive, resistanceVector, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence,
    xiIdentifiedConservativeHuntContinuousPathProperties_of_identifiedPriorFamily system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      normalization normalizationPositive properties⟩

end
end EIGS

#print axioms EIGS.xiExtendedFullFutureContinuousPathSemigroupProperties_of_priorFamily
#print axioms EIGS.xiIdentifiedExtendedFullFutureContinuousPathProperties_of_identifiedPriorFamily
#print axioms EIGS.exists_xiIdentifiedExtendedFullFutureContinuousPath_of_priorFamily_rules
#print axioms EIGS.xiConservativeHuntContinuousPathSemigroupProperties_of_priorFamily
#print axioms EIGS.xiIdentifiedConservativeHuntContinuousPathProperties_of_identifiedPriorFamily
#print axioms EIGS.exists_xiIdentifiedConservativeHuntContinuousPath_of_priorFamily_rules
