import RequestProject.Section31.EIGSHarmonicL2Density

/-! Rule-only construction of every weighted harmonic core recovery, and its
actual native speed L² scalar products. These weighted harmonic rows are
distinguished from original unit-resistance fine-graph Dirichlet profiles. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction ENNReal

set_option maxHeartbeats 1800000

variable {K : ℕ}

theorem exists_xiContinuousHarmonic_L2_recovery_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ resistanceRatePositive : 0 < resistanceRate,
      ∃ resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∀ initialLevel (initialValues : XiVtx system initialLevel → ℝ),
        ∃ extension : C(parameters.LimitSpace, ℝ),
          (∀ offset (vertex : XiVtx system (initialLevel + offset)),
            extension (parameters.vertexEmbedding (initialLevel + offset) vertex) =
              xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
                resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) ∧
          xiExtendedWeightedEnergy system resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive
              (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair) =
            ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate resistanceRatePositive resistanceVector
              resistanceVectorPositive initialLevel).energy initialValues) ∧
          core.Strong (xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive
            resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)
            (core.embed (BoundedContinuousFunction.mkOfCompact extension)) := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  obtain ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive,
      renormalizationEigenpair, harmonicExist⟩ :=
    exists_xiContinuousHarmonics_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  refine ⟨resistanceRate, resistanceVector, resistanceRatePositive, resistanceVectorPositive, renormalizationEigenpair, ?_⟩
  intro initialLevel initialValues
  obtain ⟨extension, extensionValues⟩ := harmonicExist initialLevel initialValues
  refine ⟨extension, extensionValues, ?_, ?_⟩
  · exact xiContinuousHarmonic_extended_energy system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) parameters.ratePositive parameters.eigenpair resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
      extension extensionValues
  · exact xiHarmonicNativeL2_strong system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate
      resistanceRatePositive resistanceVector resistanceVectorPositive renormalizationEigenpair initialLevel initialValues
      extension extensionValues

theorem xiHarmonicNativeL2_inner_tendsto (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (firstLevel secondLevel : ℕ)
    (firstValues : XiVtx system firstLevel → ℝ) (secondValues : XiVtx system secondLevel → ℝ)
    (firstExtension secondExtension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (firstAgreement : ∀ offset (vertex : XiVtx system (firstLevel + offset)),
      firstExtension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (firstLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair firstLevel firstValues offset vertex)
    (secondAgreement : ∀ offset (vertex : XiVtx system (secondLevel + offset)),
      secondExtension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (secondLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair secondLevel secondValues offset vertex) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    Tendsto (fun level => inner ℝ
      (xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair firstLevel firstValues level)
      (xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair secondLevel secondValues level)) atTop
      (nhds (inner ℝ (core.embed (BoundedContinuousFunction.mkOfCompact firstExtension))
        (core.embed (BoundedContinuousFunction.mkOfCompact secondExtension)))) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  exact (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass).strong_inner_tendsto
      (xiHarmonicNativeL2_strong system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair firstLevel firstValues firstExtension firstAgreement)
      (xiHarmonicNativeL2_strong system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate resistanceRatePositive resistanceVector resistanceVectorPositive
        renormalizationEigenpair secondLevel secondValues secondExtension secondAgreement)

end EIGS
