import RequestProject.Section31.EIGSNativeEnergyCompactness
import RequestProject.Section31.EIGSBoundaryLimitCompatibility
import RequestProject.Section31.EIGSHarmonicClosedLimit
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.QuadraticEnergyExtended

/-! Actual bounded-energy native sequences admit Strong subsequences in the
constructed closed energy domain, with the correct actual energy bound. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology

set_option maxHeartbeats 3000000

variable {K : ℕ}

theorem exists_xiNativeEnergy_closed_subsequence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily rulesConnected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector)))
    (levels : ℕ → ℕ) (levelsStrict : StrictMono levels)
    (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (normBound energyBound : ℝ) (normsBounded : ∀ index, ‖sequence (levels index)‖ ≤ normBound)
    (energiesBounded : ∀ index, xiNativeScaledUnitEnergy system mass resistanceRate normalization (levels index) (sequence (levels index)) ≤ energyBound) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro values energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair values energyCauchy
        (by simpa using ambientZero.norm)
    ∃ selection : ℕ → ℕ, ∃ selectionStrict : StrictMono selection,
      ∃ limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass),
        (core.reindex (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop).Strong
          (fun index => sequence (levels (selection index))) limit ∧
        QuadraticEnergySpace.closedExtendedEnergy originalDomain originalForm nonnegative closable limit ≤ ENNReal.ofReal energyBound := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
  let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro values energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair values energyCauchy
      (by simpa using ambientZero.norm)
  obtain ⟨selection, selectionStrict, limit, strongLimit, boundaries, boundaryConvergence,
      approximation, approximationAgreement, approximationConvergence⟩ :=
    exists_xiNativeEnergy_strong_subsequence system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive eigenpair normalization normalizationPositive levels levelsStrict
      sequence normBound energyBound normsBounded energiesBounded
  have compatible := xiNativeBoundaryLimits_compatible system mass sequence (levels ∘ selection)
    (levelsStrict.comp selectionStrict).tendsto_atTop boundaries boundaryConvergence
  obtain ⟨target, targetBoundary⟩ := exists_xiUnionFunction_of_compatible_boundaries system boundaries compatible
  have traceBound : ∀ coarseLevel,
      (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive coarseLevel).energy
        (boundaries coarseLevel) ≤ energyBound := by
    intro coarseLevel
    exact xiNativeBoundaryLimit_energy_le system rulesConnected mass resistanceRate normalization ratePositive normalizationPositive
      resistanceVector vectorPositive normalizedConvergence sequence (levels ∘ selection) (levelsStrict.comp selectionStrict).tendsto_atTop
      coarseLevel (boundaries coarseLevel) (boundaryConvergence coarseLevel) energyBound
      (Filter.Eventually.of_forall (fun index => energiesBounded (selection index)))
  obtain ⟨targetFinite, targetBound⟩ := xiUnionFunction_finiteEnergy_of_boundary_bound system resistanceRate ratePositive
    resistanceVector vectorPositive boundaries target targetBoundary energyBound traceBound
  have agreement : ∀ coarseLevel vertex,
      approximation coarseLevel (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
      xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        coarseLevel (target ∘ xiVertexEmbedding system coarseLevel) vertex := by
    intro coarseLevel vertex
    rw [show target ∘ xiVertexEmbedding system coarseLevel = boundaries coarseLevel from funext (targetBoundary coarseLevel)]
    exact approximationAgreement coarseLevel vertex
  obtain ⟨membership, energyIdentity⟩ := xiHarmonic_L2_limit_closed_energy system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    ⟨target, targetFinite⟩ approximation agreement limit approximationConvergence closable
  refine ⟨selection, selectionStrict, limit, strongLimit, ?_⟩
  rw [QuadraticEnergySpace.closedExtendedEnergy_of_mem originalDomain originalForm nonnegative closable limit membership, energyIdentity,
    ENNReal.ofReal_toReal ((xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive target).1 targetFinite)]
  exact targetBound

end EIGS

#print axioms EIGS.exists_xiNativeEnergy_closed_subsequence
