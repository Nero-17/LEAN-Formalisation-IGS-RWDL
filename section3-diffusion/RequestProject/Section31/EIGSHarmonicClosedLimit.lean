import RequestProject.Section31.EIGSHarmonicEnergyCauchy
import RequestProject.Section31.EIGSL2QuadraticEnergy
import RequestProject.Section31.QuadraticEnergyCauchyLimit
import RequestProject.Section31.EIGSHarmonicLinear

/-! Identification of an actual L2 limit of compatible continuous harmonic
extensions in the constructed closed domain. Closability is an explicit helper
input, supplied by the separate original-rule closability theorem. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology

set_option maxHeartbeats 2400000

variable {K : ℕ}

theorem xiHarmonic_L2_limit_closed_energy (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily connected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (eigenpair : ∀ colour, (system.ruleFamily connected).Psi resistanceVector colour =
      resistanceRate * resistanceVector colour)
    (target : xiWeightedEnergyDomain system resistanceRate ratePositive resistanceVector vectorPositive)
    (approximation : ℕ → C(XiMetricCompletion system connected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (agreement : ∀ level vertex,
      approximation level (xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair vertex) =
      xiHarmonicUnionExtension system connected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        level (target.val ∘ xiVertexEmbedding system level) vertex)
    (limit : Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass))
    (convergence : Tendsto (fun level => xiContinuousL2Map system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (approximation level)) atTop (nhds limit)) :
    let originalDomain := xiContinuousEnergyLpDomain system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
    ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
      ∃ membership : limit ∈ QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable ⟨limit, membership⟩ =
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive target).toReal := by
  classical
  dsimp only
  intro closable
  have energyIdentity : ∀ level,
      xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
        (approximation level ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) =
      ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
        (target.val ∘ xiVertexEmbedding system level)) := by
    intro level
    rw [show approximation level ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair =
        xiHarmonicUnionExtension system connected resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          level (target.val ∘ xiVertexEmbedding system level) from funext (agreement level)]
    exact xiHarmonicUnionExtension_energy system connected resistanceRate ratePositive resistanceVector vectorPositive
      eigenpair level _
  have finite : ∀ level, approximation level ∈ xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive := by
    intro level
    apply (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2
    change xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) ≠ ⊤
    rw [energyIdentity level]
    exact ENNReal.ofReal_ne_top
  let continuousSequence : ℕ → xiContinuousFiniteEnergyDomain system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive :=
    fun level => ⟨approximation level, finite level⟩
  let unionSequence := fun level => xiContinuousEnergyToUnionDomain system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive (continuousSequence level)
  have boundary : ∀ level vertex, (unionSequence level).val (xiVertexEmbedding system level vertex) =
      target.val (xiVertexEmbedding system level vertex) := by
    intro level vertex
    exact (agreement level (xiVertexEmbedding system level vertex)).trans
      (xiHarmonicUnionExtension_values system connected resistanceRate ratePositive resistanceVector vectorPositive
        eigenpair level (target.val ∘ xiVertexEmbedding system level) 0 vertex)
  have harmonic : ∀ level, unionSequence level ∈ xiHarmonicCoreAt system resistanceRate ratePositive
      resistanceVector vectorPositive level := by
    intro level
    change xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (approximation level ∘ xiCompletionUnionEmbedding system connected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair) = _
    rw [energyIdentity level]
    congr 1
    exact congrArg _ (funext (boundary level)).symm
  let nativeSequence := fun level => xiContinuousEnergyLpEquiv system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive (continuousSequence level)
  have nativeConvergence : Tendsto (fun level => (nativeSequence level).val) atTop (nhds limit) := convergence
  have nativeEnergyCauchy : ∀ tolerance > 0, ∃ threshold, ∀ first ≥ threshold, ∀ second ≥ threshold,
      xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
          (nativeSequence first - nativeSequence second) < tolerance := by
    intro tolerance positive
    obtain ⟨threshold, small⟩ := xiHarmonicCompatible_energy_cauchy system connected resistanceRate ratePositive
      resistanceVector vectorPositive eigenpair target unionSequence harmonic boundary tolerance positive
    refine ⟨threshold, ?_⟩
    intro first firstAfter second secondAfter
    change xiContinuousLpEnergyQuadraticForm system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
      metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
        ((xiContinuousEnergyLpEquiv system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive) (continuousSequence first) -
        (xiContinuousEnergyLpEquiv system connected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive) (continuousSequence second)) < tolerance
    rw [← map_sub, xiContinuousLpEnergyQuadraticForm_of_continuous]
    exact small first firstAfter second secondAfter
  obtain ⟨membership, energyConvergence⟩ := QuadraticEnergySpace.original_energy_cauchy_limit _ _
    (xiContinuousLpEnergyQuadraticForm_nonnegative system connected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair)
    closable nativeSequence limit nativeConvergence nativeEnergyCauchy
  refine ⟨membership, tendsto_nhds_unique energyConvergence ?_⟩
  have unionConvergence := xiHarmonicCompatible_energy_tendsto system connected resistanceRate ratePositive
    resistanceVector vectorPositive eigenpair target unionSequence harmonic boundary
  convert unionConvergence using 1
  ext level
  exact xiContinuousLpEnergyQuadraticForm_of_continuous system connected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive eigenpair
      (continuousSequence level)

end EIGS

#print axioms EIGS.xiHarmonic_L2_limit_closed_energy
