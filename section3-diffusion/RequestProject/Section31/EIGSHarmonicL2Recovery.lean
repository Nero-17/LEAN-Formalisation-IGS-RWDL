import RequestProject.Section31.EIGSHarmonicDensity
import RequestProject.Section31.EIGSActualL2Core

/-! Actual weighted harmonic functions in the native vertex speed L² spaces.
The sequence retains every original level. Levels before the prescribed
boundary level are zero and have no effect on Strong convergence. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

set_option maxHeartbeats 1800000

variable {K : ℕ}

noncomputable def xiFiniteSpeedL2 (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (values : XiVtx system level → ℝ) :
    Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  (MemLp.of_discrete (f := values)).toLp values

theorem xiFiniteSpeedL2_ae (system : EIGSData K) (mass : XiMassParameters system)
    (level : ℕ) (values : XiVtx system level → ℝ) :
    xiFiniteSpeedL2 system mass level values =ᵐ[xiVertexSpeedMeasure system mass level] values :=
  MemLp.coeFn_toLp _

section Metric

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)

theorem xiSpeedL2Core_restrict_eq_finiteSpeedL2
    (function : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ) (level : ℕ) :
    (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass).restrict level function =
      xiFiniteSpeedL2 system mass level
        (fun vertex => function (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) := by
  change Lp.compMeasurePreserving _ _ (BoundedContinuousFunction.toLp 2 _ ℝ function) = _
  apply Lp.ext
  have measurePreserving := IGS.Sec31.embeddingMeasurePreserving
    (xiNativeSpeedProbabilityMeasure system mass)
    (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
    (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair) level
  have functionAE := BoundedContinuousFunction.coeFn_toLp 2
    (IGS.Sec31.embeddedProbabilityMeasures (xiNativeSpeedProbabilityMeasure system mass)
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
      (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair) level : Measure _) ℝ function
  have pulledAE := measurePreserving.quasiMeasurePreserving.ae_eq functionAE
  exact (Lp.coeFn_compMeasurePreserving _ measurePreserving).trans
    (pulledAE.trans (xiFiniteSpeedL2_ae system mass level
      (fun vertex => function (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex))).symm)

variable (resistanceRate : ℝ) (resistanceRatePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (resistanceVectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

noncomputable def xiHarmonicNativeL2 (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (level : ℕ) : Lp ℝ 2 (xiVertexSpeedMeasure system mass level) :=
  if initialLevel ≤ level then
    xiFiniteSpeedL2 system mass level (fun vertex =>
      xiHarmonicUnionExtension system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues (xiVertexEmbedding system level vertex))
  else 0

theorem xiHarmonicNativeL2_at_offset (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (offset : ℕ) :
    xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive resistanceVector
      resistanceVectorPositive renormalizationEigenpair initialLevel initialValues (initialLevel + offset) =
      xiFiniteSpeedL2 system mass (initialLevel + offset)
        (xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset) := by
  rw [xiHarmonicNativeL2, if_pos (Nat.le_add_right _ _)]
  congr 1
  funext vertex
  exact xiHarmonicUnionExtension_values system rulesConnected resistanceRate resistanceRatePositive resistanceVector
    resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex

theorem xiHarmonicNativeL2_strong (initialLevel : ℕ) (initialValues : XiVtx system initialLevel → ℝ)
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ))
    (extensionValues : ∀ offset (vertex : XiVtx system (initialLevel + offset)),
      extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (initialLevel + offset) vertex) =
        xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
          resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset vertex) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    (xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass).Strong
      (xiHarmonicNativeL2 system rulesConnected mass resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues)
      ((xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact extension)) := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  intro tolerance tolerancePositive
  refine ⟨BoundedContinuousFunction.mkOfCompact extension, by simpa using tolerancePositive, ?_⟩
  filter_upwards [eventually_ge_atTop initialLevel] with level afterInitial
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le afterInitial
  rw [xiHarmonicNativeL2_at_offset, xiSpeedL2Core_restrict_eq_finiteSpeedL2]
  have valuesAgree :
      (fun vertex => (BoundedContinuousFunction.mkOfCompact extension)
        (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair (initialLevel + offset) vertex)) =
      xiHarmonicValues system rulesConnected resistanceRate resistanceRatePositive resistanceVector
        resistanceVectorPositive renormalizationEigenpair initialLevel initialValues offset :=
    funext (extensionValues offset)
  rw [valuesAgree, sub_self, norm_zero]
  exact tolerancePositive

end Metric

end EIGS
