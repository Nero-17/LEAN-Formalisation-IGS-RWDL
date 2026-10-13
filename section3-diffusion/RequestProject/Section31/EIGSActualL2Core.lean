import RequestProject.Section31.EIGSSpeedWeakLimit
import RequestProject.Section31.VaryingEmbeddedL2Core
import RequestProject.Section31.EIGSMetricOfRules

/-! The varying L2 core on the actual Xi vertex speed measures. Compactness,
the reference probability and weak convergence are proved for this system;
none is a supplied analytic conclusion. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

variable {K : ℕ}

noncomputable def xiNativeSpeedProbabilityMeasure (system : EIGSData K)
    (mass : XiMassParameters system) (level : ℕ) : ProbabilityMeasure (XiVtx system level) :=
  ⟨xiVertexSpeedMeasure system mass level, inferInstance⟩

variable (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ) (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily connected).metricLengths lengths = rate • lengths)

theorem measurable_xiCompletionEmbedding (level : ℕ) :
    Measurable (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair level) := Measurable.of_discrete

theorem xiEmbeddedSpeedProbabilityMeasure_eq (mass : XiMassParameters system) :
    IGS.Sec31.embeddedProbabilityMeasures (xiNativeSpeedProbabilityMeasure system mass)
      (xiCompletionEmbedding system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair)
      (measurable_xiCompletionEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair) =
      xiSpeedProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass := by
  funext level
  apply Subtype.ext
  exact xiVertexSpeedMeasure_map system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level

noncomputable def xiSpeedL2Core (mass : XiMassParameters system) :
    letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
    IGS.Sec31.VaryingHilbertCore
      (XiMetricCompletion system connected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ)
      (Lp ℝ 2 (xiLimitMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass))
      (fun level => Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) := by
  letI := xiCompletion_compactSpace system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair
  apply IGS.Sec31.embeddedProbabilityL2Core
    (xiNativeSpeedProbabilityMeasure system mass)
    (xiCompletionEmbedding system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair)
    (measurable_xiCompletionEmbedding system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (xiLimitProbabilityMeasure system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass)
  rw [xiEmbeddedSpeedProbabilityMeasure_eq]
  exact xiSpeedProbabilityMeasure_tendsto system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass

theorem xiSpeedL2Core_dense (mass : XiMassParameters system) :
    DenseRange (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).embed :=
  (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).dense

theorem xiSpeedL2Core_norm_tendsto (mass : XiMassParameters system)
    (function : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    Tendsto (fun level => ‖(xiSpeedL2Core system connected lengths lengthsPositive rate
      rateGreaterThanOne eigenpair mass).restrict level function‖) atTop
      (nhds ‖(xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).embed function‖) :=
  (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).norm_converges function

theorem xiSpeedL2Core_restrictions_strong (mass : XiMassParameters system)
    (function : XiMetricCompletion system connected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair →ᵇ ℝ) :
    (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).Strong
      (fun level => (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).restrict level function)
      ((xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).embed function) :=
  (xiSpeedL2Core system connected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass).strong_restrict function

end EIGS

#print axioms EIGS.xiSpeedL2Core
#print axioms EIGS.xiEmbeddedSpeedProbabilityMeasure_eq
#print axioms EIGS.xiSpeedL2Core_dense
#print axioms EIGS.xiSpeedL2Core_norm_tendsto
#print axioms EIGS.xiSpeedL2Core_restrictions_strong
