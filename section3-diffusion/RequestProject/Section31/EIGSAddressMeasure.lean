import RequestProject.Section31.EIGSAddressLimit
import RequestProject.Section31.EIGSEdgeDescendants
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! Borel measurability of the actual address limit and its probability
pushforward to the constructed completion. The original finite speed measures
are defined from the two actual endpoints of a uniform edge. Weak convergence
and the degree-stationary identity are separate obligations. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped ENNReal

variable {K : ℕ} (system : EIGSData K)
    (ruleConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (rate : ℝ)

section BorelStructure

variable (ratePositive : 0 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

noncomputable instance xiCompletionMeasurableSpace :
    MeasurableSpace (XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) :=
  borel _

instance xiCompletionBorelSpace :
    BorelSpace (XiMetricCompletion system ruleConnected lengths lengthsPositive rate ratePositive eigenpair) := ⟨rfl⟩

end BorelStructure

variable (rateGreaterThanOne : 1 < rate)
    (eigenpair : (system.ruleFamily ruleConnected).metricLengths lengths = rate • lengths)

include ruleConnected lengthsPositive rateGreaterThanOne eigenpair

theorem measurable_xiAddressTailApproximation (level : ℕ) :
    Measurable (xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne
      eigenpair level) := by
  have finiteMeasurable : Measurable (fun edge : XiEdge system.toRuleData level =>
      xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
        (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiTail system level edge)) :=
    Measurable.of_discrete
  exact finiteMeasurable.comp (measurable_xiAddressEdge system level)

theorem measurable_xiAddressLimit :
    Measurable (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair) :=
  measurable_of_tendsto_metrizable
    (measurable_xiAddressTailApproximation system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)
    (tendsto_pi_nhds.mpr
      (xiAddressTailApproximation_tendsto system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair))

noncomputable def xiLimitMeasure (mass : XiMassParameters system) :
    Measure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  mass.addressMeasure.map (xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair)

instance xiLimitMeasure_probability (mass : XiMassParameters system) :
    IsProbabilityMeasure (xiLimitMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass) :=
  Measure.isProbabilityMeasure_map
    (measurable_xiAddressLimit system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair).aemeasurable

noncomputable def xiEdgeTailPoint (level : ℕ) (edge : XiEdge system.toRuleData level) :
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair :=
  xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiTail system level edge)

noncomputable def xiEdgeHeadPoint (level : ℕ) (edge : XiEdge system.toRuleData level) :
    XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair :=
  xiCompletionEmbedding system ruleConnected lengths lengthsPositive rate
    (zero_lt_one.trans rateGreaterThanOne) eigenpair level (XiHead system level edge)

noncomputable def xiTailMeasure (mass : XiMassParameters system) (level : ℕ) :
    Measure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  (mass.uniformEdgeMeasure level).map
    (xiEdgeTailPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level)

noncomputable def xiHeadMeasure (mass : XiMassParameters system) (level : ℕ) :
    Measure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  (mass.uniformEdgeMeasure level).map
    (xiEdgeHeadPoint system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair level)

instance xiTailMeasure_probability (mass : XiMassParameters system) (level : ℕ) :
    IsProbabilityMeasure (xiTailMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

instance xiHeadMeasure_probability (mass : XiMassParameters system) (level : ℕ) :
    IsProbabilityMeasure (xiHeadMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level) :=
  Measure.isProbabilityMeasure_map Measurable.of_discrete.aemeasurable

noncomputable def xiSpeedMeasure (mass : XiMassParameters system) (level : ℕ) :
    Measure (XiMetricCompletion system ruleConnected lengths lengthsPositive rate
      (zero_lt_one.trans rateGreaterThanOne) eigenpair) :=
  (1 / 2 : ℝ≥0∞) • xiTailMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level +
    (1 / 2 : ℝ≥0∞) • xiHeadMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level

instance xiSpeedMeasure_probability (mass : XiMassParameters system) (level : ℕ) :
    IsProbabilityMeasure (xiSpeedMeasure system ruleConnected lengths lengthsPositive rate rateGreaterThanOne eigenpair mass level) where
  measure_univ := by
    simp [xiSpeedMeasure, Measure.add_apply, Measure.smul_apply, ENNReal.inv_two_add_inv_two]

end EIGS

#print axioms EIGS.measurable_xiAddressLimit
#print axioms EIGS.xiLimitMeasure_probability
#print axioms EIGS.xiSpeedMeasure_probability
