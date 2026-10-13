import RequestProject.Outlook.FourColourTwoStep
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Boundary-pair laws of the literal two-step figure process and the actual
connected critical percolation network. The sample law is constructed from the
verified outer PMF and the independent child kernel. -/
namespace Outlook.FourColourRuleAudit
open Cluster MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance : MeasurableSpace (Fin 9) := ⊤
local instance : DiscreteMeasurableSpace (Fin 9) := ⟨fun _ => trivial⟩

noncomputable def childOutcomeKernel : Kernel (Fin 9) (Fin 4 → Fin 9) where
  toFun := childOutcomeMeasure
  measurable' := Measurable.of_discrete

instance childOutcomeKernel_markov : IsMarkovKernel childOutcomeKernel where
  isProbabilityMeasure outer := childOutcomeMeasure_probability outer

noncomputable def twoStepSampleMeasure : Measure (Fin 9 × (Fin 4 → Fin 9)) :=
  (outcomePMF 0).toMeasure ⊗ₘ childOutcomeKernel

instance twoStepSampleMeasure_probability : IsProbabilityMeasure twoStepSampleMeasure := by
  unfold twoStepSampleMeasure
  infer_instance

noncomputable def literalBoundaryLaw : Measure (ℕ × ℕ) :=
  twoStepSampleMeasure.map (fun sample =>
    ((twoStepRedNetwork sample.1 sample.2).sourceTailCount,
      (twoStepRedNetwork sample.1 sample.2).sinkHeadCount))

noncomputable def actualBoundaryLaw : Measure (ℕ × ℕ) :=
  (Cluster.connectedMeasure 2).map (fun configuration =>
    ((Cluster.net 2 configuration).sourceTailCount, (Cluster.net 2 configuration).sinkHeadCount))

theorem literalBoundaryLaw_source_integral :
    (∫ pair, (pair.1 : ℝ) ∂literalBoundaryLaw) = twoStepSourceExpectation := by
  rw [literalBoundaryLaw, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  unfold twoStepSampleMeasure
  rw [Measure.integral_compProd Integrable.of_finite]
  rfl

theorem literalBoundaryLaw_sink_integral :
    (∫ pair, (pair.2 : ℝ) ∂literalBoundaryLaw) = twoStepSinkExpectation := by
  rw [literalBoundaryLaw, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]
  unfold twoStepSampleMeasure
  rw [Measure.integral_compProd Integrable.of_finite]
  rfl

theorem actualBoundaryLaw_source_integral :
    (∫ pair, (pair.1 : ℝ) ∂actualBoundaryLaw) =
      ∫ configuration, ((Cluster.net 2 configuration).sourceTailCount : ℝ)
        ∂Cluster.connectedMeasure 2 := by
  rw [actualBoundaryLaw, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]

theorem actualBoundaryLaw_sink_integral :
    (∫ pair, (pair.2 : ℝ) ∂actualBoundaryLaw) =
      ∫ configuration, ((Cluster.net 2 configuration).sinkHeadCount : ℝ)
        ∂Cluster.connectedMeasure 2 := by
  rw [actualBoundaryLaw, integral_map Measurable.of_discrete.aemeasurable
    Measurable.of_discrete.aestronglyMeasurable]

theorem literal_two_step_boundary_law_ne_actual : literalBoundaryLaw ≠ actualBoundaryLaw := by
  intro equal
  apply literal_two_step_not_actual_terminal_moments
  constructor
  · rw [← literalBoundaryLaw_source_integral, equal, actualBoundaryLaw_source_integral]
  · rw [← literalBoundaryLaw_sink_integral, equal, actualBoundaryLaw_sink_integral]
end Outlook.FourColourRuleAudit

#print axioms Outlook.FourColourRuleAudit.childOutcomeKernel_markov
#print axioms Outlook.FourColourRuleAudit.twoStepSampleMeasure_probability
#print axioms Outlook.FourColourRuleAudit.literalBoundaryLaw_source_integral
#print axioms Outlook.FourColourRuleAudit.literalBoundaryLaw_sink_integral
#print axioms Outlook.FourColourRuleAudit.actualBoundaryLaw_source_integral
#print axioms Outlook.FourColourRuleAudit.actualBoundaryLaw_sink_integral
#print axioms Outlook.FourColourRuleAudit.literal_two_step_boundary_law_ne_actual
