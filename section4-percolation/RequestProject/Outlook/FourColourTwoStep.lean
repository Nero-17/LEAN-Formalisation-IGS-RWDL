import RequestProject.Outlook.FourColourRuleAudit
import RequestProject.Outlook.FourColourTerminalAudit
import Mathlib.MeasureTheory.Integral.Pi

/-! A genuine two-step random network formed using the literal arrows in the
figure. The outer red outcome has its verified probability; conditional on it,
the four child outcomes are independent with their actual colour laws. -/
namespace Outlook.FourColourRuleAudit
open Cluster MeasureTheory
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
local instance : MeasurableSpace (Fin 9) := ⊤
local instance : DiscreteMeasurableSpace (Fin 9) := ⟨fun _ => trivial⟩

def redEdgeNetwork (selected : Fin 4) : TTN :=
  if selected=0 then TTN.edgeTTN else TTN.gapTTN

def oneStepRedNetwork (parent : Fin 4) (outcome : Fin 9) : TTN :=
  TTN.parTTN (TTN.seriesTTN (redEdgeNetwork (colour parent outcome 0))
      (redEdgeNetwork (colour parent outcome 1)))
    (TTN.seriesTTN (redEdgeNetwork (colour parent outcome 2))
      (redEdgeNetwork (colour parent outcome 3)))

theorem oneStepRedNetwork_source (parent : Fin 4) (outcome : Fin 9) :
    (oneStepRedNetwork parent outcome).sourceTailCount = outgoingCount parent outcome 0 := by
  rw [outgoingCount_eq_table]
  fin_cases parent <;> fin_cases outcome <;> decide

theorem oneStepRedNetwork_sink (parent : Fin 4) (outcome : Fin 9) :
    (oneStepRedNetwork parent outcome).sinkHeadCount = incomingCount parent outcome 0 := by
  rw [incomingCount_eq_table]
  fin_cases parent <;> fin_cases outcome <;> decide

def twoStepRedNetwork (outer : Fin 9) (children : Fin 4 → Fin 9) : TTN :=
  TTN.parTTN
    (TTN.seriesTTN (oneStepRedNetwork (colour 0 outer 0) (children 0))
      (oneStepRedNetwork (colour 0 outer 1) (children 1)))
    (TTN.seriesTTN (oneStepRedNetwork (colour 0 outer 2) (children 2))
      (oneStepRedNetwork (colour 0 outer 3) (children 3)))

noncomputable def childOutcomeMeasure (outer : Fin 9) : Measure (Fin 4 → Fin 9) :=
  Measure.pi (fun edge => (outcomePMF (colour 0 outer edge)).toMeasure)

instance childOutcomeMeasure_probability (outer : Fin 9) :
    IsProbabilityMeasure (childOutcomeMeasure outer) := by
  unfold childOutcomeMeasure
  infer_instance

noncomputable def twoStepSourceExpectation : ℝ :=
  ∫ outer, (∫ children, ((twoStepRedNetwork outer children).sourceTailCount : ℝ)
    ∂childOutcomeMeasure outer) ∂(outcomePMF 0).toMeasure

noncomputable def twoStepSinkExpectation : ℝ :=
  ∫ outer, (∫ children, ((twoStepRedNetwork outer children).sinkHeadCount : ℝ)
    ∂childOutcomeMeasure outer) ∂(outcomePMF 0).toMeasure

theorem twoStepSource_conditional (outer : Fin 9) :
    (∫ children, ((twoStepRedNetwork outer children).sourceTailCount : ℝ)
      ∂childOutcomeMeasure outer) =
      expected (colour 0 outer 0) (fun outcome => outgoingCount (colour 0 outer 0) outcome 0) +
      expected (colour 0 outer 2) (fun outcome => outgoingCount (colour 0 outer 2) outcome 0) := by
  simp only [twoStepRedNetwork, TTN.sourceTailCount_par, TTN.sourceTailCount_series,
    oneStepRedNetwork_source, Nat.cast_add]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  unfold childOutcomeMeasure
  rw [integral_comp_eval
      (μ := fun edge : Fin 4 => (outcomePMF (colour 0 outer edge)).toMeasure)
      (i := (0 : Fin 4))
      (f := fun outcome : Fin 9 => (outgoingCount (colour 0 outer 0) outcome 0 : ℝ))
      Measurable.of_discrete.aestronglyMeasurable,
    integral_comp_eval
      (μ := fun edge : Fin 4 => (outcomePMF (colour 0 outer edge)).toMeasure)
      (i := (2 : Fin 4))
      (f := fun outcome : Fin 9 => (outgoingCount (colour 0 outer 2) outcome 0 : ℝ))
      Measurable.of_discrete.aestronglyMeasurable]
  rw [← expected_eq_actual_integral, ← expected_eq_actual_integral]

theorem twoStepSink_conditional (outer : Fin 9) :
    (∫ children, ((twoStepRedNetwork outer children).sinkHeadCount : ℝ)
      ∂childOutcomeMeasure outer) =
      expected (colour 0 outer 1) (fun outcome => incomingCount (colour 0 outer 1) outcome 0) +
      expected (colour 0 outer 3) (fun outcome => incomingCount (colour 0 outer 3) outcome 0) := by
  simp only [twoStepRedNetwork, TTN.sinkHeadCount_par, TTN.sinkHeadCount_series,
    oneStepRedNetwork_sink, Nat.cast_add]
  rw [integral_add Integrable.of_finite Integrable.of_finite]
  unfold childOutcomeMeasure
  rw [integral_comp_eval
      (μ := fun edge : Fin 4 => (outcomePMF (colour 0 outer edge)).toMeasure)
      (i := (1 : Fin 4))
      (f := fun outcome : Fin 9 => (incomingCount (colour 0 outer 1) outcome 0 : ℝ))
      Measurable.of_discrete.aestronglyMeasurable,
    integral_comp_eval
      (μ := fun edge : Fin 4 => (outcomePMF (colour 0 outer edge)).toMeasure)
      (i := (3 : Fin 4))
      (f := fun outcome : Fin 9 => (incomingCount (colour 0 outer 3) outcome 0 : ℝ))
      Measurable.of_discrete.aestronglyMeasurable]
  rw [← expected_eq_actual_integral, ← expected_eq_actual_integral]

private theorem outcomeMeasure_real_singleton (parent : Fin 4) (outcome : Fin 9) :
    (outcomePMF parent).toMeasure.real {outcome} = criticalWeights parent outcome := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ _ MeasurableSet.of_discrete,
    outcomePMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal (criticalWeights_nonnegative parent outcome)]

private theorem matrixSquareSource :
    (Outlook.correctedCriticalEN^2) 0 0 =
      16*Reduced.pc^4+4*Reduced.pc^6+4*Reduced.pc^7 := by
  rw [pow_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_eight]
  change (4*Reduced.pc^2)*(4*Reduced.pc^2) + 0*0 +
    (2*Reduced.pc^4)*(2*Reduced.pc^2) + 0*0 +
    (2*Reduced.pc^5)*(2*Reduced.pc^2) + 0*0 + 0*0 + 0*0 = _
  ring

private theorem matrixSquareSink :
    (Outlook.correctedCriticalEN^2) 1 1 = 16*Reduced.pc^4+4*Reduced.pc^6 := by
  rw [pow_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_eight]
  change 0*0 + (4*Reduced.pc^2)*(4*Reduced.pc^2) + 0*0 +
    (2*Reduced.pc^4)*(2*Reduced.pc^2) + 0*0 + (2*Reduced.pc^5)*0 + 0*0 + 0*0 = _
  ring

private theorem redOutgoingExpectation (parent : Fin 4) :
    expected parent (fun outcome => outgoingCount parent outcome 0) =
      ![4*Reduced.pc^2, 2*Reduced.pc^2, 2*Reduced.pc^2, 0] parent := by
  fin_cases parent
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (0 : Fin 8)) (0 : Fin 8)
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (2 : Fin 8)) (0 : Fin 8)
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (4 : Fin 8)) (0 : Fin 8)
  · norm_num [expected, outgoingCount_eq_table, criticalWeights, outgoingCountTable,
      Fin.sum_univ_succ]

private theorem redIncomingExpectation (parent : Fin 4) :
    expected parent (fun outcome => incomingCount parent outcome 0) =
      ![4*Reduced.pc^2, 2*Reduced.pc^2, 0, 0] parent := by
  fin_cases parent
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (1 : Fin 8)) (1 : Fin 8)
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (3 : Fin 8)) (1 : Fin 8)
  · simpa [meanLiveBoundary, boundaryParent, Outlook.correctedCriticalEN, Outlook.EN] using
      congrFun (congrFun meanLiveBoundary_eq_correctedCriticalEN (5 : Fin 8)) (1 : Fin 8)
  · norm_num [expected, incomingCount_eq_table, criticalWeights, incomingCountTable,
      Fin.sum_univ_succ]
theorem twoStepSourceExpectation_eq_square :
    twoStepSourceExpectation = (Outlook.correctedCriticalEN^2) 0 0 := by
  rw [matrixSquareSource]
  unfold twoStepSourceExpectation
  simp_rw [twoStepSource_conditional]
  rw [integral_fintype _ Integrable.of_finite]
  simp_rw [outcomeMeasure_real_singleton, redOutgoingExpectation]
  simp only [Fin.sum_univ_succ]
  change Reduced.pc^3 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (2*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 2*Reduced.pc^2) + (Reduced.pc^5 * (4*Reduced.pc^2 + 2*Reduced.pc^2) + (Reduced.pc^5 * (2*Reduced.pc^2 + 4*Reduced.pc^2) + (0 * (0 + 0) + (0 * (0 + 0) + (0))))))))) = _
  linear_combination (8*Reduced.pc^5+16*Reduced.pc^4) * Reduced.pc_sq

theorem twoStepSinkExpectation_eq_square :
    twoStepSinkExpectation = (Outlook.correctedCriticalEN^2) 1 1 := by
  rw [matrixSquareSink]
  unfold twoStepSinkExpectation
  simp_rw [twoStepSink_conditional]
  rw [integral_fintype _ Integrable.of_finite]
  simp_rw [outcomeMeasure_real_singleton, redIncomingExpectation]
  simp only [Fin.sum_univ_succ]
  change Reduced.pc^3 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (2*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 2*Reduced.pc^2) + (Reduced.pc^4 * (4*Reduced.pc^2 + 4*Reduced.pc^2) + (Reduced.pc^5 * (4*Reduced.pc^2 + 0) + (Reduced.pc^5 * (0 + 4*Reduced.pc^2) + (0 * (0 + 0) + (0 * (0 + 0) + (0))))))))) = _
  linear_combination (8*Reduced.pc^5+16*Reduced.pc^4) * Reduced.pc_sq

theorem literal_two_step_terminal_difference :
    twoStepSourceExpectation-twoStepSinkExpectation = 4*Reduced.pc^7 := by
  rw [twoStepSourceExpectation_eq_square, twoStepSinkExpectation_eq_square]
  exact Outlook.correctedCriticalEN_square_terminal_difference

theorem literal_two_step_not_actual_terminal_moments :
    ¬ (twoStepSourceExpectation =
        (∫ configuration, ((Cluster.net 2 configuration).sourceTailCount : ℝ)
          ∂Cluster.connectedMeasure 2) ∧
      twoStepSinkExpectation =
        (∫ configuration, ((Cluster.net 2 configuration).sinkHeadCount : ℝ)
          ∂Cluster.connectedMeasure 2)) := by
  rintro ⟨sourceIdentity, sinkIdentity⟩
  have equal : twoStepSourceExpectation = twoStepSinkExpectation :=
    sourceIdentity.trans ((Cluster.connected_actual_terminal_expectations_equal 2).trans sinkIdentity.symm)
  have positive : 0 < 4*Reduced.pc^7 := mul_pos (by norm_num) (pow_pos Reduced.pc_pos 7)
  have difference := literal_two_step_terminal_difference
  rw [equal, sub_self] at difference
  linarith [difference]
end Outlook.FourColourRuleAudit

#print axioms Outlook.FourColourRuleAudit.oneStepRedNetwork_source
#print axioms Outlook.FourColourRuleAudit.oneStepRedNetwork_sink
#print axioms Outlook.FourColourRuleAudit.childOutcomeMeasure_probability
#print axioms Outlook.FourColourRuleAudit.twoStepSource_conditional
#print axioms Outlook.FourColourRuleAudit.twoStepSink_conditional
#print axioms Outlook.FourColourRuleAudit.twoStepSourceExpectation_eq_square
#print axioms Outlook.FourColourRuleAudit.twoStepSinkExpectation_eq_square
#print axioms Outlook.FourColourRuleAudit.literal_two_step_terminal_difference
#print axioms Outlook.FourColourRuleAudit.literal_two_step_not_actual_terminal_moments


