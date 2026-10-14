import RequestProject.Section31.EIGSLogarithmicEndpointCollar
import RequestProject.Section31.EIGSRecentVertexIncidence
import RequestProject.Section31.EIGSHarmonicTwoEndpointCutoff

/-! Actual typical-point cutoffs at the original fine level. Collar
probabilities, Borel--Cantelli avoidance, endpoint incidence, and the binary
harmonic extension are all internally constructed. No point evaluation on
the closed form domain, resistanceRate>1, or exit estimate is assumed.
This is a cutoff result, not a claimed heat-kernel lower bound. Candidate. -/

namespace EIGS
open MeasureTheory Filter Topology
open scoped Classical BigOperators BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

theorem exists_ae_xiTypical_logarithmic_cell_cutoffs (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair
    ∃ normConstant energyConstant : ℝ, 0 < normConstant ∧ 0 < energyConstant ∧
      ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index in atTop,
        ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ),
          extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
            distanceGreaterThanOne metricEigenpair address) = 1 ∧
          (∀ otherAddress : XiEdgeAddress system,
            xiAddressEdge system index otherAddress = xiAddressEdge system index address →
            extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
              distanceGreaterThanOne metricEigenpair otherAddress) = 1) ∧
          (∀ point, 0 ≤ extension point ∧ extension point ≤ 1) ∧
          ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
            metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact extension)‖ ^ 2 ≤
              normConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^
                Nat.ceil (width * Real.log (index + 2 : ℝ)) / mass.rate ^ index ∧
          xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) ≠ ⊤ ∧
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair)).toReal ≤
                energyConstant * finiteRealMatrixSpectralRadius (degreeMatrix system) ^
                  Nat.ceil (width * Real.log (index + 2 : ℝ)) * resistanceRate ^ index := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair
  obtain ⟨normConstant, energyConstant, normPositive, energyPositive, cutoffs⟩ :=
    exists_xiHarmonic_two_endpoint_cell_cutoffs system rulesConnected distancePositive oneColourDistance
      lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  obtain ⟨incidenceConstant, incidencePositive, incidenceBounds⟩ :=
    exists_xiNoncollar_endpoint_incidence_bound system primitiveDegree
  refine ⟨normConstant * incidenceConstant, energyConstant * incidenceConstant,
    mul_pos normPositive incidencePositive, mul_pos energyPositive incidencePositive, ?_⟩
  filter_upwards [xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance system rulesConnected
    rulesLoopless plantingNonadjacent distancePositive mass primitiveDegree width widthLarge] with address avoids
  filter_upwards [avoids] with index information
  obtain ⟨fineLevel, avoids⟩ := information
  have incidenceBound := incidenceBounds (index - Nat.ceil (width * Real.log (index + 2 : ℝ)))
    (Nat.ceil (width * Real.log (index + 2 : ℝ))) address avoids
  rw [fineLevel] at incidenceBound
  obtain ⟨extension, onCell, outside, bounds, normBound, finiteEnergy, energyBound⟩ :=
    cutoffs index (xiAddressEdge system index address)
  refine ⟨extension, onCell address rfl, onCell, bounds, ?_, finiteEnergy, ?_⟩
  · exact normBound.trans ((div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left incidenceBound normPositive.le) (pow_pos mass.rate_positive index).le).trans_eq
        (by ring))
  · exact energyBound.trans ((mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left incidenceBound energyPositive.le) (pow_pos ratePositive index).le).trans_eq
        (by ring))

end
end EIGS

#print axioms EIGS.exists_ae_xiTypical_logarithmic_cell_cutoffs
