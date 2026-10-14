import RequestProject.Section31.EIGSCompletionBallIncidenceMass
import RequestProject.Section31.EIGSLogarithmicEndpointCollar
import RequestProject.Section31.EIGSRecentVertexIncidence

/-! Actual almost-everywhere physical ball mass at the original coarse
level. Endpoint ages come from the proved logarithmic collar construction;
physical ball containment comes from the independently constructed flat
metric separator. Neither probability nor volume is a target hypothesis.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory Filter Topology
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem exists_xiTypicalLogarithmicBallMass_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (primitiveDegree : (degreeMatrix system).IsPrimitive) (width : ℝ) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    let distanceGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width →
    ∃ coefficient : ℝ, 0 < coefficient ∧ ∃ spatialFraction : ℝ, 0 < spatialFraction ∧
      ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index : ℕ in atTop,
      ∀ radius : ℝ, radius < spatialFraction * (system.distanceSpectralRadius rulesConnected)⁻¹ ^ index →
      (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass).real
        (Metric.closedBall
          (xiAddressLimit system rulesConnected parameters.lengths parameters.lengthsPositive
            (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair address) radius) ≤
      coefficient * finiteRealMatrixSpectralRadius (degreeMatrix system) ^
        Nat.ceil (width * Real.log (index + 2 : ℝ)) / mass.rate ^ index := by
  intro parameters mass distanceGreaterThanOne widthLarge
  obtain ⟨minimumColour, _, minimumBound⟩ := Finset.univ.exists_min_image parameters.lengths
    ⟨system.initCol, Finset.mem_univ _⟩
  have minimumPositive := parameters.lengthsPositive minimumColour
  obtain ⟨massConstant, massConstantPositive, ballMass⟩ := exists_xiCompletionBall_incidence_mass_bound
    system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceGreaterThanOne parameters.eigenpair mass
    (parameters.lengths minimumColour) minimumPositive
    (fun colour => minimumBound colour (Finset.mem_univ _))
  obtain ⟨degreeConstant, degreeConstantPositive, endpointBound⟩ :=
    exists_xiNoncollar_endpoint_incidence_bound system primitiveDegree
  refine ⟨massConstant * degreeConstant, mul_pos massConstantPositive degreeConstantPositive,
    parameters.lengths minimumColour, minimumPositive, ?_⟩
  filter_upwards [xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance system rulesConnected
    rulesLoopless plantingNonadjacent distancePositive mass primitiveDegree width widthLarge] with address avoids
  filter_upwards [avoids] with index avoided
  intro radius radiusBound
  have incidenceBound := endpointBound
    (index - Nat.ceil (width * Real.log (index + 2 : ℝ)))
    (Nat.ceil (width * Real.log (index + 2 : ℝ))) address avoided.2
  rw [avoided.1] at incidenceBound
  have measuredBound := ballMass index address radius radiusBound
  have comparison := mul_le_mul_of_nonneg_left incidenceBound
    (div_nonneg massConstantPositive.le (pow_nonneg mass.rate_positive.le index))
  exact (measuredBound.trans comparison).trans_eq (by ring)

end
end EIGS

#print axioms EIGS.exists_xiTypicalLogarithmicBallMass_of_rules
