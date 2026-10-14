import RequestProject.Section31.EIGSAddressIncidentStar
import RequestProject.Section31.EIGSAddressCellAverageEnergy
import RequestProject.Section31.EIGSHarmonicBoundaryL2

/-! An actual binary harmonic cutoff that equals one on its selected address
cell. Both cell terminals receive value one, including coincident terminals.
The numerical norm and energy costs involve the sum of their incidences.
This is a continuous finite-energy core construction, not a heat lower bound.
Candidate source; no compilation is claimed. -/

namespace EIGS
open IGS.Sec31 MeasureTheory Filter Topology
open scoped Classical BigOperators BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def xiTwoEndpointBoundary (system : EIGSData K) (level : ℕ)
    (first second vertex : XiVtx system level) : ℝ :=
  if vertex = first ∨ vertex = second then 1 else 0

theorem xiTwoEndpointBoundary_bounds (system : EIGSData K) (level : ℕ)
    (first second vertex : XiVtx system level) :
    0 ≤ xiTwoEndpointBoundary system level first second vertex ∧
      xiTwoEndpointBoundary system level first second vertex ≤ 1 := by
  unfold xiTwoEndpointBoundary
  split_ifs <;> norm_num

theorem xiTwoEndpointBoundary_edge_square_le (system : EIGSData K) (level : ℕ)
    (first second : XiVtx system level) (edge : XiEdge system.toRuleData level) :
    (xiTwoEndpointBoundary system level first second (XiTail system level edge) -
      xiTwoEndpointBoundary system level first second (XiHead system level edge)) ^ 2 ≤
        xiEdgeStarMultiplicity system level first edge + xiEdgeStarMultiplicity system level second edge := by
  unfold xiTwoEndpointBoundary xiEdgeStarMultiplicity
  split_ifs <;> simp_all <;> norm_num

theorem xiTwoEndpointBoundary_finite_energy_bound (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (level : ℕ) (first second : XiVtx system level) :
    (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
      (xiTwoEndpointBoundary system level first second) ≤
        (∑ colour, (resistanceVector colour)⁻¹) *
          ((xiVertexIncidenceCount system level first : ℝ) + (xiVertexIncidenceCount system level second : ℝ)) *
          resistanceRate ^ level := by
  have inverseBound (colour : Fin K) :
      (resistanceVector colour)⁻¹ ≤ ∑ index, (resistanceVector index)⁻¹ :=
    Finset.single_le_sum (fun index _ => (inv_pos.mpr (vectorPositive index)).le) (Finset.mem_univ colour)
  rw [xiWeightedFiniteNetwork_energy_eq_potential]
  change resistanceRate ^ level *
    (∑ edge, (resistanceVector (XiCol system.toRuleData level edge))⁻¹ *
      (xiTwoEndpointBoundary system level first second (XiTail system level edge) -
        xiTwoEndpointBoundary system level first second (XiHead system level edge)) ^ 2) ≤ _
  have sumBound : (∑ edge : XiEdge system.toRuleData level,
      (resistanceVector (XiCol system.toRuleData level edge))⁻¹ *
        (xiTwoEndpointBoundary system level first second (XiTail system level edge) -
          xiTwoEndpointBoundary system level first second (XiHead system level edge)) ^ 2) ≤
      (∑ colour, (resistanceVector colour)⁻¹) *
        ((xiVertexIncidenceCount system level first : ℝ) + (xiVertexIncidenceCount system level second : ℝ)) := by
    rw [← xiEdgeStarMultiplicity_sum, ← xiEdgeStarMultiplicity_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro edge _
    exact (mul_le_mul_of_nonneg_left (xiTwoEndpointBoundary_edge_square_le system level first second edge)
      (inv_pos.mpr (vectorPositive _)).le).trans
        (mul_le_mul_of_nonneg_right (inverseBound _)
          (add_nonneg (xiEdgeStarMultiplicity_bounds system level first edge).1
            (xiEdgeStarMultiplicity_bounds system level second edge).1))
  exact (mul_le_mul_of_nonneg_left sumBound (pow_pos ratePositive level).le).trans_eq (by ring)

theorem exists_xiHarmonic_two_endpoint_cell_cutoffs (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
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
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair
    ∃ normConstant energyConstant : ℝ, 0 < normConstant ∧ 0 < energyConstant ∧
      ∀ level (selectedEdge : XiEdge system.toRuleData level),
        ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ),
          (∀ address : XiEdgeAddress system, xiAddressEdge system level address = selectedEdge →
            extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
              distanceGreaterThanOne metricEigenpair address) = 1) ∧
          (∀ address : XiEdgeAddress system,
            xiAddressStarWeight system level (XiTail system level selectedEdge) address = 0 →
            xiAddressStarWeight system level (XiHead system level selectedEdge) address = 0 →
            extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
              distanceGreaterThanOne metricEigenpair address) = 0) ∧
          (∀ point, 0 ≤ extension point ∧ extension point ≤ 1) ∧
          ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
            metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact extension)‖ ^ 2 ≤
              normConstant * ((xiVertexIncidenceCount system level (XiTail system level selectedEdge) : ℝ) +
                (xiVertexIncidenceCount system level (XiHead system level selectedEdge) : ℝ)) / mass.rate ^ level ∧
          xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) ≠ ⊤ ∧
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair)).toReal ≤
                energyConstant * ((xiVertexIncidenceCount system level (XiTail system level selectedEdge) : ℝ) +
                  (xiVertexIncidenceCount system level (XiHead system level selectedEdge) : ℝ)) * resistanceRate ^ level := by
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
    profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
      distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus
    profilesMinimal contractionFactor profilesOscillation
  obtain ⟨_, upper, _, upperPositive, starMassBound⟩ := exists_xiAddressStarWeight_mass_comparison system mass
  have energyConstantPositive : 0 < ∑ colour, (resistanceVector colour)⁻¹ :=
    (inv_pos.mpr (vectorPositive system.initCol)).trans_le
      (Finset.single_le_sum (fun colour _ => (inv_pos.mpr (vectorPositive colour)).le) (Finset.mem_univ _))
  refine ⟨upper, ∑ colour, (resistanceVector colour)⁻¹, upperPositive, energyConstantPositive, ?_⟩
  intro level selectedEdge
  let values := xiTwoEndpointBoundary system level (XiTail system level selectedEdge) (XiHead system level selectedEdge)
  obtain ⟨extension, extensionAgreement⟩ := exists_xiContinuousHarmonic_of_step_contraction system
    rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive
    factorStrict stepContraction level values
  have extensionValues (offset : ℕ) (vertex : XiVtx system (level + offset)) :
      extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair (level + offset) vertex) =
          xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair level values offset vertex :=
    (extensionAgreement (xiVertexEmbedding system (level + offset) vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive renormalizationEigenpair level values offset vertex)
  have ranges (address : XiEdgeAddress system) := xiContinuousHarmonic_address_endpoint_range system rulesConnected
    lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair level values extension extensionAgreement address
  have addressBounds (address : XiEdgeAddress system) :
      0 ≤ extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ∧
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ≤ 1 :=
    ⟨(le_min (xiTwoEndpointBoundary_bounds system level _ _ _).1
      (xiTwoEndpointBoundary_bounds system level _ _ _).1).trans (ranges address).1,
      (ranges address).2.trans (max_le (xiTwoEndpointBoundary_bounds system level _ _ _).2
        (xiTwoEndpointBoundary_bounds system level _ _ _).2)⟩
  have globalBounds : ∀ point, 0 ≤ extension point ∧ extension point ≤ 1 := by
    have boundsClosed : IsClosed {point | 0 ≤ extension point ∧ extension point ≤ 1} :=
      (isClosed_le continuous_const extension.continuous).inter (isClosed_le extension.continuous continuous_const)
    have closureIncluded := closure_minimal
      (show Set.range (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair) ⊆ {point | 0 ≤ extension point ∧ extension point ≤ 1} from by
        rintro point ⟨address, rfl⟩
        exact addressBounds address) boundsClosed
    rw [(xiAddressLimit_denseRange system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass).closure_range] at closureIncluded
    exact fun point => closureIncluded (Set.mem_univ point)
  have onCell (address : XiEdgeAddress system) (cell : xiAddressEdge system level address = selectedEdge) :
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) = 1 := by
    have range := ranges address
    simp only [values, xiTwoEndpointBoundary, cell, eq_self, true_or, or_true,
      if_true, min_self, max_self] at range
    exact le_antisymm range.2 range.1
  have outside (address : XiEdgeAddress system)
      (firstZero : xiAddressStarWeight system level (XiTail system level selectedEdge) address = 0)
      (secondZero : xiAddressStarWeight system level (XiHead system level selectedEdge) address = 0) :
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) = 0 := by
    have range := ranges address
    unfold xiAddressStarWeight xiEdgeStarMultiplicity at firstZero secondZero
    simp only [values, xiTwoEndpointBoundary] at range
    split_ifs at firstZero secondZero range <;> simp_all
    all_goals exact le_antisymm range.2 range.1
  have addressSquareBound (address : XiEdgeAddress system) :
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ^ 2 ≤
          xiAddressStarWeight system level (XiTail system level selectedEdge) address +
            xiAddressStarWeight system level (XiHead system level selectedEdge) address := by
    have bounds := addressBounds address
    have atMostOne : extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ^ 2 ≤ 1 := by nlinarith [mul_nonneg bounds.1 (sub_nonneg.mpr bounds.2)]
    by_cases bothZero : xiAddressStarWeight system level (XiTail system level selectedEdge) address = 0 ∧
        xiAddressStarWeight system level (XiHead system level selectedEdge) address = 0
    · rw [outside address bothZero.1 bothZero.2, bothZero.1, bothZero.2]
      norm_num
    · apply atMostOne.trans
      unfold xiAddressStarWeight xiEdgeStarMultiplicity at bothZero ⊢
      split_ifs at * <;> norm_num at *
  have energyIdentity := xiContinuousHarmonic_extended_energy system rulesConnected lengths lengthsPositive
    distanceRate (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair level values extension extensionValues
  refine ⟨extension, onCell, outside, globalBounds, ?_, ?_, ?_⟩
  · rw [xiContinuous_L2_norm_sq_address_integral]
    have starIntegrable (center : XiVtx system level) : Integrable (xiAddressStarWeight system level center) mass.addressMeasure :=
      (show Integrable (xiEdgeStarMultiplicity system level center)
        (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
          (measurable_xiAddressEdge system level)
    have integralBound := integral_mono
      (xiContinuous_address_integrable system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair mass extension).2
      ((starIntegrable _).add (starIntegrable _)) (fun address => by
        simpa only [Pi.add_apply] using addressSquareBound address)
    have sumIntegral := integral_add (starIntegrable (XiTail system level selectedEdge))
      (starIntegrable (XiHead system level selectedEdge))
    simp only [Pi.add_apply] at sumIntegral integralBound
    rw [sumIntegral] at integralBound
    exact integralBound.trans ((add_le_add (starMassBound level (XiTail system level selectedEdge)).2
      (starMassBound level (XiHead system level selectedEdge)).2).trans_eq (by ring))
  · rw [energyIdentity]
    exact ENNReal.ofReal_ne_top
  · rw [energyIdentity, ENNReal.toReal_ofReal (FiniteNetwork.energy_nonneg _ _)]
    exact xiTwoEndpointBoundary_finite_energy_bound system resistanceRate ratePositive resistanceVector vectorPositive
      level (XiTail system level selectedEdge) (XiHead system level selectedEdge)

end
end EIGS

#print axioms EIGS.xiTwoEndpointBoundary_bounds
#print axioms EIGS.xiTwoEndpointBoundary_edge_square_le
#print axioms EIGS.xiTwoEndpointBoundary_finite_energy_bound
#print axioms EIGS.exists_xiHarmonic_two_endpoint_cell_cutoffs
