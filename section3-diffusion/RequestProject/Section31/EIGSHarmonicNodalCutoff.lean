import RequestProject.Section31.EIGSAddressIncidentStar
import RequestProject.Section31.EIGSAddressCellAverageEnergy
import RequestProject.Section31.EIGSHarmonicBoundaryL2
import RequestProject.Section31.EIGSL2QuadraticEnergy
import RequestProject.Section31.QuadraticEnergyCompletion

/-! Actual nodal harmonic cutoffs. A finite vertex spike is extended by the
constructed harmonic extension, not by an assumed local profile. Endpoint
convexity gives its address-star support and its squared L2 mass. The finite
weighted trace gives the incidence/resistance energy bound. No primitive
degree hypothesis or lower bound on the resistance rate beyond positivity
is required. -/

namespace EIGS

open IGS.Sec31 MeasureTheory Filter Topology Set
open scoped Classical BigOperators BoundedContinuousFunction ENNReal
noncomputable section
set_option maxHeartbeats 6000000
variable {K : ℕ}

def xiNodalSpike (system : EIGSData K) (level : ℕ) (center : XiVtx system level)
    (vertex : XiVtx system level) : ℝ := if vertex = center then 1 else 0

theorem xiNodalSpike_bounds (system : EIGSData K) (level : ℕ)
    (center vertex : XiVtx system level) :
    0 ≤ xiNodalSpike system level center vertex ∧ xiNodalSpike system level center vertex ≤ 1 := by
  unfold xiNodalSpike
  split_ifs <;> norm_num

theorem xiNodalSpike_edge_square_le_multiplicity (system : EIGSData K) (level : ℕ)
    (center : XiVtx system level) (edge : XiEdge system.toRuleData level) :
    (xiNodalSpike system level center (XiTail system level edge) -
      xiNodalSpike system level center (XiHead system level edge)) ^ 2 ≤
        xiEdgeStarMultiplicity system level center edge := by
  unfold xiNodalSpike xiEdgeStarMultiplicity
  split_ifs <;> norm_num

theorem xiNodalSpike_finite_energy_bound (system : EIGSData K)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (level : ℕ) (center : XiVtx system level) :
    (xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy
      (xiNodalSpike system level center) ≤
        (∑ colour, (resistanceVector colour)⁻¹) *
          (xiVertexIncidenceCount system level center : ℝ) * resistanceRate ^ level := by
  have inverseBound (colour : Fin K) :
      (resistanceVector colour)⁻¹ ≤ ∑ index, (resistanceVector index)⁻¹ :=
    Finset.single_le_sum (fun index _ => (inv_pos.mpr (vectorPositive index)).le) (Finset.mem_univ colour)
  rw [xiWeightedFiniteNetwork_energy_eq_potential]
  change resistanceRate ^ level *
    (∑ edge, (resistanceVector (XiCol system.toRuleData level edge))⁻¹ *
      (xiNodalSpike system level center (XiTail system level edge) -
        xiNodalSpike system level center (XiHead system level edge)) ^ 2) ≤ _
  have sumBound : (∑ edge : XiEdge system.toRuleData level,
      (resistanceVector (XiCol system.toRuleData level edge))⁻¹ *
        (xiNodalSpike system level center (XiTail system level edge) -
          xiNodalSpike system level center (XiHead system level edge)) ^ 2) ≤
      (∑ colour, (resistanceVector colour)⁻¹) * (xiVertexIncidenceCount system level center : ℝ) := by
    rw [← xiEdgeStarMultiplicity_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro edge _
    exact (mul_le_mul_of_nonneg_left (xiNodalSpike_edge_square_le_multiplicity system level center edge)
      (inv_pos.mpr (vectorPositive _)).le).trans
        (mul_le_mul_of_nonneg_right (inverseBound _) (xiEdgeStarMultiplicity_bounds system level center edge).1)
  exact (mul_le_mul_of_nonneg_left sumBound (pow_pos ratePositive level).le).trans_eq (by ring)

section ActualHarmonicCutoff

variable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)

local instance nodalCutoffCompletionCompactSpace : CompactSpace
    (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) :=
  xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair

theorem exists_xiHarmonic_nodal_cutoffs
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour)) :
    letI nodalCutoffStatementCompactSpace : CompactSpace
        (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) :=
      xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair
    ∃ normConstant energyConstant : ℝ, 0 < normConstant ∧ 0 < energyConstant ∧
      ∀ level (center : XiVtx system level),
        ∃ extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ),
          (∀ vertex, extension (xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive
            distanceRate (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair vertex) =
              xiHarmonicUnionExtension system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
                renormalizationEigenpair level (xiNodalSpike system level center) vertex) ∧
          (∀ vertex : XiVtx system level,
            extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair level vertex) =
                xiNodalSpike system level center vertex) ∧
          (∀ point, 0 ≤ extension point ∧ extension point ≤ 1) ∧
          (∀ address : XiEdgeAddress system, xiAddressStarWeight system level center address = 0 →
            extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
              distanceGreaterThanOne metricEigenpair address) = 0) ∧
          ‖(xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne
            metricEigenpair mass).embed (BoundedContinuousFunction.mkOfCompact extension)‖ ^ 2 ≤
              normConstant * (xiVertexIncidenceCount system level center : ℝ) / mass.rate ^ level ∧
          xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) =
                ENNReal.ofReal ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector
                  vectorPositive level).energy (xiNodalSpike system level center)) ∧
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair)).toReal ≤
                energyConstant * (xiVertexIncidenceCount system level center : ℝ) * resistanceRate ^ level := by
  letI nodalCutoffProofCompactSpace : CompactSpace
      (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) :=
    xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair
  dsimp only
  obtain ⟨profiles, contractionFactor, factorPositive, factorStrict, profilesPlus, profilesMinus,
    profilesMinimal, profilesOscillation⟩ := exists_rule_harmonic_profiles_strict_oscillation system rulesConnected
      distancePositive oneColourDistance resistanceVector vectorPositive
  have stepContraction := xiHarmonicStep_child_edge_contraction system rulesConnected resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair profiles profilesPlus profilesMinus
    profilesMinimal contractionFactor profilesOscillation
  obtain ⟨lower, upper, lowerPositive, upperPositive, starMassBound⟩ :=
    exists_xiAddressStarWeight_mass_comparison system mass
  have energyConstantPositive : 0 < ∑ colour, (resistanceVector colour)⁻¹ :=
    (inv_pos.mpr (vectorPositive system.initCol)).trans_le
      (Finset.single_le_sum (fun colour _ => (inv_pos.mpr (vectorPositive colour)).le) (Finset.mem_univ _))
  refine ⟨upper, ∑ colour, (resistanceVector colour)⁻¹, upperPositive, energyConstantPositive, ?_⟩
  intro level center
  obtain ⟨extension, extensionAgreement⟩ := exists_xiContinuousHarmonic_of_step_contraction system
    rulesConnected lengths lengthsPositive distanceRate distanceGreaterThanOne metricEigenpair resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair contractionFactor factorPositive
    factorStrict stepContraction level (xiNodalSpike system level center)
  have extensionValues (offset : ℕ) (vertex : XiVtx system (level + offset)) :
      extension (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair (level + offset) vertex) =
          xiHarmonicValues system rulesConnected resistanceRate ratePositive resistanceVector vectorPositive
            renormalizationEigenpair level (xiNodalSpike system level center) offset vertex :=
    (extensionAgreement (xiVertexEmbedding system (level + offset) vertex)).trans
      (xiHarmonicUnionExtension_values system rulesConnected resistanceRate ratePositive resistanceVector
        vectorPositive renormalizationEigenpair level (xiNodalSpike system level center) offset vertex)
  have addressRange (address : XiEdgeAddress system) :=
    xiContinuousHarmonic_address_endpoint_range system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive
      renormalizationEigenpair level (xiNodalSpike system level center) extension extensionAgreement address
  have addressBounds (address : XiEdgeAddress system) :
      0 ≤ extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ∧
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ≤ 1 :=
    ⟨(le_min (xiNodalSpike_bounds system level center _).1
        (xiNodalSpike_bounds system level center _).1).trans (addressRange address).1,
      (addressRange address).2.trans (max_le (xiNodalSpike_bounds system level center _).2
        (xiNodalSpike_bounds system level center _).2)⟩
  have globalBounds : ∀ point, 0 ≤ extension point ∧ extension point ≤ 1 := by
    have boundsClosed : IsClosed {point | 0 ≤ extension point ∧ extension point ≤ 1} :=
      (isClosed_le continuous_const extension.continuous).inter
        (isClosed_le extension.continuous continuous_const)
    have rangeIncluded : Set.range (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair) ⊆ {point | 0 ≤ extension point ∧ extension point ≤ 1} := by
      rintro point ⟨address, rfl⟩
      exact addressBounds address
    have closureIncluded := closure_minimal rangeIncluded boundsClosed
    rw [(xiAddressLimit_denseRange system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass).closure_range] at closureIncluded
    exact fun point => closureIncluded (Set.mem_univ point)
  have addressZero (address : XiEdgeAddress system)
      (outside : xiAddressStarWeight system level center address = 0) :
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) = 0 := by
    have ranges := addressRange address
    by_cases tail : XiTail system level (xiAddressEdge system level address) = center
    · by_cases head : XiHead system level (xiAddressEdge system level address) = center <;>
        simp [xiAddressStarWeight, xiEdgeStarMultiplicity, tail, head] at outside
    · by_cases head : XiHead system level (xiAddressEdge system level address) = center
      · simp [xiAddressStarWeight, xiEdgeStarMultiplicity, tail, head] at outside
      · simp only [xiNodalSpike, if_neg tail, if_neg head, min_self, max_self] at ranges
        exact le_antisymm ranges.2 ranges.1
  have addressSquareBound (address : XiEdgeAddress system) :
      extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ^ 2 ≤ xiAddressStarWeight system level center address := by
    have bounds := addressBounds address
    have squareAtMostOne : extension (xiAddressLimit system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair address) ^ 2 ≤ 1 := by
      nlinarith [bounds.1, bounds.2, mul_nonneg bounds.1 (sub_nonneg.mpr bounds.2)]
    by_cases tail : XiTail system level (xiAddressEdge system level address) = center
    · by_cases head : XiHead system level (xiAddressEdge system level address) = center
      · have weightTwo : xiAddressStarWeight system level center address = 2 := by
          simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, if_pos tail, if_pos head]
          norm_num
        rw [weightTwo]
        exact squareAtMostOne.trans (by norm_num)
      · have weightOne : xiAddressStarWeight system level center address = 1 := by
          simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, if_pos tail, if_neg head, add_zero]
        rw [weightOne]
        exact squareAtMostOne
    · by_cases head : XiHead system level (xiAddressEdge system level address) = center
      · simpa only [xiAddressStarWeight, xiEdgeStarMultiplicity, if_neg tail, if_pos head, zero_add] using squareAtMostOne
      · have outside : xiAddressStarWeight system level center address = 0 := by
          simp only [xiAddressStarWeight, xiEdgeStarMultiplicity, if_neg tail, if_neg head, zero_add]
        rw [addressZero address outside, outside]
        norm_num
  have energyIdentity := xiContinuousHarmonic_extended_energy system rulesConnected lengths lengthsPositive
    distanceRate (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair level (xiNodalSpike system level center)
    extension extensionValues
  refine ⟨extension, extensionAgreement, ?_, globalBounds, addressZero, ?_, energyIdentity, ?_⟩
  · intro vertex
    simpa only [Nat.add_zero, xiHarmonicValues] using extensionValues 0 vertex
  · rw [xiContinuous_L2_norm_sq_address_integral]
    have starIntegrable : Integrable (xiAddressStarWeight system level center) mass.addressMeasure :=
      (show Integrable (xiEdgeStarMultiplicity system level center)
        (mass.addressMeasure.map (xiAddressEdge system level)) from Integrable.of_finite).comp_measurable
          (measurable_xiAddressEdge system level)
    have integralBound := integral_mono
      (xiContinuous_address_integrable system rulesConnected lengths lengthsPositive distanceRate
        distanceGreaterThanOne metricEigenpair mass extension).2 starIntegrable addressSquareBound
    exact (integralBound.trans (starMassBound level center).2).trans_eq (by ring)
  · rw [energyIdentity, ENNReal.toReal_ofReal
      ((xiWeightedFiniteNetwork system resistanceRate ratePositive resistanceVector vectorPositive level).energy_nonneg _)]
    exact xiNodalSpike_finite_energy_bound system resistanceRate ratePositive resistanceVector vectorPositive level center

/-- The original finite-energy continuous representative is automatically in
the closed domain, with exactly its original energy. Applying this to the
constructed nodal cutoff transfers its numerical trace bound unchanged. -/
theorem xiContinuous_finite_energy_closedForm_eq
    (extension : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
      (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair, ℝ))
    (finiteEnergy : xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
      (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair) ≠ ⊤) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
      ∃ membership : xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
          distanceGreaterThanOne metricEigenpair mass extension ∈
            QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
        QuadraticEnergySpace.closedForm originalDomain originalForm nonnegative closable
          ⟨xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
            distanceGreaterThanOne metricEigenpair mass extension, membership⟩ =
          (xiExtendedWeightedEnergy system resistanceRate ratePositive resistanceVector vectorPositive
            (extension ∘ xiCompletionUnionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceGreaterThanOne) metricEigenpair)).toReal := by
  dsimp only
  intro closable
  have extensionFinite : extension ∈ xiContinuousFiniteEnergyDomain system rulesConnected lengths lengthsPositive
      distanceRate distanceGreaterThanOne metricEigenpair resistanceRate ratePositive resistanceVector vectorPositive :=
    (xiWeightedEnergyDomain_iff system resistanceRate ratePositive resistanceVector vectorPositive _).2 finiteEnergy
  let original := xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
    distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
      ⟨extension, extensionFinite⟩
  have membership := QuadraticEnergySpace.original_mem_closedDomain
    (xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive)
    (xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    (xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    original
  refine ⟨membership, ?_⟩
  have closedFormIdentity := QuadraticEnergySpace.closedForm_extends
    (xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive)
    (xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    (xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair)
    closable original
  exact closedFormIdentity.trans (xiContinuousLpEnergyQuadraticForm_of_continuous system rulesConnected lengths lengthsPositive
    distanceRate distanceGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair ⟨extension, extensionFinite⟩)

end ActualHarmonicCutoff
end
end EIGS

#print axioms EIGS.xiNodalSpike_finite_energy_bound
#print axioms EIGS.exists_xiHarmonic_nodal_cutoffs
#print axioms EIGS.xiContinuous_finite_energy_closedForm_eq
