import RequestProject.Section31.EIGSLogarithmicEndpointCollar
import RequestProject.Section31.EIGSPositiveDegreeAddressCollar
import RequestProject.Section31.EIGSPositiveDegreeSpectralGaps

/-! Actual collar/incidence estimates from a positive normalized degree eigenpair.
The original address measure and oriented rule graphs are unchanged. Candidate. -/

namespace EIGS
open MeasureTheory Filter Matrix
open scoped Classical BigOperators Topology ENNReal
noncomputable section
set_option maxHeartbeats 5000000
variable {K : ℕ}

theorem xiAddressEndpointCollar_logarithmic_probability_sum_finite_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (degreeData : XiPositiveDegreeSpectralData system)
    (coarse : ℕ → ℕ) (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    (∑' index : ℕ, mass.addressMeasure (xiAddressEndpointCollar system (coarse index)
      (Nat.ceil (width * Real.log (index + 2 : ℝ))))) ≠ ∞ := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have degreePositive := zero_lt_one.trans degreeData.rate_gt_one
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_positive_degree_data system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive degreeData
  obtain ⟨coefficient, coefficientPositive, probabilityBound⟩ :=
    exists_xiAddressEndpointCollar_mass_bound_of_positive_degree_data system mass degreeData
  have summable := summable_logarithmic_ceiling_geometric
    (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) width
    (div_pos degreePositive mass.rate_positive) ((div_lt_one mass.rate_positive).mpr degreeMass)
    (by simpa only [inv_div] using widthLarge)
  apply ne_top_of_le_ne_top (summable.mul_left coefficient).tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum fun index =>
    probabilityBound (coarse index) (Nat.ceil (width * Real.log (index + 2 : ℝ)))

theorem xiAddressEndpointCollar_logarithmic_ae_avoidance_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (degreeData : XiPositiveDegreeSpectralData system)
    (coarse : ℕ → ℕ) (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index in atTop,
      address ∉ xiAddressEndpointCollar system (coarse index)
        (Nat.ceil (width * Real.log (index + 2 : ℝ))) :=
  ae_eventually_notMem (xiAddressEndpointCollar_logarithmic_probability_sum_finite_of_positive_degree_data system rulesConnected
    rulesLoopless plantingNonadjacent distancePositive mass degreeData coarse width widthLarge)

theorem xiAddressEndpointCollar_all_rational_logarithmic_ae_avoidance_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (degreeData : XiPositiveDegreeSpectralData system)
    (coarse : ℕ → ℕ) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ width : ℚ,
      1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < (width : ℝ) →
      ∀ᶠ index in atTop, address ∉ xiAddressEndpointCollar system (coarse index)
        (Nat.ceil ((width : ℝ) * Real.log (index + 2 : ℝ))) := by
  apply ae_all_iff.mpr
  intro width
  by_cases large : 1 / Real.log
      (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < (width : ℝ)
  · exact (xiAddressEndpointCollar_logarithmic_ae_avoidance_of_positive_degree_data system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive mass degreeData coarse (width : ℝ) large).mono
        (fun _ avoids _ => avoids)
  · exact Eventually.of_forall (fun _ impossible => (large impossible).elim)

theorem xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (degreeData : XiPositiveDegreeSpectralData system)
    (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index : ℕ in atTop,
      (index - Nat.ceil (width * Real.log (index + 2 : ℝ))) +
          Nat.ceil (width * Real.log (index + 2 : ℝ)) = index ∧
      address ∉ xiAddressEndpointCollar system (index - Nat.ceil (width * Real.log (index + 2 : ℝ)))
        (Nat.ceil (width * Real.log (index + 2 : ℝ))) := by
  filter_upwards [xiAddressEndpointCollar_logarithmic_ae_avoidance_of_positive_degree_data system rulesConnected rulesLoopless
    plantingNonadjacent distancePositive mass degreeData
    (fun index : ℕ => index - Nat.ceil (width * Real.log (index + 2 : ℝ))) width widthLarge] with address avoids
  filter_upwards [avoids, eventually_logarithmic_ceiling_le_index width] with index avoids atMostIndex
  exact ⟨Nat.sub_add_cancel atMostIndex, avoids⟩

end
end EIGS

#print axioms EIGS.xiAddressEndpointCollar_logarithmic_probability_sum_finite_of_positive_degree_data
#print axioms EIGS.xiAddressEndpointCollar_logarithmic_ae_avoidance_of_positive_degree_data
#print axioms EIGS.xiAddressEndpointCollar_all_rational_logarithmic_ae_avoidance_of_positive_degree_data
#print axioms EIGS.xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance_of_positive_degree_data

