import RequestProject.Section31.EIGSAddressEndpointCollar
import RequestProject.Section31.LogarithmicCollarSchedule
import RequestProject.Section31.EIGSAnalyticTimeScale
import RequestProject.Section2DegreeMassGap

/-! The original rule assumptions and primitive-degree standing condition
internally supply a logarithmic collar schedule with summable probabilities.
No collar-probability or almost-everywhere avoidance hypothesis is supplied.
This result does not yet assert a heat-kernel lower bound. Candidate source. -/

namespace EIGS
open MeasureTheory Filter
open scoped Topology ENNReal
noncomputable section
set_option maxHeartbeats 3000000
variable {K : ℕ}

theorem xiAddressEndpointCollar_logarithmic_probability_sum_finite (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (coarse : ℕ → ℕ) (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    (∑' index : ℕ, mass.addressMeasure (xiAddressEndpointCollar system (coarse index)
      (Nat.ceil (width * Real.log (index + 2 : ℝ))))) ≠ ∞ := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  obtain ⟨_, _, degreePositive, _, _⟩ :=
    primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree
  have degreeMass : finiteRealMatrixSpectralRadius (degreeMatrix system) < mass.rate := by
    rw [XiMassParameters.rate_eq_spectralRadius system mass]
    exact degree_spectralRadius_lt_mass_of_primitive system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive primitiveDegree
  obtain ⟨coefficient, coefficientPositive, probabilityBound⟩ :=
    exists_xiAddressEndpointCollar_mass_bound system mass primitiveDegree
  have summable := summable_logarithmic_ceiling_geometric
    (finiteRealMatrixSpectralRadius (degreeMatrix system) / mass.rate) width
    (div_pos degreePositive mass.rate_positive) ((div_lt_one mass.rate_positive).mpr degreeMass)
    (by simpa only [inv_div] using widthLarge)
  apply ne_top_of_le_ne_top (summable.mul_left coefficient).tsum_ofReal_ne_top
  exact ENNReal.tsum_le_tsum fun index =>
    probabilityBound (coarse index) (Nat.ceil (width * Real.log (index + 2 : ℝ)))

theorem xiAddressEndpointCollar_logarithmic_ae_avoidance (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (coarse : ℕ → ℕ) (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index in atTop,
      address ∉ xiAddressEndpointCollar system (coarse index)
        (Nat.ceil (width * Real.log (index + 2 : ℝ))) :=
  ae_eventually_notMem (xiAddressEndpointCollar_logarithmic_probability_sum_finite system rulesConnected
    rulesLoopless plantingNonadjacent distancePositive mass primitiveDegree coarse width widthLarge)

theorem xiAddressEndpointCollar_all_rational_logarithmic_ae_avoidance (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (coarse : ℕ → ℕ) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ width : ℚ,
      1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < (width : ℝ) →
      ∀ᶠ index in atTop, address ∉ xiAddressEndpointCollar system (coarse index)
        (Nat.ceil ((width : ℝ) * Real.log (index + 2 : ℝ))) := by
  apply ae_all_iff.mpr
  intro width
  by_cases large : 1 / Real.log
      (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < (width : ℝ)
  · exact (xiAddressEndpointCollar_logarithmic_ae_avoidance system rulesConnected rulesLoopless
      plantingNonadjacent distancePositive mass primitiveDegree coarse (width : ℝ) large).mono
        (fun _ avoids _ => avoids)
  · exact Eventually.of_forall (fun _ impossible => (large impossible).elim)

theorem xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (mass : XiMassParameters system) (primitiveDegree : (degreeMatrix system).IsPrimitive)
    (width : ℝ)
    (widthLarge : 1 / Real.log (mass.rate / finiteRealMatrixSpectralRadius (degreeMatrix system)) < width) :
    ∀ᵐ address ∂mass.addressMeasure, ∀ᶠ index : ℕ in atTop,
      (index - Nat.ceil (width * Real.log (index + 2 : ℝ))) +
          Nat.ceil (width * Real.log (index + 2 : ℝ)) = index ∧
      address ∉ xiAddressEndpointCollar system (index - Nat.ceil (width * Real.log (index + 2 : ℝ)))
        (Nat.ceil (width * Real.log (index + 2 : ℝ))) := by
  filter_upwards [xiAddressEndpointCollar_logarithmic_ae_avoidance system rulesConnected rulesLoopless
    plantingNonadjacent distancePositive mass primitiveDegree
    (fun index : ℕ => index - Nat.ceil (width * Real.log (index + 2 : ℝ))) width widthLarge] with address avoids
  filter_upwards [avoids, eventually_logarithmic_ceiling_le_index width] with index avoids atMostIndex
  exact ⟨Nat.sub_add_cancel atMostIndex, avoids⟩

end
end EIGS

#print axioms EIGS.xiAddressEndpointCollar_logarithmic_ae_avoidance
#print axioms EIGS.xiAddressEndpointCollar_logarithmic_probability_sum_finite
#print axioms EIGS.xiAddressEndpointCollar_all_rational_logarithmic_ae_avoidance
#print axioms EIGS.xiAddressEndpointCollar_logarithmic_original_level_ae_avoidance
