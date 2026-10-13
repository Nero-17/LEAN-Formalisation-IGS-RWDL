import RequestProject.Section31.EIGSOriginalDiameterGrowth
import RequestProject.Section2LocalScaleLimits
import RequestProject.Section2FixedRadiusResistance

/-! The paper's fixed-radius local dimensions at every finitely born vertex,
using the actual original-unit diameter and actual ball counts/resistance. -/

namespace EIGS

open Filter Topology
open scoped Classical

variable {K : ℕ} (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (planting_nonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distance_positive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))

include loopless unique planting_nonadjacent distance_positive

theorem xiOriginalDiameter_birth_spectral_growth (initial_level : ℕ) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ age in atTop,
      lower * (system.distanceSpectralRadius connected) ^ age ≤
        xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one (initial_level + age) ∧
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one (initial_level + age) ≤
        upper * (system.distanceSpectralRadius connected) ^ age := by
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ :=
    xiOriginalDiameter_spectral_growth system connected loopless unique planting_nonadjacent distance_positive
  have rate_positive : 0 < system.distanceSpectralRadius connected :=
    (by norm_num : (0 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique planting_nonadjacent distance_positive)
  refine ⟨lower * (system.distanceSpectralRadius connected) ^ initial_level,
    upper * (system.distanceSpectralRadius connected) ^ initial_level,
    by positivity, by positivity, ?_⟩
  have shifted : Tendsto (fun age : ℕ => initial_level + age) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat initial_level
  filter_upwards [shifted.eventually bounds] with age bound
  simpa only [pow_add, mul_assoc] using bound

theorem xiSimpleGraph_fixed_radius_local_mass_dimension_limit
    (primitive_degree : (degreeMatrix system).IsPrimitive)
    (initial_level : ℕ) (vertex : XiVtx system initial_level)
    (radius : ℝ) (radius_gt_one : 1 < radius) :
    Tendsto (fun age =>
      Real.log ((finiteGraphBall (XiSimpleGraph system (initial_level + age))
        (xiForward system initial_level age vertex) radius).card : ℝ) /
      (-Real.log (radius / xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one (initial_level + age)))) atTop
      (nhds (Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) /
        Real.log (system.distanceSpectralRadius connected))) := by
  have radius_positive := zero_lt_one.trans radius_gt_one
  obtain ⟨buffer, birth_bounds⟩ := xiSimpleGraph_mesoscopic_ball_birth_spectral_volume system
    connected loopless unique planting_nonadjacent distance_positive primitive_degree
    radius radius radius_positive radius_positive
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ := birth_bounds initial_level vertex
  obtain ⟨diameter_lower, diameter_upper, diameter_lower_positive, diameter_upper_positive,
    diameter_bounds⟩ := xiOriginalDiameter_birth_spectral_growth system connected loopless unique
      planting_nonadjacent distance_positive initial_level
  have rate_gt_one : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique planting_nonadjacent distance_positive)
  apply local_logarithmic_dimension_limit
    (degree_spectral_growth_from_primitive_rules system connected primitive_degree).1 rate_gt_one
    lower_positive upper_positive diameter_lower_positive diameter_upper_positive radius_positive
    _ diameter_bounds
  filter_upwards [eventually_ge_atTop buffer] with age age_large
  have actual := bounds age 0 radius age_large radius_gt_one (by simp) (by simp)
  simpa only [Nat.add_zero, pow_zero, mul_one] using actual

theorem xiSimpleGraph_fixed_radius_local_resistance_dimension_limit
    (primitive_degree : (degreeMatrix system).IsPrimitive)
    (initial_level : ℕ) (vertex : XiVtx system initial_level)
    (radius : ℝ) (radius_gt_one : 1 < radius) :
    Tendsto (fun age =>
      Real.log (effResToBoundary (XiSimpleGraph system (initial_level + age))
        (finiteGraphBall (XiSimpleGraph system (initial_level + age))
          (xiForward system initial_level age vertex) radius)
        (xiForward system initial_level age vertex)) /
      (-Real.log (radius / xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
        (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one (initial_level + age)))) atTop
      (nhds (-Real.log (finiteRealMatrixSpectralRadius (degreeMatrix system)) /
        Real.log (system.distanceSpectralRadius connected))) := by
  have radius_positive := zero_lt_one.trans radius_gt_one
  obtain ⟨threshold, birth_bounds⟩ := xiSimpleGraph_fixed_radius_resistance_spectral_bounds system
    connected loopless unique planting_nonadjacent distance_positive primitive_degree radius radius_gt_one
  obtain ⟨lower, upper, lower_positive, upper_positive, bounds⟩ := birth_bounds initial_level vertex
  obtain ⟨diameter_lower, diameter_upper, diameter_lower_positive, diameter_upper_positive,
    diameter_bounds⟩ := xiOriginalDiameter_birth_spectral_growth system connected loopless unique
      planting_nonadjacent distance_positive initial_level
  have rate_gt_one : 1 < system.distanceSpectralRadius connected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius connected unique planting_nonadjacent distance_positive)
  have resistance_bounds : ∀ᶠ age in atTop,
      lower * (finiteRealMatrixSpectralRadius (degreeMatrix system))⁻¹ ^ age ≤
        effResToBoundary (XiSimpleGraph system (initial_level + age))
          (finiteGraphBall (XiSimpleGraph system (initial_level + age))
            (xiForward system initial_level age vertex) radius) (xiForward system initial_level age vertex) ∧
      effResToBoundary (XiSimpleGraph system (initial_level + age))
          (finiteGraphBall (XiSimpleGraph system (initial_level + age))
            (xiForward system initial_level age vertex) radius) (xiForward system initial_level age vertex) ≤
        upper * (finiteRealMatrixSpectralRadius (degreeMatrix system))⁻¹ ^ age := by
    filter_upwards [eventually_ge_atTop threshold] with age age_large
    exact (bounds age age_large).2
  simpa only [Real.log_inv] using local_logarithmic_dimension_limit
    (inv_pos.mpr (degree_spectral_growth_from_primitive_rules system connected primitive_degree).1)
    rate_gt_one lower_positive upper_positive diameter_lower_positive diameter_upper_positive radius_positive
    resistance_bounds diameter_bounds

end EIGS

#print axioms EIGS.xiOriginalDiameter_birth_spectral_growth
#print axioms EIGS.xiSimpleGraph_fixed_radius_local_mass_dimension_limit
#print axioms EIGS.xiSimpleGraph_fixed_radius_local_resistance_dimension_limit
