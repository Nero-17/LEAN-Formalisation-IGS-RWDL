import RequestProject.Section31.FiniteGraphEccentricity
import RequestProject.Section31.EIGSOriginalDiameterGrowth
import RequestProject.Section2WeightedMetric

/-! Exact eccentricities of the original unweighted graphs have the same
geometric growth as their original diameters. The constants are constructed
from the verified diameter limit, uniformly in every finite-level center. -/

namespace EIGS

open Filter Topology Metric Set
open scoped Classical
noncomputable section
variable {K : ℕ}

theorem xiOriginalEccentricity_diameter_bounds (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (level : ℕ) (center : XiVtx system level) :
    finiteGraphEccentricity (XiSimpleGraph system level) center ≤
        xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ∧
      xiFiniteLevelDiameter system connected (fun _ => (1 : ℝ)⁻¹)
          (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level ≤
        2 * finiteGraphEccentricity (XiSimpleGraph system level) center := by
  letI := xiLevelMetricSpace system connected (fun _ => (1 : ℝ)⁻¹)
    (fun _ => inv_pos.mpr zero_lt_one) 1 zero_lt_one level
  have distanceEquality (first last : XiVtx system level) :
      dist first last = ((XiSimpleGraph system level).dist first last : ℝ) := by
    change (1 : ℝ)⁻¹ ^ level * (XiNetwork system level).weightedDistance
      (fun _ => (1 : ℝ)⁻¹) first last = _
    simp only [inv_one, one_pow, one_mul]
    exact (XiNetwork system level).weightedDistance_unit_eq_graphDistance
      (xiSimpleGraph_connected system connected level)
      (xiNetwork_loopless system connected loopless level) first last
  constructor
  · change Finset.univ.sup' _ (fun vertex => ((XiSimpleGraph system level).dist center vertex : ℝ)) ≤
      Metric.diam (univ : Set (XiVtx system level))
    apply Finset.sup'_le
    intro vertex _
    rw [← distanceEquality]
    exact Metric.dist_le_diam_of_mem (Set.toFinite (univ : Set (XiVtx system level))).isBounded
      (mem_univ center) (mem_univ vertex)
  · change Metric.diam (univ : Set (XiVtx system level)) ≤ _
    apply Metric.diam_le_of_forall_dist_le
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (finiteGraphEccentricity_nonnegative (XiSimpleGraph system level) center))
    intro first _ last _
    rw [distanceEquality]
    exact graphDistance_le_twice_finiteGraphEccentricity (XiSimpleGraph system level)
      (xiSimpleGraph_connected system connected level) center first last

theorem xiOriginalEccentricity_spectral_growth (system : EIGSData K)
    (connected : ∀ colour, (ruleSG system colour).Connected)
    (loopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (unique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ level in atTop,
      ∀ center : XiVtx system level,
        lower * (system.distanceSpectralRadius connected) ^ level ≤
          finiteGraphEccentricity (XiSimpleGraph system level) center ∧
        finiteGraphEccentricity (XiSimpleGraph system level) center ≤
          upper * (system.distanceSpectralRadius connected) ^ level := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, growth⟩ :=
    xiOriginalDiameter_spectral_growth system connected loopless unique plantingNonadjacent distancePositive
  refine ⟨lower / 2, upper, by positivity, upperPositive, ?_⟩
  filter_upwards [growth] with level diameterBound
  intro center
  have comparison := xiOriginalEccentricity_diameter_bounds system connected loopless level center
  constructor
  · linarith [diameterBound.1, comparison.2]
  · exact comparison.1.trans diameterBound.2

end
end EIGS

#print axioms EIGS.xiOriginalEccentricity_diameter_bounds
#print axioms EIGS.xiOriginalEccentricity_spectral_growth
