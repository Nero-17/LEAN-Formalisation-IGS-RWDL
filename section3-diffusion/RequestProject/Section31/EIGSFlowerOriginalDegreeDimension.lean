import RequestProject.Section31.EIGSPrimitiveOriginalDegreeDimension
import RequestProject.Section31.EIGSFlowerCanonicalRates
import RequestProject.Section31.EIGSFlowerDegreePrimitive
import RequestProject.Section31.EIGSFlowerDegreeSpectrum

/-! Original degree-distribution dimension for paper Example ex:uvDHL.
This specializes the actual stationary degree/maxDegree and occupied
point-count theorem, not a scalar mass/degree ratio. Candidate source;
compile only after the general original-degree theorem is accepted. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem flowerSystem_original_degree_dimension (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    ∃ weights : Fin 1 ⊕ Fin 1 → ℝ, ∃ coefficient normalizer : ℝ,
      (∀ vertex, 0 < xiStationaryDegreeFromAmplitudes (flowerSystem branches segments)
        weights coefficient (branches : ℝ) normalizer vertex ∧
        xiStationaryDegreeFromAmplitudes (flowerSystem branches segments)
          weights coefficient (branches : ℝ) normalizer vertex ≤ 1) ∧
      (∀ vertex, Tendsto (fun level => xiActualMaxNormalizedDegree (flowerSystem branches segments) level vertex)
        atTop (𝓝 (xiStationaryDegreeFromAmplitudes (flowerSystem branches segments)
          weights coefficient (branches : ℝ) normalizer vertex))) ∧
      (∀ value : ℝ, Finite {vertex : XiVertexUnion (flowerSystem branches segments) //
        xiStationaryDegreeFromAmplitudes (flowerSystem branches segments)
          weights coefficient (branches : ℝ) normalizer vertex = value}) ∧
      0 < 1 + Real.log (segments : ℝ) / Real.log (branches : ℝ) ∧
      Tendsto (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity (flowerSystem branches segments)
        weights coefficient (branches : ℝ) normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport (flowerSystem branches segments)
          weights coefficient (branches : ℝ) normalizer] (0 : ℝ))
        (𝓝 (1 + Real.log (segments : ℝ) / Real.log (branches : ℝ))) ∧
      NeBot (𝓝[xiStationaryOccupiedDegreeSupport (flowerSystem branches segments)
        weights coefficient (branches : ℝ) normalizer] (0 : ℝ)) ∧
      Filter.limsup (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity (flowerSystem branches segments)
        weights coefficient (branches : ℝ) normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport (flowerSystem branches segments)
          weights coefficient (branches : ℝ) normalizer] (0 : ℝ)) =
        1 + Real.log (segments : ℝ) / Real.log (branches : ℝ) := by
  have actual := primitive_rules_original_degree_dimension (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    (flowerSystem_degreeMatrix_primitive branches segments branchesAtLeastTwo segmentsAtLeastTwo)
  have branchGreaterThanOne : (1 : ℝ) < branches := by
    exact_mod_cast (show 1 < branches by omega)
  have dimensionIdentity : Real.log ((branches : ℝ) * (segments : ℝ)) / Real.log (branches : ℝ) =
      1 + Real.log (segments : ℝ) / Real.log (branches : ℝ) := by
    rw [Real.log_mul (Nat.cast_ne_zero.mpr (show branches ≠ 0 by omega))
      (Nat.cast_ne_zero.mpr (show segments ≠ 0 by omega)), add_div,
      div_self (Real.log_pos branchGreaterThanOne).ne']
  simpa only [flowerSystem_degreeSpectralRadius branches segments (by omega) (by omega),
    flowerSystem_massSpectralRadius, dimensionIdentity] using actual

end
end EIGS

#print axioms EIGS.flowerSystem_original_degree_dimension
