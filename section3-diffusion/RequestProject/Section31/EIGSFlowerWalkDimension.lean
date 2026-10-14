import RequestProject.Section31.EIGSFlowerCanonicalRates
import RequestProject.Section2WalkDimension
import RequestProject.Section22

/-! The actual flower's canonical parameter formulas and the actual
discrete mean-exit logarithmic limit. The scalar identities alone are
not substituted for the random-walk limit. -/

namespace EIGS
open Filter Topology
noncomputable section
open scoped Classical

theorem flowerSystem_dimension_formulas (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    Real.log (realMatrixSpectralRadius (massMatrixR (flowerSystem branches segments).toRuleData)) /
      Real.log ((flowerSystem branches segments).distanceSpectralRadius
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) =
          1 + Real.log (branches : ℝ) / Real.log (segments : ℝ) ∧
    Real.log ((flowerSystem branches segments).resistanceSpectralRadius
      (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
      (flowerSystem_distancePositive branches segments)) /
      Real.log ((flowerSystem branches segments).distanceSpectralRadius
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) =
          1 - Real.log (branches : ℝ) / Real.log (segments : ℝ) ∧
    Real.log (realMatrixSpectralRadius (massMatrixR (flowerSystem branches segments).toRuleData) *
      (flowerSystem branches segments).resistanceSpectralRadius
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
        (flowerSystem_distancePositive branches segments)) /
      Real.log ((flowerSystem branches segments).distanceSpectralRadius
        (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)) = 2 := by
  rw [flowerSystem_massSpectralRadius,
    flowerSystem_distanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo,
    flowerSystem_resistanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo]
  exact flower_dims branches segments branchesAtLeastTwo segmentsAtLeastTwo

theorem flowerSystem_admissible_walk_dimension_limit (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments)
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, ∀ initialLevel (vertex : XiVtx (flowerSystem branches segments) initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (segments : ℝ) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (segments : ℝ) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph (flowerSystem branches segments) (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph (flowerSystem branches segments) (initialLevel + index))
            (xiForward (flowerSystem branches segments) initialLevel index vertex) (radius index))
          (xiForward (flowerSystem branches segments) initialLevel index vertex)) /
        Real.log (radius index)) atTop (nhds 2) := by
  have actual := xiSimpleGraph_admissible_walk_dimension_limit
    (flowerSystem branches segments)
    (flowerSystem_connected branches segments (by omega) segmentsAtLeastTwo)
    (flowerSystem_loopless branches segments)
    (flowerSystem_edgesUnique branches segments segmentsAtLeastTwo)
    (flowerSystem_plantingNonadjacent branches segments segmentsAtLeastTwo)
    (flowerSystem_distancePositive branches segments)
    radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  simpa only [flowerSystem_distanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo,
    flowerSystem_massSpectralRadius,
    flowerSystem_resistanceSpectralRadius branches segments (by omega) segmentsAtLeastTwo,
    (flower_dims branches segments branchesAtLeastTwo segmentsAtLeastTwo).2.2] using actual

end
end EIGS

#print axioms EIGS.flowerSystem_dimension_formulas
#print axioms EIGS.flowerSystem_admissible_walk_dimension_limit
