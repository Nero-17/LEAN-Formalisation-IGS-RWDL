import RequestProject.Section31.EIGSUVFlowerCanonicalResistance
import RequestProject.Section31.EIGSUVFlowerDistanceSpectrum
import RequestProject.Section2WalkDimension

/-! The genuine unequal-path flower's actual finite-graph mean-exit
logarithmic limit. The actual identity mu*rho=u*v supplies the time rate;
no scalar Einstein identity substitutes for the random-walk theorem. -/

namespace EIGS
open Filter Topology
noncomputable section
open scoped Classical

theorem uvFlowerSystem_admissible_walk_dimension_limit (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength)
    (radiusLower radiusUpper : ℝ) (radiusLowerPositive : 0 < radiusLower)
    (radiusUpperPositive : 0 < radiusUpper) :
    ∃ buffer : ℕ, ∀ initialLevel (vertex : XiVtx (uvFlowerSystem firstLength secondLength) initialLevel)
      (depth : ℕ → ℕ) (radius : ℕ → ℝ),
      Tendsto radius atTop atTop →
      (∀ᶠ index in atTop, depth index + buffer ≤ index ∧
        radiusLower * (min firstLength secondLength : ℕ) ^ depth index ≤ radius index ∧
        radius index ≤ radiusUpper * (min firstLength secondLength : ℕ) ^ depth index) →
      Tendsto (fun index =>
        Real.log (expExit (XiSimpleGraph (uvFlowerSystem firstLength secondLength) (initialLevel + index))
          (finiteGraphBall (XiSimpleGraph (uvFlowerSystem firstLength secondLength) (initialLevel + index))
            (xiForward (uvFlowerSystem firstLength secondLength) initialLevel index vertex) (radius index))
          (xiForward (uvFlowerSystem firstLength secondLength) initialLevel index vertex)) /
        Real.log (radius index)) atTop
          (𝓝 (Real.log ((firstLength : ℝ) * secondLength) / Real.log (min firstLength secondLength : ℕ))) := by
  have actual := xiSimpleGraph_admissible_walk_dimension_limit
    (uvFlowerSystem firstLength secondLength)
    (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
    (uvFlowerSystem_loopless firstLength secondLength)
    (uvFlowerSystem_edgesUnique firstLength secondLength firstAtLeastTwo secondAtLeastTwo)
    (uvFlowerSystem_plantingNonadjacent firstLength secondLength firstAtLeastTwo secondAtLeastTwo)
    (uvFlowerSystem_distancePositive firstLength secondLength)
    radiusLower radiusUpper radiusLowerPositive radiusUpperPositive
  simpa only [uvFlowerSystem_mass_times_resistance firstLength secondLength (by omega) (by omega),
    uvFlowerSystem_distanceSpectralRadius firstLength secondLength firstAtLeastTwo secondAtLeastTwo] using actual

end
end EIGS

#print axioms EIGS.uvFlowerSystem_admissible_walk_dimension_limit
