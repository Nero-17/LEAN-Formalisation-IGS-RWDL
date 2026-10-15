import RequestProject.Section31.EIGSPrimitiveOriginalDegreeDimension
import RequestProject.Section31.EIGSUVFlowerRuleConnectivity
import RequestProject.Section31.EIGSUVFlowerRuleSimplicity
import RequestProject.Section31.EIGSUVFlowerDegreeSpectrum
import RequestProject.Section31.EIGSUVFlowerMassSpectrum

/-! Original global degree-distribution dimension of the genuine
two-path flower. This retains the actual degree/maxDegree limit and
complete occupied-support point multiplicities from the general theorem;
the endpoint is not merely a scalar ratio of spectral rates. -/

namespace EIGS
open Filter Topology
noncomputable section

theorem uvFlowerSystem_original_degree_dimension (firstLength secondLength : ℕ)
    (firstAtLeastTwo : 2 ≤ firstLength) (secondAtLeastTwo : 2 ≤ secondLength) :
    ∃ weights : Fin 1 ⊕ Fin 1 → ℝ, ∃ coefficient normalizer : ℝ,
      (∀ vertex, 0 < xiStationaryDegreeFromAmplitudes (uvFlowerSystem firstLength secondLength)
        weights coefficient 2 normalizer vertex ∧
        xiStationaryDegreeFromAmplitudes (uvFlowerSystem firstLength secondLength)
          weights coefficient 2 normalizer vertex ≤ 1) ∧
      (∀ vertex, Tendsto (fun level => xiActualMaxNormalizedDegree (uvFlowerSystem firstLength secondLength) level vertex)
        atTop (𝓝 (xiStationaryDegreeFromAmplitudes (uvFlowerSystem firstLength secondLength)
          weights coefficient 2 normalizer vertex))) ∧
      (∀ value : ℝ, Finite {vertex : XiVertexUnion (uvFlowerSystem firstLength secondLength) //
        xiStationaryDegreeFromAmplitudes (uvFlowerSystem firstLength secondLength)
          weights coefficient 2 normalizer vertex = value}) ∧
      0 < Real.log ((firstLength : ℝ) + secondLength) / Real.log 2 ∧
      Tendsto (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity (uvFlowerSystem firstLength secondLength)
        weights coefficient 2 normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport (uvFlowerSystem firstLength secondLength)
          weights coefficient 2 normalizer] (0 : ℝ))
        (𝓝 (Real.log ((firstLength : ℝ) + secondLength) / Real.log 2)) ∧
      NeBot (𝓝[xiStationaryOccupiedDegreeSupport (uvFlowerSystem firstLength secondLength)
        weights coefficient 2 normalizer] (0 : ℝ)) ∧
      Filter.limsup (fun value : ℝ => Real.log (xiStationaryDegreeMultiplicity (uvFlowerSystem firstLength secondLength)
        weights coefficient 2 normalizer value : ℝ) / (-Real.log value))
        (𝓝[xiStationaryOccupiedDegreeSupport (uvFlowerSystem firstLength secondLength)
          weights coefficient 2 normalizer] (0 : ℝ)) =
        Real.log ((firstLength : ℝ) + secondLength) / Real.log 2 := by
  have actual := primitive_rules_original_degree_dimension (uvFlowerSystem firstLength secondLength)
    (uvFlowerSystem_connected firstLength secondLength (by omega) (by omega))
    (uvFlowerSystem_loopless firstLength secondLength)
    (uvFlowerSystem_edgesUnique firstLength secondLength firstAtLeastTwo secondAtLeastTwo)
    (uvFlowerSystem_plantingNonadjacent firstLength secondLength firstAtLeastTwo secondAtLeastTwo)
    (uvFlowerSystem_distancePositive firstLength secondLength)
    (uvFlowerSystem_degreeMatrix_primitive firstLength secondLength (by omega) (by omega))
  simpa only [uvFlowerSystem_degreeSpectralRadius firstLength secondLength (by omega) (by omega),
    uvFlowerSystem_massSpectralRadius] using actual

end
end EIGS

#print axioms EIGS.uvFlowerSystem_original_degree_dimension
