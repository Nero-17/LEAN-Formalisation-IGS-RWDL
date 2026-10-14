import RequestProject.Section31.EIGSFlowerDegreeSpectrum
import RequestProject.Section31.EIGSFlowerCanonicalRates

namespace EIGS
noncomputable section
open scoped Classical

 theorem flowerSystem_heat_exponent_values (branches segments : ℕ)
    (branchesAtLeastTwo : 2 ≤ branches) (segmentsAtLeastTwo : 2 ≤ segments) :
    (Real.log ((branches : ℝ) * segments) - Real.log branches) /
        Real.log (((branches : ℝ) * segments) * ((segments : ℝ) / branches)) = 1 / 2 ∧
    Real.log ((branches : ℝ) * segments) /
        Real.log (((branches : ℝ) * segments) * ((segments : ℝ) / branches)) =
          (1 + Real.log branches / Real.log segments) / 2 ∧
    1 / (Real.log ((branches : ℝ) * segments) / Real.log branches - 1) =
      Real.log branches / Real.log segments := by
  have branchesGreaterThanOne : (1 : ℝ) < branches := by exact_mod_cast (show 1 < branches by omega)
  have segmentsGreaterThanOne : (1 : ℝ) < segments := by exact_mod_cast (show 1 < segments by omega)
  have branchesNonzero : (branches : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans branchesGreaterThanOne)
  have segmentsNonzero : (segments : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans segmentsGreaterThanOne)
  have logBranchesNonzero : Real.log (branches : ℝ) ≠ 0 := ne_of_gt (Real.log_pos branchesGreaterThanOne)
  have logSegmentsNonzero : Real.log (segments : ℝ) ≠ 0 := ne_of_gt (Real.log_pos segmentsGreaterThanOne)
  have productIdentity : ((branches : ℝ) * segments) * ((segments : ℝ) / branches) =
      (segments : ℝ) * segments := by field_simp <;> ring
  rw [productIdentity, Real.log_mul branchesNonzero segmentsNonzero,
    Real.log_mul segmentsNonzero segmentsNonzero]
  constructor
  · field_simp [logSegmentsNonzero]
    <;> ring
  constructor
  · field_simp [logSegmentsNonzero]
    <;> ring
  · have quotientIdentity :
        (Real.log (branches : ℝ) + Real.log (segments : ℝ)) / Real.log branches - 1 =
          Real.log segments / Real.log branches := by
      field_simp [logBranchesNonzero]
      <;> ring
    rw [quotientIdentity]
    simp only [one_div_div]

end
end EIGS

#print axioms EIGS.flowerSystem_heat_exponent_values
