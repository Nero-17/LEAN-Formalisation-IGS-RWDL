import RequestProject.Section31.EIGSPositiveDegreeSpectralData
import RequestProject.Section31.EIGSTwoColourMatrixSpectra

/-! The original arrows give a reducible degree matrix, with the strictly
positive normalized constant eigenvector and degree rate two nonetheless.
This is actual degree growth for the unchanged rule graphs. -/

namespace EIGS
open scoped BigOperators
noncomputable section

def twoColourPositiveDegreeData : XiPositiveDegreeSpectralData twoColourSystem where
  vector := fun _ => 1 / 4
  positive := by intro state; norm_num
  normalized := by norm_num [Fintype.sum_sum_type, Fin.sum_univ_succ]
  eigenpair := by
    rw [twoColourSystem_degreeSpectralRadius, twoColourSystem_degreeMatrix]
    ext state
    cases state with
    | inl colour =>
      fin_cases colour <;>
        norm_num [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, twoColourDegreeMatrix]
    | inr colour =>
      fin_cases colour <;>
        norm_num [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_succ, twoColourDegreeMatrix]
  rate_gt_one := by rw [twoColourSystem_degreeSpectralRadius]; norm_num

theorem twoColourSystem_degree_growth (initialLevel : ℕ) (vertex : XiVtx twoColourSystem initialLevel) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps,
      lower * 2 ^ steps ≤ ∑ state, degVec twoColourSystem (initialLevel + steps)
        (xiForward twoColourSystem initialLevel steps vertex) state ∧
      (∑ state, degVec twoColourSystem (initialLevel + steps)
        (xiForward twoColourSystem initialLevel steps vertex) state) ≤ upper * 2 ^ steps := by
  simpa only [twoColourSystem_degreeSpectralRadius] using
    (degree_spectral_growth_of_positive_degree_data twoColourSystem twoColourSystem_connected
      twoColourPositiveDegreeData).2 initialLevel vertex

end
end EIGS

#print axioms EIGS.twoColourPositiveDegreeData
#print axioms EIGS.twoColourSystem_degree_growth
