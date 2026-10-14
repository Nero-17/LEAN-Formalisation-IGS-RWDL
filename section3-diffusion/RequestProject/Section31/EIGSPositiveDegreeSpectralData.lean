import RequestProject.Section2SpectralGrowth
import RequestProject.Section2PrimitiveIntegerGrowth

/-! A positive normalized eigenvector is the degree input needed by the heat
proofs. Primitivity supplies this input, but is not part of the data. The
strict degree rate condition remains explicit; rate one is not covered. -/

namespace EIGS
open scoped BigOperators Classical
noncomputable section
variable {K : ℕ}

structure XiPositiveDegreeSpectralData (system : EIGSData K) where
  vector : Fin K ⊕ Fin K → ℝ
  positive : ∀ state, 0 < vector state
  normalized : ∑ state, vector state = 1
  eigenpair : (degreeMatrix system).mulVec vector =
    finiteRealMatrixSpectralRadius (degreeMatrix system) • vector
  rate_gt_one : 1 < finiteRealMatrixSpectralRadius (degreeMatrix system)

def xiPositiveDegreeSpectralData_of_primitive (system : EIGSData K)
    (primitiveDegree : (degreeMatrix system).IsPrimitive) :
    XiPositiveDegreeSpectralData system := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  let vector := Classical.choose
    (primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree)
  have vectorProperties := Classical.choose_spec
    (primitive_matrix_spectralRadius_eigenpair_finite (degreeMatrix system) primitiveDegree)
  exact ⟨vector, vectorProperties.1, vectorProperties.2.2.1, vectorProperties.2.2.2,
    degree_spectralRadius_gt_one_of_primitive system primitiveDegree⟩

theorem degree_spectral_growth_of_positive_degree_data (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (degreeData : XiPositiveDegreeSpectralData system) :
    0 < finiteRealMatrixSpectralRadius (degreeMatrix system) ∧
      ∀ initialLevel (vertex : XiVtx system initialLevel),
        ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ steps,
          lower * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps ≤
            ∑ state, degVec system (initialLevel + steps)
              (xiForward system initialLevel steps vertex) state ∧
          (∑ state, degVec system (initialLevel + steps)
            (xiForward system initialLevel steps vertex) state) ≤
              upper * finiteRealMatrixSpectralRadius (degreeMatrix system) ^ steps := by
  letI : Nonempty (Fin K) := ⟨system.initCol⟩
  have ratePositive := lt_trans (by norm_num : (0 : ℝ) < 1) degreeData.rate_gt_one
  refine ⟨ratePositive, fun initialLevel vertex => ?_⟩
  exact degree_geometric_growth_proved system initialLevel vertex degreeData.positive degreeData.eigenpair
    ratePositive (degVec_weighted_positive system rulesConnected initialLevel vertex degreeData.vector
      degreeData.positive)

end
end EIGS

#print axioms EIGS.xiPositiveDegreeSpectralData_of_primitive
#print axioms EIGS.degree_spectral_growth_of_positive_degree_data
