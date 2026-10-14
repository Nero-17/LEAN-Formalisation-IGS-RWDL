import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! Transfer completeness across an algebraic linear equivalence after proving
both norm bounds. This uses a uniform equivalence, so the complete norm is
the original norm of the source, rather than a replacement instance.
Candidate source: compilation is not claimed. -/

namespace IGS.Sec31
noncomputable section
variable {Source Target : Type*} [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]

theorem completeSpace_of_linearEquiv_norm_bounds
    (equivalence : Source ≃ₗ[ℝ] Target)
    (forwardConstant inverseConstant : ℝ)
    (forwardBound : ∀ values, ‖equivalence values‖ ≤ forwardConstant * ‖values‖)
    (inverseBound : ∀ values, ‖equivalence.symm values‖ ≤ inverseConstant * ‖values‖) :
    CompleteSpace Source := by
  let forward := equivalence.toLinearMap.mkContinuous forwardConstant forwardBound
  let inverse := equivalence.symm.toLinearMap.mkContinuous inverseConstant inverseBound
  let uniformEquivalence : Source ≃ᵤ Target :=
    { equivalence.toEquiv with
      uniformContinuous_toFun := forward.uniformContinuous
      uniformContinuous_invFun := inverse.uniformContinuous }
  exact uniformEquivalence.completeSpace_iff.2 inferInstance

variable {Ambient : Type*} [NormedAddCommGroup Ambient] [NormedSpace ℝ Ambient]

theorem completeSpace_of_linearEquiv_energy_square_bounds
    (equivalence : Source ≃ₗ[ℝ] Target)
    (evaluation : Source →L[ℝ] ℝ) (ambient : Target →L[ℝ] Ambient)
    (forwardSquare : ∀ values, ‖equivalence values‖ ^ 2 ≤ ‖values‖ ^ 2 + (evaluation values) ^ 2)
    (inverseSquare : ∀ values, ‖equivalence.symm values‖ ^ 2 ≤ ‖values‖ ^ 2 + ‖ambient values‖ ^ 2) :
    CompleteSpace Source := by
  apply completeSpace_of_linearEquiv_norm_bounds equivalence
    (Real.sqrt (1 + ‖evaluation‖ ^ 2)) (Real.sqrt (1 + ‖ambient‖ ^ 2))
  · intro values
    have evaluationBound := (sq_le_sq₀ (norm_nonneg (evaluation values))
      (mul_nonneg evaluation.opNorm_nonneg (norm_nonneg values))).2 (evaluation.le_opNorm values)
    simp only [Real.norm_eq_abs, sq_abs, mul_pow] at evaluationBound
    apply (sq_le_sq₀ (norm_nonneg (equivalence values))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg values))).1
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [forwardSquare values]
  · intro values
    have ambientBound := (sq_le_sq₀ (norm_nonneg (ambient values))
      (mul_nonneg ambient.opNorm_nonneg (norm_nonneg values))).2 (ambient.le_opNorm values)
    rw [mul_pow] at ambientBound
    apply (sq_le_sq₀ (norm_nonneg (equivalence.symm values))
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg values))).1
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    nlinarith [inverseSquare values]

end
end IGS.Sec31

#print axioms IGS.Sec31.completeSpace_of_linearEquiv_norm_bounds
#print axioms IGS.Sec31.completeSpace_of_linearEquiv_energy_square_bounds
