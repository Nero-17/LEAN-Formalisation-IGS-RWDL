import RequestProject.Section31.EIGSUnitUniformCompletion
import RequestProject.Section31.EIGSUnitHarmonicCoercivity
import Mathlib.Algebra.BigOperators.Pi

/-! Actual finite unit harmonic interpolation has a finite basis. Its
continuous basis limits give an approximation uniform over all boundary
values after dividing the error by their sup norm. No equality between
finite unit harmonics and stationary Perron harmonics is assumed. -/

namespace EIGS

open Filter Topology
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ}

def xiUnitPotentialAtLinearMap (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse fine : ℕ) (levelsOrdered : coarse ≤ fine) :
    (XiVtx system coarse → ℝ) →ₗ[ℝ] (XiVtx system fine → ℝ) where
  toFun := xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
  map_add' := by
    intro first second
    simpa only [one_mul] using
      xiUnitPotentialAt_linear system rulesConnected coarse fine levelsOrdered first second 1 1
  map_smul' := by
    intro scalar values
    simpa only [zero_mul, add_zero, Pi.smul_apply, smul_eq_mul] using
      xiUnitPotentialAt_linear system rulesConnected coarse fine levelsOrdered values values scalar 0

theorem xiUnitPotentialAt_finite_basis (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse fine : ℕ) (levelsOrdered : coarse ≤ fine)
    (values : XiVtx system coarse → ℝ) (vertex : XiVtx system fine) :
    xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered values vertex =
      ∑ boundary, values boundary *
        xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
          (fun target => if boundary = target then 1 else 0) vertex := by
  change (xiUnitPotentialAtLinearMap system rulesConnected coarse fine levelsOrdered values) vertex = _
  calc
    _ = (xiUnitPotentialAtLinearMap system rulesConnected coarse fine levelsOrdered
        (∑ boundary, values boundary •
          (fun target => if boundary = target then (1 : ℝ) else 0))) vertex :=
      congrArg (fun boundaryValues =>
        (xiUnitPotentialAtLinearMap system rulesConnected coarse fine levelsOrdered boundaryValues) vertex)
        (pi_eq_sum_univ values)
    _ = _ := by
      simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rfl

theorem xiUnitPotentialAt_finite_basis_error (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (coarse fine : ℕ) (levelsOrdered : coarse ≤ fine)
    (values : XiVtx system coarse → ℝ) (vertex : XiVtx system fine)
    (basisValues : XiVtx system coarse → ℝ) :
    |xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered values vertex -
        ∑ boundary, values boundary * basisValues boundary| ≤
      ‖values‖ * ∑ boundary,
        |xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
          (fun target => if boundary = target then 1 else 0) vertex - basisValues boundary| := by
  rw [xiUnitPotentialAt_finite_basis]
  have difference :
      (∑ boundary, values boundary *
        xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
          (fun target => if boundary = target then 1 else 0) vertex) -
        (∑ boundary, values boundary * basisValues boundary) =
      ∑ boundary, values boundary *
        (xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
          (fun target => if boundary = target then 1 else 0) vertex - basisValues boundary) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro boundary _
    ring
  rw [difference]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ boundary, ‖values‖ *
        |xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
          (fun target => if boundary = target then 1 else 0) vertex - basisValues boundary| := by
      apply Finset.sum_le_sum
      intro boundary _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm values boundary) (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem exists_xiUnitPotential_finite_basis_uniform_approximation_of_rules
    (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∀ coarse, ∃ basis : XiVtx system coarse → C(parameters.LimitSpace, ℝ),
      ∀ tolerance : ℝ, 0 < tolerance → ∃ threshold : ℕ,
        ∀ fine, threshold ≤ fine → ∀ levelsOrdered : coarse ≤ fine,
          ∀ (values : XiVtx system coarse → ℝ) (vertex : XiVtx system fine),
          |xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered values vertex -
            ∑ boundary, values boundary * basis boundary (parameters.vertexEmbedding fine vertex)| ≤
          tolerance * ‖values‖ := by
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  dsimp only
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, eigenpair, limits⟩ :=
    exists_xiUnitPotential_continuous_uniform_limit_of_rules system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent distancePositive
  intro coarse
  choose basis basisAgreement basisConvergence using
    (fun boundary : XiVtx system coarse => limits coarse
      (fun target => if boundary = target then 1 else 0))
  refine ⟨basis, ?_⟩
  intro tolerance tolerancePositive
  have sumConvergence : Tendsto (fun fine => ∑ boundary : XiVtx system coarse,
      xiUnitPotentialUniformError system rulesConnected coarse
        (fun target => if boundary = target then 1 else 0)
        (basis boundary ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths
          parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          parameters.ratePositive parameters.eigenpair) fine) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun boundary _ => basisConvergence boundary)
  obtain ⟨threshold, errorSmall⟩ := eventually_atTop.1
    (sumConvergence.eventually (gt_mem_nhds tolerancePositive))
  refine ⟨threshold, ?_⟩
  intro fine afterThreshold levelsOrdered values vertex
  apply (xiUnitPotentialAt_finite_basis_error system rulesConnected coarse fine levelsOrdered
    values vertex (fun boundary => basis boundary (parameters.vertexEmbedding fine vertex))).trans
  calc
    _ ≤ ‖values‖ * ∑ boundary : XiVtx system coarse,
        xiUnitPotentialUniformError system rulesConnected coarse
          (fun target => if boundary = target then 1 else 0)
          (basis boundary ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths
            parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
            parameters.ratePositive parameters.eigenpair) fine := by
      apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum ?_) (norm_nonneg _)
      intro boundary _
      rw [xiUnitPotentialUniformError, dif_pos levelsOrdered]
      simpa only [Pi.sub_apply, Real.norm_eq_abs] using
        (norm_le_pi_norm
          (xiUnitPotentialAt system rulesConnected coarse fine levelsOrdered
            (fun target => if boundary = target then 1 else 0) -
            (fun finiteVertex =>
              (basis boundary ∘ xiCompletionUnionEmbedding system rulesConnected parameters.lengths
                parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
                parameters.ratePositive parameters.eigenpair)
                (xiVertexEmbedding system fine finiteVertex))) vertex)
    _ ≤ ‖values‖ * tolerance :=
      mul_le_mul_of_nonneg_left (errorSmall fine afterThreshold).le (norm_nonneg _)
    _ = _ := mul_comm _ _

end
end EIGS

#print axioms EIGS.xiUnitPotentialAtLinearMap
#print axioms EIGS.xiUnitPotentialAt_finite_basis
#print axioms EIGS.xiUnitPotentialAt_finite_basis_error
#print axioms EIGS.exists_xiUnitPotential_finite_basis_uniform_approximation_of_rules
