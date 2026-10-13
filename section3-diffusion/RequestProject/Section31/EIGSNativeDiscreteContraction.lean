import RequestProject.Section31.PoissonizedWalkMoments
import RequestProject.Section31.EIGSAnalyticTimeScale

/-! The original discrete walk is an L² contraction for its actual speed
measure. The proof uses its true transition rows, symmetry and preservation
of one; contractivity is not supplied as a model assumption. -/

namespace EIGS

open MeasureTheory Filter Topology
open scoped BigOperators

noncomputable section
set_option maxHeartbeats 3000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_square_le
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (vertex : XiVtx system level) :
    (xiNativeRandomWalk system rulesConnected mass level values vertex) ^ 2 ≤
      xiNativeRandomWalk system rulesConnected mass level
        (xiFiniteSpeedL2 system mass level (fun other => values other ^ 2)) vertex := by
  classical
  have degreePositive : 0 < (XiSimpleGraph system level).degree vertex := by
    rw [← xiVertexIncidenceCount_eq_degree system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level vertex]
    exact xiVertexIncidenceCount_positive system rulesConnected level vertex
  rw [xiNativeRandomWalk_apply, xiNativeRandomWalk_apply]
  simp_rw [xiFiniteSpeedL2_apply system rulesConnected mass level]
  have cauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (r := fun other => transProb (XiSimpleGraph system level) vertex other * values other)
    (f := fun other => transProb (XiSimpleGraph system level) vertex other)
    (g := fun other => transProb (XiSimpleGraph system level) vertex other * values other ^ 2)
    (fun other _ => transProb_nonneg (G := XiSimpleGraph system level) vertex other)
    (fun other _ => mul_nonneg (transProb_nonneg (G := XiSimpleGraph system level) vertex other)
      (sq_nonneg _)) (fun other _ => by ring)
  simpa only [transProb_sum degreePositive, one_mul] using cauchy

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_apply_norm_le
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖xiNativeRandomWalk system rulesConnected mass level values‖ ≤ ‖values‖ := by
  classical
  have integratedSquareBound :
      inner ℝ (xiNativeRandomWalk system rulesConnected mass level values)
        (xiNativeRandomWalk system rulesConnected mass level values) ≤
      inner ℝ (xiFiniteSpeedL2 system mass level (fun _ => 1))
        (xiNativeRandomWalk system rulesConnected mass level
          (xiFiniteSpeedL2 system mass level (fun vertex => values vertex ^ 2))) := by
    rw [xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent,
      xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent]
    apply Finset.sum_le_sum
    intro vertex _
    rw [xiFiniteSpeedL2_apply system rulesConnected mass level, mul_one]
    have bound := mul_le_mul_of_nonneg_left
      (xiNativeRandomWalk_square_le system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent mass level values vertex)
      (show 0 ≤ ((XiSimpleGraph system level).degree vertex : ℝ) /
        (2 * (totalEdges system.toRuleData level : ℝ)) by positivity)
    simpa only [pow_two, mul_assoc] using bound
  have squareIntegral :
      inner ℝ (xiFiniteSpeedL2 system mass level (fun _ => 1))
        (xiNativeRandomWalk system rulesConnected mass level
          (xiFiniteSpeedL2 system mass level (fun vertex => values vertex ^ 2))) =
        inner ℝ values values := by
    rw [xiNativeRandomWalk_inner_symmetric system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level,
      xiNativeRandomWalk_preserves_one system rulesConnected mass level rulesLoopless rulesUnique
        plantingNonadjacent]
    rw [xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent,
      xiNativeL2_inner_degree system rulesConnected rulesLoopless rulesUnique plantingNonadjacent]
    apply Finset.sum_congr rfl
    intro vertex _
    simp only [xiFiniteSpeedL2_apply system rulesConnected mass level, mul_one, pow_two, mul_assoc]
  rw [squareIntegral, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at integratedSquareBound
  nlinarith [norm_nonneg values, norm_nonneg (xiNativeRandomWalk system rulesConnected mass level values)]

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_norm_le_one :
    ‖xiNativeRandomWalk system rulesConnected mass level‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using xiNativeRandomWalk_apply_norm_le system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level values

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_power_apply_norm_le
    (jumps : ℕ) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖(xiNativeRandomWalk system rulesConnected mass level ^ jumps) values‖ ≤ ‖values‖ :=
  IGS.Sec31.PoissonizedWalk.contraction_power_apply_le _
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level) jumps values

include mass in
theorem xiNativeFiniteJumpRate_positive (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization) :
    0 < xiNativeFiniteJumpRate system level resistanceRate normalization := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, growth⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  have edgePositive : 0 < (totalEdges system.toRuleData level : ℝ) :=
    (mul_pos lowerPositive (pow_pos mass.rate_positive level)).trans_le (growth level).1
  unfold xiNativeFiniteJumpRate
  positivity

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_poisson_comparison (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (jumps : ℕ) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization
        ((jumps : ℝ) / xiNativeFiniteJumpRate system level resistanceRate normalization) values -
      (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values‖ ≤
      (Real.sqrt jumps / xiNativeFiniteJumpRate system level resistanceRate normalization) *
        ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values‖ := by
  have jumpRatePositive := xiNativeFiniteJumpRate_positive system mass level
    resistanceRate normalization ratePositive normalizationPositive
  have exponentIdentity :
      (-((jumps : ℝ) / xiNativeFiniteJumpRate system level resistanceRate normalization)) •
        xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization =
      (-(jumps : ℝ)) • (1 - xiNativeRandomWalk system rulesConnected mass level) := by
    rw [xiNativeFiniteGenerator_eq_jumpRate, smul_smul]
    congr 1
    field_simp [ne_of_gt jumpRatePositive]
  have normIdentity :
      ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization values‖ =
      xiNativeFiniteJumpRate system level resistanceRate normalization *
        ‖xiNativeRandomWalk system rulesConnected mass level values - values‖ := by
    rw [xiNativeFiniteGenerator_eq_jumpRate, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos jumpRatePositive, norm_sub_rev]
  rw [xiNativeFiniteSemigroup, exponentIdentity, normIdentity]
  have coefficientIdentity :
      (Real.sqrt jumps / xiNativeFiniteJumpRate system level resistanceRate normalization) *
        (xiNativeFiniteJumpRate system level resistanceRate normalization *
          ‖xiNativeRandomWalk system rulesConnected mass level values - values‖) =
      Real.sqrt jumps * ‖xiNativeRandomWalk system rulesConnected mass level values - values‖ := by
    field_simp [ne_of_gt jumpRatePositive]
  rw [coefficientIdentity]
  exact IGS.Sec31.PoissonizedWalk.discrete_power_poisson_comparison _
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level) values jumps

include rulesLoopless rulesUnique plantingNonadjacent mass in
theorem xiNativeFiniteJumpRate_tendsto_atTop
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : (system.ruleFamily rulesConnected).Psi resistanceVector =
      resistanceRate • resistanceVector) :
    Tendsto (fun depth => xiNativeFiniteJumpRate system depth resistanceRate normalization)
      atTop atTop := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, growth⟩ :=
    mass_geometric_growth system mass.amplitude_positive mass.eigenpair mass.rate_positive
  have growthRate := xiAnalyticTimeRate_gt_one system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive mass resistanceRate ratePositive resistanceVector
    vectorPositive renormalizationEigenpair
  have lowerLimit : Tendsto
      (fun depth : ℕ => (2 * normalization * lower) * (mass.rate * resistanceRate) ^ depth)
      atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt growthRate).const_mul_atTop (by positivity)
  apply tendsto_atTop_mono _ lowerLimit
  intro depth
  calc
    (2 * normalization * lower) * (mass.rate * resistanceRate) ^ depth =
        (2 * normalization * resistanceRate ^ depth) * (lower * mass.rate ^ depth) := by
          rw [mul_pow]
          ring
    _ ≤ (2 * normalization * resistanceRate ^ depth) *
        (totalEdges system.toRuleData depth : ℝ) :=
          mul_le_mul_of_nonneg_left (growth depth).1 (by positivity)
    _ = xiNativeFiniteJumpRate system depth resistanceRate normalization := rfl

end
end EIGS

#print axioms EIGS.xiNativeRandomWalk_square_le
#print axioms EIGS.xiNativeRandomWalk_apply_norm_le
#print axioms EIGS.xiNativeRandomWalk_norm_le_one
#print axioms EIGS.xiNativeRandomWalk_power_apply_norm_le
#print axioms EIGS.xiNativeFiniteJumpRate_positive
#print axioms EIGS.xiNativeRandomWalk_poisson_comparison
#print axioms EIGS.xiNativeFiniteJumpRate_tendsto_atTop
