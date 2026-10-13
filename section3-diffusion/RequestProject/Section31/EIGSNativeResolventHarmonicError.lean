import RequestProject.Section31.FiniteGraphPoissonComparison
import RequestProject.Section31.EIGSNativeDiscreteContraction

/-! Pointwise bounds for the actual finite resolvent and its actual skeleton
harmonic interpolation. No uniform exit estimate is assumed. -/

namespace EIGS

open MeasureTheory Matrix
open scoped BigOperators Classical

noncomputable section
set_option maxHeartbeats 3000000

theorem finiteMarkov_resolvent_abs_le
    {Vertex : Type} [Fintype Vertex] (transition : Vertex → Vertex → ℝ)
    (transitionNonnegative : ∀ source target, 0 ≤ transition source target)
    (transitionSum : ∀ source, ∑ target, transition source target = 1)
    (coefficient : ℝ) (coefficientNonnegative : 0 ≤ coefficient)
    (forcing solution : Vertex → ℝ) (bound : ℝ)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound)
    (equation : ∀ vertex, solution vertex + coefficient *
      (solution vertex - ∑ target, transition vertex target * solution target) = forcing vertex)
    (vertex : Vertex) : |solution vertex| ≤ bound := by
  classical
  letI : Nonempty Vertex := ⟨vertex⟩
  obtain ⟨maximumVertex, _, maximal⟩ := Finset.univ.exists_max_image
    (fun target => |solution target|) Finset.univ_nonempty
  have averageBound :
      |∑ target, transition maximumVertex target * solution target| ≤ |solution maximumVertex| := by
    calc
      _ ≤ ∑ target, |transition maximumVertex target * solution target| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ target, transition maximumVertex target * |solution target| := by
        apply Finset.sum_congr rfl
        intro target _
        rw [abs_mul, abs_of_nonneg (transitionNonnegative _ _)]
      _ ≤ ∑ target, transition maximumVertex target * |solution maximumVertex| := by
        apply Finset.sum_le_sum
        intro target _
        exact mul_le_mul_of_nonneg_left (maximal target (Finset.mem_univ _))
          (transitionNonnegative _ _)
      _ = |solution maximumVertex| := by rw [← Finset.sum_mul, transitionSum, one_mul]
  have rearranged : (1 + coefficient) * solution maximumVertex = forcing maximumVertex +
      coefficient * (∑ target, transition maximumVertex target * solution target) := by
    linarith [equation maximumVertex]
  have maximumBound : |solution maximumVertex| ≤ bound := by
    have triangle := abs_add_le (forcing maximumVertex)
      (coefficient * (∑ target, transition maximumVertex target * solution target))
    rw [← rearranged, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 + coefficient),
      abs_mul, abs_of_nonneg coefficientNonnegative] at triangle
    have averageScaled := mul_le_mul_of_nonneg_left averageBound coefficientNonnegative
    nlinarith [forcingBound maximumVertex]
  exact (maximal vertex (Finset.mem_univ _)).trans maximumBound

theorem graph_resolvent_laplacian_abs_le
    {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex)
    (coefficient : ℝ) (coefficientPositive : 0 < coefficient)
    (forcing solution : Vertex → ℝ) (bound : ℝ)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound)
    (equation : ∀ vertex, solution vertex + coefficient *
      (solution vertex - ∑ target, transProb graph vertex target * solution target) = forcing vertex)
    (vertex : Vertex) :
    |(graph.lapMatrix ℝ *ᵥ solution) vertex| ≤
      (2 * bound / coefficient) * graph.degree vertex := by
  have solutionBound := finiteMarkov_resolvent_abs_le (transProb graph)
    (transProb_nonneg (G := graph)) (fun source => transProb_sum (degreePositive source))
    coefficient coefficientPositive.le forcing solution bound forcingBound equation vertex
  have multiplied : coefficient *
      (solution vertex - ∑ target, transProb graph vertex target * solution target) =
        forcing vertex - solution vertex := by linarith [equation vertex]
  have forcingDifference : |forcing vertex - solution vertex| ≤ 2 * bound := by
    exact (abs_sub (forcing vertex) (solution vertex)).trans (by
      linarith [forcingBound vertex, solutionBound])
  have differenceBound :
      |solution vertex - ∑ target, transProb graph vertex target * solution target| ≤
        2 * bound / coefficient := by
    apply (le_div_iff₀ coefficientPositive).2
    calc
      _ = |coefficient *
          (solution vertex - ∑ target, transProb graph vertex target * solution target)| := by
        rw [abs_mul, abs_of_pos coefficientPositive]
        ring
      _ = |forcing vertex - solution vertex| := by rw [multiplied]
      _ ≤ 2 * bound := forcingDifference
  rw [lapMatrix_mulVec_eq_degree_mul_randomWalk_difference graph solution vertex
    (degreePositive vertex), abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left differenceBound
    (show (0 : ℝ) ≤ graph.degree vertex by positivity)

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system)

theorem xiNativeFiniteResolvent_pointwise_equation
    (level : ℕ) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)
    (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (vertex : XiVtx system level) :
    let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization rateNonnegative
        normalizationNonnegative step stepPositive forcing
    solution vertex + (step * xiNativeFiniteJumpRate system level resistanceRate normalization) *
      (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target *
        solution target) = forcing vertex := by
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level resistanceRate normalization rateNonnegative
      normalizationNonnegative step stepPositive forcing
  have identity := (xiNativeFiniteResolvent_properties system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level resistanceRate normalization rateNonnegative
      normalizationNonnegative step stepPositive).1 forcing |>.1
  have evaluated := congrArg (fun values =>
    xiNativeEvaluationLinearEquiv system rulesConnected mass level values vertex) identity
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at evaluated
  have generatorEvaluation :
      xiNativeEvaluationLinearEquiv system rulesConnected mass level
        (xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization solution)
          vertex = xiNativeFiniteJumpRate system level resistanceRate normalization *
            (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target *
              solution target) := by
    unfold xiNativeFiniteGenerator
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.id_apply, map_smul, map_sub]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change xiNativeFiniteJumpRate system level resistanceRate normalization *
      (solution vertex - xiNativeRandomWalk system rulesConnected mass level solution vertex) = _
    rw [xiNativeRandomWalk_apply]
  rw [generatorEvaluation] at evaluated
  change solution vertex + (step * xiNativeFiniteJumpRate system level resistanceRate normalization) *
    (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target *
      solution target) = forcing vertex
  change solution vertex + step * (xiNativeFiniteJumpRate system level resistanceRate normalization *
    (solution vertex - ∑ target, transProb (XiSimpleGraph system level) vertex target *
      solution target)) = forcing vertex at evaluated
  simpa only [mul_assoc] using evaluated

theorem xiNativeFiniteResolvent_sup_bound
    (level : ℕ) (resistanceRate normalization : ℝ)
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (step : ℝ) (stepPositive : 0 < step)
    (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (vertex : XiVtx system level) :
    |xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      mass level resistanceRate normalization rateNonnegative normalizationNonnegative step
        stepPositive forcing vertex| ≤ ‖fun target : XiVtx system level => forcing target‖ := by
  apply finiteMarkov_resolvent_abs_le (transProb (XiSimpleGraph system level))
    (transProb_nonneg (G := XiSimpleGraph system level))
    (fun source => transProb_sum (by
      exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected level source))
    (step * xiNativeFiniteJumpRate system level resistanceRate normalization)
    (mul_nonneg stepPositive.le (xiNativeFiniteJumpRate_nonnegative system level resistanceRate
      normalization rateNonnegative normalizationNonnegative))
    (fun target => forcing target)
  · intro target
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun target : XiVtx system level => forcing target) target
  · exact xiNativeFiniteResolvent_pointwise_equation system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent mass level resistanceRate normalization rateNonnegative
        normalizationNonnegative step stepPositive forcing

theorem xiNativeFiniteResolvent_skeleton_error_le_exit
    (coarse steps : ℕ) (resistanceRate normalization : ℝ)
    (ratePositive : 0 < resistanceRate) (normalizationPositive : 0 < normalization)
    (step : ℝ) (stepPositive : 0 < step)
    (forcing : Lp ℝ 2 (xiVertexSpeedMeasure system mass (coarse + steps)))
    (vertex : XiVtx system (coarse + steps)) :
    let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass (coarse + steps) resistanceRate normalization ratePositive.le
        normalizationPositive.le step stepPositive forcing
    |solution vertex - xiUnitTraceExtension system rulesConnected coarse steps
        (fun oldVertex => solution (xiForward system coarse steps oldVertex)) vertex| ≤
      (2 * ‖fun target : XiVtx system (coarse + steps) => forcing target‖ /
        (step * xiNativeFiniteJumpRate system (coarse + steps) resistanceRate normalization)) *
          expExit (XiSimpleGraph system (coarse + steps))
            (Finset.univ.image (xiForward system coarse steps))ᶜ vertex := by
  classical
  let solution := xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass (coarse + steps) resistanceRate normalization ratePositive.le
      normalizationPositive.le step stepPositive forcing
  let boundary := Finset.univ.image (xiForward system coarse steps)
  let harmonicValues := xiUnitTraceExtension system rulesConnected coarse steps
    (fun oldVertex => solution (xiForward system coarse steps oldVertex))
  have boundaryNonempty : boundary.Nonempty := by
    exact Finset.image_nonempty.mpr Finset.univ_nonempty
  apply harmonic_interpolation_error_le_exit (XiSimpleGraph system (coarse + steps))
    (xiSimpleGraph_connected system rulesConnected _) boundaryᶜ (by simpa using boundaryNonempty)
    (fun target => solution target) harmonicValues
  · intro target outside
    have inside : target ∈ boundary := by simpa only [Finset.mem_compl, not_not] using outside
    obtain ⟨oldVertex, _, rfl⟩ := Finset.mem_image.mp inside
    exact (xiUnitTraceExtension_boundary system rulesConnected coarse steps
      (fun oldVertex => solution (xiForward system coarse steps oldVertex)) oldVertex).symm
  · intro target inside
    apply (XiNetwork system (coarse + steps)).unit_minimum_harmonic
      (xiNetwork_loopless system rulesConnected rulesLoopless _)
      (xiNetwork_edges_unique system rulesConnected rulesLoopless rulesUnique plantingNonadjacent _)
      boundary harmonicValues _ target (Finset.mem_compl.mp inside)
    intro competitor competitorBoundary
    apply xiUnitTraceExtension_minimal system rulesConnected coarse steps _ competitor
    intro oldVertex
    exact (competitorBoundary (xiForward system coarse steps oldVertex)
      (Finset.mem_image.mpr ⟨oldVertex, Finset.mem_univ _, rfl⟩)).trans
        (xiUnitTraceExtension_boundary system rulesConnected coarse steps _ oldVertex)
  · intro target _
    apply graph_resolvent_laplacian_abs_le (XiSimpleGraph system (coarse + steps))
      (fun target => by
        exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) target) _
      (mul_pos stepPositive (xiNativeFiniteJumpRate_positive system mass (coarse + steps)
        resistanceRate normalization ratePositive normalizationPositive))
      (fun other => forcing other)
    · intro other
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun other : XiVtx system (coarse + steps) => forcing other) other
    · exact xiNativeFiniteResolvent_pointwise_equation system rulesConnected rulesLoopless
        rulesUnique plantingNonadjacent mass (coarse + steps) resistanceRate normalization
          ratePositive.le normalizationPositive.le step stepPositive forcing

end
end EIGS

#print axioms EIGS.finiteMarkov_resolvent_abs_le
#print axioms EIGS.graph_resolvent_laplacian_abs_le
#print axioms EIGS.xiNativeFiniteResolvent_pointwise_equation
#print axioms EIGS.xiNativeFiniteResolvent_sup_bound
#print axioms EIGS.xiNativeFiniteResolvent_skeleton_error_le_exit
