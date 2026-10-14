import RequestProject.Section31.EIGSNativeFloorCutoffExpectation
import RequestProject.Section31.EIGSMovingStartApproximation
import RequestProject.Section31.BanachBackwardObservations

/-! The finite-walk stay estimate passes to the specified continuous
semigroup through its already proved native floor-clock uniform limit.
The floor-limit premise is the field supplied by
XiNativeSupDiscreteConvergenceProperties; it is not a stay or heat-bound
premise. An eventual actual-model wrapper must fill that field internally
and align the same closed L2 semigroup before applying kernel estimates.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter IGS.Sec31
open scoped Topology Classical NNReal
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem xiNativeFloorStayLimit_of_uniform_convergence (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)]
    [CompactSpace (xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive).LimitSpace] :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    ∀ semigroup : ℝ≥0 → C(parameters.LimitSpace, ℝ) →L[ℝ] C(parameters.LimitSpace, ℝ),
    (∀ (time : ℝ≥0) (function : C(parameters.LimitSpace, ℝ)),
      Tendsto (fun level => ‖(xiNativeSupTransition system rulesConnected level ^
        Nat.floor ((time : ℝ) * xiNativeFiniteJumpRate system level
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization))
        (fun vertex => function (parameters.vertexEmbedding level vertex)) -
        (fun vertex => semigroup time function (parameters.vertexEmbedding level vertex))‖) atTop (𝓝 0)) →
    ∃ fraction : ℝ, 0 < fraction ∧ ∃ count : ℕ,
      ∀ (coarse : ℕ) (time : ℝ≥0),
      (time : ℝ) ≤ fraction *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse →
      let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
      ∀ center : parameters.LimitSpace,
        (3 / 4 : ℝ) ≤ semigroup time (continuousMetricBallCutoff center (2 * radius)) center := by
  intro parameters semigroup floorLimit
  obtain ⟨fraction, fractionPositive, count, finiteExpectation⟩ :=
    exists_xiNativeFloorCutoffExpectation_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  refine ⟨fraction, fractionPositive, count, ?_⟩
  intro coarse time timeBound radius center
  obtain ⟨starts, startsConverge⟩ := parameters.exists_moving_starts center
  have radiusPositive : 0 < radius := by
    have ruleRadiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    have distanceRatePositive := parameters.ratePositive
    dsimp only [radius]
    positivity
  have shifted : Tendsto (fun steps : ℕ => coarse + steps) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat coarse
  have sourceNear : ∀ᶠ steps in atTop,
      dist (parameters.vertexEmbedding (coarse + steps) (starts (coarse + steps))) center ≤ radius := by
    have distanceConverges : Tendsto
        (fun steps : ℕ => dist (parameters.vertexEmbedding (coarse + steps)
          (starts (coarse + steps))) center) atTop (𝓝 (0 : ℝ)) := by
      simpa only [dist_self] using (startsConverge.comp shifted).dist tendsto_const_nhds
    exact (distanceConverges.eventually (gt_mem_nhds radiusPositive)).mono (fun _ near => near.le)
  have limit := (BanachBackwardObservations.moving_start_evaluation_limit parameters.vertexEmbedding
    (fun level => (xiNativeSupTransition system rulesConnected level ^
      Nat.floor ((time : ℝ) * xiNativeFiniteJumpRate system level
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization))
      (fun vertex => continuousMetricBallCutoff center (2 * radius) (parameters.vertexEmbedding level vertex)))
    (semigroup time (continuousMetricBallCutoff center (2 * radius)))
    (floorLimit time (continuousMetricBallCutoff center (2 * radius)))
    starts center startsConverge).comp shifted
  apply le_of_tendsto limit
  filter_upwards [sourceNear] with steps near
  exact finiteExpectation coarse steps (time : ℝ) time.coe_nonneg timeBound
    center (starts (coarse + steps)) near

end
end EIGS

#print axioms EIGS.xiNativeFloorStayLimit_of_uniform_convergence
