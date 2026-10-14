import RequestProject.Section31.EIGSNativeFloorDisplacementStay
import RequestProject.Section31.DiscreteMetricCutoffExpectation
import RequestProject.Section31.EIGSNativeSupTransition

/-! Actual finite-walk continuous-test expectation, uniformly over the fine
starting vertex. The probability estimate is constructed from the original
rules and used at the genuine floor clock. No continuum path law is used.
Candidate source: no compilation is claimed. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped Topology Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

theorem exists_xiNativeFloorCutoffExpectation_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization : ℝ) (normalizationPositive : 0 < normalization) :
    ∃ fraction : ℝ, 0 < fraction ∧ ∃ count : ℕ,
      ∀ (coarse steps : ℕ) (window : ℝ), 0 ≤ window →
      window ≤ fraction *
        (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse →
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let radius := (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)
      ∀ (center : parameters.LimitSpace) (source : XiVtx system (coarse + steps)),
      dist (parameters.vertexEmbedding (coarse + steps) source) center ≤ radius →
      (3 / 4 : ℝ) ≤
        ((xiNativeSupTransition system rulesConnected (coarse + steps) ^
          Nat.floor (window * xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization))
          (fun vertex => continuousMetricBallCutoff center (2 * radius)
            (parameters.vertexEmbedding (coarse + steps) vertex))) source := by
  obtain ⟨fraction, fractionPositive, count, tails⟩ :=
    exists_xiNativeFloorDisplacementStay_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  refine ⟨fraction, fractionPositive, count, ?_⟩
  intro coarse steps window windowNonnegative windowBound parameters radius center source sourceNear
  let horizon := Nat.floor (window * xiNativeFiniteJumpRate system (coarse + steps)
    (system.resistanceSpectralRadius rulesConnected distancePositive) normalization)
  let transition := xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent (coarse + steps)
  let law := pathLaw transition (Measure.dirac source)
  let bad := xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps 0 horizon count
  let values : XiVtx system (coarse + steps) → ℝ := fun vertex =>
    continuousMetricBallCutoff center (2 * radius) (parameters.vertexEmbedding (coarse + steps) vertex)
  have radiusPositive : 0 < radius := by
    have ruleRadiusNonnegative := xiRuleRadius_nonnegative system
      (fun colour => (parameters.lengthsPositive colour).le)
    have distanceRatePositive : 0 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (0 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    dsimp only [radius]
    positivity
  have sourceAtZero : ∀ᵐ path ∂law, path 0 = source := by
    have mapped : ∀ᵐ vertex ∂law.map (fun path => path 0), vertex = source := by
      change ∀ᵐ vertex ∂(pathLaw transition (Measure.dirac source)).map (fun path => path 0), vertex = source
      rw [pathLaw_coordinate_zero]
      simp
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable mapped
  have testIntegrable : Integrable (fun path => values (path horizon)) law := by
    apply (integrable_const (1 : ℝ)).mono'
      (((measurable_of_countable values).comp (measurable_pi_apply horizon)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun path => by
      have bounds := continuousMetricBallCutoff_bounds center
        (parameters.vertexEmbedding (coarse + steps) (path horizon)) (2 * radius)
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by dsimp only [values]; linarith [bounds.1], bounds.2⟩)
  have expectationBound := continuousMetricBallCutoff_integral_ge_of_displacement law
    (parameters.vertexEmbedding (coarse + steps)) center radius radiusPositive source sourceNear
    sourceAtZero horizon bad
    (xiOriginCoarseDisplacementEvent_measurable system rulesConnected parameters coarse steps horizon count)
    (fun path displacement => by
      refine ⟨horizon, le_rfl, ?_⟩
      simpa only [Nat.zero_add] using displacement) testIntegrable
  have tail : law.real bad ≤ (1 / 4 : ℝ) := by
    exact tails coarse steps window windowNonnegative windowBound
      (⟨Measure.dirac source, inferInstance⟩ : ProbabilityMeasure (XiVtx system (coarse + steps)))
  have endpointIdentity := xiNativeSupTransition_pathLaw_endpoint_expectation system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent (coarse + steps) horizon values source
  change (∫ path, values (path horizon) ∂law) = _ at endpointIdentity
  change 1 - law.real bad ≤ (∫ path, values (path horizon) ∂law) at expectationBound
  rw [endpointIdentity] at expectationBound
  have quarterBound : (3 / 4 : ℝ) ≤ 1 - law.real bad := by linarith
  exact quarterBound.trans expectationBound

end
end EIGS

#print axioms EIGS.exists_xiNativeFloorCutoffExpectation_of_rules
