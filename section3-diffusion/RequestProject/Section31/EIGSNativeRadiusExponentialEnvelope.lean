import RequestProject.Section31.EIGSSingleWindowDisplacementTail
import RequestProject.Section31.IntegerCrossingRadiusTail

/-! A genuine arbitrary-radius exponential envelope for the actual native
finite walk. The crossing-probability estimate is supplied internally from
the original rules. Geometric scale optimization is a separate next step. -/

namespace EIGS
open MeasureTheory ProbabilityTheory IGS.Sec31
open scoped Classical
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiNativeMaximalDisplacementEvent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected)
    (level horizon : ℕ) (start : XiVtx system level) (radius : ℝ) :
    Set (ℕ → XiVtx system level) :=
  {path | ∃ index, index ≤ horizon ∧ radius ≤
    dist (parameters.vertexEmbedding level (path index)) (parameters.vertexEmbedding level start)}

theorem exists_xiNativeRadiusExponentialEnvelope_of_rules (system : EIGSData K)
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
    [∀ level, MeasurableSingletonClass (XiVtx system level)] :
    ∃ fraction decay : ℝ, 0 < fraction ∧ 0 < decay ∧ decay < 1 ∧
      ∀ (coarse steps : ℕ) (start : XiVtx system (coarse + steps))
        (radius window : ℝ), 0 < radius → 0 ≤ window →
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      ((xiGraphWalkPathLaw system rulesConnected (coarse + steps) start)
        (xiNativeMaximalDisplacementEvent system rulesConnected parameters (coarse + steps)
          ⌊xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊ start radius)).toReal ≤
        Real.exp (2 * (-Real.log decay) +
          window / (fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
            system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse) +
          Real.log decay * (radius / (4 * ((3 * xiRuleRadius system parameters.lengths + 1) *
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse)))) := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive,
      decayNonnegative, decayLessThanOne, tails⟩ :=
    exists_xiSingleWindowDisplacementTail_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  let decay := ((1 - probability * (1 - Real.exp (-1))) + 1) / 2
  have newDecayPositive : 0 < decay := by dsimp [decay]; linarith
  have newDecayLessThanOne : decay < 1 := by dsimp [decay]; linarith
  have oldDecayAtMost : 1 - probability * (1 - Real.exp (-1)) ≤ decay := by
    dsimp [decay]
    linarith
  refine ⟨fraction, decay, fractionPositive, newDecayPositive, newDecayLessThanOne, ?_⟩
  intro coarse steps start radius window radiusPositive windowNonnegative parameters
  let law := xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
  let horizon := Nat.floor (xiNativeFiniteJumpRate system (coarse + steps)
    (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window)
  let spatialScale := (3 * xiRuleRadius system parameters.lengths + 1) *
    (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse
  let timeScale := fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
    system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse
  haveI : IsProbabilityMeasure law := by dsimp [law, xiGraphWalkPathLaw]; infer_instance
  have distancePositiveRate : 0 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (0 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  have radiusNonnegative := xiRuleRadius_nonnegative system
    (fun colour => (parameters.lengthsPositive colour).le)
  have spatialScalePositive : 0 < spatialScale := by dsimp [spatialScale]; positivity
  have massPositive := (eigs_mass_spectral_growth system rulesConnected distancePositive).1
  have resistancePositive :=
    (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  have timeScalePositive : 0 < timeScale := by dsimp [timeScale]; positivity
  have crossingTail (count : ℕ) :
      law.real {path | ∃ index, index ≤ horizon ∧
        (count + 2 : ℝ) * spatialScale < dist (parameters.vertexEmbedding (coarse + steps) (path index))
          (parameters.vertexEmbedding (coarse + steps) start)} ≤
      Real.exp (window / timeScale) * decay ^ count := by
    have actual := tails coarse steps count start window windowNonnegative
    have enlarged := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ decayNonnegative oldDecayAtMost count)
      (Real.exp_pos (window / timeScale)).le
    have raw : law.real {path | ∃ index, index ≤ horizon ∧
        (count + 2 : ℝ) * spatialScale < dist (parameters.vertexEmbedding (coarse + steps) (path index))
          (parameters.vertexEmbedding (coarse + steps) start)} ≤
        Real.exp (window / timeScale) * (1 - probability * (1 - Real.exp (-1))) ^ count := by
      simpa only [law, horizon, spatialScale, timeScale, Measure.real,
        xiCoarseDisplacementEvent] using actual
    exact raw.trans enlarged
  exact radius_tail_le_crossing_exponential law
    (fun path index => parameters.vertexEmbedding (coarse + steps) (path index))
    (parameters.vertexEmbedding (coarse + steps) start) horizon radius spatialScale window timeScale decay
    radiusPositive spatialScalePositive windowNonnegative timeScalePositive
    newDecayPositive newDecayLessThanOne crossingTail

end
end EIGS

#print axioms EIGS.exists_xiNativeRadiusExponentialEnvelope_of_rules
