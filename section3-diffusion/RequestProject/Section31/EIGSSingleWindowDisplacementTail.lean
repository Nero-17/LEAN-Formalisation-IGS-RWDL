import RequestProject.Section31.EIGSCompletedCoarseLaplaceIteration
import RequestProject.Section31.EIGSCoarseArrivalPathProbability

/-! A single-window maximal displacement tail for the actual discrete graph
walk, at its literal floor clock and in the same canonical completion metric.
The original-rule consumer supplies both the probability and geometric inputs
internally. This is not a full-horizon modulus or a path convergence theorem. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

def xiCoarseDisplacementEvent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps horizon count : ℕ)
    (start : XiVtx system (coarse + steps)) : Set (ℕ → XiVtx system (coarse + steps)) :=
  {path | ∃ time, time ≤ horizon ∧
    (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
      dist (parameters.vertexEmbedding (coarse + steps) (path time))
        (parameters.vertexEmbedding (coarse + steps) start)}

theorem xiCoarseDisplacementEvent_measurable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (start : XiVtx system (coarse + steps)) :
    MeasurableSet (xiCoarseDisplacementEvent system rulesConnected parameters coarse steps horizon count start) := by
  have eventEquality : xiCoarseDisplacementEvent system rulesConnected parameters coarse steps horizon count start =
      (frestrictLe horizon) ⁻¹' {history | ∃ time : Finset.Iic horizon,
        (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
          dist (parameters.vertexEmbedding (coarse + steps) (history time))
            (parameters.vertexEmbedding (coarse + steps) start)} := by
    ext path
    constructor
    · rintro ⟨time, bounded, displacement⟩
      exact ⟨⟨time, Finset.mem_Iic.mpr bounded⟩, displacement⟩
    · rintro ⟨time, displacement⟩
      exact ⟨time.val, Finset.mem_Iic.mp time.property, displacement⟩
  rw [eventEquality]
  exact (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe horizon)

theorem xiGraphWalkPathLaw_displacement_anchor_eq (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (start : XiVtx system (coarse + steps)) :
    xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
        (xiCoarseDisplacementEvent system rulesConnected parameters coarse steps horizon count start) =
      xiGraphWalkPathLaw system rulesConnected (coarse + steps) start
        {path | ∃ time, time ≤ horizon ∧
          (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
            (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
          dist (parameters.vertexEmbedding (coarse + steps) (path time))
            (parameters.vertexEmbedding (coarse + steps) (path 0))} := by
  have starts := finiteGraphPathLaw_ae_start (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)) start
  apply measure_congr
  filter_upwards [starts] with path started
  apply propext
  change (∃ time, time ≤ horizon ∧
    (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
      dist (parameters.vertexEmbedding (coarse + steps) (path time))
        (parameters.vertexEmbedding (coarse + steps) start)) ↔
    (∃ time, time ≤ horizon ∧
      (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
        (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
        dist (parameters.vertexEmbedding (coarse + steps) (path time))
          (parameters.vertexEmbedding (coarse + steps) (path 0)))
  rw [started]

/-- The raw helper combines the actual completion tail and actual geometric
event inclusion. The path laws are identified by their genuine definitions. -/
theorem xiSingleWindowDisplacementTail_of_native_iteration (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (normalization fraction probability : ℝ) (coarse steps count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (start : XiVtx system (coarse + steps)) (window : ℝ) (windowNonnegative : 0 ≤ window)
    (iteration : XiNativeCoarseLaplaceIteration system rulesConnected distancePositive normalization fraction probability
      coarse steps (⟨Measure.dirac start, inferInstance⟩ : ProbabilityMeasure (XiVtx system (coarse + steps)))) :
    ((xiGraphWalkPathLaw system rulesConnected (coarse + steps) start)
      (xiCoarseDisplacementEvent system rulesConnected parameters coarse steps
        ⌊xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊ count start)).toReal ≤
      Real.exp (window / (fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) *
          (1 - probability * (1 - Real.exp (-1))) ^ count := by
  letI : IsProbabilityMeasure (xiGraphWalkPathLaw system rulesConnected (coarse + steps) start) := by
    unfold xiGraphWalkPathLaw
    infer_instance
  obtain ⟨scalePositive, iterates, tails⟩ := iteration
  have tail := tails count window windowNonnegative
  have geometry := xiGraphWalkPathLaw_displacement_le_coarse_hit system rulesConnected parameters rateGeTwo
    coarse steps start
    ⌊xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊ count
  rw [xiGraphWalkPathLaw_displacement_anchor_eq] 
  have realGeometry := ENNReal.toReal_mono (measure_ne_top _ _) geometry
  change ((xiGraphWalkPathLaw system rulesConnected (coarse + steps) start)
      (completedCoarseHitEvent (Finset.univ.image (xiForward system coarse steps)) count
        ⌊xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊)).toReal ≤ _ at tail
  exact realGeometry.trans tail

/-- A genuine one-window probability-of-sup tail, uniformly in the fine start.
Both the canonical completion metric and the actual probability estimate are
supplied from the five original rule assumptions. -/
theorem exists_xiSingleWindowDisplacementTail_of_rules (system : EIGSData K)
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
    ∃ fraction probability : ℝ, 0 < fraction ∧ 0 < probability ∧
      0 ≤ 1 - probability * (1 - Real.exp (-1)) ∧
      1 - probability * (1 - Real.exp (-1)) < 1 ∧
      ∀ (coarse steps count : ℕ) (start : XiVtx system (coarse + steps)) (window : ℝ),
      0 ≤ window →
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      ((xiGraphWalkPathLaw system rulesConnected (coarse + steps) start)
        (xiCoarseDisplacementEvent system rulesConnected parameters coarse steps
          ⌊xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊ count start)).toReal ≤
        Real.exp (window / (fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) *
            (1 - probability * (1 - Real.exp (-1))) ^ count := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, iteration⟩ :=
    exists_xiNativeCoarseLaplaceIteration_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  refine ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, ?_⟩
  intro coarse steps count start window windowNonnegative parameters
  exact xiSingleWindowDisplacementTail_of_native_iteration system rulesConnected distancePositive parameters
    (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    normalization fraction probability coarse steps count start window windowNonnegative
    (iteration coarse steps (⟨Measure.dirac start, inferInstance⟩ : ProbabilityMeasure (XiVtx system (coarse + steps))))

end
end EIGS

#print axioms EIGS.xiCoarseDisplacementEvent_measurable
#print axioms EIGS.xiGraphWalkPathLaw_displacement_anchor_eq
#print axioms EIGS.xiSingleWindowDisplacementTail_of_native_iteration
#print axioms EIGS.exists_xiSingleWindowDisplacementTail_of_rules
