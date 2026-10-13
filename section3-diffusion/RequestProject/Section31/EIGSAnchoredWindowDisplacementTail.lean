import RequestProject.Section31.EIGSCompletedCoarseLaplaceIteration
import RequestProject.Section31.EIGSCoarseArrivalPathProbability
import RequestProject.Section31.DiscreteMarkovDeterministicShift

/-! Genuine natural-number anchored displacement tails for every initial
probability measure. The restarted law is the actual coordinate marginal,
identified by the homogeneous IFT deterministic-shift theorem. The horizon is
an arbitrary natural number, so subsequent differences of floor clocks retain
their full one-step correction. No strong Markov property is assumed. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

theorem finiteGraphPathLaw_ae_adjacent_of_probability (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree : ∀ vertex, 0 < graph.degree vertex)
    (initial : ProbabilityMeasure Vertex) (index : ℕ) :
    ∀ᵐ path ∂pathLaw (finiteGraphTransitionKernel graph degree) (initial : Measure Vertex),
      graph.Adj (path index) (path (index + 1)) := by
  have joint : ∀ᵐ pair ∂(pathLaw (finiteGraphTransitionKernel graph degree) (initial : Measure Vertex)).map
      (fun path => (frestrictLe index path, path (index + 1))),
      graph.Adj (pair.1 ⟨index, Finset.mem_Iic.mpr le_rfl⟩) pair.2 := by
    rw [pathLaw_history_endpoint_joint (finiteGraphTransitionKernel graph degree)
      (initial : Measure Vertex) index 1, pow_one]
    apply Measure.ae_compProd_of_ae_ae (Set.to_countable _).measurableSet
    apply Eventually.of_forall
    intro history
    change ∀ᵐ other ∂finiteGraphTransitionKernel graph degree
      (history ⟨index, Finset.mem_Iic.mpr le_rfl⟩),
      graph.Adj (history ⟨index, Finset.mem_Iic.mpr le_rfl⟩) other
    exact finiteGraphTransitionKernel_ae_adjacent graph degree _
  exact ae_of_ae_map
    ((measurable_frestrictLe index).prodMk (measurable_pi_apply (index + 1))).aemeasurable joint

variable {K : ℕ}

def xiAnchoredCoarseDisplacementEvent (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps anchor horizon count : ℕ) :
    Set (ℕ → XiVtx system (coarse + steps)) :=
  {path | ∃ index, index ≤ horizon ∧
    (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
      (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
      dist (parameters.vertexEmbedding (coarse + steps) (path (anchor + index)))
        (parameters.vertexEmbedding (coarse + steps) (path anchor))}

theorem xiAnchoredCoarseDisplacementEvent_eq_shift_preimage (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps anchor horizon count : ℕ) :
    xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps anchor horizon count =
      (shiftPath anchor) ⁻¹' xiAnchoredCoarseDisplacementEvent system rulesConnected parameters
        coarse steps 0 horizon count := by
  ext path
  simp only [xiAnchoredCoarseDisplacementEvent, Set.mem_preimage, Set.mem_setOf_eq,
    shiftPath, Nat.zero_add, Nat.add_zero]

theorem xiOriginCoarseDisplacementEvent_measurable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))] :
    MeasurableSet (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters
      coarse steps 0 horizon count) := by
  have eventEquality : xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps 0 horizon count =
      (frestrictLe horizon) ⁻¹' {history | ∃ index : Finset.Iic horizon,
        (count + 2 : ℝ) * ((3 * xiRuleRadius system parameters.lengths + 1) *
          (system.distanceSpectralRadius rulesConnected)⁻¹ ^ coarse) <
          dist (parameters.vertexEmbedding (coarse + steps) (history index))
            (parameters.vertexEmbedding (coarse + steps) (history ⟨0, Finset.mem_Iic.mpr (Nat.zero_le horizon)⟩))} := by
    ext path
    constructor
    · rintro ⟨index, bounded, displacement⟩
      exact ⟨⟨index, Finset.mem_Iic.mpr bounded⟩, by simpa only [Nat.zero_add] using displacement⟩
    · rintro ⟨index, displacement⟩
      exact ⟨index.val, Finset.mem_Iic.mp index.property, by simpa only [Nat.zero_add] using displacement⟩
  rw [eventEquality]
  exact (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe horizon)

theorem xiAnchoredCoarseDisplacementEvent_measurable (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (parameters : XiPathMetricData system rulesConnected) (coarse steps anchor horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))] :
    MeasurableSet (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters
      coarse steps anchor horizon count) := by
  rw [xiAnchoredCoarseDisplacementEvent_eq_shift_preimage]
  exact (xiOriginCoarseDisplacementEvent_measurable system rulesConnected parameters coarse steps horizon count).preimage
    (shiftPath_measurable anchor)

/-- The origin-window bound holds under every actual initial probability
measure. Adjacency is supplied by the actual IFT law internally. -/
theorem xiOriginWindowDisplacementTail_of_native_iteration (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (normalization fraction probability : ℝ) (coarse steps horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
    (iteration : XiNativeCoarseLaplaceIteration system rulesConnected distancePositive normalization fraction probability
      coarse steps initial) :
    let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
    ((pathLaw transition (initial : Measure _))
      (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps 0 horizon count)).toReal ≤
      Real.exp ((horizon : ℝ) /
        xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps) *
          (1 - probability * (1 - Real.exp (-1))) ^ count := by
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let actualLaw := pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))
  let skeleton := Finset.univ.image (xiForward system coarse steps)
  let scale := xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps
  obtain ⟨scalePositive, iterates, nativeTails⟩ := iteration
  have iterated : (∫ path, completedCoarseHitLaplace skeleton count (horizon + 1) scale path ∂actualLaw) ≤
      (1 - probability * (1 - Real.exp (-1))) ^ count := iterates count (horizon + 1)
  have completionTail := (completedCoarseHitEvent_probability_le_laplace actualLaw skeleton count horizon scale scalePositive).trans
    (mul_le_mul_of_nonneg_left iterated (Real.exp_pos _).le)
  have adjacency : ∀ᵐ path ∂actualLaw,
      ∀ index, (XiSimpleGraph system (coarse + steps)).Adj (path index) (path (index + 1)) := by
    exact ae_all_iff.mpr (fun index => finiteGraphPathLaw_ae_adjacent_of_probability
      (XiSimpleGraph system (coarse + steps))
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
      initial index)
  have geometry : actualLaw (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters
      coarse steps 0 horizon count) ≤ actualLaw (completedCoarseHitEvent skeleton count horizon) := by
    apply measure_mono_ae
    filter_upwards [adjacency] with path support
    intro displacement
    apply xiBoundedCoarseArrival_le_of_displacement system rulesConnected parameters rateGeTwo
      coarse steps path horizon count (fun index _ => support index)
    simpa only [xiAnchoredCoarseDisplacementEvent, Set.mem_setOf_eq, Nat.zero_add] using displacement
  exact (ENNReal.toReal_mono (measure_ne_top actualLaw _) geometry).trans completionTail

/-- Deterministic restart uses the actual coordinate marginal. There is no
stationarity assumption and no assumed strong Markov property. -/
theorem xiAnchoredWindowDisplacementTail_of_native_iteration (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (parameters : XiPathMetricData system rulesConnected)
    (rateGeTwo : 2 ≤ system.distanceSpectralRadius rulesConnected)
    (normalization fraction probability : ℝ) (coarse steps anchor horizon count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
    (allIteration : ∀ restarted : ProbabilityMeasure (XiVtx system (coarse + steps)),
      XiNativeCoarseLaplaceIteration system rulesConnected distancePositive normalization fraction probability
        coarse steps restarted) :
    let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
      (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
    ((pathLaw transition (initial : Measure _))
      (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps anchor horizon count)).toReal ≤
      Real.exp ((horizon : ℝ) /
        xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps) *
          (1 - probability * (1 - Real.exp (-1))) ^ count := by
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let restarted : ProbabilityMeasure (XiVtx system (coarse + steps)) :=
    ⟨(transition ^ anchor : Kernel _ _) ∘ₘ (initial : Measure _), inferInstance⟩
  have origin := xiOriginWindowDisplacementTail_of_native_iteration system rulesConnected distancePositive parameters rateGeTwo
    normalization fraction probability coarse steps horizon count restarted (allIteration restarted)
  change ((pathLaw transition (initial : Measure _))
    (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps anchor horizon count)).toReal ≤ _
  rw [xiAnchoredCoarseDisplacementEvent_eq_shift_preimage,
    pathLaw_shiftPath_event transition (initial : Measure _) anchor _
      (xiOriginCoarseDisplacementEvent_measurable system rulesConnected parameters coarse steps horizon count)]
  exact origin

/-- The actual natural-anchor, natural-horizon maximal displacement estimate,
with all probability and geometry inputs filled from the original rules. -/
theorem exists_xiAnchoredWindowDisplacementTail_of_rules (system : EIGSData K)
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
      ∀ (coarse steps anchor horizon count : ℕ)
      (initial : ProbabilityMeasure (XiVtx system (coarse + steps))),
      let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
      let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
      ((pathLaw transition (initial : Measure _))
        (xiAnchoredCoarseDisplacementEvent system rulesConnected parameters coarse steps anchor horizon count)).toReal ≤
        Real.exp ((horizon : ℝ) /
          xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps) *
            (1 - probability * (1 - Real.exp (-1))) ^ count := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, iteration⟩ :=
    exists_xiNativeCoarseLaplaceIteration_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive normalization normalizationPositive
  refine ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, ?_⟩
  intro coarse steps anchor horizon count initial parameters transition
  exact xiAnchoredWindowDisplacementTail_of_native_iteration system rulesConnected distancePositive parameters
    (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    normalization fraction probability coarse steps anchor horizon count initial (iteration coarse steps)

end
end EIGS

#print axioms EIGS.finiteGraphPathLaw_ae_adjacent_of_probability
#print axioms EIGS.xiAnchoredCoarseDisplacementEvent_measurable
#print axioms EIGS.xiOriginWindowDisplacementTail_of_native_iteration
#print axioms EIGS.xiAnchoredWindowDisplacementTail_of_native_iteration
#print axioms EIGS.exists_xiAnchoredWindowDisplacementTail_of_rules
