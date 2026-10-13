import RequestProject.Section31.EIGSCompletedCoarseLaplaceContraction
import RequestProject.Section31.EIGSNativeStarSurvival

/-! Actual repeated completed coarse-hit Laplace weights and finite-horizon
probability tails. Arrival k is coarse arrival number k+1. The initial completed
weight is only bounded by one; arbitrary initial points are permitted. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

theorem completedCoarseHitLaplace_integral_le_pow (measure : Measure (ℕ → X))
    [IsProbabilityMeasure measure] (coarse : Finset X) (cap : ℕ) (scale decay : ℝ)
    (scalePositive : 0 < scale) (decayNonnegative : 0 ≤ decay)
    (contraction : ∀ arrival : ℕ,
      (∫ path, completedCoarseHitLaplace coarse (arrival + 1) cap scale path ∂measure) ≤
        decay * ∫ path, completedCoarseHitLaplace coarse arrival cap scale path ∂measure)
    (arrival : ℕ) :
    (∫ path, completedCoarseHitLaplace coarse arrival cap scale path ∂measure) ≤ decay ^ arrival := by
  induction arrival with
  | zero =>
    calc
      _ ≤ ∫ _path, (1 : ℝ) ∂measure :=
        integral_mono (completedCoarseHitLaplace_integrable measure coarse 0 cap scale)
          (integrable_const 1) (completedCoarseHitLaplace_le_one coarse 0 cap scale scalePositive)
      _ = _ := by simp
  | succ arrival inductionHypothesis =>
    calc
      _ ≤ decay * ∫ path, completedCoarseHitLaplace coarse arrival cap scale path ∂measure := contraction arrival
      _ ≤ decay * decay ^ arrival := mul_le_mul_of_nonneg_left inductionHypothesis decayNonnegative
      _ = _ := by rw [pow_succ]; ring

def completedCoarseHitEvent (coarse : Finset X) (arrival time : ℕ) : Set (ℕ → X) :=
  {path | ((boundedCoarseArrival coarse arrival (time + 1)).time path).val ≤ time}

theorem completedCoarseHitEvent_measurable (coarse : Finset X) (arrival time : ℕ) :
    MeasurableSet (completedCoarseHitEvent coarse arrival time) := by
  have eventEquality : completedCoarseHitEvent coarse arrival time =
      (frestrictLe time) ⁻¹' {history | arrival + 1 ≤ (coarseArrivalHistory coarse time history).2} := by
    ext path
    change ((boundedCoarseArrival coarse arrival (time + 1)).time path).val ≤ time ↔
      arrival + 1 ≤ (coarseArrivalHistory coarse time (frestrictLe time path)).2
    rw [coarseArrivalHistory_restrict]
    exact boundedCoarseArrival_le_iff coarse arrival (time + 1) time (Nat.lt_succ_self time) path
  rw [eventEquality]
  exact (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe time)

theorem completedCoarseHitEvent_indicator_le_laplace (coarse : Finset X) (arrival time : ℕ)
    (scale : ℝ) (scalePositive : 0 < scale) (path : ℕ → X) :
    (completedCoarseHitEvent coarse arrival time).indicator (fun _ => (1 : ℝ)) path ≤
      Real.exp ((time : ℝ) / scale) * completedCoarseHitLaplace coarse arrival (time + 1) scale path := by
  by_cases completed : path ∈ completedCoarseHitEvent coarse arrival time
  · rw [Set.indicator_of_mem completed]
    have bounded : ((boundedCoarseArrival coarse arrival (time + 1)).time path).val ≤ time := completed
    have beforeCap : ((boundedCoarseArrival coarse arrival (time + 1)).time path).val < time + 1 :=
      Nat.lt_succ_of_le bounded
    rw [completedCoarseHitLaplace, if_pos beforeCap, ← Real.exp_add, Real.one_le_exp_iff]
    have castBound : (((boundedCoarseArrival coarse arrival (time + 1)).time path).val : ℝ) ≤ (time : ℝ) := by
      exact_mod_cast bounded
    have divided := div_le_div_of_nonneg_right castBound scalePositive.le
    rw [neg_div]
    linarith
  · rw [Set.indicator_of_notMem completed]
    exact mul_nonneg (Real.exp_pos _).le
      (completedCoarseHitLaplace_nonnegative coarse arrival (time + 1) scale path)

theorem completedCoarseHitEvent_probability_le_laplace (measure : Measure (ℕ → X))
    [IsProbabilityMeasure measure] (coarse : Finset X) (arrival time : ℕ)
    (scale : ℝ) (scalePositive : 0 < scale) :
    (measure (completedCoarseHitEvent coarse arrival time)).toReal ≤
      Real.exp ((time : ℝ) / scale) *
        ∫ path, completedCoarseHitLaplace coarse arrival (time + 1) scale path ∂measure := by
  have indicatorIntegral :
      (∫ path, (completedCoarseHitEvent coarse arrival time).indicator (fun _ => (1 : ℝ)) path ∂measure) =
        (measure (completedCoarseHitEvent coarse arrival time)).toReal := by
    simpa only [smul_eq_mul, mul_one, measureReal_def] using
      (integral_indicator_const (μ := measure) (1 : ℝ) (completedCoarseHitEvent_measurable coarse arrival time))
  rw [← indicatorIntegral, ← integral_const_mul]
  apply integral_mono
  · exact (integrable_const (1 : ℝ)).indicator (completedCoarseHitEvent_measurable coarse arrival time)
  · exact (completedCoarseHitLaplace_integrable measure coarse arrival (time + 1) scale).const_mul _
  · exact completedCoarseHitEvent_indicator_le_laplace coarse arrival time scale scalePositive

theorem completedCoarseHitEvent_probability_le_pow (measure : Measure (ℕ → X))
    [IsProbabilityMeasure measure] (coarse : Finset X) (arrival time : ℕ) (scale decay : ℝ)
    (scalePositive : 0 < scale) (decayNonnegative : 0 ≤ decay)
    (contraction : ∀ index : ℕ,
      (∫ path, completedCoarseHitLaplace coarse (index + 1) (time + 1) scale path ∂measure) ≤
        decay * ∫ path, completedCoarseHitLaplace coarse index (time + 1) scale path ∂measure) :
    (measure (completedCoarseHitEvent coarse arrival time)).toReal ≤
      Real.exp ((time : ℝ) / scale) * decay ^ arrival := by
  exact (completedCoarseHitEvent_probability_le_laplace measure coarse arrival time scale scalePositive).trans
    (mul_le_mul_of_nonneg_left
      (completedCoarseHitLaplace_integral_le_pow measure coarse (time + 1) scale decay scalePositive
        decayNonnegative contraction arrival) (Real.exp_pos _).le)

theorem floor_native_clock_ratio_le (jumpRate fraction spatial window : ℝ)
    (ratePositive : 0 < jumpRate) (fractionPositive : 0 < fraction)
    (spatialPositive : 0 < spatial) (windowNonnegative : 0 ≤ window) :
    (⌊jumpRate * window⌋₊ : ℝ) / (jumpRate * fraction * spatial) ≤ window / (fraction * spatial) := by
  have scalePositive : 0 < jumpRate * fraction * spatial := by positivity
  calc
    _ ≤ (jumpRate * window) / (jumpRate * fraction * spatial) :=
      div_le_div_of_nonneg_right (Nat.floor_le (mul_nonneg ratePositive.le windowNonnegative)) scalePositive.le
    _ = _ := by field_simp [ratePositive.ne', fractionPositive.ne', spatialPositive.ne']

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000
variable {K : ℕ}

def xiCoarseNativeLaplaceScale (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization fraction : ℝ) (coarse steps : ℕ) : ℝ :=
  xiNativeFiniteJumpRate system (coarse + steps)
      (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * fraction *
    (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
      system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse

theorem xiCoarseNativeLaplaceScale_positive (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization fraction : ℝ) (normalizationPositive : 0 < normalization)
    (fractionPositive : 0 < fraction) (coarse steps : ℕ) :
    0 < xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps := by
  obtain ⟨massRatePositive, massLower, massUpper, massLowerPositive, massUpperPositive, growth⟩ :=
    eigs_mass_spectral_growth system rulesConnected distancePositive
  have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
  have edgePositive : 0 < (totalEdges system.toRuleData (coarse + steps) : ℝ) :=
    (mul_pos massLowerPositive (pow_pos massRatePositive (coarse + steps))).trans_le (growth (coarse + steps)).1
  unfold xiCoarseNativeLaplaceScale xiNativeFiniteJumpRate
  positivity

/-- This conclusion concerns the genuine graph path law at the actual clock.
It includes all completed-weight iterates and the probability of completing
coarse arrival k+1 by the floor of the scaled observation time. -/
def XiNativeCoarseLaplaceIteration (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (normalization fraction probability : ℝ) (coarse steps : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps))) : Prop :=
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let scale := xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps
  0 < scale ∧
    (∀ arrival cap : ℕ,
      (∫ path, completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps))
        arrival cap scale path ∂pathLaw transition (initial : Measure _)) ≤
        (1 - probability * (1 - Real.exp (-1))) ^ arrival) ∧
    ∀ (arrival : ℕ) (window : ℝ), 0 ≤ window →
      ((pathLaw transition (initial : Measure _))
        (completedCoarseHitEvent (Finset.univ.image (xiForward system coarse steps)) arrival
          ⌊xiNativeFiniteJumpRate system (coarse + steps)
            (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊)).toReal ≤
        Real.exp (window / (fraction * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
          system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse)) *
            (1 - probability * (1 - Real.exp (-1))) ^ arrival

/-- Actual repeated-stopping contraction and completion tails from the five
original rule assumptions. The count is floor(actual real scale), including
zero. No contraction, regeneration or conditional tail bound is assumed. -/
theorem exists_xiNativeCoarseLaplaceIteration_of_rules (system : EIGSData K)
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
      ∀ (coarse steps : ℕ) (initial : ProbabilityMeasure (XiVtx system (coarse + steps))),
        XiNativeCoarseLaplaceIteration system rulesConnected distancePositive normalization fraction probability
          coarse steps initial := by
  obtain ⟨fraction, probability, fractionPositive, probabilityPositive, nativeSurvival⟩ :=
    xiIncidentStarDomain_native_clock_positive_survival system rulesConnected distancePositive
      normalization normalizationPositive rulesLoopless rulesUnique plantingNonadjacent
  have probabilityBound : probability ≤ 1 :=
    (nativeSurvival 0 0 (xiPositiveTerminal system 0)).trans (surv_le_one _ _)
  have decayNonnegative := exit_laplace_contraction_nonnegative probability probabilityPositive.le probabilityBound
  have decayLessThanOne := exit_laplace_contraction_lt_one probability probabilityPositive
  refine ⟨fraction, probability, fractionPositive, probabilityPositive, decayNonnegative, decayLessThanOne, ?_⟩
  intro coarse steps initial
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let actualLaw := pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))
  let skeleton := Finset.univ.image (xiForward system coarse steps)
  let scale := xiCoarseNativeLaplaceScale system rulesConnected distancePositive normalization fraction coarse steps
  have scalePositive : 0 < scale :=
    xiCoarseNativeLaplaceScale_positive system rulesConnected distancePositive normalization fraction
      normalizationPositive fractionPositive coarse steps
  have scaleBound : scale ≤ ((⌊scale⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one scale).le
  have contraction (arrival cap : ℕ) :
      (∫ path, completedCoarseHitLaplace skeleton (arrival + 1) cap scale path ∂actualLaw) ≤
        (1 - probability * (1 - Real.exp (-1))) *
          ∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw := by
    have stay := xiCoarseArrival_weighted_stay_of_survival system rulesConnected coarse steps ⌊scale⌋₊ arrival cap
      initial (fun index _history => Real.exp (-(index.val : ℝ) / scale))
      (fun index _history => (Real.exp_pos _).le) probability probabilityBound (nativeSurvival coarse steps)
    exact xiCompletedCoarseLaplace_contraction_of_weighted_stay system rulesConnected coarse steps ⌊scale⌋₊ arrival cap
      scale scalePositive scaleBound initial probability stay
  change 0 < scale ∧ (∀ arrival cap : ℕ,
      (∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw) ≤
        (1 - probability * (1 - Real.exp (-1))) ^ arrival) ∧ _
  refine ⟨scalePositive, ?_, ?_⟩
  · intro arrival cap
    exact completedCoarseHitLaplace_integral_le_pow actualLaw skeleton cap scale _ scalePositive decayNonnegative
      (fun index => contraction index cap) arrival
  · intro arrival window windowNonnegative
    have resistancePositive := (system.resistanceSpectralRadius_positive_eigenpair rulesConnected distancePositive).1
    have timeRatePositive := mul_pos (eigs_mass_spectral_growth system rulesConnected distancePositive).1 resistancePositive
    have spatialPositive : 0 < (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive)⁻¹ ^ coarse := by positivity
    have jumpPositive : 0 < xiNativeFiniteJumpRate system (coarse + steps)
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization := by
      have productPositive : 0 < xiNativeFiniteJumpRate system (coarse + steps)
          (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * fraction :=
        (mul_pos_iff_of_pos_right spatialPositive).mp scalePositive
      exact (mul_pos_iff_of_pos_right fractionPositive).mp productPositive
    have tail := completedCoarseHitEvent_probability_le_pow actualLaw skeleton arrival
      ⌊xiNativeFiniteJumpRate system (coarse + steps)
        (system.resistanceSpectralRadius rulesConnected distancePositive) normalization * window⌋₊
      scale _ scalePositive decayNonnegative (fun index => contraction index _)
    apply tail.trans
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg decayNonnegative arrival)
    apply Real.exp_le_exp.mpr
    exact floor_native_clock_ratio_le _ fraction _ window jumpPositive fractionPositive spatialPositive windowNonnegative

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_integral_le_pow
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitEvent_probability_le_pow
#print axioms IGS.Sec31.DiscreteMarkov.floor_native_clock_ratio_le
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitEvent_measurable
#print axioms EIGS.xiCoarseNativeLaplaceScale_positive
#print axioms EIGS.exists_xiNativeCoarseLaplaceIteration_of_rules
