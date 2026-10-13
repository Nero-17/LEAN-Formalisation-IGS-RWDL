import RequestProject.Section31.BoundedCoarseHittingStops
import RequestProject.Section31.EIGSAllStartStarSurvival
import RequestProject.Section31.FiniteGraphSurvivalPathLaw

/-! A genuine whole-future-block survival lower bound after the actual capped
coarse hitting stops. The original rule hypotheses supply the Dirac-start star
survival estimate. No regeneration or conditional tail bound is assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
noncomputable section

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

theorem boundedCoarseArrival_history_last_mem (coarse : Finset X) (arrival cap : ℕ)
    (index : Fin (cap + 1)) (history : Finset.Iic index.val → X)
    (belongs : history ∈ (boundedCoarseArrival coarse arrival cap).historyEvent index)
    (beforeCap : index.val < cap) :
    history ⟨index.val, Finset.mem_Iic.mpr le_rfl⟩ ∈ coarse := by
  have historyPrefix : frestrictLe index.val (completedHistory history) = history := by
    funext entry
    simp only [frestrictLe_apply, completedHistory,
      dif_pos (Finset.mem_Iic.mp entry.property)]
  have hit : (boundedCoarseArrival coarse arrival cap).time (completedHistory history) = index := by
    apply ((boundedCoarseArrival coarse arrival cap).level_iff index _).mpr
    rwa [historyPrefix]
  have stopped := (boundedCoarseArrival_is_coarse coarse arrival cap (completedHistory history)
    (by rw [hit]; exact beforeCap)).1
  rw [hit] at stopped
  simpa only [completedHistory, dif_pos le_rfl] using stopped

def uncappedHistoryWeight {cap : ℕ}
    (weight : (index : Fin (cap + 1)) → (Finset.Iic index.val → X) → ℝ)
    (index : Fin (cap + 1)) (history : Finset.Iic index.val → X) : ℝ :=
  if index.val < cap then weight index history else 0

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

def xiCoarseStarStayTest (system : EIGSData K) (coarse steps count : ℕ)
    (block : Finset.Iic count → XiVtx system (coarse + steps)) : ℝ :=
  if ∃ center : XiVtx system coarse,
      block ⟨0, Finset.mem_Iic.mpr (Nat.zero_le count)⟩ = xiForward system coarse steps center ∧
      ∀ index, block index ∈ xiIncidentStarDomain system coarse steps center then 1 else 0

theorem xiCoarseStarStayTest_nonnegative (system : EIGSData K) (coarse steps count : ℕ)
    (block : Finset.Iic count → XiVtx system (coarse + steps)) :
    0 ≤ xiCoarseStarStayTest system coarse steps count block := by
  unfold xiCoarseStarStayTest
  split_ifs <;> norm_num

/-- The whole-block stay test dominates actual star survival under the actual
Dirac-start walk. Its initial coordinate is proved correct almost surely. -/
theorem xiCoarseStarStayTest_dirac_integral_ge_surv (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps count : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (center : XiVtx system coarse) :
    surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) count (xiForward system coarse steps center) ≤
      ∫ continuation, xiCoarseStarStayTest system coarse steps count (frestrictLe count continuation)
        ∂pathLaw (finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
          (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))) (Measure.dirac (xiForward system coarse steps center)) := by
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let actualLaw := pathLaw transition (Measure.dirac (xiForward system coarse steps center))
  have starts : ∀ᵐ continuation ∂actualLaw,
      continuation 0 = xiForward system coarse steps center := by
    have projected : ∀ᵐ point ∂actualLaw.map (fun continuation => continuation 0),
        point = xiForward system coarse steps center := by
      dsimp only [actualLaw]
      rw [pathLaw_coordinate_zero]
      simp
    exact ae_of_ae_map (measurable_pi_apply 0).aemeasurable projected
  have survivalIntegral :
      (∫ continuation, (graphSurvivalEvent (xiIncidentStarDomain system coarse steps center) count).indicator
        (fun _ => (1 : ℝ)) continuation ∂actualLaw) =
      surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) count (xiForward system coarse steps center) := by
    calc
      _ = (actualLaw (graphSurvivalEvent (xiIncidentStarDomain system coarse steps center) count)).toReal := by
        simpa only [smul_eq_mul, mul_one, measureReal_def] using
          (integral_indicator_const (μ := actualLaw) (1 : ℝ)
            (graphSurvivalEvent_measurable (xiIncidentStarDomain system coarse steps center) count))
      _ = _ := graphSurvivalEvent_probability (XiSimpleGraph system (coarse + steps))
        (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex)) (xiIncidentStarDomain system coarse steps center) count
        (xiForward system coarse steps center)
  rw [← survivalIntegral]
  apply integral_mono_ae
  · exact (integrable_const (1 : ℝ)).indicator
      (graphSurvivalEvent_measurable (xiIncidentStarDomain system coarse steps center) count)
  · exact finite_observable_integrable
      (X := XiVtx system (coarse + steps)) (Y := Finset.Iic count → XiVtx system (coarse + steps))
      actualLaw (frestrictLe count) (measurable_frestrictLe count)
      (xiCoarseStarStayTest system coarse steps count)
  · filter_upwards [starts] with continuation start
    by_cases survives : continuation ∈ graphSurvivalEvent (xiIncidentStarDomain system coarse steps center) count
    · rw [Set.indicator_of_mem survives]
      have stays : ∃ original : XiVtx system coarse,
          (frestrictLe count continuation) ⟨0, Finset.mem_Iic.mpr (Nat.zero_le count)⟩ =
            xiForward system coarse steps original ∧
          ∀ index, (frestrictLe count continuation) index ∈ xiIncidentStarDomain system coarse steps original := by
        exact ⟨center, start, fun index => survives index.val (Finset.mem_Iic.mp index.property)⟩
      rw [xiCoarseStarStayTest, if_pos stays]
    · rw [Set.indicator_of_notMem survives]
      exact xiCoarseStarStayTest_nonnegative system coarse steps count _

/-- This transparent conclusion contains only the actual graph IFT law, actual
coarse hit scanner and the whole future-block star-stay test. The cap sentinel
has zero past weight and therefore is not counted as a completed hit. -/
def XiCoarseArrivalStayExpectationBound (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps count arrival cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
    (weight : (index : Fin (cap + 1)) → (Finset.Iic index.val → XiVtx system (coarse + steps)) → ℝ)
    (probability : ℝ) : Prop :=
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let coarseStop := boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps)) arrival cap
  probability * (∫ path,
    uncappedHistoryWeight weight (coarseStop.time path) (frestrictLe (coarseStop.time path).val path)
      ∂pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))) ≤
    ∫ path, uncappedHistoryWeight weight (coarseStop.time path)
      (frestrictLe (coarseStop.time path).val path) *
      xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path)
      ∂pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))

theorem xiCoarseArrival_weighted_stay_of_survival (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps count arrival cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
    (weight : (index : Fin (cap + 1)) → (Finset.Iic index.val → XiVtx system (coarse + steps)) → ℝ)
    (weightNonnegative : ∀ index history, 0 ≤ weight index history)
    (probability : ℝ) (probabilityBound : probability ≤ 1)
    (survivalLower : ∀ center : XiVtx system coarse,
      probability ≤ surv (XiSimpleGraph system (coarse + steps))
        (xiIncidentStarDomain system coarse steps center) count (xiForward system coarse steps center)) :
    XiCoarseArrivalStayExpectationBound system rulesConnected coarse steps count arrival cap initial weight probability := by
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let coarseStop := boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps)) arrival cap
  have lower := boundedStopping_weighted_future_ge transition initial coarseStop count
    (uncappedHistoryWeight weight)
    (fun index block => if index.val < cap then xiCoarseStarStayTest system coarse steps count block else 1)
    probability (by
      intro index history _
      unfold uncappedHistoryWeight
      split_ifs
      · exact weightNonnegative index history
      · exact le_rfl) (by
      intro index history belongs
      by_cases beforeCap : index.val < cap
      · simp only [if_pos beforeCap]
        have coarsePoint := boundedCoarseArrival_history_last_mem
          (Finset.univ.image (xiForward system coarse steps)) arrival cap index history belongs beforeCap
        obtain ⟨center, _, centerEquality⟩ := Finset.mem_image.mp coarsePoint
        rw [← centerEquality]
        exact (survivalLower center).trans
          (xiCoarseStarStayTest_dirac_integral_ge_surv system rulesConnected coarse steps count center)
      · simp only [if_neg beforeCap]
        simpa using probabilityBound)
  change probability * (∫ path, uncappedHistoryWeight weight (coarseStop.time path)
      (frestrictLe (coarseStop.time path).val path) ∂pathLaw transition (initial : Measure _)) ≤ _
  convert lower using 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro path
  dsimp only
  change uncappedHistoryWeight weight (coarseStop.time path)
      (frestrictLe (coarseStop.time path).val path) *
      xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path) =
    uncappedHistoryWeight weight (coarseStop.time path)
      (frestrictLe (coarseStop.time path).val path) *
      (if (coarseStop.time path).val < cap then
        xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path) else 1)
  by_cases beforeCap : (coarseStop.time path).val < cap
  · simp only [if_pos beforeCap]
  · simp only [uncappedHistoryWeight, if_neg beforeCap, zero_mul]

/-- Original rule hypotheses supply a uniform positive whole-block survival
probability after every completed actual coarse arrival, for every initial law
and every nonnegative stopped-history weight. There is no regeneration or tail
bound hypothesis in this consumer. -/
theorem exists_xiCoarseArrival_weighted_star_survival_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    [∀ level, MeasurableSpace (XiVtx system level)]
    [∀ level, MeasurableSingletonClass (XiVtx system level)] :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ lower / (2 * upper) ≤ 1 ∧
      ∀ (coarse steps count arrival cap : ℕ)
      (initial : ProbabilityMeasure (XiVtx system (coarse + steps)))
      (weight : (index : Fin (cap + 1)) → (Finset.Iic index.val → XiVtx system (coarse + steps)) → ℝ),
      (∀ index history, 0 ≤ weight index history) →
      (count : ℝ) ≤ lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps / 2 →
      XiCoarseArrivalStayExpectationBound system rulesConnected coarse steps count arrival cap initial weight
        (lower / (2 * upper)) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, survivalLower⟩ :=
    xiIncidentStarDomain_uniform_positive_survival system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have probabilityBound : lower / (2 * upper) ≤ 1 := by
    have zeroTime : (0 : ℝ) ≤ lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ 0 / 2 := by
      simp only [pow_zero, mul_one]
      positivity
    exact (survivalLower 0 0 (xiPositiveTerminal system 0) 0
      (by simpa only [Nat.cast_zero] using zeroTime)).trans
      (surv_le_one 0 (xiForward system 0 0 (xiPositiveTerminal system 0)))
  refine ⟨lower, upper, lowerPositive, upperPositive, probabilityBound, ?_⟩
  intro coarse steps count arrival cap initial weight weightNonnegative timeBound
  exact xiCoarseArrival_weighted_stay_of_survival system rulesConnected coarse steps count arrival cap
    initial weight weightNonnegative (lower / (2 * upper)) probabilityBound
    (fun center => survivalLower coarse steps center count timeBound)

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.boundedCoarseArrival_history_last_mem
#print axioms EIGS.xiCoarseStarStayTest_dirac_integral_ge_surv
#print axioms EIGS.xiCoarseArrival_weighted_stay_of_survival
#print axioms EIGS.exists_xiCoarseArrival_weighted_star_survival_of_rules
