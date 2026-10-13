import RequestProject.Section31.CompletedCoarseHitLaplace
import RequestProject.Section31.EIGSCoarseArrivalStarSurvival
import RequestProject.Section31.EIGSIncidentStarBoundaryLocalization
import RequestProject.Section31.FiniteExitLaplaceBound

/-! The single-step contraction of actual completed coarse-hit Laplace weights.
The real scale is positive and at most one plus the survival count. Cap noncompletion has
weight zero throughout. The original-rule consumer fills the actual weighted
whole-future-block survival lower bound internally. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [DecidableEq X]
    [MeasurableSpace X] [MeasurableSingletonClass X]

theorem stopped_history_future_integrable (measure : Measure (ℕ → X)) [IsFiniteMeasure measure]
    {cap : ℕ} (stop : BoundedHistoryStop (X := X) cap) (count : ℕ)
    (past : (index : Fin (cap + 1)) → (Finset.Iic index.val → X) → ℝ)
    (future : Fin (cap + 1) → (Finset.Iic count → X) → ℝ) :
    Integrable (fun path => past (stop.time path) (frestrictLe (stop.time path).val path) *
      future (stop.time path) (futurePrefix (stop.time path).val count path)) measure := by
  have summand (index : Fin (cap + 1)) : Integrable
      (fun path => (stop.historyEvent index).indicator
        (fun history => past index history * future index (futurePrefix index.val count path))
        (frestrictLe index.val path)) measure := by
    exact finite_observable_integrable measure
      (fun path => (frestrictLe index.val path, futurePrefix index.val count path))
      ((measurable_frestrictLe index.val).prodMk (futurePrefix_measurable index.val count))
      (fun pair => (stop.historyEvent index).indicator
        (fun history => past index history * future index pair.2) pair.1)
  have sumIntegrable := integrable_finset_sum Finset.univ (fun index _ => summand index)
  apply sumIntegrable.congr
  apply Eventually.of_forall
  intro path
  dsimp only
  rw [Finset.sum_eq_single (stop.time path)]
  · rw [Set.indicator_of_mem ((stop.level_iff (stop.time path) path).mp rfl)]
  · intro index _ different
    exact Set.indicator_of_notMem
      (fun belongs => different ((stop.level_iff index path).mpr belongs).symm) _
  · simp

theorem completedCoarseHitLaplace_integrable (measure : Measure (ℕ → X)) [IsFiniteMeasure measure]
    (coarse : Finset X) (arrival cap : ℕ) (scale : ℝ) :
    Integrable (completedCoarseHitLaplace coarse arrival cap scale) measure := by
  have represented := stopped_history_future_integrable measure (boundedCoarseArrival coarse arrival cap)
    0 (completedCoarseHitPastWeight scale) (fun _ _ => 1)
  simpa only [mul_one, ← completedCoarseHitLaplace_eq_past_weight] using represented

/-- The block length covers both the remaining hit horizon and the survival
count. The completed-duration payoff itself uses only its cap-length prefix. -/
def completedCoarseHitLargeFutureWeight (coarse : Finset X) (cap count : ℕ) (scale : ℝ)
    (index : Fin (cap + 1)) (block : Finset.Iic (max cap count) → X) : ℝ :=
  completedCoarseHitFutureWeight coarse cap scale index
    (historyBefore cap (Nat.le_max_left cap count) block)

theorem completedCoarseHitLargeFutureWeight_eq_shift (coarse : Finset X) (cap count : ℕ)
    (scale : ℝ) (index : Fin (cap + 1)) (path : ℕ → X) :
    completedCoarseHitLargeFutureWeight coarse cap count scale index
        (futurePrefix index.val (max cap count) path) =
      completedCoarseHitLaplace coarse 1 (cap - index.val) scale (shiftPath index.val path) := by
  have projected : historyBefore cap (Nat.le_max_left cap count)
      (futurePrefix index.val (max cap count) path) = futurePrefix index.val cap path := by
    funext entry
    rfl
  rw [completedCoarseHitLargeFutureWeight, projected, completedCoarseHitFutureWeight_eq_shift]

theorem completedCoarseHitLaplace_succ_large_block_product (coarse : Finset X) (arrival cap count : ℕ)
    (scale : ℝ) (path : ℕ → X) :
    completedCoarseHitLaplace coarse (arrival + 1) cap scale path =
      completedCoarseHitPastWeight scale ((boundedCoarseArrival coarse arrival cap).time path)
        (frestrictLe ((boundedCoarseArrival coarse arrival cap).time path).val path) *
      completedCoarseHitLargeFutureWeight coarse cap count scale
        ((boundedCoarseArrival coarse arrival cap).time path)
        (futurePrefix ((boundedCoarseArrival coarse arrival cap).time path).val (max cap count) path) := by
  rw [completedCoarseHitLargeFutureWeight_eq_shift, ← completedCoarseHitLaplace_eq_past_weight,
    completedCoarseHitLaplace_succ_product]

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical
open IGS.Sec31.DiscreteMarkov
noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ}

/-- Staying in a star rules out a completed different-coarse hit through count.
This deterministic implication uses the actual scanner and the actual fact
that the center is the star's only coarse point. -/
theorem xiCoarseStarStay_local_laplace_bound (system : EIGSData K) (coarse steps count cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (scale : ℝ) (scalePositive : 0 < scale)
    (scaleBound : scale ≤ ((count + 1 : ℕ) : ℝ)) (path : ℕ → XiVtx system (coarse + steps)) :
    completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps)) 1 cap scale path ≤
      1 - (1 - Real.exp (-1)) * xiCoarseStarStayTest system coarse steps count (frestrictLe count path) := by
  let skeleton := Finset.univ.image (xiForward system coarse steps)
  by_cases stays : ∃ center : XiVtx system coarse,
      (frestrictLe count path) ⟨0, Finset.mem_Iic.mpr (Nat.zero_le count)⟩ =
        xiForward system coarse steps center ∧
      ∀ index, (frestrictLe count path) index ∈ xiIncidentStarDomain system coarse steps center
  · rw [xiCoarseStarStayTest, if_pos stays, mul_one]
    have reduceRight : 1 - (1 - Real.exp (-1)) = Real.exp (-1) := by ring
    rw [reduceRight]
    obtain ⟨center, start, inside⟩ := stays
    change path 0 = xiForward system coarse steps center at start
    by_cases completed : ((boundedCoarseArrival skeleton 1 cap).time path).val < cap
    · have startsCoarse : path 0 ∈ skeleton := by
        rw [start]
        exact Finset.mem_image.mpr ⟨center, Finset.mem_univ _, rfl⟩
      have firstZero : ((boundedCoarseArrival skeleton 0 cap).time path).val = 0 := by
        have initialCount : 1 ≤ (coarseArrivalState skeleton path 0).2 := by
          simpa only [coarseArrivalState, if_pos startsCoarse] using (show (1 : ℕ) ≤ 1 from le_rfl)
        have earliest := boundedCoarseArrival_le_of_count skeleton 0 cap 0 path initialCount
        omega
      have distinct := boundedCoarseArrival_next_distinct skeleton 0 cap path completed
      have long : count < ((boundedCoarseArrival skeleton 1 cap).time path).val := by
        by_contra notLong
        have bounded : ((boundedCoarseArrival skeleton 1 cap).time path).val ≤ count := Nat.le_of_not_gt notLong
        have inStar := inside ⟨((boundedCoarseArrival skeleton 1 cap).time path).val,
          Finset.mem_Iic.mpr bounded⟩
        obtain ⟨other, _, forwardEquality⟩ := Finset.mem_image.mp distinct.2.1
        have same : other = center := (xiIncidentStarDomain_forward_mem_iff system coarse steps center other).mp
          (by simpa only [forwardEquality, frestrictLe_apply] using inStar)
        have different := distinct.2.2.1
        rw [firstZero] at different
        apply different
        exact forwardEquality.symm.trans ((congrArg (xiForward system coarse steps) same).trans start.symm)
      change (if ((boundedCoarseArrival skeleton 1 cap).time path).val < cap then
        Real.exp (-(((boundedCoarseArrival skeleton 1 cap).time path).val : ℝ) / scale) else 0) ≤ _
      rw [if_pos completed]
      apply Real.exp_le_exp.mpr
      have durationLower : ((count + 1 : ℕ) : ℝ) ≤
          (((boundedCoarseArrival skeleton 1 cap).time path).val : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt long)
      have ratio : 1 ≤ (((boundedCoarseArrival skeleton 1 cap).time path).val : ℝ) / scale := by
        apply (le_div_iff₀ scalePositive).mpr
        simpa only [one_mul] using scaleBound.trans durationLower
      rw [neg_div]
      exact neg_le_neg ratio
    · change (if ((boundedCoarseArrival skeleton 1 cap).time path).val < cap then
        Real.exp (-(((boundedCoarseArrival skeleton 1 cap).time path).val : ℝ) / scale) else 0) ≤ _
      rw [if_neg completed]
      exact (Real.exp_pos _).le
  · rw [xiCoarseStarStayTest, if_neg stays, mul_zero, sub_zero]
    exact completedCoarseHitLaplace_le_one _ 1 cap scale scalePositive path

theorem xiCompletedCoarseHitLaplace_succ_pointwise (system : EIGSData K)
    (coarse steps count arrival cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (scale : ℝ) (scalePositive : 0 < scale) (scaleBound : scale ≤ ((count + 1 : ℕ) : ℝ))
    (path : ℕ → XiVtx system (coarse + steps)) :
    completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps)) (arrival + 1) cap scale path ≤
      completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps)) arrival cap scale path *
        (1 - (1 - Real.exp (-1)) * xiCoarseStarStayTest system coarse steps count
          (futurePrefix ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps))
            arrival cap).time path).val count path)) := by
  rw [completedCoarseHitLaplace_succ_product]
  have futureBound := xiCoarseStarStay_local_laplace_bound system coarse steps count
    (cap - ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps)) arrival cap).time path).val)
    scale scalePositive scaleBound
    (shiftPath ((boundedCoarseArrival (Finset.univ.image (xiForward system coarse steps)) arrival cap).time path).val path)
  exact mul_le_mul_of_nonneg_left futureBound (completedCoarseHitLaplace_nonnegative _ arrival cap scale path)

def XiCompletedCoarseLaplaceContraction (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps arrival cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (scale : ℝ) (initial : ProbabilityMeasure (XiVtx system (coarse + steps))) (probability : ℝ) : Prop :=
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  (∫ path, completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps))
      (arrival + 1) cap scale path ∂pathLaw transition (initial : Measure _)) ≤
    (1 - probability * (1 - Real.exp (-1))) *
      ∫ path, completedCoarseHitLaplace (Finset.univ.image (xiForward system coarse steps))
        arrival cap scale path ∂pathLaw transition (initial : Measure _)

theorem xiCompletedCoarseLaplace_contraction_of_weighted_stay (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (coarse steps count arrival cap : ℕ)
    [MeasurableSpace (XiVtx system (coarse + steps))]
    [MeasurableSingletonClass (XiVtx system (coarse + steps))]
    (scale : ℝ) (scalePositive : 0 < scale) (scaleBound : scale ≤ ((count + 1 : ℕ) : ℝ))
    (initial : ProbabilityMeasure (XiVtx system (coarse + steps))) (probability : ℝ)
    (stayLower : XiCoarseArrivalStayExpectationBound system rulesConnected coarse steps count arrival cap initial
      (fun index _history => Real.exp (-(index.val : ℝ) / scale)) probability) :
    XiCompletedCoarseLaplaceContraction system rulesConnected coarse steps arrival cap scale initial probability := by
  let transition := finiteGraphTransitionKernel (XiSimpleGraph system (coarse + steps))
    (fun vertex => by exact_mod_cast (xiSimpleGraph_degree_positive system rulesConnected (coarse + steps) vertex))
  let actualLaw := pathLaw transition (initial : Measure (XiVtx system (coarse + steps)))
  let skeleton := Finset.univ.image (xiForward system coarse steps)
  let coarseStop := boundedCoarseArrival skeleton arrival cap
  have currentIntegrable := completedCoarseHitLaplace_integrable actualLaw skeleton arrival cap scale
  have nextIntegrable := completedCoarseHitLaplace_integrable actualLaw skeleton (arrival + 1) cap scale
  have representedStay := stopped_history_future_integrable actualLaw coarseStop (max cap count)
    (completedCoarseHitPastWeight scale)
    (fun _ block => xiCoarseStarStayTest system coarse steps count
      (historyBefore count (Nat.le_max_right cap count) block))
  have stayIntegrable : Integrable (fun path => completedCoarseHitLaplace skeleton arrival cap scale path *
      xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path)) actualLaw := by
    apply representedStay.congr
    apply Eventually.of_forall
    intro path
    dsimp only
    rw [completedCoarseHitLaplace_eq_past_weight]
    rfl
  have actualStayLower : probability * (∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw) ≤
      ∫ path, completedCoarseHitLaplace skeleton arrival cap scale path *
        xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path) ∂actualLaw := by
    simpa only [XiCoarseArrivalStayExpectationBound, uncappedHistoryWeight, completedCoarseHitLaplace] using stayLower
  have decayNonnegative : 0 ≤ 1 - Real.exp (-1) :=
    sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by norm_num))
  have domination := integral_mono nextIntegrable
    (currentIntegrable.sub (stayIntegrable.const_mul (1 - Real.exp (-1)))) (fun path => by
      simp only [Pi.sub_apply, skeleton, coarseStop]
      have bound := xiCompletedCoarseHitLaplace_succ_pointwise system coarse steps count arrival cap
        scale scalePositive scaleBound path
      convert bound using 1 <;> ring)
  simp only [Pi.sub_apply] at domination
  rw [integral_sub currentIntegrable (stayIntegrable.const_mul (1 - Real.exp (-1))), integral_const_mul] at domination
  have weightedLower := mul_le_mul_of_nonneg_left actualStayLower decayNonnegative
  change (∫ path, completedCoarseHitLaplace skeleton (arrival + 1) cap scale path ∂actualLaw) ≤ _
  calc
    _ ≤ (∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw) -
        (1 - Real.exp (-1)) * (∫ path, completedCoarseHitLaplace skeleton arrival cap scale path *
          xiCoarseStarStayTest system coarse steps count (futurePrefix (coarseStop.time path).val count path) ∂actualLaw) := domination
    _ ≤ (∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw) -
        (1 - Real.exp (-1)) * (probability *
          ∫ path, completedCoarseHitLaplace skeleton arrival cap scale path ∂actualLaw) :=
      sub_le_sub_left weightedLower _
    _ = _ := by ring

/-- The original rule assumptions supply the contraction uniformly in the
initial law, fine graph and coarse-arrival number. The selected real scale may
lie in (0,1], so a zero survival count is explicitly permitted. -/
theorem exists_xiCompletedCoarseLaplaceContraction_of_rules (system : EIGSData K)
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
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      0 ≤ 1 - (lower / (2 * upper)) * (1 - Real.exp (-1)) ∧
      1 - (lower / (2 * upper)) * (1 - Real.exp (-1)) < 1 ∧
      ∀ (coarse steps count arrival cap : ℕ) (scale : ℝ)
      (initial : ProbabilityMeasure (XiVtx system (coarse + steps))),
      0 < scale → scale ≤ ((count + 1 : ℕ) : ℝ) →
      (count : ℝ) ≤ lower * (realMatrixSpectralRadius (massMatrixR system.toRuleData) *
        system.resistanceSpectralRadius rulesConnected distancePositive) ^ steps / 2 →
      XiCompletedCoarseLaplaceContraction system rulesConnected coarse steps arrival cap scale initial
        (lower / (2 * upper)) := by
  obtain ⟨lower, upper, lowerPositive, upperPositive, probabilityBound, weightedStay⟩ :=
    exists_xiCoarseArrival_weighted_star_survival_of_rules system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive
  have probabilityPositive : 0 < lower / (2 * upper) :=
    div_pos lowerPositive (mul_pos (by norm_num) upperPositive)
  refine ⟨lower, upper, lowerPositive, upperPositive,
    exit_laplace_contraction_nonnegative _ probabilityPositive.le probabilityBound,
    exit_laplace_contraction_lt_one _ probabilityPositive, ?_⟩
  intro coarse steps count arrival cap scale initial scalePositive scaleBound timeBound
  have stay := weightedStay coarse steps count arrival cap initial
    (fun index _history => Real.exp (-(index.val : ℝ) / scale))
    (fun index _history => (Real.exp_pos _).le) timeBound
  exact xiCompletedCoarseLaplace_contraction_of_weighted_stay system rulesConnected coarse steps count arrival cap
    scale scalePositive scaleBound initial (lower / (2 * upper)) stay

end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.stopped_history_future_integrable
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_integrable
#print axioms EIGS.xiCoarseStarStay_local_laplace_bound
#print axioms IGS.Sec31.DiscreteMarkov.completedCoarseHitLaplace_succ_large_block_product
#print axioms EIGS.xiCompletedCoarseLaplace_contraction_of_weighted_stay
#print axioms EIGS.exists_xiCompletedCoarseLaplaceContraction_of_rules
