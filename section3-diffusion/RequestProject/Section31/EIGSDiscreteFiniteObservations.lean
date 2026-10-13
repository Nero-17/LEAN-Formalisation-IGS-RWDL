import RequestProject.Section31.EIGSNativeDiscreteStrongLimit
import RequestProject.Section31.EIGSStationaryFiniteObservations
import RequestProject.Section31.FiniteGraphSurvivalPathLaw

/-! Finite observations of the original integer-time walk. Joint transition
times are differences of absolute floors. They are never replaced by floors
of time differences without the proved one-step correction. -/

namespace IGS.Sec31.PoissonizedWalk

open Filter Topology

theorem floor_increment_bounds (rate first second : ℝ)
    (rateNonnegative : 0 ≤ rate) (firstNonnegative : 0 ≤ first)
    (ordered : first ≤ second) :
    Nat.floor ((second - first) * rate) ≤
        Nat.floor (second * rate) - Nat.floor (first * rate) ∧
    Nat.floor (second * rate) - Nat.floor (first * rate) ≤
        Nat.floor ((second - first) * rate) + 1 := by
  have secondNonnegative := firstNonnegative.trans ordered
  have firstFloor := Nat.floor_le (mul_nonneg firstNonnegative rateNonnegative)
  have secondFloor := Nat.floor_le (mul_nonneg secondNonnegative rateNonnegative)
  have gapFloor := Nat.floor_le (mul_nonneg (sub_nonneg.mpr ordered) rateNonnegative)
  have firstUpper := Nat.lt_floor_add_one (first * rate)
  have gapUpper := Nat.lt_floor_add_one ((second - first) * rate)
  have sumLower : Nat.floor (first * rate) + Nat.floor ((second - first) * rate) ≤
      Nat.floor (second * rate) := by
    apply Nat.le_floor
    push_cast
    nlinarith
  have sumUpperReal : (Nat.floor (second * rate) : ℝ) <
      (Nat.floor (first * rate) : ℝ) + Nat.floor ((second - first) * rate) + 2 := by
    nlinarith
  have sumUpper : Nat.floor (second * rate) <
      Nat.floor (first * rate) + Nat.floor ((second - first) * rate) + 2 := by
    exact_mod_cast sumUpperReal
  omega

theorem floor_increment_error_le_one (rate first second : ℝ)
    (rateNonnegative : 0 ≤ rate) (firstNonnegative : 0 ≤ first)
    (ordered : first ≤ second) :
    |((Nat.floor (second * rate) - Nat.floor (first * rate) : ℕ) : ℝ) -
      Nat.floor ((second - first) * rate)| ≤ 1 := by
  obtain ⟨lower, upper⟩ :=
    floor_increment_bounds rate first second rateNonnegative firstNonnegative ordered
  have lowerReal : (Nat.floor ((second - first) * rate) : ℝ) ≤
      ((Nat.floor (second * rate) - Nat.floor (first * rate) : ℕ) : ℝ) := by
    exact_mod_cast lower
  have upperReal : ((Nat.floor (second * rate) - Nat.floor (first * rate) : ℕ) : ℝ) ≤
      (Nat.floor ((second - first) * rate) : ℝ) + 1 := by
    exact_mod_cast upper
  rw [abs_of_nonneg (sub_nonneg.mpr lowerReal)]
  linarith

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [CompleteSpace Space]

theorem contraction_floor_increment_comparison (transition : Space →L[ℝ] Space)
    (contraction : ‖transition‖ ≤ 1) (rate first second : ℝ)
    (rateNonnegative : 0 ≤ rate) (firstNonnegative : 0 ≤ first)
    (ordered : first ≤ second) (values : Space) :
    ‖(transition ^ (Nat.floor (second * rate) - Nat.floor (first * rate))) values -
      (transition ^ Nat.floor ((second - first) * rate)) values‖ ≤
        ‖transition values - values‖ := by
  have comparison := contraction_power_difference_le transition contraction values
    (Nat.floor (second * rate) - Nat.floor (first * rate))
    (Nat.floor ((second - first) * rate))
  exact comparison.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (floor_increment_error_le_one rate first second rateNonnegative firstNonnegative ordered)
      (norm_nonneg (transition values - values)))

end IGS.Sec31.PoissonizedWalk

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ProbabilityTheory BigOperators

noncomputable section
set_option maxHeartbeats 4000000

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def scheduledOperatorBackward (transition : Hilbert →L[ℝ] Hilbert)
    (multiplication : ℕ → Hilbert →L[ℝ] Hilbert) (schedule : ℕ → ℕ) :
    ℕ → Hilbert → Hilbert
  | 0, terminal => terminal
  | count + 1, terminal => scheduledOperatorBackward transition multiplication schedule count
      (multiplication count ((transition ^ (schedule (count + 1) - schedule count)) terminal))

theorem scheduledOperatorBackward_eq_backwardProduct
    (transition : Hilbert →L[ℝ] Hilbert)
    (multiplication : ℕ → Hilbert →L[ℝ] Hilbert) (schedule : ℕ → ℕ)
    (count : ℕ) (terminal : Hilbert) :
    scheduledOperatorBackward transition multiplication schedule count terminal =
      FiniteObservations.backwardProduct
        (fun index : ℕ => transition ^ (schedule (index + 1) - schedule index)) multiplication
        ((List.range count).map (fun index => (index, index))) terminal := by
  induction count generalizing terminal with
  | zero => rfl
  | succ count induction =>
      simp only [scheduledOperatorBackward, List.range_succ, List.map_append,
        List.map_cons, List.map_nil, backwardProduct_append, FiniteObservations.backwardProduct]
      exact induction _

variable {X : Type*} [MeasurableSpace X]

/-- The observation recursion uses the actual integer gaps. -/
def scheduledBackward (kernel : Kernel X X) (schedule : ℕ → ℕ)
    (tests : ℕ → X → ℝ) : ℕ → (X → ℝ) → X → ℝ
  | 0, terminal => terminal
  | count + 1, terminal => scheduledBackward kernel schedule tests count
      (fun point => tests count point *
        ∫ target, terminal target ∂(kernel ^ (schedule (count + 1) - schedule count)) point)

def scheduledHistoryProduct (schedule : ℕ → ℕ) (monotone : Monotone schedule)
    (tests : ℕ → X → ℝ) (count : ℕ) (history : Finset.Iic (schedule count) → X) : ℝ :=
  ∏ index : Fin (count + 1), tests index.val
    (history ⟨schedule index.val, Finset.mem_Iic.mpr
      (monotone (Nat.le_of_lt_succ index.isLt))⟩)

theorem scheduledHistoryProduct_measurable (schedule : ℕ → ℕ) (monotone : Monotone schedule)
    (tests : ℕ → X → ℝ) (count : ℕ) (testsMeasurable : ∀ index, Measurable (tests index)) :
    Measurable (scheduledHistoryProduct schedule monotone tests count) := by
  apply Finset.measurable_prod
  intro index _
  exact (testsMeasurable index.val).comp (measurable_pi_apply _)

omit [MeasurableSpace X] in
theorem scheduledHistoryProduct_norm_le (schedule : ℕ → ℕ) (monotone : Monotone schedule)
    (tests : ℕ → X → ℝ) (count : ℕ) (bounds : ℕ → ℝ)
    (_boundsNonnegative : ∀ index, 0 ≤ bounds index)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (history : Finset.Iic (schedule count) → X) :
    ‖scheduledHistoryProduct schedule monotone tests count history‖ ≤
      ∏ index : Fin (count + 1), bounds index.val := by
  unfold scheduledHistoryProduct
  rw [norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun index _ => testsBounded index.val _)

/-- Remove the final sampled observation using the proved joint law of the
entire genuine history and its later endpoint. Equal sampled times are allowed. -/
theorem scheduled_product_integral_step (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (schedule : ℕ → ℕ) (monotone : Monotone schedule)
    (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    (∫ path, (∏ index : Fin (count + 1), tests index.val (path (schedule index.val))) *
        terminal (path (schedule (count + 1))) ∂pathLaw kernel (initial : Measure X)) =
      ∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
        (tests count (path (schedule count)) *
          ∫ target, terminal target
            ∂(kernel ^ (schedule (count + 1) - schedule count)) (path (schedule count)))
        ∂pathLaw kernel (initial : Measure X) := by
  let endpoint : Kernel (Finset.Iic (schedule count) → X) X :=
    (kernel ^ (schedule (count + 1) - schedule count)).comap
      (fun history => history ⟨schedule count, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)
  let jointTest : (Finset.Iic (schedule count) → X) × X → ℝ :=
    fun pair => scheduledHistoryProduct schedule monotone tests count pair.1 * terminal pair.2
  have jointMeasurable : Measurable jointTest :=
    ((scheduledHistoryProduct_measurable schedule monotone tests count testsMeasurable).comp
      measurable_fst).mul (terminalMeasurable.comp measurable_snd)
  have jointIntegrable : Integrable jointTest
      (((pathLaw kernel (initial : Measure X)).map (frestrictLe (schedule count))) ⊗ₘ endpoint) := by
    apply Integrable.of_bound jointMeasurable.aestronglyMeasurable
      ((∏ index : Fin (count + 1), bounds index.val) * terminalBound)
    apply Eventually.of_forall
    intro pair
    change ‖scheduledHistoryProduct schedule monotone tests count pair.1 * terminal pair.2‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul
      (scheduledHistoryProduct_norm_le schedule monotone tests count bounds boundsNonnegative testsBounded pair.1)
      (terminalBounded pair.2) (norm_nonneg _)
      (Finset.prod_nonneg (fun index _ => boundsNonnegative index.val))
  have actualJoint := pathLaw_history_endpoint_joint kernel (initial : Measure X)
    (schedule count) (schedule (count + 1) - schedule count)
  rw [Nat.add_sub_of_le (monotone (Nat.le_succ count))] at actualJoint
  have jointIntegral :
      (∫ path, jointTest (frestrictLe (schedule count) path, path (schedule (count + 1)))
        ∂pathLaw kernel (initial : Measure X)) =
      ∫ pair, jointTest pair
        ∂(((pathLaw kernel (initial : Measure X)).map (frestrictLe (schedule count))) ⊗ₘ endpoint) := by
    rw [← actualJoint]
    exact (integral_map ((measurable_frestrictLe (schedule count)).prodMk
      (measurable_pi_apply (schedule (count + 1)))).aemeasurable
      jointMeasurable.aestronglyMeasurable).symm
  change (∫ path, jointTest (frestrictLe (schedule count) path, path (schedule (count + 1)))
    ∂pathLaw kernel (initial : Measure X)) = _
  rw [jointIntegral, Measure.integral_compProd jointIntegrable]
  simp_rw [jointTest, integral_const_mul]
  rw [integral_map (measurable_frestrictLe (schedule count)).aemeasurable]
  · apply integral_congr_ae
    apply Eventually.of_forall
    intro path
    simp only [scheduledHistoryProduct, frestrictLe_apply, Fin.prod_univ_castSucc,
      Fin.val_castSucc, Fin.val_last]
    change (∏ index : Fin count, tests index.val (path (schedule index.val))) *
      tests count (path (schedule count)) *
        (∫ target, terminal target ∂(kernel ^ (schedule (count + 1) - schedule count))
          (path (schedule count))) =
      (∏ index : Fin count, tests index.val (path (schedule index.val))) *
        (tests count (path (schedule count)) *
          ∫ target, terminal target ∂(kernel ^ (schedule (count + 1) - schedule count))
            (path (schedule count)))
    ring
  · apply AEStronglyMeasurable.mul
    · exact (scheduledHistoryProduct_measurable schedule monotone tests count testsMeasurable).aestronglyMeasurable
    · exact ((kernel_integral_measurable
        (kernel ^ (schedule (count + 1) - schedule count)) terminal terminalMeasurable).comp
          (measurable_pi_apply _)).aestronglyMeasurable

theorem scheduled_pathLaw_integral_backward (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (schedule : ℕ → ℕ)
    (monotone : Monotone schedule) (startsAtZero : schedule 0 = 0)
    (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    (∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
      terminal (path (schedule count)) ∂pathLaw kernel (initial : Measure X)) =
      ∫ point, scheduledBackward kernel schedule tests count terminal point ∂(initial : Measure X) := by
  induction count generalizing terminal terminalBound with
  | zero =>
      simp only [Fin.prod_univ_zero, one_mul, startsAtZero, scheduledBackward]
      have zeroIntegral := integral_map (μ := pathLaw kernel (initial : Measure X))
        (measurable_pi_apply 0).aemeasurable terminalMeasurable.aestronglyMeasurable
      rw [pathLaw_coordinate_zero] at zeroIntegral
      exact zeroIntegral.symm
  | succ count induction =>
      rw [scheduled_product_integral_step kernel initial schedule monotone tests count terminal
        bounds terminalBound testsMeasurable terminalMeasurable boundsNonnegative
        terminalBoundNonnegative testsBounded terminalBounded]
      change (∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
        (tests count (path (schedule count)) * ∫ target, terminal target
          ∂(kernel ^ (schedule (count + 1) - schedule count)) (path (schedule count)))
        ∂pathLaw kernel (initial : Measure X)) =
          ∫ point, scheduledBackward kernel schedule tests count
            (fun point => tests count point * ∫ target, terminal target
              ∂(kernel ^ (schedule (count + 1) - schedule count)) point) point ∂(initial : Measure X)
      apply induction
        (terminal := fun point => tests count point * ∫ target, terminal target
          ∂(kernel ^ (schedule (count + 1) - schedule count)) point)
        (terminalBound := bounds count * terminalBound)
      · exact (testsMeasurable count).mul (kernel_integral_measurable _ terminal terminalMeasurable)
      · exact mul_nonneg (boundsNonnegative count) terminalBoundNonnegative
      · intro point
        rw [norm_mul]
        exact mul_le_mul (testsBounded count point)
          (kernel_integral_norm_le _ terminal terminalBound terminalBounded point)
          (norm_nonneg _) (boundsNonnegative count)

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators ProbabilityTheory NNReal BoundedContinuousFunction Classical

noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ} (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (mass : XiMassParameters system) (level : ℕ)

/-- The actual one-step PMF law of the original graph walk. -/
def xiNativeDiscreteKernel : Kernel (XiVtx system level) (XiVtx system level) :=
  finiteGraphTransitionKernel (XiSimpleGraph system level) (fun vertex => by
    rw [← xiVertexIncidenceCount_eq_degree system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level vertex]
    exact xiVertexIncidenceCount_positive system rulesConnected level vertex)

instance xiNativeDiscreteKernel_isMarkov :
    IsMarkovKernel (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level) := by
  unfold xiNativeDiscreteKernel
  infer_instance

theorem xiNativeDiscreteKernel_integral
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (vertex : XiVtx system level) :
    (∫ target, values target ∂xiNativeDiscreteKernel system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent level vertex) =
      xiNativeRandomWalk system rulesConnected mass level values vertex := by
  rw [xiNativeDiscreteKernel, finiteGraphTransitionKernel_integral, xiNativeRandomWalk_apply]

include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_integral_preservation
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    (∫ vertex, xiNativeRandomWalk system rulesConnected mass level values vertex
      ∂xiVertexSpeedMeasure system mass level) =
      ∫ vertex, values vertex ∂xiVertexSpeedMeasure system mass level := by
  let one := xiFiniteSpeedL2 system mass level (fun _ => 1)
  have oneAE : ∀ᵐ vertex ∂xiVertexSpeedMeasure system mass level, one vertex = 1 :=
    Eventually.of_forall fun vertex => xiFiniteSpeedL2_apply system rulesConnected mass level (fun _ => 1) vertex
  have onePreserved : xiNativeRandomWalk system rulesConnected mass level one = one :=
    xiNativeRandomWalk_preserves_one system rulesConnected mass level rulesLoopless rulesUnique plantingNonadjacent
  have pairing := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (xiNativeRandomWalk_selfAdjoint system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level)) values one
  change inner ℝ (xiNativeRandomWalk system rulesConnected mass level values) one =
    inner ℝ values (xiNativeRandomWalk system rulesConnected mass level one) at pairing
  rw [onePreserved] at pairing
  simpa only [QuadraticEnergySpace.lp_inner_one_eq_integral
    (xiVertexSpeedMeasure system mass level) one oneAE] using pairing

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeDiscreteTransition_stationary (target : XiVtx system level) :
    ∑ source : XiVtx system level, (xiVertexSpeedMeasure system mass level).real {source} *
      transProb (XiSimpleGraph system level) source target =
      (xiVertexSpeedMeasure system mass level).real {target} := by
  classical
  have preservation := xiNativeRandomWalk_integral_preservation system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass level (xiFiniteSpeedL2 system mass level (Pi.single target 1))
  rw [integral_fintype _ Integrable.of_finite, integral_fintype _ Integrable.of_finite] at preservation
  simpa [xiNativeRandomWalk_apply, xiFiniteSpeedL2_apply system rulesConnected mass level,
    Pi.single_apply, smul_eq_mul] using preservation

theorem xiNativeDiscreteKernel_invariant :
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level).Invariant
      (xiVertexSpeedMeasure system mass level) := by
  classical
  change (xiVertexSpeedMeasure system mass level).bind
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level) = _
  apply Measure.ext_of_singleton
  intro target
  rw [Measure.bind_apply (measurableSet_singleton target) (Kernel.aemeasurable _), lintegral_fintype]
  have kernelSingleton (source : XiVtx system level) :
      xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level source {target} =
        ENNReal.ofReal (transProb (XiSimpleGraph system level) source target) := by
    simp [xiNativeDiscreteKernel, finiteGraphTransitionKernel, rwStep_apply]
  simp_rw [kernelSingleton]
  have massAsReal (vertex : XiVtx system level) :
      xiVertexSpeedMeasure system mass level {vertex} =
        ENNReal.ofReal ((xiVertexSpeedMeasure system mass level).real {vertex}) :=
    (ENNReal.ofReal_toReal (measure_ne_top (xiVertexSpeedMeasure system mass level) {vertex})).symm
  simp_rw [massAsReal]
  calc
    _ = ∑ source : XiVtx system level, ENNReal.ofReal
        ((xiVertexSpeedMeasure system mass level).real {source} *
          transProb (XiSimpleGraph system level) source target) := by
      apply Finset.sum_congr rfl
      intro source _
      rw [ENNReal.ofReal_mul measureReal_nonneg, mul_comm]
    _ = ENNReal.ofReal (∑ source : XiVtx system level,
        (xiVertexSpeedMeasure system mass level).real {source} *
          transProb (XiSimpleGraph system level) source target) := by
      symm
      apply ENNReal.ofReal_sum_of_nonneg
      intro source _
      exact mul_nonneg measureReal_nonneg (transProb_nonneg (G := XiSimpleGraph system level) source target)
    _ = _ := congrArg ENNReal.ofReal
      (xiNativeDiscreteTransition_stationary system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level target)

theorem xiNativeDiscreteKernel_power_integral (jumps : ℕ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) (vertex : XiVtx system level) :
    (∫ target, values target ∂(xiNativeDiscreteKernel system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent level ^ jumps) vertex) =
      (xiNativeRandomWalk system rulesConnected mass level ^ jumps) values vertex := by
  induction jumps generalizing values vertex with
  | zero =>
      change (∫ target, values target ∂Measure.dirac vertex) = values vertex
      simp
  | succ jumps induction =>
      rw [pow_succ]
      change (∫ target, values target ∂((xiNativeDiscreteKernel system rulesConnected
        rulesLoopless rulesUnique plantingNonadjacent level ^ jumps) ∘ₖ
          xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level) vertex) = _
      rw [Kernel.integral_comp (Integrable.of_finite)]
      simp_rw [induction]
      rw [xiNativeDiscreteKernel_integral, pow_succ', ContinuousLinearMap.mul_apply]

theorem xiNativeDiscrete_scheduledBackward_eq_operator
    (schedule : ℕ → ℕ) (tests : ℕ → XiVtx system level → ℝ)
    (multiplication : ℕ → Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (multiplicationEvaluation : ∀ index values vertex,
      multiplication index values vertex = tests index vertex * values vertex)
    (count : ℕ) (terminal : XiVtx system level → ℝ)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (terminalEvaluation : ∀ vertex, terminal vertex = values vertex) (vertex : XiVtx system level) :
    DiscreteMarkov.scheduledBackward
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      schedule tests count terminal vertex =
    DiscreteMarkov.scheduledOperatorBackward (xiNativeRandomWalk system rulesConnected mass level)
      multiplication schedule count values vertex := by
  induction count generalizing terminal values vertex with
  | zero => exact terminalEvaluation vertex
  | succ count induction =>
      apply induction
      intro point
      rw [multiplicationEvaluation]
      congr 1
      calc
        _ = ∫ target, values target ∂(xiNativeDiscreteKernel system rulesConnected
            rulesLoopless rulesUnique plantingNonadjacent level ^
              (schedule (count + 1) - schedule count)) point :=
          integral_congr_ae (Eventually.of_forall terminalEvaluation)
        _ = _ := xiNativeDiscreteKernel_power_integral system rulesConnected rulesLoopless
          rulesUnique plantingNonadjacent mass level _ values point

theorem xiNativeDiscrete_scheduled_integral_operator
    (schedule : ℕ → ℕ) (monotone : Monotone schedule) (startsAtZero : schedule 0 = 0)
    (tests : ℕ → XiVtx system level → ℝ) (count : ℕ) (terminal : XiVtx system level → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound)
    (multiplication : ℕ → Lp ℝ 2 (xiVertexSpeedMeasure system mass level) →L[ℝ]
      Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (multiplicationEvaluation : ∀ index values vertex,
      multiplication index values vertex = tests index vertex * values vertex)
    (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
    (terminalEvaluation : ∀ vertex, terminal vertex = values vertex) :
    (∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
      terminal (path (schedule count)) ∂DiscreteMarkov.pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (xiVertexSpeedMeasure system mass level)) =
    ∫ point, DiscreteMarkov.scheduledOperatorBackward
      (xiNativeRandomWalk system rulesConnected mass level) multiplication schedule count values point
      ∂xiVertexSpeedMeasure system mass level := by
  change (∫ path, (∏ index : Fin count, tests index.val (path (schedule index.val))) *
    terminal (path (schedule count)) ∂DiscreteMarkov.pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
      (xiNativeSpeedProbabilityMeasure system mass level : Measure _)) = _
  rw [DiscreteMarkov.scheduled_pathLaw_integral_backward
    (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
    (xiNativeSpeedProbabilityMeasure system mass level) schedule monotone startsAtZero
    tests count terminal bounds terminalBound (fun _ => measurable_of_countable _)
    (measurable_of_countable _) boundsNonnegative terminalBoundNonnegative testsBounded terminalBounded]
  apply integral_congr_ae
  exact Eventually.of_forall (xiNativeDiscrete_scheduledBackward_eq_operator system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent mass level schedule tests multiplication
    multiplicationEvaluation count terminal values terminalEvaluation)

theorem xiNativeDiscrete_continuous_scheduled_integral_operator
    {Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (embeddings : ∀ level, XiVtx system level → Space)
    (measurableEmbeddings : ∀ level, Measurable (embeddings level))
    (schedule : ℕ → ℕ) (monotone : Monotone schedule) (startsAtZero : schedule 0 = 0)
    (tests : ℕ → Space →ᵇ ℝ) (count : ℕ) (terminal : Space →ᵇ ℝ) :
    (∫ path, (∏ index : Fin count, tests index.val (embeddings level (path (schedule index.val)))) *
      terminal (embeddings level (path (schedule count))) ∂DiscreteMarkov.pathLaw
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (xiVertexSpeedMeasure system mass level)) =
      ∫ point, DiscreteMarkov.scheduledOperatorBackward
        (xiNativeRandomWalk system rulesConnected mass level)
        (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
          embeddings measurableEmbeddings (tests index) level) schedule count
        (xiFiniteSpeedL2 system mass level (fun vertex => terminal (embeddings level vertex))) point
        ∂xiVertexSpeedMeasure system mass level := by
  apply xiNativeDiscrete_scheduled_integral_operator system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent mass level schedule monotone startsAtZero
    (fun index vertex => tests index (embeddings level vertex)) count
    (fun vertex => terminal (embeddings level vertex)) (fun index => ‖tests index‖) ‖terminal‖
    (fun _ => norm_nonneg _) (norm_nonneg _)
    (fun index vertex => (tests index).norm_coe_le_norm _) (fun vertex => terminal.norm_coe_le_norm _)
  · intro index values vertex
    exact (xiVertexSpeedMeasure_ae_iff system rulesConnected mass level _).1
      (BoundedL2Multiplication.operator_ae _ _ _ _ _ _ values) vertex
  · intro vertex
    exact (xiFiniteSpeedL2_apply system rulesConnected mass level
      (fun point => terminal (embeddings level point)) vertex).symm

/- Same-input comparison for the actual joint transition increment. -/
include rulesLoopless rulesUnique plantingNonadjacent in
theorem xiNativeRandomWalk_floor_increment_comparison
    (resistanceRate normalization : ℝ) (ratePositive : 0 < resistanceRate)
    (normalizationPositive : 0 < normalization) (first second : ℝ≥0)
    (ordered : first ≤ second) (values : Lp ℝ 2 (xiVertexSpeedMeasure system mass level)) :
    ‖(xiNativeRandomWalk system rulesConnected mass level ^
      (Nat.floor ((second : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) -
        Nat.floor ((first : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))) values -
      (xiNativeRandomWalk system rulesConnected mass level ^
        Nat.floor (((second : ℝ) - first) * xiNativeFiniteJumpRate system level resistanceRate normalization)) values‖ ≤
      ‖xiNativeRandomWalk system rulesConnected mass level values - values‖ :=
  PoissonizedWalk.contraction_floor_increment_comparison _
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level)
    _ first second
    (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization ratePositive normalizationPositive).le
    first.coe_nonneg (by exact_mod_cast ordered) values

theorem xiNativeRandomWalk_one_step_norm_sub_tendsto_zero (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      Tendsto (fun level => ‖xiNativeRandomWalk system rulesConnected mass level
        (forcing level) - forcing level‖) atTop (nhds 0) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense forcing target forcingStrong
  let finiteResolvent (index level : ℕ) :=
    xiNativeFiniteResolvent system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level
      resistanceRate normalization ratePositive.le normalizationPositive.le
      (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
  let limitResolvent (index : ℕ) :=
    QuadraticEnergySpace.smallStepResolvent originalDomain originalForm nonnegative closable originalDense
      (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have resolventStrong (index : ℕ) :
      ∀ (sequence : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (limit : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong sequence limit →
        core.Strong (fun level => finiteResolvent index level (sequence level)) (limitResolvent index limit) :=
    xiNativeFiniteResolvent_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
      normalizedConvergence originalDense (QuadraticEnergySpace.canonicalYosidaStep index)
      (QuadraticEnergySpace.canonicalYosidaStep_positive index)
      (QuadraticEnergySpace.canonicalYosidaStep_le_one index)
  have resolventIdentityLimit
      (values : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)) :
      Tendsto (fun index => limitResolvent index values) atTop (nhds values) :=
    QuadraticEnergySpace.smallStepResolvent_strong_limit originalDomain originalForm nonnegative closable originalDense
      QuadraticEnergySpace.canonicalYosidaStep QuadraticEnergySpace.canonicalYosidaStep_positive
      QuadraticEnergySpace.canonicalYosidaStep_le_one QuadraticEnergySpace.canonicalYosidaStep_tendsto values

  have jumpRateLimit := xiNativeFiniteJumpRate_tendsto_atTop system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent mass distancePositive resistanceRate normalization ratePositive
    normalizationPositive resistanceVector vectorPositive (by
      funext colour
      exact renormalizationEigenpair colour)
  have inverseLimit : Tendsto (fun level =>
      (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp jumpRateLimit
  have inputNormLimit := core.strong_norm_tendsto forcingStrong
  have smoothingLimit : Tendsto (fun index => ‖target - limitResolvent index target‖)
      atTop (nhds 0) := by
    simpa only [sub_self, norm_zero] using
      ((tendsto_const_nhds (x := target)).sub (resolventIdentityLimit target)).norm
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  obtain ⟨smoothingIndex, smoothingSmall⟩ :=
    (smoothingLimit.eventually_lt_const (by positivity : 0 < tolerance / 8)).exists
  have smoothedStrong := resolventStrong smoothingIndex forcing target forcingStrong
  have inputErrorLimit := core.strong_norm_sub_tendsto forcingStrong smoothedStrong
  have eventualInputSmall : ∀ᶠ level in atTop,
      ‖forcing level - finiteResolvent smoothingIndex level (forcing level)‖ < tolerance / 4 :=
    inputErrorLimit.eventually_lt_const (by linarith)
  have errorLimit : Tendsto (fun level =>
      (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹ *
        ((2 / QuadraticEnergySpace.canonicalYosidaStep smoothingIndex) * ‖forcing level‖))
      atTop (nhds (0 : ℝ)) := by
    simpa only [zero_mul] using inverseLimit.mul
      (inputNormLimit.const_mul (2 / QuadraticEnergySpace.canonicalYosidaStep smoothingIndex))
  have eventualErrorSmall := errorLimit.eventually_lt_const
    (by positivity : 0 < tolerance / 2)
  filter_upwards [eventualInputSmall, eventualErrorSmall] with level inputSmall errorSmall
  have jumpRatePositive := xiNativeFiniteJumpRate_positive system mass level
    resistanceRate normalization ratePositive normalizationPositive
  have generatorNorm :
      ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
        (finiteResolvent smoothingIndex level (forcing level))‖ =
      xiNativeFiniteJumpRate system level resistanceRate normalization *
        ‖xiNativeRandomWalk system rulesConnected mass level
          (finiteResolvent smoothingIndex level (forcing level)) -
          finiteResolvent smoothingIndex level (forcing level)‖ := by
    rw [xiNativeFiniteGenerator_eq_jumpRate, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, norm_smul,
      Real.norm_eq_abs, abs_of_pos jumpRatePositive, norm_sub_rev]
  have smoothedComparison :
      ‖xiNativeRandomWalk system rulesConnected mass level
        (finiteResolvent smoothingIndex level (forcing level)) -
          finiteResolvent smoothingIndex level (forcing level)‖ ≤
      (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹ *
        ((2 / QuadraticEnergySpace.canonicalYosidaStep smoothingIndex) * ‖forcing level‖) := by
    calc
      _ = (xiNativeFiniteJumpRate system level resistanceRate normalization)⁻¹ *
          ‖xiNativeFiniteGenerator system rulesConnected mass level resistanceRate normalization
            (finiteResolvent smoothingIndex level (forcing level))‖ := by
        rw [generatorNorm, ← mul_assoc, inv_mul_cancel₀ jumpRatePositive.ne', one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (xiNativeFiniteGenerator_resolvent_norm_le system rulesConnected rulesLoopless rulesUnique
          plantingNonadjacent mass level resistanceRate normalization ratePositive normalizationPositive
          (QuadraticEnergySpace.canonicalYosidaStep smoothingIndex)
          (QuadraticEnergySpace.canonicalYosidaStep_positive smoothingIndex) (forcing level))
        (inv_nonneg.mpr jumpRatePositive.le)
  have comparison := contraction_comparison_after_smoothing
    (xiNativeRandomWalk system rulesConnected mass level) 1
    (xiNativeRandomWalk_norm_le_one system rulesConnected rulesLoopless rulesUnique plantingNonadjacent mass level)
    (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Lp ℝ 2 (xiVertexSpeedMeasure system mass level)))
    (forcing level) (finiteResolvent smoothingIndex level (forcing level)) _
    (by simpa only [ContinuousLinearMap.one_apply] using smoothedComparison)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  simpa only [ContinuousLinearMap.one_apply] using comparison.trans_lt (by linarith)

theorem xiNativeRandomWalk_floor_increment_strong_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (first second : ℝ≥0) (ordered : first ≤ second)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target →
      core.Strong (fun level => (xiNativeRandomWalk system rulesConnected mass level ^
        (Nat.floor ((second : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization) -
        Nat.floor ((first : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))) (forcing level))
        (QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
          originalDense (second - first) target) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense first second ordered forcing target forcingStrong
  have gapStrong := xiNativeDiscreteWalk_strong_limit system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive
    distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive
    resistanceVector vectorPositive renormalizationEigenpair normalization normalizationPositive
    normalizedConvergence originalDense (second - first) forcing target forcingStrong
  apply core.strong_of_norm_sub_tendsto_zero _ _ _ gapStrong
  have defectLimit := xiNativeRandomWalk_one_step_norm_sub_tendsto_zero system rulesConnected
    rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths
    lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass resistanceRate
    ratePositive resistanceVector vectorPositive renormalizationEigenpair normalization
    normalizationPositive normalizedConvergence originalDense forcing target forcingStrong
  apply squeeze_zero' (Eventually.of_forall (fun level => norm_nonneg _))
    (Eventually.of_forall (fun level => ?_)) defectLimit
  simpa only [NNReal.coe_sub ordered] using
    xiNativeRandomWalk_floor_increment_comparison system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent mass level resistanceRate normalization ratePositive normalizationPositive
      first second ordered (forcing level)


theorem xiNativeDiscreteFiniteObservations_strong_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times)
        (tests : ℕ → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ)
        (count : ℕ)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass)),
      core.Strong forcing target → core.Strong
        (fun level => DiscreteMarkov.scheduledOperatorBackward
          (xiNativeRandomWalk system rulesConnected mass level)
          (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
            (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair) (tests index) level)
          (fun index => Nat.floor ((times index : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization)) count (forcing level))
        (FiniteObservations.backwardProduct
          (fun index : ℕ => QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense (times (index + 1) - times index))
          (fun index => boundedContinuousLimitMultiplication
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) (tests index))
          ((List.range count).map (fun index => (index, index))) target) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense times timesMonotone tests count forcing target forcingStrong
  simp_rw [DiscreteMarkov.scheduledOperatorBackward_eq_backwardProduct]
  apply FiniteObservations.backwardProduct_strong core
  · intro index sequence limit convergence
    exact xiNativeRandomWalk_floor_increment_strong_limit system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive normalizedConvergence
      originalDense (times index) (times (index + 1)) (timesMonotone (Nat.le_succ index))
      sequence limit convergence
  · intro index sequence limit convergence
    exact xiSpeedL2Core_strong_multiplication system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass (tests index) sequence limit convergence
  · exact forcingStrong

theorem xiNativeDiscreteFiniteObservations_expectation_limit (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour))
    (oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour))
    (lengths : Fin K → ℝ) (lengthsPositive : ∀ colour, 0 < lengths colour)
    (distanceRate : ℝ) (distanceRateGreaterThanOne : 1 < distanceRate)
    (metricEigenpair : (system.ruleFamily rulesConnected).metricLengths lengths = distanceRate • lengths)
    (mass : XiMassParameters system)
    (resistanceRate : ℝ) (ratePositive : 0 < resistanceRate)
    (resistanceVector : Fin K → ℝ) (vectorPositive : ∀ colour, 0 < resistanceVector colour)
    (renormalizationEigenpair : ∀ colour,
      (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour)
    (normalization : ℝ) (normalizationPositive : 0 < normalization)
    (normalizedConvergence : Tendsto (fun offset => fun colour =>
      (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
      atTop (nhds (normalization • resistanceVector))) :
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
    let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
      intro sequence energyCauchy ambientZero
      exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
        distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
        mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
        (by simpa using ambientZero.norm)
    ∀ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected
        lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass))),
      ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
        (tests : ℕ → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ)
        (count : ℕ) (terminal : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ),
      Tendsto (fun level => ∫ path,
        (∏ index : Fin count, tests index.val (xiCompletionEmbedding system rulesConnected
          lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne)
          metricEigenpair level (path (Nat.floor ((times index.val : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
        terminal (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
          (path (Nat.floor ((times count : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))
        ∂DiscreteMarkov.pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (xiVertexSpeedMeasure system mass level)) atTop
        (nhds (inner ℝ (core.embed 1) (FiniteObservations.backwardProduct
          (fun index : ℕ => QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense (times (index + 1) - times index))
          (fun index => boundedContinuousLimitMultiplication
            (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) (tests index))
          ((List.range count).map (fun index => (index, index))) (core.embed terminal)))) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let core := xiSpeedL2Core system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  have closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
    intro sequence energyCauchy ambientZero
    exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
      distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair
      mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
      (by simpa using ambientZero.norm)
  dsimp only
  intro originalDense times timesMonotone startsAtZero tests count terminal
  have strong := xiNativeDiscreteFiniteObservations_strong_limit system rulesConnected rulesLoopless
    rulesUnique plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    renormalizationEigenpair normalization normalizationPositive normalizedConvergence originalDense
    times timesMonotone tests count (fun level => core.restrict level terminal) (core.embed terminal)
    (core.strong_restrict terminal)
  have pairingConvergence := core.strong_inner_tendsto (core.strong_restrict (1 : _ →ᵇ ℝ)) strong
  have levelExpectation (level : ℕ) :
      (∫ path, (∏ index : Fin count, tests index.val (xiCompletionEmbedding system rulesConnected
          lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne)
          metricEigenpair level (path (Nat.floor ((times index.val : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
        terminal (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level
          (path (Nat.floor ((times count : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))
        ∂DiscreteMarkov.pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (xiVertexSpeedMeasure system mass level)) =
      inner ℝ (core.restrict level 1) (DiscreteMarkov.scheduledOperatorBackward
        (xiNativeRandomWalk system rulesConnected mass level)
        (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
          (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair) (tests index) level)
        (fun index => Nat.floor ((times index : ℝ) *
          xiNativeFiniteJumpRate system level resistanceRate normalization)) count (core.restrict level terminal)) := by
    rw [xiNativeDiscrete_continuous_scheduled_integral_operator system rulesConnected rulesLoopless
      rulesUnique plantingNonadjacent mass level
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
      (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair)
      (fun index => Nat.floor ((times index : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))
      (fun first second ordered => Nat.floor_mono (mul_le_mul_of_nonneg_right
        (by exact_mod_cast timesMonotone ordered)
        (xiNativeFiniteJumpRate_positive system mass level resistanceRate normalization
          ratePositive normalizationPositive).le))
      (by simp [startsAtZero]) tests count terminal]
    have terminalIdentity := xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected lengths lengthsPositive
      distanceRate distanceRateGreaterThanOne metricEigenpair mass terminal level
    rw [← terminalIdentity]
    apply DiscreteMarkov.integral_eq_inner_one (xiNativeSpeedProbabilityMeasure system mass level)
    apply Eventually.of_forall
    intro point
    simp only [core, xiSpeedL2Core_restrict_eq_finiteSpeedL2,
      xiFiniteSpeedL2_apply system rulesConnected mass, BoundedContinuousFunction.coe_one, Pi.one_apply]
  exact pairingConvergence.congr' (Eventually.of_forall (fun level => (levelExpectation level).symm))

theorem exists_xiNativeDiscreteFiniteObservations_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times)
        (tests : ℕ → XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair →ᵇ ℝ)
        (count : ℕ)
        (forcing : ∀ level, Lp ℝ 2 (xiVertexSpeedMeasure system mass level))
        (target : Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          distanceRateGreaterThanOne parameters.eigenpair mass)),
      core.Strong forcing target → core.Strong
        (fun level => DiscreteMarkov.scheduledOperatorBackward
          (xiNativeRandomWalk system rulesConnected mass level)
          (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
            (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair)
            (measurable_xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceRateGreaterThanOne parameters.eigenpair) (tests index) level)
          (fun index => Nat.floor ((times index : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization)) count (forcing level))
        (FiniteObservations.backwardProduct
          (fun index : ℕ => QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense (times (index + 1) - times index))
          (fun index => boundedContinuousLimitMultiplication
            (xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceRateGreaterThanOne parameters.eigenpair mass) (tests index))
          ((List.range count).map (fun index => (index, index))) target) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeDiscreteFiniteObservations_strong_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

theorem exists_xiNativeDiscreteObservationExpectations_of_rules (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (distancePositive : ∀ ruleColour edgeColour : Fin K,
      ¬ ((system.ruleNetwork ruleColour).withoutColour edgeColour).Reachable
        (system.plantPlus ruleColour) (system.plantMinus ruleColour)) :
    let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
    let distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
      (by norm_num : (1 : ℝ) < 2).trans_le
        (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
    let mass := xiMassParametersOfRules system rulesConnected distancePositive
    letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
    let core := xiSpeedL2Core system rulesConnected parameters.lengths parameters.lengthsPositive
      (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    let oneColourDistance : K = 1 → ∀ colour,
        2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
      intro _ colour
      exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
        (system.plant_ne colour) (plantingNonadjacent colour)
    ∃ resistanceRate : ℝ, ∃ resistanceVector : Fin K → ℝ,
      ∃ ratePositive : 0 < resistanceRate, ∃ vectorPositive : ∀ colour, 0 < resistanceVector colour,
      ∃ renormalizationEigenpair : ∀ colour,
        (system.ruleFamily rulesConnected).Psi resistanceVector colour = resistanceRate * resistanceVector colour,
      ∃ normalization : ℝ, ∃ normalizationPositive : 0 < normalization,
      Tendsto (fun offset => fun colour =>
        (system.ruleFamily rulesConnected).Psi^[offset] (fun _ => 1) colour / resistanceRate ^ offset)
        atTop (nhds (normalization • resistanceVector)) ∧
      let originalDomain := xiContinuousEnergyLpDomain system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive
      let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
      let closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm := by
        intro sequence energyCauchy ambientZero
        exact xiContinuousLpEnergyQuadraticForm_closable_without_primitive system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
          distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
          mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair sequence energyCauchy
          (by simpa using ambientZero.norm)
      ∃ originalDense : Dense (originalDomain : Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      ∀ (times : ℕ → ℝ≥0) (timesMonotone : Monotone times) (startsAtZero : times 0 = 0)
        (tests : ℕ → XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair →ᵇ ℝ)
        (count : ℕ) (terminal : XiMetricCompletion system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair →ᵇ ℝ),
      Tendsto (fun level => ∫ path,
        (∏ index : Fin count, tests index.val (xiCompletionEmbedding system rulesConnected
          parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected) (zero_lt_one.trans distanceRateGreaterThanOne)
          parameters.eigenpair level (path (Nat.floor ((times index.val : ℝ) *
            xiNativeFiniteJumpRate system level resistanceRate normalization))))) *
        terminal (xiCompletionEmbedding system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
          (zero_lt_one.trans distanceRateGreaterThanOne) parameters.eigenpair level
          (path (Nat.floor ((times count : ℝ) * xiNativeFiniteJumpRate system level resistanceRate normalization))))
        ∂DiscreteMarkov.pathLaw
          (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
          (xiVertexSpeedMeasure system mass level)) atTop
        (nhds (inner ℝ (core.embed 1) (FiniteObservations.backwardProduct
          (fun index : ℕ => QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable
            originalDense (times (index + 1) - times index))
          (fun index => boundedContinuousLimitMultiplication
            (xiLimitProbabilityMeasure system rulesConnected parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
              distanceRateGreaterThanOne parameters.eigenpair mass) (tests index))
          ((List.range count).map (fun index => (index, index))) (core.embed terminal)))) := by
  classical
  let parameters := xiPathMetricDataOfRules system rulesConnected rulesLoopless rulesUnique distancePositive
  have distanceRateGreaterThanOne : 1 < system.distanceSpectralRadius rulesConnected :=
    (by norm_num : (1 : ℝ) < 2).trans_le
      (system.two_le_distanceSpectralRadius rulesConnected rulesUnique plantingNonadjacent distancePositive)
  let mass := xiMassParametersOfRules system rulesConnected distancePositive
  letI := xiCompletion_compactSpace system rulesConnected parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair
  have oneColourDistance : K = 1 → ∀ colour,
      2 ≤ (ruleSG system colour).dist (system.plantPlus colour) (system.plantMinus colour) := by
    intro _ colour
    exact (rulesConnected colour).one_lt_dist_of_ne_of_not_adj
      (system.plant_ne colour) (plantingNonadjacent colour)
  obtain ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
      originalDense, originalNonnegative⟩ :=
    exists_xiDenseLpQuadraticEnergy_of_rules system rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive
  obtain ⟨normalization, normalizationPositive, normalizedConvergence⟩ :=
    exists_normalized_resistance_limit_of_positive_eigenpair system rulesConnected distancePositive resistanceRate ratePositive
      resistanceVector vectorPositive renormalizationEigenpair
  refine ⟨resistanceRate, resistanceVector, ratePositive, vectorPositive, renormalizationEigenpair,
    normalization, normalizationPositive, normalizedConvergence, originalDense, ?_⟩
  exact xiNativeDiscreteFiniteObservations_expectation_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense

end
end EIGS

#print axioms IGS.Sec31.PoissonizedWalk.floor_increment_bounds
#print axioms IGS.Sec31.PoissonizedWalk.floor_increment_error_le_one
#print axioms IGS.Sec31.PoissonizedWalk.contraction_floor_increment_comparison
#print axioms IGS.Sec31.DiscreteMarkov.scheduled_product_integral_step
#print axioms IGS.Sec31.DiscreteMarkov.scheduled_pathLaw_integral_backward
#print axioms EIGS.xiNativeDiscreteKernel_integral
#print axioms EIGS.xiNativeDiscreteKernel_power_integral
#print axioms EIGS.xiNativeRandomWalk_floor_increment_comparison

#print axioms EIGS.xiNativeRandomWalk_one_step_norm_sub_tendsto_zero

#print axioms EIGS.xiNativeRandomWalk_floor_increment_strong_limit

#print axioms EIGS.xiNativeDiscreteFiniteObservations_strong_limit

#print axioms EIGS.exists_xiNativeDiscreteFiniteObservations_of_rules

#print axioms EIGS.xiNativeDiscreteFiniteObservations_expectation_limit

#print axioms EIGS.exists_xiNativeDiscreteObservationExpectations_of_rules

#print axioms IGS.Sec31.DiscreteMarkov.scheduledOperatorBackward_eq_backwardProduct

#print axioms EIGS.xiNativeDiscrete_continuous_scheduled_integral_operator

#print axioms EIGS.xiNativeDiscreteKernel_invariant
