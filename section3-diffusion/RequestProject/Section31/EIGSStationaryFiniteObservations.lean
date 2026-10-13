import RequestProject.Section31.DiscreteMarkovFiniteObservations
import RequestProject.Section31.EIGSNativeFiniteObservations
import RequestProject.Section31.EIGSNativeFiniteKernel
import RequestProject.Section31.EIGSInvariantMarkovKernelOfRules
import RequestProject.Section31.MarkovKernelBoundedApproximation

/-! Genuine stationary fixed-step finite-prefix observation expectations.
The scalar backward kernel recursion is identified with the actual L2
operators through invariant-kernel AE transport. This file concerns arbitrary
prefix lengths at one fixed nonnegative real step; arbitrary unequal gaps
and weak convergence of full finite-dimensional laws are separate steps. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped BigOperators BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]

def operatorBackwardPrefix (operator : Hilbert →L[ℝ] Hilbert)
    (multiplication : ℕ → Hilbert →L[ℝ] Hilbert) : ℕ → Hilbert → Hilbert
  | 0, terminal => terminal
  | count + 1, terminal => operatorBackwardPrefix operator multiplication count
      (multiplication count (operator terminal))

theorem backwardProduct_append {Time Test : Type*}
    (evolution : Time → Hilbert →L[ℝ] Hilbert)
    (multiplication : Test → Hilbert →L[ℝ] Hilbert)
    (first second : List (Time × Test)) (terminal : Hilbert) :
    FiniteObservations.backwardProduct evolution multiplication (first ++ second) terminal =
      FiniteObservations.backwardProduct evolution multiplication first
        (FiniteObservations.backwardProduct evolution multiplication second terminal) := by
  induction first with
  | nil => rfl
  | cons observation remaining induction =>
    simp only [List.cons_append, FiniteObservations.backwardProduct, induction]

theorem operatorBackwardPrefix_eq_backwardProduct {Time Test : Type*}
    (evolution : Time → Hilbert →L[ℝ] Hilbert)
    (multiplication : Test → Hilbert →L[ℝ] Hilbert)
    (step : Time) (tests : ℕ → Test) (count : ℕ) (terminal : Hilbert) :
    operatorBackwardPrefix (evolution step) (fun index => multiplication (tests index)) count terminal =
      FiniteObservations.backwardProduct evolution multiplication
        ((List.range count).map (fun index => (step, tests index))) terminal := by
  induction count generalizing terminal with
  | zero => rfl
  | succ count induction =>
    simp only [operatorBackwardPrefix, List.range_succ, List.map_append,
      List.map_cons, List.map_nil, backwardProduct_append, FiniteObservations.backwardProduct]
    exact induction _

variable {X : Type*} [MeasurableSpace X]

theorem backwardPrefix_ae_operator (measure : ProbabilityMeasure X)
    (kernel : Kernel X X) [IsMarkovKernel kernel]
    (invariant : kernel.Invariant (measure : Measure X))
    (operator : Lp ℝ 2 (measure : Measure X) →L[ℝ] Lp ℝ 2 (measure : Measure X))
    (representation : ∀ (forcing : Lp ℝ 2 (measure : Measure X)) (bound : ℝ),
      0 ≤ bound → (∀ᵐ point ∂(measure : Measure X), ‖forcing point‖ ≤ bound) →
      ∀ᵐ point ∂(measure : Measure X),
        (∫ target, forcing target ∂kernel point) = operator forcing point)
    (tests : ℕ → X → ℝ) (testsMeasurable : ∀ index, Measurable (tests index))
    (bounds : ℕ → ℝ) (boundsNonnegative : ∀ index, 0 ≤ bounds index)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (multiplication : ℕ → Lp ℝ 2 (measure : Measure X) →L[ℝ] Lp ℝ 2 (measure : Measure X))
    (multiplicationAE : ∀ index forcing, ∀ᵐ point ∂(measure : Measure X),
      multiplication index forcing point = tests index point * forcing point)
    (count : ℕ) (terminal : X → ℝ) (terminalMeasurable : Measurable terminal)
    (terminalBound : ℝ) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound)
    (forcing : Lp ℝ 2 (measure : Measure X))
    (terminalAE : terminal =ᵐ[(measure : Measure X)] forcing) :
    backwardPrefix kernel tests count terminal =ᵐ[(measure : Measure X)]
      ((operatorBackwardPrefix operator multiplication count forcing :
        Lp ℝ 2 (measure : Measure X)) : X → ℝ) := by
  induction count generalizing terminal terminalBound forcing with
  | zero => exact terminalAE
  | succ count induction =>
    have forcingBounded : ∀ᵐ point ∂(measure : Measure X), ‖forcing point‖ ≤ terminalBound := by
      filter_upwards [terminalAE] with point equality
      rw [← equality]
      exact terminalBounded point
    have terminalComposed : terminal =ᵐ[kernel ∘ₘ (measure : Measure X)] forcing := by
      simpa only [invariant.def] using terminalAE
    have terminalTransported := Measure.ae_ae_of_ae_comp terminalComposed
    have integralAE : ∀ᵐ point ∂(measure : Measure X),
        (∫ target, terminal target ∂kernel point) = operator forcing point := by
      filter_upwards [terminalTransported,
        representation forcing terminalBound terminalBoundNonnegative forcingBounded]
        with point terminalEquality operatorEquality
      exact (integral_congr_ae terminalEquality).trans operatorEquality
    have transformedAE :
        (fun point => tests count point * ∫ target, terminal target ∂kernel point)
          =ᵐ[(measure : Measure X)] multiplication count (operator forcing) := by
      filter_upwards [integralAE, multiplicationAE count (operator forcing)]
        with point integralEquality multiplicationEquality
      rw [integralEquality, multiplicationEquality]
    change backwardPrefix kernel tests count
      (fun point => tests count point * ∫ target, terminal target ∂kernel point)
      =ᵐ[(measure : Measure X)] ((operatorBackwardPrefix operator multiplication count
        (multiplication count (operator forcing)) : Lp ℝ 2 (measure : Measure X)) : X → ℝ)
    apply induction (terminalBound := bounds count * terminalBound)
    · exact (testsMeasurable count).mul (kernel_integral_measurable kernel terminal terminalMeasurable)
    · exact mul_nonneg (boundsNonnegative count) terminalBoundNonnegative
    · intro point
      rw [norm_mul]
      exact mul_le_mul (testsBounded count point)
        (kernel_integral_norm_le kernel terminal terminalBound terminalBounded point)
        (norm_nonneg _) (boundsNonnegative count)
    · exact transformedAE

theorem pathLaw_prefix_integral_operator (measure : ProbabilityMeasure X)
    (kernel : Kernel X X) [IsMarkovKernel kernel]
    (invariant : kernel.Invariant (measure : Measure X))
    (operator : Lp ℝ 2 (measure : Measure X) →L[ℝ] Lp ℝ 2 (measure : Measure X))
    (representation : ∀ (forcing : Lp ℝ 2 (measure : Measure X)) (bound : ℝ),
      0 ≤ bound → (∀ᵐ point ∂(measure : Measure X), ‖forcing point‖ ≤ bound) →
      ∀ᵐ point ∂(measure : Measure X),
        (∫ target, forcing target ∂kernel point) = operator forcing point)
    (tests : ℕ → X → ℝ) (testsMeasurable : ∀ index, Measurable (tests index))
    (bounds : ℕ → ℝ) (boundsNonnegative : ∀ index, 0 ≤ bounds index)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (multiplication : ℕ → Lp ℝ 2 (measure : Measure X) →L[ℝ] Lp ℝ 2 (measure : Measure X))
    (multiplicationAE : ∀ index forcing, ∀ᵐ point ∂(measure : Measure X),
      multiplication index forcing point = tests index point * forcing point)
    (count : ℕ) (terminal : X → ℝ) (terminalMeasurable : Measurable terminal)
    (terminalBound : ℝ) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound)
    (forcing : Lp ℝ 2 (measure : Measure X))
    (terminalAE : terminal =ᵐ[(measure : Measure X)] forcing) :
    (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
      ∂pathLaw kernel (measure : Measure X)) =
      ∫ point, operatorBackwardPrefix operator multiplication count forcing point ∂(measure : Measure X) := by
  rw [pathLaw_prefix_integral_backward kernel measure tests count terminal bounds terminalBound
    testsMeasurable terminalMeasurable boundsNonnegative terminalBoundNonnegative testsBounded terminalBounded]
  exact integral_congr_ae (backwardPrefix_ae_operator measure kernel invariant operator representation
    tests testsMeasurable bounds boundsNonnegative testsBounded multiplication multiplicationAE count
    terminal terminalMeasurable terminalBound terminalBoundNonnegative terminalBounded forcing terminalAE)

theorem integral_eq_inner_one (measure : ProbabilityMeasure X)
    (one values : Lp ℝ 2 (measure : Measure X))
    (oneAE : (one : X → ℝ) =ᵐ[(measure : Measure X)] fun _ => 1) :
    (∫ point, values point ∂(measure : Measure X)) = inner ℝ one values := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [oneAE] with point equality
  change values point = values point * one point
  rw [equality, mul_one]

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

theorem continuous_pathLaw_prefix_integral_operator (measure : ProbabilityMeasure Space)
    (kernel : Kernel Space Space) [IsMarkovKernel kernel]
    (invariant : kernel.Invariant (measure : Measure Space))
    (operator : Lp ℝ 2 (measure : Measure Space) →L[ℝ] Lp ℝ 2 (measure : Measure Space))
    (representation : ∀ values : C(Space, ℝ), ∀ᵐ point ∂(measure : Measure Space),
      (∫ target, values target ∂kernel point) = operator (ContinuousMap.toLp 2 (measure : Measure Space) ℝ values) point)
    (tests : ℕ → Space →ᵇ ℝ) (count : ℕ) (terminal : Space →ᵇ ℝ) :
    (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
      ∂pathLaw kernel (measure : Measure Space)) =
      ∫ point, operatorBackwardPrefix operator
        (fun index => boundedContinuousLimitMultiplication measure (tests index)) count
        (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ terminal) point
        ∂(measure : Measure Space) := by
  apply pathLaw_prefix_integral_operator measure kernel invariant operator
    (fun forcing bound nonnegative bounded =>
      CountableMarkov.ae_kernel_integral_of_bounded_L2 (measure : Measure Space)
        operator kernel invariant representation forcing bound nonnegative bounded)
    (fun index point => tests index point) (fun index => (tests index).continuous.measurable)
    (fun index => ‖tests index‖) (fun _ => norm_nonneg _)
    (fun index point => (tests index).norm_coe_le_norm point)
    (fun index => boundedContinuousLimitMultiplication measure (tests index))
    (fun index forcing => BoundedL2Multiplication.operator_ae _ _ _ _ _ _ forcing)
    count terminal terminal.continuous.measurable ‖terminal‖ (norm_nonneg _)
    terminal.norm_coe_le_norm (BoundedContinuousFunction.toLp 2 (measure : Measure Space) ℝ terminal)
  exact (BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2 (measure : Measure Space) terminal).symm

end
end IGS.Sec31.DiscreteMarkov

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31 Filter Topology
open scoped BigOperators NNReal ENNReal Classical BoundedContinuousFunction

noncomputable section
set_option maxHeartbeats 4000000

variable {K : ℕ} {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]

omit [CompactSpace Space] in
theorem xiNativeFixedStep_prefix_integral_operator (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (mass : XiMassParameters system) (level : ℕ) (resistanceRate normalization : ℝ)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (rateNonnegative : 0 ≤ resistanceRate) (normalizationNonnegative : 0 ≤ normalization)
    (embeddings : ∀ level, XiVtx system level → Space)
    (embeddingsMeasurable : ∀ level, Measurable (embeddings level))
    (step : ℝ≥0) (tests : ℕ → Space →ᵇ ℝ) (count : ℕ) (terminal : Space →ᵇ ℝ) :
    (∫ path, (∏ index : Fin count, tests index.val (embeddings level (path index.val))) *
      terminal (embeddings level (path count)) ∂DiscreteMarkov.pathLaw
        (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
          rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative step)
        (xiVertexSpeedMeasure system mass level)) =
      ∫ point, DiscreteMarkov.operatorBackwardPrefix
        (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization step)
        (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
          embeddings embeddingsMeasurable (tests index) level) count
        (xiFiniteSpeedL2 system mass level (fun point => terminal (embeddings level point))) point
        ∂xiVertexSpeedMeasure system mass level := by
  apply DiscreteMarkov.pathLaw_prefix_integral_operator (xiNativeSpeedProbabilityMeasure system mass level)
    (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative step)
    (xiNativeFiniteKernel_invariant system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative step)
    (xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization step)
    (fun forcing _ _ _ => Eventually.of_forall fun point =>
      xiNativeFiniteKernel_integral system rulesConnected mass level resistanceRate normalization
        rulesLoopless rulesUnique plantingNonadjacent rateNonnegative normalizationNonnegative step point forcing)
    (fun index point => tests index (embeddings level point))
    (fun index => (tests index).continuous.measurable.comp (embeddingsMeasurable level))
    (fun index => ‖tests index‖) (fun _ => norm_nonneg _)
    (fun index point => (tests index).norm_coe_le_norm (embeddings level point))
    (fun index => boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
      embeddings embeddingsMeasurable (tests index) level)
    (fun index forcing => BoundedL2Multiplication.operator_ae _ _ _ _ _ _ forcing)
    count (fun point => terminal (embeddings level point))
    (terminal.continuous.measurable.comp (embeddingsMeasurable level)) ‖terminal‖ (norm_nonneg _)
    (fun point => terminal.norm_coe_le_norm (embeddings level point))
    (xiFiniteSpeedL2 system mass level (fun point => terminal (embeddings level point)))
  exact Eventually.of_forall fun point =>
    (xiFiniteSpeedL2_apply system rulesConnected mass level
      (fun location => terminal (embeddings level location)) point).symm


def XiNativeStationaryFixedStepObservationProperties (system : EIGSData K)
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
    (normalization : ℝ) (normalizationPositive : 0 < normalization) : Prop :=
    letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair
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
      ∀ _defaultPoint : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair,
      ∃ transition : ℝ≥0 → Kernel
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
          (XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair),
      ∃ markov : ∀ time, IsMarkovKernel (transition time),
        (∀ (time : ℝ≥0) (values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ)),
          ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass,
            (∫ location, values location ∂transition time point) =
              QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense time
                (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate
                  distanceRateGreaterThanOne metricEigenpair mass values) point) ∧
        (∀ time, (transition time).Invariant
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) ∧
        ∀ (step : ℝ≥0)
          (tests : ℕ → XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ)
          (count : ℕ)
          (terminal : XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair →ᵇ ℝ),
        Tendsto (fun level => ∫ path,
          (∏ index : Fin count, tests index.val (xiCompletionEmbedding system rulesConnected
            lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne)
            metricEigenpair level (path index.val))) *
          terminal (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
            (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (path count))
          ∂DiscreteMarkov.pathLaw
            (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
              rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le step)
            (xiVertexSpeedMeasure system mass level)) atTop
          (nhds (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
            ∂DiscreteMarkov.pathLaw (transition step)
              (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
                distanceRateGreaterThanOne metricEigenpair mass)))

theorem xiNativeStationaryFixedStepObservations_limit (system : EIGSData K)
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
    XiNativeStationaryFixedStepObservationProperties system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector
      vectorPositive renormalizationEigenpair normalization normalizationPositive := by
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
  dsimp only [XiNativeStationaryFixedStepObservationProperties]
  intro originalDense defaultPoint
  have kernelProperties := xiInvariantMarkovKernelProperties_of_dense_core system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair originalDense
  dsimp only [XiInvariantMarkovKernelProperties] at kernelProperties
  obtain ⟨kernelDensity, kernelForDefault⟩ := kernelProperties
  obtain ⟨transition, markov, representation, invariant⟩ := kernelForDefault defaultPoint
  refine ⟨transition, markov, representation, invariant, ?_⟩
  intro step tests count terminal
  letI : IsMarkovKernel (transition step) := markov step
  let observations := (List.range count).map (fun index => (step, tests index))
  let levelEvolution := fun level (time : ℝ≥0) =>
    xiNativeFiniteSemigroup system rulesConnected mass level resistanceRate normalization time
  let evolution := QuadraticEnergySpace.closedSemigroup originalDomain originalForm nonnegative closable originalDense
  let levelMultiplication := fun level multiplier =>
    boundedContinuousLevelMultiplication (xiNativeSpeedProbabilityMeasure system mass)
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
      (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair) multiplier level
  let multiplication := boundedContinuousLimitMultiplication
    (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass)
  have strong := xiNativeFiniteObservations_strong_limit system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent distancePositive oneColourDistance lengths lengthsPositive distanceRate distanceRateGreaterThanOne
    metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence originalDense observations
    (fun level => core.restrict level terminal) (core.embed terminal) (core.strong_restrict terminal)
  have pairingConvergence := core.strong_inner_tendsto (core.strong_restrict (1 : _ →ᵇ ℝ)) strong
  have levelExpectation (level : ℕ) :
      (∫ path, (∏ index : Fin count, tests index.val (xiCompletionEmbedding system rulesConnected
        lengths lengthsPositive distanceRate (zero_lt_one.trans distanceRateGreaterThanOne)
        metricEigenpair level (path index.val))) *
        terminal (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
          (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level (path count))
        ∂DiscreteMarkov.pathLaw
          (xiNativeFiniteKernel system rulesConnected mass level resistanceRate normalization
            rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le step)
          (xiVertexSpeedMeasure system mass level)) =
      inner ℝ (core.restrict level 1)
        (FiniteObservations.backwardProduct (levelEvolution level) (levelMultiplication level)
          observations (core.restrict level terminal)) := by
    rw [xiNativeFixedStep_prefix_integral_operator system rulesConnected mass level resistanceRate normalization
      rulesLoopless rulesUnique plantingNonadjacent ratePositive.le normalizationPositive.le
      (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair)
      (measurable_xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair) step tests count terminal]
    have terminalIdentity := xiSpeedL2Core_restrict_eq_finiteSpeedL2 system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass terminal level
    rw [← terminalIdentity]
    change (∫ point, DiscreteMarkov.operatorBackwardPrefix (levelEvolution level step)
      (fun index => levelMultiplication level (tests index)) count (core.restrict level terminal) point
      ∂xiVertexSpeedMeasure system mass level) = _
    rw [DiscreteMarkov.operatorBackwardPrefix_eq_backwardProduct]
    apply DiscreteMarkov.integral_eq_inner_one (xiNativeSpeedProbabilityMeasure system mass level)
    apply Eventually.of_forall
    intro point
    simp only [core, xiSpeedL2Core_restrict_eq_finiteSpeedL2,
      xiFiniteSpeedL2_apply system rulesConnected mass, BoundedContinuousFunction.coe_one, Pi.one_apply]
  have limitExpectation :
      (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
        ∂DiscreteMarkov.pathLaw (transition step)
          (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
            distanceRateGreaterThanOne metricEigenpair mass)) =
      inner ℝ (core.embed 1)
        (FiniteObservations.backwardProduct evolution multiplication observations (core.embed terminal)) := by
    have continuousRepresentation : ∀ values : C(XiMetricCompletion system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair, ℝ),
        ∀ᵐ point ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass,
        (∫ target, values target ∂transition step point) =
          evolution step (ContinuousMap.toLp 2
            (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
              distanceRateGreaterThanOne metricEigenpair mass) ℝ values) point := by
      intro values
      simpa only [evolution, xiContinuousL2Map] using representation step values
    change (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
      ∂DiscreteMarkov.pathLaw (transition step)
        (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass : Measure _)) = _
    rw [DiscreteMarkov.continuous_pathLaw_prefix_integral_operator
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) (transition step) (invariant step)
      (evolution step) continuousRepresentation tests count terminal]
    change (∫ point, DiscreteMarkov.operatorBackwardPrefix (evolution step)
      (fun index => multiplication (tests index)) count (core.embed terminal) point
      ∂xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) = _
    rw [DiscreteMarkov.operatorBackwardPrefix_eq_backwardProduct]
    apply DiscreteMarkov.integral_eq_inner_one
      (xiLimitProbabilityMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass)
    change (BoundedContinuousFunction.toLp 2
      (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass) ℝ (1 : _ →ᵇ ℝ) : _ → ℝ) =ᵐ[_] fun _ => 1
    simpa only [BoundedContinuousFunction.coe_one, Pi.one_apply] using
      BoundedContinuousFunction.coeFn_toLp (𝕜 := ℝ) 2
        (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass) (1 : _ →ᵇ ℝ)
  change Tendsto (fun level => inner ℝ (core.restrict level 1)
      (FiniteObservations.backwardProduct (levelEvolution level) (levelMultiplication level)
        observations (core.restrict level terminal))) atTop
      (nhds (inner ℝ (core.embed 1)
        (FiniteObservations.backwardProduct evolution multiplication observations (core.embed terminal))))
      at pairingConvergence
  simpa only [← levelExpectation, ← limitExpectation] using pairingConvergence

theorem exists_xiNativeStationaryFixedStepObservations_of_rules (system : EIGSData K)
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
      ∃ _originalDense : Dense ((xiContinuousEnergyLpDomain system rulesConnected
        parameters.lengths parameters.lengthsPositive (system.distanceSpectralRadius rulesConnected)
        distanceRateGreaterThanOne parameters.eigenpair mass resistanceRate ratePositive resistanceVector vectorPositive) :
        Set (Lp ℝ 2 (xiLimitMeasure system rulesConnected parameters.lengths parameters.lengthsPositive
          (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass))),
      XiNativeStationaryFixedStepObservationProperties system rulesConnected rulesLoopless rulesUnique
        plantingNonadjacent distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
        (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
        resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
        normalization normalizationPositive := by
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
  exact xiNativeStationaryFixedStepObservations_limit system rulesConnected rulesLoopless rulesUnique plantingNonadjacent
    distancePositive oneColourDistance parameters.lengths parameters.lengthsPositive
    (system.distanceSpectralRadius rulesConnected) distanceRateGreaterThanOne parameters.eigenpair mass
    resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    normalization normalizationPositive normalizedConvergence


end
end EIGS

#print axioms IGS.Sec31.DiscreteMarkov.backwardProduct_append
#print axioms IGS.Sec31.DiscreteMarkov.operatorBackwardPrefix_eq_backwardProduct
#print axioms IGS.Sec31.DiscreteMarkov.backwardPrefix_ae_operator
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_prefix_integral_operator
#print axioms IGS.Sec31.DiscreteMarkov.continuous_pathLaw_prefix_integral_operator
#print axioms EIGS.xiNativeFixedStep_prefix_integral_operator
#print axioms EIGS.XiNativeStationaryFixedStepObservationProperties
#print axioms EIGS.xiNativeStationaryFixedStepObservations_limit
#print axioms EIGS.exists_xiNativeStationaryFixedStepObservations_of_rules
