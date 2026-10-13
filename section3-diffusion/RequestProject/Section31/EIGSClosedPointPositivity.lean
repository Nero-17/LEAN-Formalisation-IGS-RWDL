import RequestProject.Section31.EIGSPointEnergyFunctional
import RequestProject.Section31.EIGSL2ClosabilityWithoutPrimitive
import RequestProject.Section31.EIGSL2EnergyContraction

/-! Point evaluation on the actual E1 completion preserves ambient positivity.
This is proved by positive-part core contraction and the bounded simultaneous
ambient/evaluation lift; it is not an extra positivity premise. -/

namespace EIGS

open MeasureTheory Filter Topology IGS.Sec31
open scoped BoundedContinuousFunction

set_option maxHeartbeats 3000000
variable {K : ℕ} (system : EIGSData K)
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

include rulesConnected rulesLoopless rulesUnique plantingNonadjacent distancePositive oneColourDistance

theorem xiClosed_point_functional_nonnegative (level : ℕ) (vertex : XiVtx system level) :
    let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
    let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
      distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
    ∀ closable : QuadraticEnergySpace.SequentiallyClosable originalDomain originalForm,
    ∀ functional : QuadraticEnergySpace originalDomain originalForm nonnegative →L[ℝ] ℝ,
    (∀ values, functional values =
        ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm values.value).val
            (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
              (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)) →
    ∀ target : QuadraticEnergySpace.closedDomain originalDomain originalForm nonnegative,
      (∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass), 0 ≤ (target.val : _ → ℝ) point) →
      0 ≤ QuadraticEnergySpace.completionFunctional originalDomain originalForm nonnegative functional
        ((QuadraticEnergySpace.closedDomainEquiv originalDomain originalForm nonnegative closable).symm target) := by
  classical
  letI := xiCompletion_compactSpace system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair
  let originalDomain := xiContinuousEnergyLpDomain system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive
  let originalForm := xiContinuousLpEnergyQuadraticForm system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  let nonnegative := xiContinuousLpEnergyQuadraticForm_nonnegative system rulesConnected lengths lengthsPositive distanceRate
    distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair
  dsimp only
  intro closable functional functionalAgreement target targetNonnegative
  have positivePartLipschitz : LipschitzWith 1 (fun value : ℝ => max value 0) := LipschitzWith.id.max_const 0
  have positivePartZero : max (0 : ℝ) 0 = 0 := max_self 0
  apply QuadraticEnergySpace.completionFunctional_nonnegative_of_core_contraction originalDomain originalForm nonnegative
    closable functional (positivePartLipschitz.compLp positivePartZero)
    (positivePartLipschitz.continuous_compLp positivePartZero)
  · intro original
    obtain ⟨contracted, contractedAE, contractedEnergy⟩ := xiContinuousLpEnergy_normal_contraction
      system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass
      resistanceRate ratePositive resistanceVector vectorPositive renormalizationEigenpair (fun value => max value 0)
      (fun first second => by simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
        positivePartLipschitz.dist_le_mul first second) original
    refine ⟨contracted, ?_, contractedEnergy, ?_⟩
    · apply Lp.ext
      exact contractedAE.trans (positivePartLipschitz.coeFn_compLp positivePartZero original.val).symm
    · rw [functionalAgreement]
      let representative := (xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate
        distanceRateGreaterThanOne metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).symm contracted
      have representativeClass := congrArg Subtype.val
        ((xiContinuousEnergyLpEquiv system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
          metricEigenpair mass resistanceRate ratePositive resistanceVector vectorPositive).apply_symm_apply contracted)
      change xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass representative.val = contracted.val at representativeClass
      have representativeAE := ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2)
        (xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne metricEigenpair mass)
        representative.val
      change (xiContinuousL2Map system rulesConnected lengths lengthsPositive distanceRate distanceRateGreaterThanOne
        metricEigenpair mass representative.val : _ → ℝ) =ᵐ[_] representative.val at representativeAE
      rw [representativeClass] at representativeAE
      have positiveAE : ∀ᵐ point ∂(xiLimitMeasure system rulesConnected lengths lengthsPositive distanceRate
          distanceRateGreaterThanOne metricEigenpair mass), 0 ≤ representative.val point := by
        filter_upwards [representativeAE, contractedAE] with point sameRepresentative sameContraction
        rw [← sameRepresentative, sameContraction]
        exact le_max_right _ _
      have equality : (fun point => representative.val point) = fun point => max (representative.val point) 0 :=
        Measure.eq_of_ae_eq (positiveAE.mono fun _ bound => (max_eq_left bound).symm)
          representative.val.continuous (representative.val.continuous.max continuous_const)
      have atPoint := congrFun equality (xiCompletionEmbedding system rulesConnected lengths lengthsPositive distanceRate
        (zero_lt_one.trans distanceRateGreaterThanOne) metricEigenpair level vertex)
      change 0 ≤ representative.val _
      rw [atPoint]
      exact le_max_right _ _
  · apply Lp.ext
    filter_upwards [positivePartLipschitz.coeFn_compLp positivePartZero target.val, targetNonnegative]
      with point sameValue bound
    exact sameValue.trans (max_eq_left bound)

end EIGS

#print axioms EIGS.xiClosed_point_functional_nonnegative

