import RequestProject.Section31.QuadraticEnergyYosida

/-! Algebraic identities for continuous representatives of the actual closed
resolvent. Injective intertwining transfers the identities from the constructed
closed quadratic form; no commutation or Yosida compatibility is assumed. -/

namespace IGS.Sec31.QuadraticEnergySpace

variable {Space Hilbert : Type*}
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]
  [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert] [CompleteSpace Hilbert]

variable (domain : Submodule ℝ Hilbert) (form : QuadraticForm ℝ domain)
  (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
  (domainDense : Dense (domain : Set Hilbert))
  (embedding : Space →ₗ[ℝ] Hilbert) (embeddingInjective : Function.Injective embedding)
  (step otherStep : ℝ) (stepPositive : 0 < step) (stepAtMostOne : step ≤ 1)
  (otherPositive : 0 < otherStep) (otherAtMostOne : otherStep ≤ 1)
  (resolver otherResolver : Space →L[ℝ] Space)
  (intertwining : ∀ values, embedding (resolver values) =
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
      (embedding values))
  (otherIntertwining : ∀ values, embedding (otherResolver values) =
    smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
      (embedding values))

include embeddingInjective intertwining otherIntertwining in
theorem lifted_smallStepResolvent_commute : Commute resolver otherResolver := by
  apply ContinuousLinearMap.ext
  intro values
  apply embeddingInjective
  change embedding (resolver (otherResolver values)) = embedding (otherResolver (resolver values))
  rw [intertwining, otherIntertwining, otherIntertwining, intertwining]
  exact congrArg (fun operator : Hilbert →L[ℝ] Hilbert => operator (embedding values))
    (smallStepResolvent_commute domain form nonnegative closable domainDense
      step stepPositive stepAtMostOne otherStep otherPositive otherAtMostOne)

include embeddingInjective intertwining otherIntertwining in
theorem lifted_yosidaGenerator_resolvent_compatibility (values : Space) :
    (step⁻¹ • (ContinuousLinearMap.id ℝ Space - resolver)) (otherResolver values) =
      resolver ((otherStep⁻¹ • (ContinuousLinearMap.id ℝ Space - otherResolver)) values) := by
  apply embeddingInjective
  have firstTransport (argument : Space) :
      embedding ((step⁻¹ • (ContinuousLinearMap.id ℝ Space - resolver)) argument) =
        yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne
          (embedding argument) := by
    change embedding (step⁻¹ • (argument - resolver argument)) =
      step⁻¹ • (embedding argument -
        smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
          (embedding argument))
    rw [map_smul, map_sub, intertwining]
  have secondTransport :
      embedding ((otherStep⁻¹ • (ContinuousLinearMap.id ℝ Space - otherResolver)) values) =
        yosidaGenerator domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
          (embedding values) := by
    change embedding (otherStep⁻¹ • (values - otherResolver values)) =
      otherStep⁻¹ • (embedding values -
        smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
          (embedding values))
    rw [map_smul, map_sub, otherIntertwining]
  rw [firstTransport, intertwining, secondTransport, otherIntertwining]
  change yosidaGenerator domain form nonnegative closable domainDense step stepPositive stepAtMostOne
      (smallStepResolvent domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
        (embedding values)) =
    smallStepResolvent domain form nonnegative closable domainDense step stepPositive stepAtMostOne
      (yosidaGenerator domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne
        (embedding values))
  rw [yosidaGenerator_eq_closedGenerator domain form nonnegative closable domainDense
    otherStep otherPositive otherAtMostOne]
  exact yosidaGenerator_on_domain domain form nonnegative closable domainDense step stepPositive stepAtMostOne
    ((smallStepEquiv domain form nonnegative closable domainDense otherStep otherPositive otherAtMostOne).symm
      (embedding values))

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.lifted_smallStepResolvent_commute
#print axioms IGS.Sec31.QuadraticEnergySpace.lifted_yosidaGenerator_resolvent_compatibility
