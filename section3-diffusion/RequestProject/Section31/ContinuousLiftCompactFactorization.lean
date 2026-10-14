import Mathlib.Analysis.Normed.Operator.Compact

/-! A continuous lift at twice a time factors through the L² operator at
half that time. Injective embedding identifies the factorization. -/

namespace IGS.Sec31

variable {Hilbert Continuous : Type*}
    [NormedAddCommGroup Hilbert] [NormedSpace ℝ Hilbert]
    [NormedAddCommGroup Continuous] [NormedSpace ℝ Continuous]

theorem continuousLift_compact_of_half_time
    (embedding : Continuous →L[ℝ] Hilbert) (embeddingInjective : Function.Injective embedding)
    (lifted halfLifted : Hilbert →L[ℝ] Continuous)
    (operator halfOperator : Hilbert →L[ℝ] Hilbert)
    (liftedCompatibility : ∀ values, embedding (lifted values) = operator values)
    (halfCompatibility : ∀ values, embedding (halfLifted values) = halfOperator values)
    (factorization : operator = halfOperator.comp halfOperator)
    (halfCompact : IsCompactOperator halfOperator) : IsCompactOperator lifted := by
  have liftedFactorization : lifted = halfLifted.comp halfOperator := by
    ext values
    apply embeddingInjective
    rw [liftedCompatibility, ContinuousLinearMap.comp_apply, halfCompatibility, factorization]
    rfl
  rw [liftedFactorization]
  exact halfCompact.clm_comp halfLifted

end IGS.Sec31

#print axioms IGS.Sec31.continuousLift_compact_of_half_time
