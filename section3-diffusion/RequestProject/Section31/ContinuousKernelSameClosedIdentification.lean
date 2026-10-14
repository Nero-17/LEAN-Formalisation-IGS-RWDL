import RequestProject.Section31.ContinuousKernelFixedWindow

/-! Continuous kernel rows representing lifts of the same closed L2
operator coincide at every point. Full support upgrades the integral
identification to pointwise equality; equality of the kernels is a conclusion.
Candidate source, awaiting independent full-file compilation. -/

namespace IGS.Sec31
open MeasureTheory
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

theorem continuousKernel_eq_of_same_closed_operator
    (law : Measure Space) [IsFiniteMeasure law] [law.IsOpenPosMeasure]
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingInjective : Function.Injective embedding)
    (operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (firstKernel secondKernel : Space → Space → ℝ)
    (firstContinuous : Continuous (fun points : Space × Space => firstKernel points.1 points.2))
    (secondContinuous : Continuous (fun points : Space × Space => secondKernel points.1 points.2))
    (firstLift secondLift : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (firstRepresentation : ∀ forcing point,
      firstLift forcing point = ∫ other, firstKernel point other * forcing other ∂law)
    (secondRepresentation : ∀ forcing point,
      secondLift forcing point = ∫ other, secondKernel point other * forcing other ∂law)
    (firstCompatibility : ∀ forcing, embedding (firstLift forcing) = operator forcing)
    (secondCompatibility : ∀ forcing, embedding (secondLift forcing) = operator forcing) :
    firstKernel = secondKernel := by
  have liftEquality : firstLift = secondLift := by
    apply ContinuousLinearMap.ext
    intro forcing
    apply embeddingInjective
    exact (firstCompatibility forcing).trans (secondCompatibility forcing).symm
  funext point other
  have rowEquality := continuous_L2_kernel_row_unique law
    (⟨firstKernel point, firstContinuous.comp (continuous_const.prodMk continuous_id)⟩ : C(Space, ℝ))
    (⟨secondKernel point, secondContinuous.comp (continuous_const.prodMk continuous_id)⟩ : C(Space, ℝ))
    (fun forcing => (firstRepresentation forcing point).symm.trans
      ((congrArg (fun lifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ) => lifted forcing point)
        liftEquality).trans (secondRepresentation forcing point)))
  exact congrArg (fun row : C(Space, ℝ) => row other) rowEquality

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousKernel_eq_of_same_closed_operator
