import RequestProject.Section31.ContinuousKernelFixedWindow

/-! Strict positivity from the same closed L² semigroup. Each Riesz row is
identified internally with the embedded continuous density row. Thus its
continuity, nonnegativity, and nonzero mass are proved rather than assumptions
on a choice of representatives. Three equal time factors and full-support
continuous-row uniqueness identify the given kernel with the positive scalar
correlation. The actual consumer supplies that correlation from its form.
Candidate source, awaiting whole-file compilation. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space)
    [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuousOperatorKernelRow_eq_embedded_density
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (lifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ)) (kernel : Space → Space → ℝ)
    (kernelContinuous : Continuous (fun points : Space × Space => kernel points.1 points.2))
    (representation : ∀ values point, lifted values point = ∫ other, kernel point other * values other ∂law)
    (point : Space) :
    continuousOperatorKernelRow lifted point = embedding
      ⟨kernel point, kernelContinuous.comp (continuous_const.prodMk continuous_id)⟩ := by
  apply ext_inner_right ℝ
  intro values
  rw [← continuousOperatorKernelRow_represents, representation, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [embeddingAE
    ⟨kernel point, kernelContinuous.comp (continuous_const.prodMk continuous_id)⟩] with other identity
  rw [identity]
  simp only [RCLike.inner_apply, conj_trivial]
  exact mul_comm _ _

theorem continuousOperatorKernelRow_density_properties
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (lifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ)) (kernel : Space → Space → ℝ)
    (kernelContinuous : Continuous (fun points : Space × Space => kernel points.1 points.2))
    (kernelNonnegative : ∀ first second, 0 ≤ kernel first second)
    (kernelMass : ∀ point, (∫ other, kernel point other ∂law) = 1)
    (representation : ∀ values point, lifted values point = ∫ other, kernel point other * values other ∂law) :
    Continuous (continuousOperatorKernelRow lifted) ∧
      ∀ point, (∀ᵐ other ∂law, 0 ≤ continuousOperatorKernelRow lifted point other) ∧
        continuousOperatorKernelRow lifted point ≠ 0 := by
  let continuousRows : Space → C(Space, ℝ) := fun point =>
    ⟨kernel point, kernelContinuous.comp (continuous_const.prodMk continuous_id)⟩
  have rowsContinuous : Continuous continuousRows := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact kernelContinuous
  have rowEquality (point : Space) : continuousOperatorKernelRow lifted point = embedding (continuousRows point) :=
    continuousOperatorKernelRow_eq_embedded_density law embedding embeddingAE lifted kernel kernelContinuous representation point
  refine ⟨(embedding.continuous.comp rowsContinuous).congr (fun point => (rowEquality point).symm), ?_⟩
  intro point
  have rowAE : (fun other => continuousOperatorKernelRow lifted point other) =ᵐ[law] kernel point := by
    rw [rowEquality]
    exact embeddingAE (continuousRows point)
  refine ⟨?_, ?_⟩
  · filter_upwards [rowAE] with other identity
    change continuousOperatorKernelRow lifted point other = kernel point other at identity
    change 0 ≤ continuousOperatorKernelRow lifted point other
    rw [identity]
    exact kernelNonnegative point other
  · have mass : (∫ other, continuousOperatorKernelRow lifted point other ∂law) = 1 :=
      (integral_congr_ae rowAE).trans (kernelMass point)
    intro zero
    rw [zero, integral_congr_ae (Lp.coeFn_zero ℝ 2 law)] at mass
    simp only [Pi.zero_apply, integral_zero] at mass
    norm_num at mass

theorem continuous_kernel_strict_positive_of_same_closed_semigroup
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law) (embeddingInjective : Function.Injective embedding)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (semigroup : ℝ≥0 → Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (addition : ∀ firstTime secondTime,
      semigroup (firstTime + secondTime) = (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (positiveCorrelation : ∀ time, 0 < time → ∀ first second : Lp ℝ 2 law,
      (∀ᵐ point ∂law, 0 ≤ first point) → (∀ᵐ point ∂law, 0 ≤ second point) →
      first ≠ 0 → second ≠ 0 → 0 < inner ℝ first (semigroup time second))
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ)
    (kernelContinuous : ∀ time, Continuous (fun points : Space × Space => kernel time points.1 points.2))
    (kernelNonnegative : ∀ time first second, 0 ≤ kernel time first second)
    (kernelMass : ∀ time point, (∫ other, kernel time point other ∂law) = 1)
    (lifted : {time : ℝ≥0 // 0 < time} → Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (representation : ∀ time values point,
      lifted time values point = ∫ other, kernel time point other * values other ∂law)
    (compatibility : ∀ time values, embedding (lifted time values) = semigroup time.val values) :
    ∀ time first second, 0 < kernel time first second := by
  intro time first second
  let window : ℝ≥0 := time.val / 3
  have windowPositive : 0 < window := div_pos time.prop (by norm_num)
  let windowTime : {time : ℝ≥0 // 0 < time} := ⟨window, windowPositive⟩
  have windowProperties := continuousOperatorKernelRow_density_properties law embedding embeddingAE
    (lifted windowTime) (kernel windowTime) (kernelContinuous windowTime)
    (kernelNonnegative windowTime) (kernelMass windowTime) (representation windowTime)
  have timeDecomposition : window + (window + window) = time.val := by
    dsimp only [window]
    ring
  have factorization : (semigroup window).comp ((semigroup window).comp (semigroup window)) = semigroup time.val := by
    rw [← addition window window, ← addition window (window + window), timeDecomposition]
  have liftedEquality (values : Lp ℝ 2 law) :
      lifted time values = lifted windowTime (semigroup window (semigroup window values)) := by
    apply embeddingInjective
    rw [compatibility, compatibility]
    exact (congrArg (fun operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law => operator values) factorization).symm
  let givenRow : C(Space, ℝ) :=
    ⟨kernel time first, (kernelContinuous time).comp (continuous_const.prodMk continuous_id)⟩
  let factoredRow : C(Space, ℝ) :=
    ⟨fun other => inner ℝ (continuousOperatorKernelRow (lifted windowTime) first)
      (semigroup window (continuousOperatorKernelRow (lifted windowTime) other)),
      continuous_const.inner ((semigroup window).continuous.comp windowProperties.1)⟩
  have rowEquality : givenRow = factoredRow := by
    apply continuous_L2_kernel_row_unique law
    intro values
    calc
      _ = lifted time values first := (representation time values first).symm
      _ = lifted windowTime (semigroup window (semigroup window values)) first :=
        congrArg (fun function : C(Space, ℝ) => function first) (liftedEquality values)
      _ = _ := continuousOperator_fixed_window_integral law embedding embeddingAE (lifted windowTime)
        (semigroup window) (semigroup window) (symmetric window) (symmetric window)
        (compatibility windowTime) first values
  have kernelEquality : kernel time first second =
      inner ℝ (continuousOperatorKernelRow (lifted windowTime) first)
        (semigroup window (continuousOperatorKernelRow (lifted windowTime) second)) :=
    congrArg (fun function : C(Space, ℝ) => function second) rowEquality
  rw [kernelEquality]
  exact positiveCorrelation window windowPositive _ _ (windowProperties.2 first).1
    (windowProperties.2 second).1 (windowProperties.2 first).2 (windowProperties.2 second).2

end
end IGS.Sec31

#print axioms IGS.Sec31.continuousOperatorKernelRow_eq_embedded_density
#print axioms IGS.Sec31.continuousOperatorKernelRow_density_properties
#print axioms IGS.Sec31.continuous_kernel_strict_positive_of_same_closed_semigroup
