import RequestProject.Section31.ContinuousKernelFixedWindow

/-! Joint continuity of a given spatially continuous density from compact
smoothing windows of the same L² semigroup. This isolates the analytic proof
from the large concrete rule construction. No time continuity of chosen Riesz
rows is assumed. Candidate, awaiting compilation. -/
namespace IGS.Sec31
open MeasureTheory Filter Topology
open scoped NNReal
noncomputable section
set_option maxHeartbeats 3000000
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space)
    [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuous_kernel_joint_of_compact_windows
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law) (embeddingInjective : Function.Injective embedding)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (semigroup : ℝ≥0 → Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (addition : ∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime))
    (symmetric : ∀ time, IsSelfAdjoint (semigroup time))
    (jointOperatorContinuous : Continuous (fun point : Lp ℝ 2 law × ℝ≥0 => semigroup point.2 point.1))
    (kernel : {time : ℝ≥0 // 0 < time} → Space → Space → ℝ)
    (kernelContinuous : ∀ time, Continuous (fun points : Space × Space => kernel time points.1 points.2))
    (lifted : {time : ℝ≥0 // 0 < time} → Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (liftedRepresentation : ∀ time forcing point, lifted time forcing point =
      ∫ other, kernel time point other * forcing other ∂law)
    (liftedCompatibility : ∀ time forcing, embedding (lifted time forcing) = semigroup time.val forcing)
    (smoothing : ∀ window : ℝ≥0, 0 < window → ∃ windowLifted : Lp ℝ 2 law →L[ℝ] C(Space, ℝ),
      IsCompactOperator windowLifted ∧ ∀ forcing, embedding (windowLifted forcing) = semigroup window forcing) :
    Continuous (fun point : {time : ℝ≥0 // 0 < time} × Space × Space =>
      kernel point.1 point.2.1 point.2.2) := by
    rw [continuous_iff_continuousAt]
    intro reference
    let window : ℝ≥0 := reference.1.val / 4
    have windowPositive : 0 < window := div_pos reference.1.prop (by norm_num)
    obtain ⟨windowLifted, windowCompact, windowCompatibility⟩ := smoothing window windowPositive
    have rowContinuous : Continuous (continuousOperatorKernelRow windowLifted) :=
      continuousOperatorKernelRow_continuous windowLifted windowCompact
    let alternateKernel := fun point : {time : ℝ≥0 // 0 < time} × Space × Space =>
      inner ℝ (continuousOperatorKernelRow windowLifted point.2.1)
        (semigroup (point.1.val - (window + window)) (continuousOperatorKernelRow windowLifted point.2.2))
    have alternateContinuous : Continuous alternateKernel := by
      have firstRowContinuous : Continuous (fun point :
          {time : ℝ≥0 // 0 < time} × Space × Space =>
          continuousOperatorKernelRow windowLifted point.2.1) :=
        rowContinuous.comp (continuous_fst.comp continuous_snd)
      have secondRowContinuous : Continuous (fun point :
          {time : ℝ≥0 // 0 < time} × Space × Space =>
          continuousOperatorKernelRow windowLifted point.2.2) :=
        rowContinuous.comp (continuous_snd.comp continuous_snd)
      have residualTimeContinuous : Continuous (fun point :
          {time : ℝ≥0 // 0 < time} × Space × Space =>
          point.1.val - (window + window)) :=
        (continuous_subtype_val.comp continuous_fst).sub continuous_const
      have inputContinuous : Continuous (fun point :
          {time : ℝ≥0 // 0 < time} × Space × Space =>
          (continuousOperatorKernelRow windowLifted point.2.2, point.1.val - (window + window))) :=
        secondRowContinuous.prodMk residualTimeContinuous
      have outputContinuous : Continuous (fun point :
          {time : ℝ≥0 // 0 < time} × Space × Space =>
          semigroup (point.1.val - (window + window))
            (continuousOperatorKernelRow windowLifted point.2.2)) :=
        jointOperatorContinuous.comp inputContinuous
      exact firstRowContinuous.inner outputContinuous
    have kernelEquality (time : {time : ℝ≥0 // 0 < time}) (timeLarge : window + window ≤ time.val)
        (first second : Space) :
        kernel time first second = alternateKernel (time, first, second) := by
      let residual := time.val - (window + window)
      have timeDecomposition : window + (residual + window) = time.val := by
        calc
          _ = (window + window) + residual := by ring
          _ = time.val := add_tsub_cancel_of_le timeLarge
      have factorization : (semigroup window).comp
          ((semigroup residual).comp (semigroup window)) = semigroup time.val := by
        calc
          _ = (semigroup window).comp (semigroup (residual + window)) :=
            congrArg (fun operator => (semigroup window).comp operator)
              (addition residual window).symm
          _ = semigroup (window + (residual + window)) :=
            (addition
              window (residual + window)).symm
          _ = _ := congrArg semigroup timeDecomposition
      have windowOutputEquality (forcing : Lp ℝ 2 law) :
          lifted time forcing = windowLifted (semigroup residual (semigroup window forcing)) := by
        apply embeddingInjective
        rw [liftedCompatibility, windowCompatibility]
        exact (congrArg (fun operator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law => operator forcing) factorization).symm
      let firstRow : C(Space, ℝ) := ⟨kernel time first,
        (kernelContinuous time).comp (continuous_const.prodMk continuous_id)⟩
      let secondRow : C(Space, ℝ) :=
        ⟨fun other => inner ℝ (continuousOperatorKernelRow windowLifted first)
          (semigroup residual (continuousOperatorKernelRow windowLifted other)),
          continuous_const.inner ((semigroup residual).continuous.comp rowContinuous)⟩
      have rowEquality : firstRow = secondRow := by
        apply continuous_L2_kernel_row_unique law
        intro forcing
        calc
          _ = lifted time forcing first := (liftedRepresentation time forcing first).symm
          _ = windowLifted (semigroup residual (semigroup window forcing)) first :=
            congrArg (fun function : C(Space, ℝ) => function first) (windowOutputEquality forcing)
          _ = _ := continuousOperator_fixed_window_integral law embedding embeddingAE windowLifted
            (semigroup window) (semigroup residual)
            (symmetric window)
            (symmetric residual)
            windowCompatibility first forcing
      exact congrArg (fun function : C(Space, ℝ) => function second) rowEquality
    have referenceLarge : window + window < reference.1.val := by
      change (window : ℝ) + (window : ℝ) < (reference.1.val : ℝ)
      simp only [window, NNReal.coe_div, NNReal.coe_ofNat]
      have referencePositive : 0 < (reference.1.val : ℝ) := reference.1.prop
      linarith
    have eventuallyLarge : ∀ᶠ nearby in 𝓝 reference, window + window < nearby.1.val :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.tendsto.eventually (lt_mem_nhds referenceLarge)
    apply alternateContinuous.continuousAt.congr_of_eventuallyEq
    filter_upwards [eventuallyLarge] with nearby nearbyLarge
    exact kernelEquality nearby.1 nearbyLarge.le nearby.2.1 nearby.2.2

end
end IGS.Sec31

#print axioms IGS.Sec31.continuous_kernel_joint_of_compact_windows