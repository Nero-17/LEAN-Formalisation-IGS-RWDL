import RequestProject.Section31.ContinuousKernelDensity

/-! Uniqueness of continuous L² kernel rows and a fixed smoothing-window
representation. These avoid any continuity assumption on chosen time-indexed
Riesz representatives. -/

namespace IGS.Sec31

open MeasureTheory Filter Topology
open scoped ENNReal
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] (law : Measure Space)
    [IsFiniteMeasure law] [law.IsOpenPosMeasure]

theorem continuous_L2_kernel_row_unique (first second : C(Space, ℝ))
    (pairingEquality : ∀ test : Lp ℝ 2 law,
      (∫ point, first point * test point ∂law) = ∫ point, second point * test point ∂law) :
    first = second := by
  have firstIntegrable : Integrable first law := by
    apply Integrable.of_bound first.continuous.measurable.aestronglyMeasurable ‖first‖
    exact Eventually.of_forall fun point => first.norm_coe_le_norm point
  have secondIntegrable : Integrable second law := by
    apply Integrable.of_bound second.continuous.measurable.aestronglyMeasurable ‖second‖
    exact Eventually.of_forall fun point => second.norm_coe_le_norm point
  have equalityAE : (first : Space → ℝ) =ᵐ[law] second := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq first second firstIntegrable secondIntegrable
    intro region regionMeasurable regionFinite
    let test := indicatorConstLp 2 regionMeasurable regionFinite.ne (1 : ℝ)
    have indicatorAE := indicatorConstLp_coeFn (p := (2 : ℝ≥0∞))
      (hs := regionMeasurable) (hμs := regionFinite.ne) (c := (1 : ℝ))
    have indicatorIntegral (function : C(Space, ℝ)) :
        (∫ point, function point * test point ∂law) = ∫ point in region, function point ∂law := by
      calc
        _ = ∫ point, region.indicator function point ∂law := by
          apply integral_congr_ae
          filter_upwards [indicatorAE] with point indicator
          rw [indicator]
          by_cases membership : point ∈ region <;> simp [Set.indicator, membership]
        _ = _ := integral_indicator regionMeasurable
    have equality := pairingEquality test
    rw [indicatorIntegral, indicatorIntegral] at equality
    exact equality
  exact ContinuousMap.ext (congrFun (MeasureTheory.Measure.eq_of_ae_eq equalityAE first.continuous second.continuous))

theorem continuousOperator_fixed_window_integral
    (embedding : C(Space, ℝ) →L[ℝ] Lp ℝ 2 law)
    (embeddingAE : ∀ function : C(Space, ℝ), (embedding function : Space → ℝ) =ᵐ[law] function)
    (smoothing : Lp ℝ 2 law →L[ℝ] C(Space, ℝ))
    (smoothingOperator residualOperator : Lp ℝ 2 law →L[ℝ] Lp ℝ 2 law)
    (smoothingSelfAdjoint : IsSelfAdjoint smoothingOperator)
    (residualSelfAdjoint : IsSelfAdjoint residualOperator)
    (compatibility : ∀ values, embedding (smoothing values) = smoothingOperator values)
    (point : Space) (values : Lp ℝ 2 law) :
    smoothing (residualOperator (smoothingOperator values)) point =
      ∫ other, inner ℝ (continuousOperatorKernelRow smoothing point)
        (residualOperator (continuousOperatorKernelRow smoothing other)) * values other ∂law := by
  calc
    _ = inner ℝ (continuousOperatorKernelRow smoothing point)
        (residualOperator (smoothingOperator values)) := continuousOperatorKernelRow_represents _ _ _
    _ = inner ℝ (residualOperator (continuousOperatorKernelRow smoothing point)) (smoothingOperator values) :=
      (residualSelfAdjoint.isSymmetric _ _).symm
    _ = inner ℝ (smoothingOperator (residualOperator (continuousOperatorKernelRow smoothing point))) values :=
      (smoothingSelfAdjoint.isSymmetric _ _).symm
    _ = inner ℝ (embedding (smoothing (residualOperator (continuousOperatorKernelRow smoothing point)))) values := by
      rw [compatibility]
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [embeddingAE (smoothing (residualOperator (continuousOperatorKernelRow smoothing point)))]
        with other representative
      rw [representative, continuousOperatorKernelRow_represents]
      simp only [RCLike.inner_apply, conj_trivial]
      have symmetry := residualSelfAdjoint.isSymmetric
        (continuousOperatorKernelRow smoothing point) (continuousOperatorKernelRow smoothing other)
      rw [real_inner_comm] at symmetry
      simpa only [mul_comm] using congrArg (fun scalar : ℝ => values other * scalar) symmetry

end
end IGS.Sec31

#print axioms IGS.Sec31.continuous_L2_kernel_row_unique
#print axioms IGS.Sec31.continuousOperator_fixed_window_integral
