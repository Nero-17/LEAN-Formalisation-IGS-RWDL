import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.ContinuousMap.Compact

/-! A local anchored integral estimate identifies a point limit with the value
of a continuous L² limit. All weights and decay estimates are intermediate
data; the actual address-star consumer constructs them internally.
Candidate source, awaiting compilation. -/

namespace IGS.Sec31
open MeasureTheory Filter Topology
noncomputable section

variable {Space Address : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space] [MeasurableSpace Address]
    (law : Measure Address) [IsFiniteMeasure law]

private theorem weighted_square_triangle_le (value limit anchor weight : ℝ)
    (weightNonnegative : 0 ≤ weight) (weightBound : weight ≤ 2) :
    weight * (value - anchor) ^ 2 ≤ 4 * (value - limit) ^ 2 +
      2 * (weight * (limit - anchor) ^ 2) := by
  have triangle : (value - anchor) ^ 2 ≤ 2 * (value - limit) ^ 2 + 2 * (limit - anchor) ^ 2 := by
    nlinarith [sq_nonneg ((value - limit) - (limit - anchor))]
  have multiplied := mul_le_mul_of_nonneg_left triangle weightNonnegative
  have bounded := mul_le_mul_of_nonneg_right weightBound (sq_nonneg (value - limit))
  nlinarith

theorem continuous_point_limit_eq_of_weighted_stars
    (addressPoint : Address → Space) (addressMeasurable : Measurable addressPoint)
    (point : Space) (weights : ℕ → Address → ℝ)
    (weightsMeasurable : ∀ level, Measurable (weights level))
    (weightsNonnegative : ∀ level address, 0 ≤ weights level address)
    (weightsBounded : ∀ level address, weights level address ≤ 2)
    (massPositive : ∀ level, 0 < ∫ address, weights level address ∂law)
    (mesh : ℕ → ℝ) (meshLimit : Tendsto mesh atTop (𝓝 0))
    (supportMesh : ∀ level address, weights level address ≠ 0 →
      dist (addressPoint address) point ≤ mesh level)
    (decay : ℕ → ℝ) (decayLimit : Tendsto decay atTop (𝓝 0))
    (constant : ℝ) (sequence : ℕ → C(Space, ℝ)) (limit : C(Space, ℝ))
    (energies : ℕ → ℝ) (energy : ℝ) (energyLimit : Tendsto energies atTop (𝓝 energy))
    (pointLimit : ℝ) (pointConvergence : Tendsto (fun index => sequence index point) atTop (𝓝 pointLimit))
    (ambientConvergence : Tendsto (fun index =>
      ∫ address, (sequence index (addressPoint address) - limit (addressPoint address)) ^ 2 ∂law)
      atTop (𝓝 0))
    (anchorBound : ∀ index level anchor,
      (∫ address, weights level address ∂law) * (sequence index point - anchor) ^ 2 ≤
        constant * decay level * (∫ address, weights level address ∂law) * energies index +
        3 * ∫ address, weights level address * (sequence index (addressPoint address) - anchor) ^ 2 ∂law) :
    pointLimit = limit point := by
  have squareIntegrable (function : C(Space, ℝ)) (anchor : ℝ) :
      Integrable (fun address => (function (addressPoint address) - anchor) ^ 2) law := by
    apply Integrable.of_bound
      (((function.continuous.measurable.comp addressMeasurable).sub measurable_const).pow_const 2).aestronglyMeasurable
      (‖function - ContinuousMap.const _ anchor‖ ^ 2)
    exact Eventually.of_forall fun address => by
      have bound := (function - ContinuousMap.const _ anchor).norm_coe_le_norm (addressPoint address)
      simpa only [Real.norm_eq_abs, abs_pow, sq_abs] using
        pow_le_pow_left₀ (abs_nonneg _) bound 2
  have localIntegrable (level : ℕ) (function : C(Space, ℝ)) (anchor : ℝ) :
      Integrable (fun address => weights level address * (function (addressPoint address) - anchor) ^ 2) law :=
    (squareIntegrable function anchor).bdd_mul (weightsMeasurable level).aestronglyMeasurable
      (Eventually.of_forall fun address => by
        rw [Real.norm_eq_abs, abs_of_nonneg (weightsNonnegative level address)]
        exact weightsBounded level address)
  have weightIntegrable (level : ℕ) : Integrable (weights level) law := by
    apply Integrable.of_bound (weightsMeasurable level).aestronglyMeasurable 2
    exact Eventually.of_forall fun address => by
      rw [Real.norm_eq_abs, abs_of_nonneg (weightsNonnegative level address)]
      exact weightsBounded level address
  have closedAnchor (level : ℕ) :
      (∫ address, weights level address ∂law) * (pointLimit - limit point) ^ 2 ≤
        constant * decay level * (∫ address, weights level address ∂law) * energy +
        6 * ∫ address, weights level address * (limit (addressPoint address) - limit point) ^ 2 ∂law := by
    have comparison (index : ℕ) :
        (∫ address, weights level address * (sequence index (addressPoint address) - limit point) ^ 2 ∂law) ≤
          4 * (∫ address, (sequence index (addressPoint address) - limit (addressPoint address)) ^ 2 ∂law) +
          2 * ∫ address, weights level address * (limit (addressPoint address) - limit point) ^ 2 ∂law := by
      have differenceIntegrable := squareIntegrable (sequence index - limit) 0
      have compared := integral_mono (localIntegrable level (sequence index) (limit point))
        ((differenceIntegrable.const_mul 4).add ((localIntegrable level limit (limit point)).const_mul 2))
        (fun address => by
          change weights level address * (sequence index (addressPoint address) - limit point) ^ 2 ≤
            4 * (sequence index (addressPoint address) - limit (addressPoint address)) ^ 2 +
              2 * (weights level address * (limit (addressPoint address) - limit point) ^ 2)
          exact weighted_square_triangle_le (sequence index (addressPoint address))
            (limit (addressPoint address)) (limit point) (weights level address)
            (weightsNonnegative level address) (weightsBounded level address))
      simpa only [ContinuousMap.sub_apply, sub_zero, integral_add
        (differenceIntegrable.const_mul 4) ((localIntegrable level limit (limit point)).const_mul 2),
        integral_const_mul] using compared
    have inequalities (index : ℕ) := (anchorBound index level (limit point)).trans
      (add_le_add_right (mul_le_mul_of_nonneg_left (comparison index) (by norm_num : (0 : ℝ) ≤ 3)) _)
    have leftLimit := ((pointConvergence.sub_const (limit point)).pow 2).const_mul
      (∫ address, weights level address ∂law)
    have errorLimit := ((ambientConvergence.const_mul 4).add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ =>
        2 * ∫ address, weights level address * (limit (addressPoint address) - limit point) ^ 2 ∂law)
        atTop (𝓝 (2 * ∫ address, weights level address *
          (limit (addressPoint address) - limit point) ^ 2 ∂law)))).const_mul 3
    have rightLimit := (energyLimit.const_mul
      (constant * decay level * (∫ address, weights level address ∂law))).add errorLimit
    have bound := le_of_tendsto_of_tendsto leftLimit rightLimit (Eventually.of_forall inequalities)
    convert bound using 1 <;> ring
  have epsilonBound (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
      (pointLimit - limit point) ^ 2 ≤ 6 * tolerance ^ 2 := by
    obtain ⟨radius, radiusPositive, withinRadius⟩ :=
      Metric.continuousAt_iff.mp (show ContinuousAt limit point from limit.continuous.continuousAt)
        tolerance tolerancePositive
    have meshEventually : ∀ᶠ level in atTop, mesh level < radius :=
      (tendsto_order.mp meshLimit).2 radius radiusPositive
    have eventuallyBound : ∀ᶠ level in atTop,
        (pointLimit - limit point) ^ 2 ≤ constant * decay level * energy + 6 * tolerance ^ 2 := by
      filter_upwards [meshEventually] with level meshSmall
      have localBound :
          (∫ address, weights level address * (limit (addressPoint address) - limit point) ^ 2 ∂law) ≤
            (∫ address, weights level address ∂law) * tolerance ^ 2 := by
        have compared := integral_mono (localIntegrable level limit (limit point))
          ((weightIntegrable level).mul_const (tolerance ^ 2)) (fun address => by
            by_cases zero : weights level address = 0
            · simp only [zero, zero_mul, le_refl]
            have near := withinRadius (x := addressPoint address) ((supportMesh level address zero).trans_lt meshSmall)
            rw [Real.dist_eq] at near
            have squared : (limit (addressPoint address) - limit point) ^ 2 ≤ tolerance ^ 2 := by
              simpa only [sq_abs] using
                pow_le_pow_left₀ (abs_nonneg (limit (addressPoint address) - limit point)) near.le 2
            exact mul_le_mul_of_nonneg_left squared (weightsNonnegative level address))
        simpa only [integral_mul_const] using compared
      apply (mul_le_mul_iff_right₀ (massPositive level)).mp
      calc
        _ ≤ _ := (closedAnchor level).trans
          (add_le_add_right (mul_le_mul_of_nonneg_left localBound (by norm_num : (0 : ℝ) ≤ 6)) _)
        _ = _ := by ring
    have upperLimit := ((decayLimit.const_mul constant).mul_const energy).add_const (6 * tolerance ^ 2)
    have limitBound := ge_of_tendsto upperLimit eventuallyBound
    simpa only [mul_zero, zero_mul, zero_add, mul_comm constant] using limitBound
  by_contra different
  have differenceNonzero : pointLimit - limit point ≠ 0 := sub_ne_zero.mpr different
  have tolerancePositive : 0 < |pointLimit - limit point| / 3 := div_pos (abs_pos.mpr differenceNonzero) (by norm_num)
  have bound := epsilonBound _ tolerancePositive
  nlinarith [sq_abs (pointLimit - limit point), sq_pos_of_ne_zero differenceNonzero]

end
end IGS.Sec31

#print axioms IGS.Sec31.continuous_point_limit_eq_of_weighted_stars
