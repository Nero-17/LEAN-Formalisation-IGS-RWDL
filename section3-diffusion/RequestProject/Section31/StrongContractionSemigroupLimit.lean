import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Analysis.Normed.Operator.CompleteCodomain
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-! A conditional construction of a strong limit of contraction semigroups.
The strong Cauchy hypothesis and the uniform time estimate on a dense core are
explicit inputs. This file does not assert that a particular Yosida family
satisfies them. Times are nonnegative reals. -/

namespace IGS.Sec31.StrongContractionSemigroupLimit

open Filter Topology Bornology
open scoped NNReal

set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]

variable (operators : ℕ → ℝ≥0 → H →L[ℝ] H)
  (contraction : ∀ index time, ‖operators index time‖ ≤ 1)
  (strongCauchy : ∀ time values, CauchySeq (fun index => operators index time values))

/-- The actual pointwise limit, bundled using boundedness of the operator family. -/
noncomputable def limit (time : ℝ≥0) : H →L[ℝ] H :=
  ContinuousLinearMap.ofTendstoOfBoundedRange
    (fun values => limUnder atTop (fun index => operators index time values))
    (fun index => operators index time)
    (tendsto_pi_nhds.mpr fun values =>
      tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (strongCauchy time values)))
    (isBounded_iff_forall_norm_le.mpr ⟨1, by
      rintro operator ⟨index, rfl⟩
      exact contraction index time⟩)

theorem tendsto_limit (time : ℝ≥0) (values : H) :
    Tendsto (fun index => operators index time values) atTop
      (nhds (limit operators contraction strongCauchy time values)) := by
  change Tendsto _ atTop
    (nhds (limUnder atTop (fun index => operators index time values)))
  exact tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (strongCauchy time values))

theorem limit_apply_norm_le (time : ℝ≥0) (values : H) :
    ‖limit operators contraction strongCauchy time values‖ ≤ ‖values‖ := by
  apply le_of_tendsto (tendsto_limit operators contraction strongCauchy time values).norm
  exact Eventually.of_forall fun index => by
    simpa only [one_mul] using
      (operators index time).le_of_opNorm_le (contraction index time) values

theorem limit_norm_le_one (time : ℝ≥0) :
    ‖limit operators contraction strongCauchy time‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using limit_apply_norm_le operators contraction strongCauchy time values

/-- Strong convergence remains valid when the input vectors also converge. -/
theorem tendsto_varying_apply (time : ℝ≥0) (sequence : ℕ → H) (values : H)
    (convergence : Tendsto sequence atTop (nhds values)) :
    Tendsto (fun index => operators index time (sequence index)) atTop
      (nhds (limit operators contraction strongCauchy time values)) := by
  have errorBound : ∀ index,
      ‖operators index time (sequence index) - operators index time values‖ ≤
        ‖sequence index - values‖ := by
    intro index
    rw [← map_sub]
    simpa only [one_mul] using
      (operators index time).le_of_opNorm_le (contraction index time) (sequence index - values)
  have errorZero : Tendsto (fun index =>
      operators index time (sequence index) - operators index time values) atTop (nhds 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) errorBound
      (tendsto_iff_norm_sub_tendsto_zero.mp convergence)
  simpa only [sub_add_cancel, zero_add] using
    errorZero.add (tendsto_limit operators contraction strongCauchy time values)

theorem limit_zero (zeroLaw : ∀ index, operators index 0 = ContinuousLinearMap.id ℝ H) :
    limit operators contraction strongCauchy 0 = ContinuousLinearMap.id ℝ H := by
  ext values
  apply tendsto_nhds_unique (tendsto_limit operators contraction strongCauchy 0 values)
  simpa only [zeroLaw, ContinuousLinearMap.id_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => values) atTop (nhds values))

theorem limit_add
    (additionLaw : ∀ index firstTime secondTime,
      operators index (firstTime + secondTime) =
        (operators index firstTime).comp (operators index secondTime))
    (firstTime secondTime : ℝ≥0) :
    limit operators contraction strongCauchy (firstTime + secondTime) =
      (limit operators contraction strongCauchy firstTime).comp
        (limit operators contraction strongCauchy secondTime) := by
  ext values
  have compositionConvergence := tendsto_varying_apply operators contraction strongCauchy
    firstTime (fun index => operators index secondTime values)
    (limit operators contraction strongCauchy secondTime values)
    (tendsto_limit operators contraction strongCauchy secondTime values)
  have additionConvergence : Tendsto
      (fun index => operators index (firstTime + secondTime) values) atTop
      (nhds (limit operators contraction strongCauchy firstTime
        (limit operators contraction strongCauchy secondTime values))) := by
    simpa only [additionLaw, ContinuousLinearMap.comp_apply] using compositionConvergence
  exact tendsto_nhds_unique
    (tendsto_limit operators contraction strongCauchy (firstTime + secondTime) values)
    additionConvergence

theorem limit_time_bound (values : H) (constant : ℝ≥0)
    (timeBound : ∀ index time,
      ‖operators index time values - values‖ ≤ (time : ℝ) * constant)
    (time : ℝ≥0) :
    ‖limit operators contraction strongCauchy time values - values‖ ≤
      (time : ℝ) * constant := by
  apply le_of_tendsto
    ((tendsto_limit operators contraction strongCauchy time values).sub tendsto_const_nhds).norm
  exact Eventually.of_forall fun index => timeBound index time

/-- The time estimate and the semigroup law give Lipschitz orbits on the core. -/
theorem limit_orbit_lipschitz
    (additionLaw : ∀ index firstTime secondTime,
      operators index (firstTime + secondTime) =
        (operators index firstTime).comp (operators index secondTime))
    (values : H) (constant : ℝ≥0)
    (timeBound : ∀ index time,
      ‖operators index time values - values‖ ≤ (time : ℝ) * constant) :
    LipschitzWith constant (fun time => limit operators contraction strongCauchy time values) := by
  have orderedBound (firstTime secondTime : ℝ≥0) (ordered : firstTime ≤ secondTime) :
      dist (limit operators contraction strongCauchy secondTime values)
          (limit operators contraction strongCauchy firstTime values) ≤
        (constant : ℝ) * dist secondTime firstTime := by
    have differenceIdentity :
        limit operators contraction strongCauchy secondTime values -
          limit operators contraction strongCauchy firstTime values =
        limit operators contraction strongCauchy firstTime
          (limit operators contraction strongCauchy (secondTime - firstTime) values - values) := by
      rw [map_sub, ← ContinuousLinearMap.comp_apply,
        ← limit_add operators contraction strongCauchy additionLaw,
        add_tsub_cancel_of_le ordered]
    calc
      dist (limit operators contraction strongCauchy secondTime values)
          (limit operators contraction strongCauchy firstTime values) =
          ‖limit operators contraction strongCauchy firstTime
            (limit operators contraction strongCauchy (secondTime - firstTime) values - values)‖ := by
              rw [dist_eq_norm, differenceIdentity]
      _ ≤ ‖limit operators contraction strongCauchy (secondTime - firstTime) values - values‖ :=
        limit_apply_norm_le operators contraction strongCauchy firstTime _
      _ ≤ ((secondTime - firstTime : ℝ≥0) : ℝ) * constant :=
        limit_time_bound operators contraction strongCauchy values constant timeBound _
      _ = (constant : ℝ) * dist secondTime firstTime := by
        have orderedReal : (firstTime : ℝ) ≤ (secondTime : ℝ) := ordered
        rw [NNReal.coe_sub ordered, NNReal.dist_eq, abs_of_nonneg (sub_nonneg.mpr orderedReal)]
        ring
  apply LipschitzWith.of_dist_le_mul
  intro firstTime secondTime
  rcases le_total firstTime secondTime with ordered | ordered
  · simpa only [dist_comm] using orderedBound firstTime secondTime ordered
  · exact orderedBound secondTime firstTime ordered

/-- Dense-core time estimates produce joint continuity in time and state. -/
theorem limit_joint_continuous
    (additionLaw : ∀ index firstTime secondTime,
      operators index (firstTime + secondTime) =
        (operators index firstTime).comp (operators index secondTime))
    (core : Submodule ℝ H) (coreDense : Dense (core : Set H))
    (coreTimeBound : ∀ values : core, ∃ constant : ℝ≥0, ∀ index time,
      ‖operators index time values.val - values.val‖ ≤ (time : ℝ) * constant) :
    Continuous (fun point : H × ℝ≥0 =>
      limit operators contraction strongCauchy point.2 point.1) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith
    (fun point : H × ℝ≥0 => limit operators contraction strongCauchy point.2 point.1)
    1 coreDense
  · intro values membership
    obtain ⟨constant, timeBound⟩ := coreTimeBound ⟨values, membership⟩
    exact (limit_orbit_lipschitz operators contraction strongCauchy additionLaw
      values constant timeBound).continuous
  · intro time
    exact (ContinuousLinearMap.opNorm_le_iff_lipschitz
      (f := limit operators contraction strongCauchy time) (K := 1)).mp
      (by simpa using limit_norm_le_one operators contraction strongCauchy time)

theorem limit_strong_continuous
    (additionLaw : ∀ index firstTime secondTime,
      operators index (firstTime + secondTime) =
        (operators index firstTime).comp (operators index secondTime))
    (core : Submodule ℝ H) (coreDense : Dense (core : Set H))
    (coreTimeBound : ∀ values : core, ∃ constant : ℝ≥0, ∀ index time,
      ‖operators index time values.val - values.val‖ ≤ (time : ℝ) * constant)
    (values : H) :
    Continuous (fun time => limit operators contraction strongCauchy time values) := by
  have pairedContinuous : Continuous (fun time : ℝ≥0 => (values, time)) :=
    continuous_const.prodMk continuous_id
  have jointContinuous := limit_joint_continuous operators contraction strongCauchy additionLaw
    core coreDense coreTimeBound
  simpa only [Function.comp_def] using jointContinuous.comp pairedContinuous

theorem limit_tendsto_zero
    (zeroLaw : ∀ index, operators index 0 = ContinuousLinearMap.id ℝ H)
    (additionLaw : ∀ index firstTime secondTime,
      operators index (firstTime + secondTime) =
        (operators index firstTime).comp (operators index secondTime))
    (core : Submodule ℝ H) (coreDense : Dense (core : Set H))
    (coreTimeBound : ∀ values : core, ∃ constant : ℝ≥0, ∀ index time,
      ‖operators index time values.val - values.val‖ ≤ (time : ℝ) * constant)
    (values : H) :
    Tendsto (fun time => limit operators contraction strongCauchy time values)
      (nhds (0 : ℝ≥0)) (nhds values) := by
  simpa only [limit_zero operators contraction strongCauchy zeroLaw,
    ContinuousLinearMap.id_apply] using
    (limit_strong_continuous operators contraction strongCauchy additionLaw
      core coreDense coreTimeBound values).tendsto 0

end IGS.Sec31.StrongContractionSemigroupLimit

#print axioms IGS.Sec31.StrongContractionSemigroupLimit.tendsto_limit
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_norm_le_one
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.tendsto_varying_apply
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_zero
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_add
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_orbit_lipschitz
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_joint_continuous
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_strong_continuous
#print axioms IGS.Sec31.StrongContractionSemigroupLimit.limit_tendsto_zero
