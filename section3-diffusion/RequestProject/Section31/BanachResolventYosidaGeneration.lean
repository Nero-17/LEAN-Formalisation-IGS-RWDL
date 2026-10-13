import RequestProject.Section31.BoundedYosidaSemigroup
import RequestProject.Section31.BoundedSemigroupComparison
import RequestProject.Section31.StrongContractionSemigroupLimit

/-! Generation from compatible contraction resolvents in a Banach space.
The inputs are resolvent contraction, strong approximation of the identity,
commutation and the resolvent graph identity. The strong Cauchy property of
the Yosida exponentials and their time bounds on a dense core are proved,
rather than required as inputs. This applies to C(X) with its supremum norm.
In the native application the graph identity is transported from the actual
closed L² resolvents through the injective continuous-function embedding. -/

namespace IGS.Sec31.BanachResolventYosidaGeneration

open Filter Topology Set
open scoped BigOperators NNReal

variable {Space : Type*} [NormedAddCommGroup Space] [NormedSpace ℝ Space]
    [CompleteSpace Space]

variable (resolvents : ℕ → Space →L[ℝ] Space) (steps : ℕ → ℝ)

def convergenceCore : Submodule ℝ Space where
  carrier := {values | ∃ limit : Space,
    Tendsto (fun index => BoundedYosida.generator (resolvents index) (steps index) values)
      atTop (𝓝 limit)}
  zero_mem' := ⟨0, by simpa only [map_zero] using (tendsto_const_nhds :
    Tendsto (fun _ : ℕ => (0 : Space)) atTop (𝓝 0))⟩
  add_mem' := by
    rintro first second ⟨firstLimit, firstConverges⟩ ⟨secondLimit, secondConverges⟩
    exact ⟨firstLimit + secondLimit, by simpa only [map_add] using firstConverges.add secondConverges⟩
  smul_mem' := by
    rintro scalar values ⟨limit, converges⟩
    exact ⟨scalar • limit, by simpa only [map_smul] using converges.const_smul scalar⟩

omit [CompleteSpace Space] in
theorem resolvent_mem_convergenceCore
    (approximateIdentity : ∀ values : Space,
      Tendsto (fun index => resolvents index values) atTop (𝓝 values))
    (compatible : ∀ first second (values : Space),
      BoundedYosida.generator (resolvents first) (steps first) (resolvents second values) =
        resolvents first (BoundedYosida.generator (resolvents second) (steps second) values))
    (index : ℕ) (values : Space) : resolvents index values ∈ convergenceCore resolvents steps := by
  refine ⟨BoundedYosida.generator (resolvents index) (steps index) values, ?_⟩
  simpa only [compatible] using
    approximateIdentity (BoundedYosida.generator (resolvents index) (steps index) values)

theorem convergenceCore_dense
    (approximateIdentity : ∀ values : Space,
      Tendsto (fun index => resolvents index values) atTop (𝓝 values))
    (compatible : ∀ first second (values : Space),
      BoundedYosida.generator (resolvents first) (steps first) (resolvents second values) =
        resolvents first (BoundedYosida.generator (resolvents second) (steps second) values)) :
    Dense (convergenceCore resolvents steps : Set Space) := by
  intro values
  apply mem_closure_of_tendsto (approximateIdentity values)
  exact Eventually.of_forall fun index =>
    resolvent_mem_convergenceCore resolvents steps approximateIdentity compatible index values

omit [CompleteSpace Space] in
theorem convergenceCore_generator_bound (values : convergenceCore resolvents steps) :
    ∃ constant : ℝ≥0, ∀ index,
      ‖BoundedYosida.generator (resolvents index) (steps index) values.val‖ ≤ constant := by
  obtain ⟨limit, converges⟩ := values.property
  obtain ⟨threshold, close⟩ := eventually_atTop.mp
    (converges.eventually (Metric.ball_mem_nhds limit (by norm_num : (0 : ℝ) < 1)))
  let constant := (∑ index ∈ Finset.range threshold,
    ‖BoundedYosida.generator (resolvents index) (steps index) values.val‖) + ‖limit‖ + 1
  have sumNonnegative : 0 ≤ ∑ index ∈ Finset.range threshold,
      ‖BoundedYosida.generator (resolvents index) (steps index) values.val‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have constantNonnegative : 0 ≤ constant := by dsimp only [constant]; positivity
  refine ⟨⟨constant, constantNonnegative⟩, ?_⟩
  intro index
  change ‖BoundedYosida.generator (resolvents index) (steps index) values.val‖ ≤ constant
  by_cases before : index < threshold
  · have finiteBound := Finset.single_le_sum
      (fun other (_ : other ∈ Finset.range threshold) =>
        norm_nonneg (BoundedYosida.generator (resolvents other) (steps other) values.val))
      (Finset.mem_range.mpr before)
    dsimp only [constant]
    exact finiteBound.trans (by linarith [norm_nonneg limit])
  · have after : threshold ≤ index := Nat.le_of_not_gt before
    have closeNorm : ‖BoundedYosida.generator (resolvents index) (steps index) values.val - limit‖ < 1 := by
      simpa only [Metric.mem_ball, dist_eq_norm] using close index after
    calc
      ‖BoundedYosida.generator (resolvents index) (steps index) values.val‖ =
          ‖(BoundedYosida.generator (resolvents index) (steps index) values.val - limit) + limit‖ := by
        rw [sub_add_cancel]
      _ ≤ ‖BoundedYosida.generator (resolvents index) (steps index) values.val - limit‖ + ‖limit‖ :=
        norm_add_le _ _
      _ ≤ 1 + ‖limit‖ := add_le_add closeNorm.le le_rfl
      _ ≤ constant := by dsimp only [constant]; linarith

noncomputable def operators (index : ℕ) (time : ℝ≥0) : Space →L[ℝ] Space :=
  BoundedYosida.semigroup (resolvents index) (steps index) (time : ℝ)

theorem operators_contraction (stepsPositive : ∀ index, 0 < steps index)
    (resolventContraction : ∀ index, ‖resolvents index‖ ≤ 1) (index : ℕ) (time : ℝ≥0) :
    ‖operators resolvents steps index time‖ ≤ 1 :=
  BoundedYosida.semigroup_norm_le_one _ (resolventContraction index) _ (stepsPositive index)
    time time.property

omit [CompleteSpace Space] in
theorem generators_commute (commuting : ∀ first second, Commute (resolvents first) (resolvents second))
    (first second : ℕ) :
    Commute (BoundedYosida.generator (resolvents first) (steps first))
      (BoundedYosida.generator (resolvents second) (steps second)) := by
  have differenceCommutes : Commute (1 - resolvents first) (1 - resolvents second) :=
    (Commute.one_left _).sub_left ((Commute.one_right _).sub_right (commuting first second))
  exact (differenceCommutes.smul_left (steps first)⁻¹).smul_right (steps second)⁻¹

theorem convergenceCore_time_bound (stepsPositive : ∀ index, 0 < steps index)
    (resolventContraction : ∀ index, ‖resolvents index‖ ≤ 1)
    (values : convergenceCore resolvents steps) :
    ∃ constant : ℝ≥0, ∀ index (time : ℝ≥0),
      ‖operators resolvents steps index time values.val - values.val‖ ≤ (time : ℝ) * constant := by
  obtain ⟨constant, generatorBound⟩ := convergenceCore_generator_bound resolvents steps values
  refine ⟨constant, ?_⟩
  intro index time
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_self_le
    (BoundedYosida.generator (resolvents index) (steps index))
    (fun parameter parameterNonnegative => BoundedYosida.semigroup_norm_le_one _
      (resolventContraction index) _ (stepsPositive index) parameter parameterNonnegative)
    time time.property values.val
  exact comparison.trans (mul_le_mul_of_nonneg_left (generatorBound index) time.property)

theorem operators_strong_cauchy (stepsPositive : ∀ index, 0 < steps index)
    (resolventContraction : ∀ index, ‖resolvents index‖ ≤ 1)
    (approximateIdentity : ∀ values : Space,
      Tendsto (fun index => resolvents index values) atTop (𝓝 values))
    (commuting : ∀ first second, Commute (resolvents first) (resolvents second))
    (compatible : ∀ first second (values : Space),
      BoundedYosida.generator (resolvents first) (steps first) (resolvents second values) =
        resolvents first (BoundedYosida.generator (resolvents second) (steps second) values))
    (time : ℝ≥0) (forcing : Space) :
    CauchySeq (fun index => operators resolvents steps index time forcing) := by
  apply Metric.cauchySeq_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨approximation, approximationMember, approximationClose⟩ :=
    Metric.mem_closure_iff.mp
      (convergenceCore_dense resolvents steps approximateIdentity compatible forcing)
        (tolerance / 4) (by positivity)
  obtain ⟨limit, generatorConverges⟩ := approximationMember
  have scaledLimit := generatorConverges.const_smul (time : ℝ)
  obtain ⟨threshold, scaledClose⟩ := Metric.cauchySeq_iff.mp scaledLimit.cauchySeq
    (tolerance / 2) (by positivity)
  refine ⟨threshold, ?_⟩
  intro first firstLarge second secondLarge
  have comparison := BoundedSemigroupComparison.norm_exp_apply_sub_le
    (BoundedYosida.generator (resolvents first) (steps first))
    (BoundedYosida.generator (resolvents second) (steps second))
    (generators_commute resolvents steps commuting first second)
    (fun parameter parameterNonnegative => BoundedYosida.semigroup_norm_le_one _
      (resolventContraction first) _ (stepsPositive first) parameter parameterNonnegative)
    (fun parameter parameterNonnegative => BoundedYosida.semigroup_norm_le_one _
      (resolventContraction second) _ (stepsPositive second) parameter parameterNonnegative)
    time time.property approximation
  have scaledSmall := scaledClose first firstLarge second secondLarge
  simp only [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs] at scaledSmall
  have scalarAbs : |(time : ℝ)| = (time : ℝ) :=
    abs_of_nonneg (show 0 ≤ (time : ℝ) from time.property)
  rw [scalarAbs] at scaledSmall
  have firstContraction : dist (operators resolvents steps first time forcing)
      (operators resolvents steps first time approximation) ≤ dist forcing approximation := by
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (operators resolvents steps first time).le_of_opNorm_le
        (operators_contraction resolvents steps stepsPositive resolventContraction first time)
          (forcing - approximation)
  have secondContraction : dist (operators resolvents steps second time approximation)
      (operators resolvents steps second time forcing) ≤ dist forcing approximation := by
    rw [dist_comm]
    simpa only [dist_eq_norm, ← map_sub, one_mul] using
      (operators resolvents steps second time).le_of_opNorm_le
        (operators_contraction resolvents steps stepsPositive resolventContraction second time)
          (forcing - approximation)
  have middle : dist (operators resolvents steps first time approximation)
      (operators resolvents steps second time approximation) < tolerance / 2 := by
    rw [dist_eq_norm]
    exact comparison.trans_lt scaledSmall
  have firstTriangle := dist_triangle
    (operators resolvents steps first time forcing)
    (operators resolvents steps first time approximation)
    (operators resolvents steps second time forcing)
  have secondTriangle := dist_triangle
    (operators resolvents steps first time approximation)
    (operators resolvents steps second time approximation)
    (operators resolvents steps second time forcing)
  linarith

/-- A genuine C0 contraction semigroup is constructed from the resolvent
inputs above. Strong Cauchy and dense-core time estimates are conclusions
of the preceding proofs, and do not appear in this theorem's hypotheses. -/
theorem exists_stronglyContinuous_contraction_semigroup
    (stepsPositive : ∀ index, 0 < steps index)
    (resolventContraction : ∀ index, ‖resolvents index‖ ≤ 1)
    (approximateIdentity : ∀ values : Space,
      Tendsto (fun index => resolvents index values) atTop (𝓝 values))
    (commuting : ∀ first second, Commute (resolvents first) (resolvents second))
    (compatible : ∀ first second (values : Space),
      BoundedYosida.generator (resolvents first) (steps first) (resolvents second values) =
        resolvents first (BoundedYosida.generator (resolvents second) (steps second) values)) :
    ∃ semigroup : ℝ≥0 → Space →L[ℝ] Space,
      (∀ time, ‖semigroup time‖ ≤ 1) ∧
      semigroup 0 = ContinuousLinearMap.id ℝ Space ∧
      (∀ firstTime secondTime, semigroup (firstTime + secondTime) =
        (semigroup firstTime).comp (semigroup secondTime)) ∧
      Continuous (fun point : Space × ℝ≥0 => semigroup point.2 point.1) ∧
      ∀ (time : ℝ≥0) (values : Space),
        Tendsto (fun index => operators resolvents steps index time values) atTop (𝓝 (semigroup time values)) := by
  let contraction := operators_contraction resolvents steps stepsPositive resolventContraction
  let strongCauchy := operators_strong_cauchy resolvents steps stepsPositive resolventContraction
    approximateIdentity commuting compatible
  have zeroLaw : ∀ index, operators resolvents steps index 0 = ContinuousLinearMap.id ℝ Space := by
    intro index
    exact BoundedYosida.semigroup_zero _ _
  have additionLaw : ∀ index firstTime secondTime,
      operators resolvents steps index (firstTime + secondTime) =
        (operators resolvents steps index firstTime).comp (operators resolvents steps index secondTime) := by
    intro index firstTime secondTime
    exact BoundedYosida.semigroup_add _ _ _ _
  refine ⟨StrongContractionSemigroupLimit.limit (operators resolvents steps) contraction strongCauchy,
    StrongContractionSemigroupLimit.limit_norm_le_one _ _ _,
    StrongContractionSemigroupLimit.limit_zero _ _ _ zeroLaw,
    StrongContractionSemigroupLimit.limit_add _ _ _ additionLaw, ?_, ?_⟩
  · exact StrongContractionSemigroupLimit.limit_joint_continuous _ _ _ additionLaw
      (convergenceCore resolvents steps)
      (convergenceCore_dense resolvents steps approximateIdentity compatible)
      (convergenceCore_time_bound resolvents steps stepsPositive resolventContraction)
  · exact StrongContractionSemigroupLimit.tendsto_limit _ _ _

end IGS.Sec31.BanachResolventYosidaGeneration

#print axioms IGS.Sec31.BanachResolventYosidaGeneration.convergenceCore_dense
#print axioms IGS.Sec31.BanachResolventYosidaGeneration.convergenceCore_generator_bound
#print axioms IGS.Sec31.BanachResolventYosidaGeneration.generators_commute
#print axioms IGS.Sec31.BanachResolventYosidaGeneration.convergenceCore_time_bound
#print axioms IGS.Sec31.BanachResolventYosidaGeneration.operators_strong_cauchy
#print axioms IGS.Sec31.BanachResolventYosidaGeneration.exists_stronglyContinuous_contraction_semigroup
