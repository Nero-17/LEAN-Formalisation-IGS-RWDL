import RequestProject.Section31.QuadraticEnergyYosidaCauchy
import RequestProject.Section31.StrongContractionSemigroupLimit
import Mathlib.Analysis.SpecificLimits.Basic

/-! A genuine strongly continuous contraction semigroup, constructed as the
strong limit of the actual closed-form Yosida approximants. Cauchy and
dense-core continuity estimates are discharged, not assumed. Identification
of its infinitesimal generator and its Markov properties are separate steps. -/

namespace IGS.Sec31.QuadraticEnergySpace

open Filter Topology
open scoped NNReal

set_option maxHeartbeats 2000000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (domainDense : Dense (domain : Set H))

noncomputable def canonicalYosidaStep (index : ℕ) : ℝ := 1 / ((index : ℝ) + 1)

theorem canonicalYosidaStep_positive (index : ℕ) : 0 < canonicalYosidaStep index := by
  unfold canonicalYosidaStep
  positivity

theorem canonicalYosidaStep_le_one (index : ℕ) : canonicalYosidaStep index ≤ 1 := by
  unfold canonicalYosidaStep
  apply (div_le_one (by positivity)).mpr
  linarith [Nat.cast_nonneg (α := ℝ) index]

theorem canonicalYosidaStep_tendsto : Tendsto canonicalYosidaStep atTop (nhds 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

noncomputable def closedSemigroupApproximation (index : ℕ) (time : ℝ≥0) : H →L[ℝ] H :=
  yosidaSemigroup domain form nonnegative closable domainDense (canonicalYosidaStep index)
    (canonicalYosidaStep_positive index) (canonicalYosidaStep_le_one index) time

theorem closedSemigroupApproximation_norm (index : ℕ) (time : ℝ≥0) :
    ‖closedSemigroupApproximation domain form nonnegative closable domainDense index time‖ ≤ 1 :=
  yosidaSemigroup_norm domain form nonnegative closable domainDense _ _ _ time time.coe_nonneg

theorem closedSemigroupApproximation_cauchy (time : ℝ≥0) (values : H) :
    CauchySeq (fun index => closedSemigroupApproximation domain form nonnegative closable domainDense index time values) :=
  yosidaSemigroup_strong_cauchy domain form nonnegative closable domainDense
    canonicalYosidaStep canonicalYosidaStep_positive canonicalYosidaStep_le_one canonicalYosidaStep_tendsto
    time time.coe_nonneg values

theorem closedSemigroupApproximation_zero (index : ℕ) :
    closedSemigroupApproximation domain form nonnegative closable domainDense index 0 = ContinuousLinearMap.id ℝ H :=
  yosidaSemigroup_zero domain form nonnegative closable domainDense _ _ _

theorem closedSemigroupApproximation_add (index : ℕ) (firstTime secondTime : ℝ≥0) :
    closedSemigroupApproximation domain form nonnegative closable domainDense index (firstTime + secondTime) =
      (closedSemigroupApproximation domain form nonnegative closable domainDense index firstTime).comp
        (closedSemigroupApproximation domain form nonnegative closable domainDense index secondTime) :=
  yosidaSemigroup_add domain form nonnegative closable domainDense _ _ _ _ _

theorem closedSemigroupApproximation_core_time_bound
    (values : generatorDomain domain form nonnegative closable) :
    ∃ constant : ℝ≥0, ∀ index time,
      ‖closedSemigroupApproximation domain form nonnegative closable domainDense index time values.val - values.val‖ ≤
        (time : ℝ) * constant := by
  refine ⟨‖closedGenerator domain form nonnegative closable domainDense values‖₊, ?_⟩
  intro index time
  exact yosidaSemigroup_domain_time_bound domain form nonnegative closable domainDense _ _ _ time time.coe_nonneg values

noncomputable def closedSemigroup (time : ℝ≥0) : H →L[ℝ] H :=
  StrongContractionSemigroupLimit.limit
    (closedSemigroupApproximation domain form nonnegative closable domainDense)
    (closedSemigroupApproximation_norm domain form nonnegative closable domainDense)
    (closedSemigroupApproximation_cauchy domain form nonnegative closable domainDense) time

theorem closedSemigroup_approximation_limit (time : ℝ≥0) (values : H) :
    Tendsto (fun index => closedSemigroupApproximation domain form nonnegative closable domainDense index time values)
      atTop (nhds (closedSemigroup domain form nonnegative closable domainDense time values)) :=
  StrongContractionSemigroupLimit.tendsto_limit _ _ _ _ _

theorem closedSemigroup_norm (time : ℝ≥0) :
    ‖closedSemigroup domain form nonnegative closable domainDense time‖ ≤ 1 :=
  StrongContractionSemigroupLimit.limit_norm_le_one _ _ _ _

@[simp] theorem closedSemigroup_zero :
    closedSemigroup domain form nonnegative closable domainDense 0 = ContinuousLinearMap.id ℝ H :=
  StrongContractionSemigroupLimit.limit_zero _ _ _
    (closedSemigroupApproximation_zero domain form nonnegative closable domainDense)

theorem closedSemigroup_add (firstTime secondTime : ℝ≥0) :
    closedSemigroup domain form nonnegative closable domainDense (firstTime + secondTime) =
      (closedSemigroup domain form nonnegative closable domainDense firstTime).comp
        (closedSemigroup domain form nonnegative closable domainDense secondTime) :=
  StrongContractionSemigroupLimit.limit_add _ _ _
    (closedSemigroupApproximation_add domain form nonnegative closable domainDense) _ _

theorem closedSemigroup_joint_continuous :
    Continuous (fun point : H × ℝ≥0 => closedSemigroup domain form nonnegative closable domainDense point.2 point.1) :=
  StrongContractionSemigroupLimit.limit_joint_continuous _ _ _
    (closedSemigroupApproximation_add domain form nonnegative closable domainDense)
    (generatorDomain domain form nonnegative closable)
    (generatorDomain_dense domain form nonnegative closable domainDense)
    (closedSemigroupApproximation_core_time_bound domain form nonnegative closable domainDense)

end IGS.Sec31.QuadraticEnergySpace

#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_approximation_limit
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_norm
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_zero
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_add
#print axioms IGS.Sec31.QuadraticEnergySpace.closedSemigroup_joint_continuous
