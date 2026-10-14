import RequestProject.Section31.QuadraticEnergyClosureRecovery
import RequestProject.Section31.QuadraticEnergyClosedSublevel
import Mathlib.Analysis.Normed.Operator.Compact
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Sequences

/-! Closed energy error bounds and compact bounded-energy balls from
compact finite-rank approximations in an ambient isometric image. -/

namespace IGS.Sec31

open Filter Topology
noncomputable section

variable {H Target : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup Target] [NormedSpace ℝ Target]

namespace QuadraticEnergySpace

theorem closedForm_operator_error_bound
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (embedding : H →L[ℝ] Target) (average : Target →L[ℝ] Target) (coefficient : ℝ)
    (originalBound : ∀ values : domain,
      ‖embedding values.val - average (embedding values.val)‖ ^ 2 ≤ coefficient * form values)
    (target : closedDomain domain form nonnegative) :
    ‖embedding target.val - average (embedding target.val)‖ ^ 2 ≤
      coefficient * closedForm domain form nonnegative closable target := by
  obtain ⟨sequence, stateConvergence, energyConvergence⟩ :=
    exists_original_state_energy_approximation domain form nonnegative closable target
  have embeddedConvergence := embedding.continuous.continuousAt.tendsto.comp stateConvergence
  have averagedConvergence := average.continuous.continuousAt.tendsto.comp embeddedConvergence
  exact le_of_tendsto_of_tendsto ((embeddedConvergence.sub averagedConvergence).norm.pow 2)
    (tendsto_const_nhds.mul energyConvergence) (Eventually.of_forall fun index => originalBound (sequence index))

def closedEnergyBoundedBall
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (normBound energyBound : ℝ) : Set H :=
  {values | ‖values‖ ≤ normBound ∧ ∃ lifted : closedDomain domain form nonnegative,
    lifted.val = values ∧ closedForm domain form nonnegative closable lifted ≤ energyBound}

theorem closedEnergyBoundedBall_isClosed
    (domain : Submodule ℝ H) (form : QuadraticForm ℝ domain)
    (nonnegative : ∀ values, 0 ≤ form values) (closable : SequentiallyClosable domain form)
    (normBound energyBound : ℝ) (energyNonnegative : 0 ≤ energyBound) :
    IsClosed (closedEnergyBoundedBall domain form nonnegative closable normBound energyBound) := by
  apply IsSeqClosed.isClosed
  intro sequence target sequenceMember convergence
  choose lifted liftedEquality liftedEnergy using fun index => (sequenceMember index).2
  have liftedConvergence : Tendsto (fun index => (lifted index : H)) atTop (nhds target) := by
    simpa only [liftedEquality] using convergence
  obtain ⟨targetLift, targetEquality, targetEnergy⟩ :=
    closedForm_sublevel_limit domain form nonnegative closable lifted target energyBound energyNonnegative
      liftedConvergence (Eventually.of_forall liftedEnergy)
  exact ⟨le_of_tendsto convergence.norm (Eventually.of_forall fun index => (sequenceMember index).1),
    targetLift, targetEquality, targetEnergy⟩

end QuadraticEnergySpace

theorem totallyBounded_of_compact_approximations
    (embedding : H →ₗᵢ[ℝ] Target) (averages : ℕ → Target →L[ℝ] Target)
    (averagesCompact : ∀ level, IsCompactOperator (averages level))
    (boundedSet : Set H) (normBound : ℝ) (normsBounded : ∀ values ∈ boundedSet, ‖values‖ ≤ normBound)
    (errors : ℕ → ℝ) (errorsTendsto : Tendsto errors atTop (nhds 0))
    (errorBound : ∀ level values, values ∈ boundedSet →
      ‖embedding values - averages level (embedding values)‖ ≤ errors level) :
    TotallyBounded boundedSet := by
  apply (totallyBounded_image_iff embedding.isometry.isUniformInducing).mp
  apply Metric.totallyBounded_iff.mpr
  intro tolerance tolerancePositive
  obtain ⟨level, errorSmall⟩ :=
    (errorsTendsto.eventually (gt_mem_nhds (half_pos tolerancePositive))).exists
  obtain ⟨compactImage, imageCompact, imageSubset⟩ :=
    IsCompactOperator.image_closedBall_subset_compact
      (f := (averages level).toLinearMap) (averagesCompact level) normBound
  obtain ⟨centres, centresFinite, centresCover⟩ :=
    Metric.totallyBounded_iff.mp imageCompact.totallyBounded (tolerance / 2) (half_pos tolerancePositive)
  refine ⟨centres, centresFinite, ?_⟩
  rintro _ ⟨values, valuesMember, rfl⟩
  have averageMember : averages level (embedding values) ∈ compactImage := by
    apply imageSubset
    refine ⟨embedding values, ?_, rfl⟩
    simpa only [Metric.mem_closedBall, dist_zero_right, embedding.norm_map] using normsBounded values valuesMember
  obtain ⟨centre, centreMember, centreClose⟩ := Set.mem_iUnion₂.mp (centresCover averageMember)
  apply Set.mem_iUnion₂.mpr
  refine ⟨centre, centreMember, ?_⟩
  apply Metric.mem_ball.mpr
  have approximationClose : dist (embedding values) (averages level (embedding values)) < tolerance / 2 := by
    rw [dist_eq_norm]
    exact (errorBound level values valuesMember).trans_lt errorSmall
  exact (dist_triangle _ _ _).trans_lt (add_lt_add approximationClose (Metric.mem_ball.mp centreClose))
    |>.trans_eq (by ring)

end
end IGS.Sec31

#print axioms IGS.Sec31.QuadraticEnergySpace.closedForm_operator_error_bound
#print axioms IGS.Sec31.QuadraticEnergySpace.closedEnergyBoundedBall_isClosed
#print axioms IGS.Sec31.totallyBounded_of_compact_approximations
