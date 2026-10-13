import RequestProject.Section31.EIGSDiscreteFiniteObservations
import RequestProject.Section31.BanachPoissonizedWalkTimeRounding
import RequestProject.Section2GroundedResistanceBounds

/-! The actual finite Xi transition on vertex functions with the supremum
norm. Its contraction bound follows from the nonnegative transition rows
summing to one. Its powers agree with the genuine transition kernel and
with endpoint expectations of the Ionescu--Tulcea trajectory. Thus the
Banach de-Poissonization estimates have a proved native operator input. -/

namespace EIGS

open MeasureTheory ProbabilityTheory IGS.Sec31
open IGS.Sec31.DiscreteMarkov
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 3000000

section FiniteGraph

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]

def finiteGraphSupTransitionLinear (graph : SimpleGraph Vertex) [DecidableRel graph.Adj] :
    (Vertex → ℝ) →ₗ[ℝ] (Vertex → ℝ) where
  toFun := fun (values : Vertex → ℝ) (source : Vertex) =>
    ∑ target : Vertex, transProb graph source target * values target
  map_add' first second := by
    funext source
    change (∑ target : Vertex, transProb graph source target * (first target + second target)) =
      (∑ target : Vertex, transProb graph source target * first target) +
        (∑ target : Vertex, transProb graph source target * second target)
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' scalar values := by
    funext source
    change (∑ target : Vertex, transProb graph source target * (scalar * values target)) =
      scalar * (∑ target : Vertex, transProb graph source target * values target)
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro target _
    ring

theorem finiteGraphSupTransitionLinear_norm_le (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degreePositive : ∀ vertex, 0 < graph.degree vertex)
    (values : Vertex → ℝ) :
    ‖finiteGraphSupTransitionLinear graph values‖ ≤ ‖values‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg values)).mpr
  intro source
  change ‖∑ target : Vertex, transProb graph source target * values target‖ ≤ ‖values‖
  rw [Real.norm_eq_abs]
  calc
    |∑ target : Vertex, transProb graph source target * values target| ≤
        ∑ target : Vertex, |transProb graph source target * values target| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ target : Vertex, transProb graph source target * |values target| := by
      apply Finset.sum_congr rfl
      intro target _
      rw [abs_mul, abs_of_nonneg (transProb_nonneg (G := graph) source target)]
    _ ≤ ∑ target : Vertex, transProb graph source target * ‖values‖ := by
      apply Finset.sum_le_sum
      intro target _
      apply mul_le_mul_of_nonneg_left
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm values target
      · exact transProb_nonneg (G := graph) source target
    _ = ‖values‖ := by
      rw [← Finset.sum_mul, transProb_sum (degreePositive source), one_mul]

def finiteGraphSupTransition (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) :
    (Vertex → ℝ) →L[ℝ] (Vertex → ℝ) :=
  (finiteGraphSupTransitionLinear graph).mkContinuous 1 (fun values => by
    simpa only [one_mul] using finiteGraphSupTransitionLinear_norm_le graph degreePositive values)

theorem finiteGraphSupTransition_apply (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (values : Vertex → ℝ) (source : Vertex) :
    finiteGraphSupTransition graph degreePositive values source =
      ∑ target : Vertex, transProb graph source target * values target := rfl

theorem finiteGraphSupTransition_norm_le_one (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degreePositive : ∀ vertex, 0 < graph.degree vertex) :
    ‖finiteGraphSupTransition graph degreePositive‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro values
  simpa only [one_mul] using finiteGraphSupTransitionLinear_norm_le graph degreePositive values

end FiniteGraph

variable {K : ℕ}

def xiNativeSupTransition (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    (XiVtx system level → ℝ) →L[ℝ] (XiVtx system level → ℝ) :=
  finiteGraphSupTransition (XiSimpleGraph system level)
    (fun vertex => by exact_mod_cast xiSimpleGraph_degree_positive system rulesConnected level vertex)

theorem xiNativeSupTransition_apply (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    (values : XiVtx system level → ℝ) (source : XiVtx system level) :
    xiNativeSupTransition system rulesConnected level values source =
      ∑ target : XiVtx system level, transProb (XiSimpleGraph system level) source target * values target := rfl

theorem xiNativeSupTransition_norm_le_one (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ) :
    ‖xiNativeSupTransition system rulesConnected level‖ ≤ 1 :=
  finiteGraphSupTransition_norm_le_one (XiSimpleGraph system level) _

theorem xiNativeSupTransition_kernel_integral (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level : ℕ) (values : XiVtx system level → ℝ) (source : XiVtx system level) :
    (∫ target, values target ∂xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level source) = xiNativeSupTransition system rulesConnected level values source := by
  rw [xiNativeDiscreteKernel, finiteGraphTransitionKernel_integral, xiNativeSupTransition_apply]

theorem xiNativeSupTransition_kernel_power_integral (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level jumps : ℕ) (values : XiVtx system level → ℝ) (source : XiVtx system level) :
    (∫ target, values target ∂(xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique
      plantingNonadjacent level ^ jumps) source) =
        (xiNativeSupTransition system rulesConnected level ^ jumps) values source := by
  induction jumps generalizing values source with
  | zero =>
      change (∫ target, values target ∂Measure.dirac source) = values source
      simp
  | succ jumps induction =>
      rw [pow_succ]
      change (∫ target, values target ∂((xiNativeDiscreteKernel system rulesConnected rulesLoopless
        rulesUnique plantingNonadjacent level ^ jumps) ∘ₖ
          xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level) source) = _
      rw [Kernel.integral_comp (Integrable.of_finite)]
      simp_rw [induction]
      rw [xiNativeSupTransition_kernel_integral, pow_succ', ContinuousLinearMap.mul_apply]

theorem xiNativeSupTransition_pathLaw_endpoint_expectation (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected)
    (rulesLoopless : ∀ colour, (system.ruleNetwork colour).Loopless)
    (rulesUnique : ∀ colour, (system.ruleNetwork colour).EdgesUnique)
    (plantingNonadjacent : ∀ colour, ¬ (ruleSG system colour).Adj
      (system.plantPlus colour) (system.plantMinus colour))
    (level jumps : ℕ) (values : XiVtx system level → ℝ) (source : XiVtx system level) :
    (∫ path, values (path jumps) ∂pathLaw
      (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        (Measure.dirac source)) =
      (xiNativeSupTransition system rulesConnected level ^ jumps) values source := by
  rw [← xiNativeSupTransition_kernel_power_integral system rulesConnected rulesLoopless rulesUnique
    plantingNonadjacent level jumps values source,
      ← pathLaw_coordinate_dirac
        (xiNativeDiscreteKernel system rulesConnected rulesLoopless rulesUnique plantingNonadjacent level)
        source jumps]
  exact (integral_map (measurable_pi_apply jumps).aemeasurable
    (measurable_of_countable values).aestronglyMeasurable).symm

theorem xiNativeSupTransition_floor_poisson_comparison (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    (rate : ℝ) (ratePositive : 0 < rate) (time : ℝ) (timeNonnegative : 0 ≤ time)
    (values : XiVtx system level → ℝ) :
    ‖(xiNativeSupTransition system rulesConnected level ^ Nat.floor (time * rate)) values -
      NormedSpace.exp ((-(time * rate)) • (1 - xiNativeSupTransition system rulesConnected level)) values‖ ≤
      ((Real.sqrt (Nat.floor (time * rate)) + 1) / rate) *
        ‖(rate • (1 - xiNativeSupTransition system rulesConnected level)) values‖ :=
  PoissonizedWalk.Banach.discrete_power_floor_poisson_comparison _
    (xiNativeSupTransition_norm_le_one system rulesConnected level) rate ratePositive time timeNonnegative values

theorem xiNativeSupTransition_absolute_floor_increment_poisson_comparison (system : EIGSData K)
    (rulesConnected : ∀ colour, (ruleSG system colour).Connected) (level : ℕ)
    (rate : ℝ) (ratePositive : 0 < rate) (first second : ℝ)
    (firstNonnegative : 0 ≤ first) (ordered : first ≤ second)
    (values : XiVtx system level → ℝ) :
    ‖(xiNativeSupTransition system rulesConnected level ^
        (Nat.floor (second * rate) - Nat.floor (first * rate))) values -
      NormedSpace.exp ((-((second - first) * rate)) •
        (1 - xiNativeSupTransition system rulesConnected level)) values‖ ≤
      ((Real.sqrt (Nat.floor ((second - first) * rate)) + 2) / rate) *
        ‖(rate • (1 - xiNativeSupTransition system rulesConnected level)) values‖ :=
  PoissonizedWalk.Banach.discrete_power_absolute_floor_increment_poisson_comparison _
    (xiNativeSupTransition_norm_le_one system rulesConnected level) rate ratePositive
      first second firstNonnegative ordered values

end
end EIGS

#print axioms EIGS.finiteGraphSupTransitionLinear_norm_le
#print axioms EIGS.finiteGraphSupTransition_norm_le_one
#print axioms EIGS.xiNativeSupTransition_norm_le_one
#print axioms EIGS.xiNativeSupTransition_kernel_integral
#print axioms EIGS.xiNativeSupTransition_kernel_power_integral
#print axioms EIGS.xiNativeSupTransition_pathLaw_endpoint_expectation
#print axioms EIGS.xiNativeSupTransition_floor_poisson_comparison
#print axioms EIGS.xiNativeSupTransition_absolute_floor_increment_poisson_comparison
