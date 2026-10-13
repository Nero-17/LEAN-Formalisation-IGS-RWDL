import RequestProject.Section31.DiscreteMarkovFiniteObservations
import RequestProject.Section2SurvivalFromExit
import Mathlib.Probability.ProbabilityMassFunction.Integrals

/-! Identify the actual graph survival recursion with an event of the genuine
Ionescu--Tulcea infinite path law, then transfer the proved exit-tail bound. -/

namespace EIGS

open MeasureTheory ProbabilityTheory Preorder
open scoped BigOperators ProbabilityTheory
open IGS.Sec31.DiscreteMarkov

noncomputable section

variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def finiteGraphTransitionKernel (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) : Kernel Vertex Vertex where
  toFun vertex := (rwStep (degree_positive vertex)).toMeasure
  measurable' := measurable_of_countable _

instance finiteGraphTransitionKernel_isMarkov (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree_positive : ∀ vertex, 0 < graph.degree vertex) :
    IsMarkovKernel (finiteGraphTransitionKernel graph degree_positive) := by
  constructor
  intro vertex
  change IsProbabilityMeasure (rwStep (degree_positive vertex)).toMeasure
  infer_instance

theorem finiteGraphTransitionKernel_integral (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (function : Vertex → ℝ) (vertex : Vertex) :
    (∫ neighbour, function neighbour ∂finiteGraphTransitionKernel graph degree_positive vertex) =
      ∑ neighbour, transProb graph vertex neighbour * function neighbour := by
  change (∫ neighbour, function neighbour ∂(rwStep (degree_positive vertex)).toMeasure) = _
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro neighbour _
  simp [rwStep_apply, ENNReal.toReal_ofReal (transProb_nonneg (G := graph) vertex neighbour)]

def graphSurvivalEvent (domain : Finset Vertex) (time : ℕ) : Set (ℕ → Vertex) :=
  {path | ∀ index ≤ time, path index ∈ domain}

theorem graphSurvivalEvent_measurable (domain : Finset Vertex) (time : ℕ) :
    MeasurableSet (graphSurvivalEvent domain time) := by
  have event_eq : graphSurvivalEvent domain time =
      ⋂ index : ℕ, ⋂ (_ : index ≤ time), {path : ℕ → Vertex | path index ∈ domain} := by
    ext path
    simp [graphSurvivalEvent]
  rw [event_eq]
  exact MeasurableSet.iInter (fun index => MeasurableSet.iInter (fun _ =>
    domain.measurableSet.preimage (measurable_pi_apply index)))

theorem graphSurvival_indicator_product (domain : Finset Vertex) (time : ℕ)
    (path : ℕ → Vertex) :
    (∏ index : Fin time, if path index.val ∈ domain then (1 : ℝ) else 0) *
        (if path time ∈ domain then (1 : ℝ) else 0) =
      (graphSurvivalEvent domain time).indicator (fun _ => (1 : ℝ)) path := by
  classical
  by_cases survives : ∀ index ≤ time, path index ∈ domain
  · have earlier : ∀ index : Fin time, path index.val ∈ domain :=
      fun index => survives index.val (Nat.le_of_lt index.isLt)
    rw [Set.indicator_of_mem (show path ∈ graphSurvivalEvent domain time from survives)]
    simp [earlier, survives time le_rfl]
  · have witness : ∃ index, index ≤ time ∧ path index ∉ domain := by
      push_neg at survives
      exact survives
    obtain ⟨index, bounded, outside⟩ := witness
    have absent : path ∉ graphSurvivalEvent domain time := survives
    rw [Set.indicator_of_notMem absent]
    by_cases last : index = time
    · subst index
      simp [outside]
    · have earlier : index < time := lt_of_le_of_ne bounded last
      have product_zero :
          (∏ index : Fin time, if path index.val ∈ domain then (1 : ℝ) else 0) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ (⟨index, earlier⟩ : Fin time))
        simp [outside]
      rw [product_zero, zero_mul]

theorem finiteGraph_backward_survival (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) (domain : Finset Vertex)
    (time remaining : ℕ) :
    backwardPrefix (finiteGraphTransitionKernel graph degree_positive)
      (fun _ point => if point ∈ domain then (1 : ℝ) else 0) time
      (surv graph domain remaining) = surv graph domain (time + remaining) := by
  induction time generalizing remaining with
  | zero => simp [backwardPrefix]
  | succ time inductionHypothesis =>
      rw [backwardPrefix]
      have one_step : (fun point => (if point ∈ domain then (1 : ℝ) else 0) *
          ∫ target, surv graph domain remaining target
            ∂finiteGraphTransitionKernel graph degree_positive point) =
          surv graph domain (remaining + 1) := by
        funext point
        rw [finiteGraphTransitionKernel_integral]
        by_cases inside : point ∈ domain <;> simp [surv, inside]
      rw [one_step, inductionHypothesis]
      congr 1
      omega

theorem graphSurvivalEvent_probability (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degree_positive : ∀ vertex, 0 < graph.degree vertex) (domain : Finset Vertex)
    (time : ℕ) (vertex : Vertex) :
    ((pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex))
      (graphSurvivalEvent domain time)).toReal = surv graph domain time vertex := by
  classical
  let initial : ProbabilityMeasure Vertex := ⟨Measure.dirac vertex, inferInstance⟩
  have representation := pathLaw_prefix_integral_backward
    (finiteGraphTransitionKernel graph degree_positive) initial
    (fun _ point => if point ∈ domain then (1 : ℝ) else 0) time
    (fun point => if point ∈ domain then (1 : ℝ) else 0)
    (fun _ => 1) 1 (fun _ => measurable_of_countable _) (measurable_of_countable _)
    (fun _ => zero_le_one) zero_le_one
    (fun _ point => by by_cases inside : point ∈ domain <;> simp [inside])
    (fun point => by by_cases inside : point ∈ domain <;> simp [inside])
  have product_identity :
      (fun path : ℕ → Vertex =>
        (∏ index : Fin time, if path index.val ∈ domain then (1 : ℝ) else 0) *
          (if path time ∈ domain then (1 : ℝ) else 0)) =
      (graphSurvivalEvent domain time).indicator (fun _ => (1 : ℝ)) :=
    funext (graphSurvival_indicator_product domain time)
  rw [product_identity] at representation
  have indicatorIntegral := integral_indicator_const
    (μ := pathLaw (finiteGraphTransitionKernel graph degree_positive) (initial : Measure Vertex))
    (1 : ℝ) (graphSurvivalEvent_measurable domain time)
  simp only [smul_eq_mul, mul_one] at indicatorIntegral
  rw [indicatorIntegral] at representation
  have backward_identity :
      backwardPrefix (finiteGraphTransitionKernel graph degree_positive)
        (fun _ point => if point ∈ domain then (1 : ℝ) else 0) time
        (fun point => if point ∈ domain then (1 : ℝ) else 0) =
      surv graph domain time := by
    simpa only [surv, Nat.add_zero] using
      finiteGraph_backward_survival graph degree_positive domain time 0
  rw [backward_identity] at representation
  simpa [initial, measureReal_def] using representation

theorem graphSurvivalEvent_probability_lower (graph : SimpleGraph Vertex)
    [DecidableRel graph.Adj] (degree_positive : ∀ vertex, 0 < graph.degree vertex)
    (connected : graph.Connected) {domain : Finset Vertex} (proper : domainᶜ.Nonempty)
    (upper : ℝ) (upper_positive : 0 < upper)
    (upper_bound : ∀ vertex, expExit graph domain vertex ≤ upper)
    (time : ℕ) (vertex : Vertex) :
    (expExit graph domain vertex - (time : ℝ)) / upper ≤
      ((pathLaw (finiteGraphTransitionKernel graph degree_positive) (Measure.dirac vertex))
        (graphSurvivalEvent domain time)).toReal := by
  rw [graphSurvivalEvent_probability]
  exact survival_lower_of_exit_bounds graph connected proper upper upper_positive upper_bound time vertex

end
end EIGS

#print axioms EIGS.finiteGraphTransitionKernel_integral
#print axioms EIGS.graphSurvival_indicator_product
#print axioms EIGS.finiteGraph_backward_survival
#print axioms EIGS.graphSurvivalEvent_probability
#print axioms EIGS.graphSurvivalEvent_probability_lower
