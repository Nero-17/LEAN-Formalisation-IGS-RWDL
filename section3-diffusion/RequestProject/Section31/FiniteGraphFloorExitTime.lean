import RequestProject.Section31.FiniteGraphExitDuration
import RequestProject.Section31.ExtendedExitTailIntegral

/-! The deterministic native floor clock has exit duration equal to the
actual discrete first exit divided by the jump rate. Its whole tail
integral is the genuine survival-series mean divided by that rate. -/

namespace EIGS
open MeasureTheory ProbabilityTheory Filter Set
open IGS.Sec31 IGS.Sec31.DiscreteMarkov
open scoped Classical ENNReal NNReal
noncomputable section
variable {Vertex : Type} [Fintype Vertex] [DecidableEq Vertex]
variable [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]

def graphFloorExitTime (domain : Finset Vertex) (rate : ℝ≥0) (path : ℕ → Vertex) : ℝ≥0∞ :=
  graphExitDuration domain path / (rate : ℝ≥0∞)

theorem graphFloorExitTime_measurable (domain : Finset Vertex) (rate : ℝ≥0) :
    Measurable (graphFloorExitTime domain rate) :=
  (graphExitDuration_measurable domain).div measurable_const

theorem graphFloorExitTime_survival_iff (domain : Finset Vertex) (rate : ℝ≥0)
    (ratePositive : 0 < rate) (path : ℕ → Vertex) (time : ℝ≥0) :
    (time : ℝ≥0∞) < graphFloorExitTime domain rate path ↔
      path ∈ graphSurvivalEvent domain ⌊(time : ℝ) * (rate : ℝ)⌋₊ := by
  by_cases exits : ∃ index : ℕ, path index ∉ domain
  · let duration := Nat.find exits
    have atExit : path duration ∉ domain := Nat.find_spec exits
    have beforeExit : ∀ index < duration, path index ∈ domain := by
      intro index earlier
      by_contra outside
      exact (not_lt_of_ge (Nat.find_min' exits outside)) earlier
    have survival : ∀ count, path ∈ graphSurvivalEvent domain count ↔ count < duration := by
      intro count
      constructor
      · intro survives
        by_contra late
        exact atExit (survives duration (Nat.le_of_not_gt late))
      · intro earlier index bounded
        exact beforeExit index (lt_of_le_of_lt bounded earlier)
    rw [survival]
    have rateRealPositive : 0 < (rate : ℝ) := ratePositive
    have scaled : (duration : ℝ≥0∞) / (rate : ℝ≥0∞) =
        ENNReal.ofReal ((duration : ℝ) / (rate : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos rateRealPositive]
      simp only [ENNReal.ofReal_natCast, ENNReal.ofReal_coe_nnreal]
    change (time : ℝ≥0∞) < graphExitDuration domain path / (rate : ℝ≥0∞) ↔ _
    rw [graphExitDuration_eq_of_first_exit domain path duration beforeExit atExit, scaled,
      ← ENNReal.ofReal_coe_nnreal (p := time)]
    calc
      ENNReal.ofReal (time : ℝ) < ENNReal.ofReal ((duration : ℝ) / (rate : ℝ)) ↔
          (time : ℝ) < (duration : ℝ) / (rate : ℝ) :=
        ENNReal.ofReal_lt_ofReal_iff_of_nonneg time.property
      _ ↔ (time : ℝ) * (rate : ℝ) < (duration : ℝ) := lt_div_iff₀ rateRealPositive
      _ ↔ ⌊(time : ℝ) * (rate : ℝ)⌋₊ < duration :=
        (Nat.floor_lt (mul_nonneg time.property rate.property)).symm
  · have neverExits : ∀ index, path index ∈ domain := by
      intro index
      by_contra outside
      exact exits ⟨index, outside⟩
    have survives : path ∈ graphSurvivalEvent domain ⌊(time : ℝ) * (rate : ℝ)⌋₊ :=
      fun index _ => neverExits index
    simp only [graphFloorExitTime, graphExitDuration_eq_top_of_never_exit domain path neverExits,
      ENNReal.top_div_coe, ENNReal.coe_lt_top, survives]

theorem graphFloorExitTime_lintegral (graph : SimpleGraph Vertex) [DecidableRel graph.Adj]
    (degreePositive : ∀ vertex, 0 < graph.degree vertex) (connected : graph.Connected)
    {domain : Finset Vertex} (proper : domainᶜ.Nonempty) (rate : ℝ≥0) (source : Vertex) :
    (∫⁻ path, graphFloorExitTime domain rate path
      ∂pathLaw (finiteGraphTransitionKernel graph degreePositive) (Measure.dirac source)) =
      ENNReal.ofReal (expExit graph domain source) / (rate : ℝ≥0∞) := by
  simp only [graphFloorExitTime, div_eq_mul_inv]
  rw [lintegral_mul_const _ (graphExitDuration_measurable domain),
    graphExitDuration_lintegral graph degreePositive connected proper source]

end
end EIGS

#print axioms EIGS.graphFloorExitTime_measurable
#print axioms EIGS.graphFloorExitTime_survival_iff
#print axioms EIGS.graphFloorExitTime_lintegral
