import RequestProject.Section31.FiniteGraphFloorExitTime
import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw
import RequestProject.Section31.SkorokhodJ1PrefixRadius

/-! Every discrete coordinate in a floor-clock prefix is observed at its
actual clock time. Therefore an open uniform-radius prefix is contained
in the true discrete ball-survival event, with a spatial center margin. -/

namespace IGS.Sec31.DiscreteMarkov
open Set MeasureTheory ProbabilityTheory
open scoped Classical NNReal ENNReal UniformConvergence
noncomputable section
variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]
variable [∀ level, DecidableEq (Vertex level)]

local instance stepRadiusStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance stepRadiusTimeBounded (horizon : ℝ≥0) :
    BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) := ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteHorizonStepMap_radius_lt_implies_survival (horizon : ℝ≥0)
    (rates : ℕ → ℝ≥0) (embedding : ∀ level, Vertex level → State)
    (level : ℕ) (ratePositive : 0 < rates level) (path : ℕ → Vertex level)
    (center : State) (discreteCenter : Vertex level) (innerRadius outerRadius : ℝ)
    (centerNear : dist (embedding level discreteCenter) center ≤ outerRadius - innerRadius)
    (near : dist (finiteHorizonStepMap horizon rates embedding level path).val
      (UniformFun.ofFun (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < innerRadius) :
    path ∈ EIGS.graphSurvivalEvent
      (Finset.univ.filter fun vertex : Vertex level => dist (embedding level discreteCenter) (embedding level vertex) < outerRadius)
      ⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ := by
  have rateRealPositive : 0 < (rates level : ℝ) := ratePositive
  intro index bounded
  have castBound : (index : ℝ) ≤ (⌊(horizon : ℝ) * (rates level : ℝ)⌋₊ : ℕ) := by
    exact_mod_cast bounded
  have indexBound : (index : ℝ) ≤ (horizon : ℝ) * (rates level : ℝ) :=
    castBound.trans (Nat.floor_le (mul_nonneg horizon.property (rates level).property))
  let observed : Icc (0 : ℝ) (horizon : ℝ) :=
    ⟨(index : ℝ) / (rates level : ℝ),
      div_nonneg (Nat.cast_nonneg index) (rates level).property,
      (div_le_iff₀ rateRealPositive).mpr indexBound⟩
  have floorEquality : ⌊observed.val * (rates level : ℝ)⌋₊ = index := by
    dsimp only [observed]
    rw [div_mul_cancel₀ _ rateRealPositive.ne', Nat.floor_natCast]
  have pointBound := (uniformFunction_dist_eval_le
    (UniformFun.toFun (finiteHorizonStepMap horizon rates embedding level path).val)
    (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center) observed).trans_lt near
  rw [finiteHorizonStepMap_apply, floorEquality] at pointBound
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have triangle := dist_triangle (embedding level discreteCenter) center (embedding level (path index))
  rw [dist_comm center] at triangle
  linarith

theorem finiteHorizonStepLaw_radius_le_floorExitTail (horizon : ℝ≥0)
    (rates : ℕ → ℝ≥0) (embedding : ∀ level, Vertex level → State)
    (kernels : ∀ level, Kernel (Vertex level) (Vertex level))
    [∀ level, IsMarkovKernel (kernels level)]
    (initial : ∀ level, ProbabilityMeasure (Vertex level))
    (level : ℕ) (ratePositive : 0 < rates level)
    (center : State) (discreteCenter : Vertex level) (innerRadius outerRadius : ℝ)
    (centerNear : dist (embedding level discreteCenter) center ≤ outerRadius - innerRadius) :
    (finiteHorizonStepLaw horizon rates embedding kernels initial level :
      Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
      {path | dist path.val (UniformFun.ofFun
        (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < innerRadius} ≤
    pathLaw (kernels level) (initial level)
      {path | (horizon : ℝ≥0∞) < EIGS.graphFloorExitTime
        (Finset.univ.filter fun vertex : Vertex level =>
          dist (embedding level discreteCenter) (embedding level vertex) < outerRadius) (rates level) path} := by
  have goodOpen : IsOpen {path : FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding) |
      dist path.val (UniformFun.ofFun
        (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < innerRadius} :=
    isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  rw [finiteHorizonStepLaw_eq_map, Measure.map_apply
    (finiteHorizonStepMap_measurable horizon rates embedding level)
    goodOpen.measurableSet]
  apply measure_mono
  intro path near
  apply (EIGS.graphFloorExitTime_survival_iff _ _ ratePositive path horizon).mpr
  exact finiteHorizonStepMap_radius_lt_implies_survival horizon rates embedding level ratePositive
    path center discreteCenter innerRadius outerRadius centerNear near

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepMap_radius_lt_implies_survival
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_radius_le_floorExitTail
