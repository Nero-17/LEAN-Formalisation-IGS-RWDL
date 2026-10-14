import RequestProject.Section31.FiniteGraphExponentialPhysicalJ1PathLaw
import RequestProject.Section31.FiniteSupportUnitGlobalLawIdentification

/-! Literal physical-interval holding-law weak limits are the J1 images
of the very same global continuous path law's actual restriction. -/

namespace IGS.Sec31.PoissonClock
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Topology
open IGS.Sec31.DiscreteMarkov EIGS
open scoped NNReal
set_option maxHeartbeats 4000000

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
local instance physicalGlobalStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalGlobalPathMeasurable : MeasurableSpace C(ℝ≥0, State) := borel _
local instance physicalGlobalPathBorel : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩
local instance physicalGlobalTimeBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance physicalGlobalTimeMapMeasurable (horizon : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := borel _
local instance physicalGlobalTimeMapBorel (horizon : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := ⟨rfl⟩
local instance physicalGlobalCadlagMeasurable (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance physicalGlobalCadlagBorel (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩

theorem unitToPhysicalCadlagJ1_global_path (horizon : ℝ≥0) (positive : 0 < horizon)
    (path : C(ℝ≥0, State)) :
    unitToPhysicalCadlagJ1 horizon positive (continuousPathToUnitCadlagJ1 horizon path) =
      compactContinuousMapToCadlagJ1 (continuousPathFiniteHorizonRestriction horizon path) := by
  apply Subtype.ext
  have functions :
      (unitToPhysicalCadlagJ1 horizon positive (continuousPathToUnitCadlagJ1 horizon path)).val.toFun =
        (compactContinuousMapToCadlagJ1 (continuousPathFiniteHorizonRestriction horizon path)).val.toFun := by
    funext time
    rw [unitToPhysicalCadlagJ1_apply]
    have clockEquality : (horizon : ℝ) * (time.val / horizon) = time.val := by
      field_simp [ne_of_gt (show (0 : ℝ) < horizon from positive)]
    simp only [continuousPathToUnitCadlagJ1, compactContinuousMapToCadlagJ1,
      ContinuousMap.comp_apply, continuousPathFiniteHorizonRestriction]
    apply congrArg path
    apply Subtype.ext
    exact clockEquality
  have reconstruct (function : J1Function (Icc (0 : ℝ) (horizon : ℝ)) State) :
      J1Function.mk function.toFun = function := by cases function; rfl
  exact (reconstruct _).symm.trans ((congrArg J1Function.mk functions).trans (reconstruct _))

theorem unitToPhysicalCadlagJ1_global_law (horizon : ℝ≥0) (positive : 0 < horizon)
    (law : ProbabilityMeasure C(ℝ≥0, State)) :
    ProbabilityMeasure.map
      (ProbabilityMeasure.map law (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable)
      (unitToPhysicalCadlagJ1_continuous horizon positive).measurable.aemeasurable =
      ProbabilityMeasure.map
        (ProbabilityMeasure.map law (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
        compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_map (unitToPhysicalCadlagJ1_continuous horizon positive).measurable
    (continuousPathToUnitCadlagJ1_continuous horizon).measurable,
    Measure.map_map compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable
      (continuousPathFiniteHorizonRestriction_continuous horizon).measurable]
  congr 1
  exact funext (unitToPhysicalCadlagJ1_global_path horizon positive)

theorem finiteGraphExponentialPhysicalJ1Laws_tendsto_global_restriction
    (Vertex : ℕ → Type) [∀ level, Fintype (Vertex level)] [∀ level, DecidableEq (Vertex level)]
    [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]
    (graphs : ∀ level, SimpleGraph (Vertex level)) [∀ level, DecidableRel (graphs level).Adj]
    (degreePositive : ∀ level vertex, 0 < (graphs level).degree vertex)
    (initial : ∀ level, ProbabilityMeasure (Vertex level)) (embedding : ∀ level, Vertex level → State)
    (rates : ℕ → ℝ) (ratesPositive : ∀ level, 0 < rates level)
    (horizon : ℝ≥0) (positive : 0 < horizon) (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (unitConverges : Tendsto (fun level => finiteGraphExponentialJ1Law (graphs level) (degreePositive level)
      (initial level) (embedding level) (rates level * horizon)
      (mul_pos (ratesPositive level) (show (0 : ℝ) < horizon from positive))) atTop
      (𝓝 (ProbabilityMeasure.map globalLaw (continuousPathToUnitCadlagJ1_continuous horizon).measurable.aemeasurable))) :
    Tendsto (fun level => finiteGraphExponentialPhysicalJ1Law (graphs level) (degreePositive level)
      (initial level) (embedding level) (rates level) (ratesPositive level) horizon positive) atTop
      (𝓝 (ProbabilityMeasure.map
        (ProbabilityMeasure.map globalLaw (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable)
        compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable)) := by
  have result := unitToPhysicalCadlagJ1_weak_convergence horizon positive _ _ unitConverges
  rw [unitToPhysicalCadlagJ1_global_law] at result
  exact result

end
end IGS.Sec31.PoissonClock

#print axioms IGS.Sec31.PoissonClock.unitToPhysicalCadlagJ1_global_law
#print axioms IGS.Sec31.PoissonClock.finiteGraphExponentialPhysicalJ1Laws_tendsto_global_restriction
