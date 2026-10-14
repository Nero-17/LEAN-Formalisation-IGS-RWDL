import RequestProject.Section31.FiniteSupportContinuousJ1LawIdentification
import RequestProject.Section31.ContinuousTimePathBorel

/-! The actual finite-horizon support law's J1 pushforward is the same global
continuous law's genuine continuous-map restriction, then its J1 pushforward.
The input equality is only the already proved function-valued restriction
law. No J1-law identity or D Polishness is an assumption. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Classical NNReal UniformConvergence
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)] [∀ level, MeasurableSingletonClass (Vertex level)]

local instance globalJ1RestrictionPathMeasurable : MeasurableSpace C(ℝ≥0, State) := borel _
local instance globalJ1RestrictionPathBorel : BorelSpace C(ℝ≥0, State) := ⟨rfl⟩
local instance globalJ1RestrictionIntervalNonempty (horizon : ℝ≥0) : Nonempty (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨⟨0, ⟨le_rfl, horizon.property⟩⟩⟩
local instance globalJ1RestrictionIntervalBounded (horizon : ℝ≥0) : BoundedSpace (Icc (0 : ℝ) (horizon : ℝ)) :=
  ⟨Metric.isBounded_of_compactSpace⟩
local instance globalJ1RestrictionStateBounded : BoundedSpace State := ⟨Metric.isBounded_of_compactSpace⟩
local instance globalJ1RestrictionMapMeasurable (horizon : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := borel _
local instance globalJ1RestrictionMapBorel (horizon : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (horizon : ℝ), State) := ⟨rfl⟩
local instance globalJ1RestrictionTargetMeasurable (horizon : ℝ≥0) :
    MeasurableSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := borel _
local instance globalJ1RestrictionTargetBorel (horizon : ℝ≥0) :
    BorelSpace (CadlagJ1Path (Icc (0 : ℝ) (horizon : ℝ)) State) := ⟨rfl⟩

def continuousPathFiniteHorizonRestriction (horizon : ℝ≥0) :
    C(ℝ≥0, State) → C(Icc (0 : ℝ) (horizon : ℝ), State) :=
  fun path => path.comp
    ⟨fun time => ⟨time.val, time.property.1⟩, continuous_subtype_val.subtype_mk (fun time => time.property.1)⟩

theorem continuousPathFiniteHorizonRestriction_continuous (horizon : ℝ≥0) :
    Continuous (continuousPathFiniteHorizonRestriction (State := State) horizon) :=
  ContinuousMap.continuous_precomp _

theorem finiteHorizon_nativeJ1Law_eq_globalRestriction
    (horizon : ℝ≥0) (rates : ℕ → ℝ≥0) (embedding : ∀ level, Vertex level → State)
    (law : ProbabilityMeasure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (lawContinuous : ∀ᵐ path ∂(law : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))),
      Continuous (UniformFun.toFun path.val))
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (functionLawEquality :
      (law : Measure (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding))).map
        (fun path => UniformFun.toFun path.val) =
      (globalLaw : Measure C(ℝ≥0, State)).map
        (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩)) :
    law.map (finiteHorizonPathToCadlagJ1_continuous horizon rates embedding).measurable.aemeasurable =
      (globalLaw.map (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable).map
        compactContinuousMapToCadlagJ1_lipschitz.continuous.measurable.aemeasurable := by
  let restrictedLaw := globalLaw.map (continuousPathFiniteHorizonRestriction_continuous horizon).measurable.aemeasurable
  have continuousFunctionMeasurable : Measurable
      (fun path : C(Icc (0 : ℝ) (horizon : ℝ), State) => fun time => path time) :=
    measurable_pi_lambda _ fun time => (continuous_eval_const time).measurable
  have restrictionFunctions : (restrictedLaw : Measure C(Icc (0 : ℝ) (horizon : ℝ), State)).map
      (fun path => fun time => path time) =
      (globalLaw : Measure C(ℝ≥0, State)).map
        (fun path => fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩) := by
    change ((globalLaw : Measure C(ℝ≥0, State)).map (continuousPathFiniteHorizonRestriction horizon)).map
      (fun path => fun time => path time) = _
    rw [Measure.map_map continuousFunctionMeasurable (continuousPathFiniteHorizonRestriction_continuous horizon).measurable]
    rfl
  exact finiteSupportPath_j1Law_eq_continuousLaw (finiteHorizonStepPaths horizon rates embedding)
    (finiteHorizonStepPaths_isCadlag horizon rates embedding) law lawContinuous restrictedLaw
    (functionLawEquality.trans restrictionFunctions.symm)

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuousPathFiniteHorizonRestriction_continuous
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizon_nativeJ1Law_eq_globalRestriction
