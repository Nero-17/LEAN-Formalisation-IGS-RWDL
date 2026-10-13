import RequestProject.Section31.FiniteHorizonMarkovStepPathLaw

/-! Finite evaluations of a weak path limit. These lemmas transfer an already
proved weak convergence to the finite-dimensional distributions of the actual
floor-clock trajectories. They do not identify the limiting distributions or
assert uniqueness of a path limit. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Filter Topology
open scoped UniformConvergence NNReal

variable {Time State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

theorem finiteSupportPathSpace_continuous_finite_evaluations
    (paths : (level : ℕ) → History level → Time → State)
    (dimension : ℕ) (times : Fin dimension → Time) :
    Continuous (fun path : FiniteSupportPathSpace paths =>
      fun index => UniformFun.toFun path.val (times index)) :=
  continuous_pi fun index => finiteSupportPathSpace_continuous_eval paths (times index)

theorem finiteSupportPath_weakLimit_finite_evaluations
    (paths : (level : ℕ) → History level → Time → State)
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (weakConvergence : Tendsto laws atTop (𝓝 limit))
    (dimension : ℕ) (times : Fin dimension → Time) :
    Tendsto (fun level => (laws level).map
      (finiteSupportPathSpace_continuous_finite_evaluations paths dimension times).measurable.aemeasurable)
      atTop (𝓝 (limit.map
        (finiteSupportPathSpace_continuous_finite_evaluations paths dimension times).measurable.aemeasurable)) :=
  ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous laws limit weakConvergence
    (finiteSupportPathSpace_continuous_finite_evaluations paths dimension times)

variable {Vertex : ℕ → Type*} [∀ level, Fintype (Vertex level)]
variable [∀ level, MeasurableSpace (Vertex level)]
variable [∀ level, MeasurableSingletonClass (Vertex level)]

theorem finiteHorizonStepLaw_weakLimit_finite_evaluations
    (horizon : ℝ≥0) (rates : ℕ → ℝ≥0)
    (embedding : (level : ℕ) → Vertex level → State)
    (kernels : (level : ℕ) → Kernel (Vertex level) (Vertex level))
    [∀ level, IsMarkovKernel (kernels level)]
    (initial : (level : ℕ) → ProbabilityMeasure (Vertex level))
    (levels : ℕ → ℕ)
    (limit : ProbabilityMeasure
      (FiniteSupportPathSpace (finiteHorizonStepPaths horizon rates embedding)))
    (weakConvergence : Tendsto
      (fun index => finiteHorizonStepLaw horizon rates embedding kernels initial (levels index))
      atTop (𝓝 limit))
    (dimension : ℕ) (times : Fin dimension → Set.Icc (0 : ℝ) (horizon : ℝ)) :
    Tendsto (fun index =>
      (finiteHorizonStepLaw horizon rates embedding kernels initial (levels index)).map
        (finiteSupportPathSpace_continuous_finite_evaluations
          (finiteHorizonStepPaths horizon rates embedding) dimension times).measurable.aemeasurable)
      atTop (𝓝 (limit.map (finiteSupportPathSpace_continuous_finite_evaluations
        (finiteHorizonStepPaths horizon rates embedding) dimension times).measurable.aemeasurable)) :=
  finiteSupportPath_weakLimit_finite_evaluations _ _ limit weakConvergence dimension times

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPathSpace_continuous_finite_evaluations
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_weakLimit_finite_evaluations
#print axioms IGS.Sec31.DiscreteMarkov.finiteHorizonStepLaw_weakLimit_finite_evaluations
