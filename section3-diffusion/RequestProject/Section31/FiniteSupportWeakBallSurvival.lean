import RequestProject.Section31.ContinuousPathBallExit
import RequestProject.Section31.FiniteSupportUniformPathSpace
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.DenseEmbedding

/-! A closed countable-prefix event transfers a maximal displacement budget
under weak convergence of the actual uniform carriers. The existing function
restriction law identity then transfers that event to the global continuous
law. Density and an inner-radius margin imply genuine exit survival.
No coupling theorem or single-time stay substitute is used. Candidate source. -/

namespace IGS.Sec31.DiscreteMarkov
open Set Filter Topology MeasureTheory
open scoped UniformConvergence NNReal ENNReal
noncomputable section

variable {State : Type*} [MetricSpace State] [CompactSpace State]
variable [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

def finiteSupportDensePrefixClosedSet {Time : Type*}
    (paths : (level : ℕ) → History level → Time → State)
    (times : ℕ → Time) (center : State) (radius : ℝ) : Set (FiniteSupportPathSpace paths) :=
  {path | ∀ index, dist (UniformFun.toFun path.val (times index)) center ≤ radius}

theorem finiteSupportDensePrefixClosedSet_isClosed {Time : Type*}
    (paths : (level : ℕ) → History level → Time → State)
    (times : ℕ → Time) (center : State) (radius : ℝ) :
    IsClosed (finiteSupportDensePrefixClosedSet paths times center radius) := by
  have representation : finiteSupportDensePrefixClosedSet paths times center radius =
      ⋂ index, {path : FiniteSupportPathSpace paths |
        dist (UniformFun.toFun path.val (times index)) center ≤ radius} := by
    ext path
    simp only [finiteSupportDensePrefixClosedSet, mem_setOf_eq, mem_iInter]
  rw [representation]
  exact isClosed_iInter fun index => isClosed_le
    ((finiteSupportPathSpace_continuous_eval paths (times index)).dist continuous_const)
    continuous_const

theorem finiteSupport_weak_global_ball_survival
    [MeasurableSpace C(ℝ≥0, State)] [BorelSpace C(ℝ≥0, State)]
    (horizon : ℝ≥0)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (times : ℕ → Icc (0 : ℝ) (horizon : ℝ)) (timesDense : DenseRange times)
    (center : State) (innerRadius outerRadius : ℝ) (radiusMargin : innerRadius < outerRadius)
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (convergence : Tendsto laws atTop (𝓝 limit))
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (restriction :
      (limit : Measure (FiniteSupportPathSpace paths)).map (fun path => UniformFun.toFun path.val) =
        (globalLaw : Measure C(ℝ≥0, State)).map
          (fun path => fun observed : Icc (0 : ℝ) (horizon : ℝ) =>
            path ⟨observed.val, observed.property.1⟩))
    (finiteBad : ∀ᶠ level in atTop,
      (laws level : Measure (FiniteSupportPathSpace paths))
        (finiteSupportDensePrefixClosedSet paths times center innerRadius)ᶜ ≤ ENNReal.ofReal (1 / 4)) :
    (3 / 4 : ℝ) ≤ (globalLaw : Measure C(ℝ≥0, State)).real
      {path | (horizon : ℝ≥0∞) < continuousPathBallExit path center outerRadius} := by
  let good : Set (FiniteSupportPathSpace paths) :=
    finiteSupportDensePrefixClosedSet paths times center innerRadius
  have goodClosed : IsClosed good := finiteSupportDensePrefixClosedSet_isClosed paths times center innerRadius
  have limitBad : (limit : Measure (FiniteSupportPathSpace paths)) goodᶜ ≤ ENNReal.ofReal (1 / 4) := by
    apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto convergence goodClosed.isOpen_compl).trans
    exact Filter.liminf_le_of_frequently_le' finiteBad.frequently
  let functionGood : Set (Icc (0 : ℝ) (horizon : ℝ) → State) :=
    {path | ∀ index, dist (path (times index)) center ≤ innerRadius}
  have functionGoodMeasurable : MeasurableSet functionGood := by
    have representation : functionGood = ⋂ index,
        {path : Icc (0 : ℝ) (horizon : ℝ) → State | dist (path (times index)) center ≤ innerRadius} := by
      ext path
      simp only [functionGood, mem_setOf_eq, mem_iInter]
    rw [representation]
    exact MeasurableSet.iInter fun index => measurableSet_le
      ((measurable_pi_apply (times index)).dist measurable_const) measurable_const
  have localMapMeasurable : Measurable
      (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) :=
    measurable_pi_lambda _ fun observed => (finiteSupportPathSpace_continuous_eval paths observed).measurable
  have globalMapMeasurable : Measurable
      (fun path : C(ℝ≥0, State) => fun observed : Icc (0 : ℝ) (horizon : ℝ) =>
        path ⟨observed.val, observed.property.1⟩) :=
    measurable_pi_lambda _ fun observed => (continuous_eval_const _).measurable
  have badEquality := congrArg (fun law : Measure (Icc (0 : ℝ) (horizon : ℝ) → State) =>
    law functionGoodᶜ) restriction
  dsimp only at badEquality
  rw [Measure.map_apply localMapMeasurable functionGoodMeasurable.compl,
    Measure.map_apply globalMapMeasurable functionGoodMeasurable.compl] at badEquality
  let globalGood : Set C(ℝ≥0, State) :=
    {path | ∀ index, dist (path ⟨(times index).val, (times index).property.1⟩) center ≤ innerRadius}
  have globalGoodMeasurable : MeasurableSet globalGood :=
    functionGoodMeasurable.preimage globalMapMeasurable
  have globalBad : (globalLaw : Measure C(ℝ≥0, State)) globalGoodᶜ ≤ ENNReal.ofReal (1 / 4) := by
    change (limit : Measure (FiniteSupportPathSpace paths)) goodᶜ = _ at badEquality
    rw [← badEquality]
    exact limitBad
  have realGlobalBad : (globalLaw : Measure C(ℝ≥0, State)).real globalGoodᶜ ≤ (1 / 4 : ℝ) := by
    exact (ENNReal.toReal_mono (by simp) globalBad).trans (by norm_num)
  have globalGoodLower : (3 / 4 : ℝ) ≤ (globalLaw : Measure C(ℝ≥0, State)).real globalGood := by
    rw [probReal_compl_eq_one_sub globalGoodMeasurable] at realGlobalBad
    linarith
  apply globalGoodLower.trans (measureReal_mono ?_)
  intro path denseBound
  apply (time_lt_continuousPathBallExit_iff path center outerRadius horizon).mpr
  intro observed beforeHorizon
  have observedInInterval : (observed : ℝ) ≤ (horizon : ℝ) := by exact_mod_cast beforeHorizon
  have restrictedContinuous : Continuous
      (fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩) :=
    path.continuous.comp (continuous_subtype_val.subtype_mk fun time => time.property.1)
  have bound : dist (path observed) center ≤ innerRadius :=
    timesDense.induction_on ⟨observed, observed.property, observedInInterval⟩
      (isClosed_le (restrictedContinuous.dist continuous_const) continuous_const) denseBound
  exact bound.trans_lt radiusMargin

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportDensePrefixClosedSet_isClosed
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupport_weak_global_ball_survival
