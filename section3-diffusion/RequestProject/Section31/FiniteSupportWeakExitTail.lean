import RequestProject.Section31.FiniteSupportWeakBallSurvival
import RequestProject.Section31.SkorokhodJ1PrefixRadius

/-! An open maximal-distance event transfers a true continuous exit tail
under the already proved uniform weak laws. The function-valued restriction
identity is used only on a countable measurable union of dense-prefix
events. Continuity of the limiting paths supplies the strict-radius margin. -/

namespace IGS.Sec31.DiscreteMarkov
open Set Filter Topology MeasureTheory
open scoped Classical UniformConvergence NNReal ENNReal
noncomputable section

variable {Time State : Type*} [TopologicalSpace Time]
variable [MetricSpace State] [BoundedSpace State]

theorem continuous_uniformRadius_lt_iff_dense (path : Time → State)
    (pathContinuous : Continuous path) (times : ℕ → Time) (timesDense : DenseRange times)
    (center : State) (radius : ℝ) :
    dist (UniformFun.ofFun path) (UniformFun.ofFun (fun _ : Time => center)) < radius ↔
      ∃ margin : ℕ, ∀ index,
        dist (path (times index)) center ≤ radius - 1 / (margin + 1 : ℝ) := by
  constructor
  · intro near
    obtain ⟨margin, marginBound⟩ := exists_nat_one_div_lt (sub_pos.mpr near)
    refine ⟨margin, fun index => ?_⟩
    have bound : dist (path (times index)) center ≤
        dist (UniformFun.ofFun path) (UniformFun.ofFun (fun _ : Time => center)) :=
      (UniformFun.dist_le (dist_nonneg : 0 ≤ dist (UniformFun.ofFun path)
        (UniformFun.ofFun (fun _ : Time => center)))).mp le_rfl (times index)
    linarith
  · rintro ⟨margin, bounds⟩
    have fullBounds : ∀ time, dist (path time) center ≤ radius - 1 / (margin + 1 : ℝ) := by
      intro time
      exact timesDense.induction_on
        (p := fun time => dist (path time) center ≤ radius - 1 / (margin + 1 : ℝ)) time
        (isClosed_le (pathContinuous.dist continuous_const) continuous_const) bounds
    have nonnegative : 0 ≤ radius - 1 / (margin + 1 : ℝ) :=
      dist_nonneg.trans (fullBounds (times 0))
    have uniformBound : dist (UniformFun.ofFun path) (UniformFun.ofFun (fun _ : Time => center)) ≤
        radius - 1 / (margin + 1 : ℝ) := (UniformFun.dist_le nonnegative).mpr fullBounds
    have marginPositive : 0 < 1 / (margin + 1 : ℝ) := by positivity
    linarith

theorem continuous_uniformRadius_lt_iff_forall [CompactSpace Time] [Nonempty Time]
    (path : Time → State) (pathContinuous : Continuous path) (center : State) (radius : ℝ) :
    dist (UniformFun.ofFun path) (UniformFun.ofFun (fun _ : Time => center)) < radius ↔
      ∀ time, dist (path time) center < radius := by
  rw [UniformFun.dist_def]
  change sSup (Set.range (fun time => dist (path time) center)) < radius ↔ _
  simpa only [Set.image_univ, Set.mem_univ, forall_const] using
    isCompact_univ.sSup_lt_iff_of_continuous (Set.univ_nonempty : (Set.univ : Set Time).Nonempty)
      (pathContinuous.dist continuous_const).continuousOn radius

variable [CompactSpace State] [MeasurableSpace State] [BorelSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]

theorem finiteSupport_weak_global_exit_tail
    [MeasurableSpace C(ℝ≥0, State)] [BorelSpace C(ℝ≥0, State)]
    (horizon : ℝ≥0)
    (paths : (level : ℕ) → History level → Icc (0 : ℝ) (horizon : ℝ) → State)
    (times : ℕ → Icc (0 : ℝ) (horizon : ℝ)) (timesDense : DenseRange times)
    (center : State) (radius : ℝ)
    (laws : ℕ → ProbabilityMeasure (FiniteSupportPathSpace paths))
    (limit : ProbabilityMeasure (FiniteSupportPathSpace paths))
    (convergence : Tendsto laws atTop (𝓝 limit))
    (limitContinuous : ∀ᵐ path ∂(limit : Measure (FiniteSupportPathSpace paths)),
      Continuous (UniformFun.toFun path.val))
    (globalLaw : ProbabilityMeasure C(ℝ≥0, State))
    (restriction :
      (limit : Measure (FiniteSupportPathSpace paths)).map (fun path => UniformFun.toFun path.val) =
        (globalLaw : Measure C(ℝ≥0, State)).map
          (fun path => fun observed : Icc (0 : ℝ) (horizon : ℝ) =>
            path ⟨observed.val, observed.property.1⟩)) :
    (globalLaw : Measure C(ℝ≥0, State))
      {path | (horizon : ℝ≥0∞) < continuousPathBallExit path center radius} ≤
        liminf (fun level => (laws level : Measure (FiniteSupportPathSpace paths))
          {path | dist path.val (UniformFun.ofFun (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < radius}) atTop := by
  let functionGood : Set (Icc (0 : ℝ) (horizon : ℝ) → State) :=
    {path | ∃ margin : ℕ, ∀ index,
      dist (path (times index)) center ≤ radius - 1 / (margin + 1 : ℝ)}
  have functionGoodMeasurable : MeasurableSet functionGood := by
    have representation : functionGood = ⋃ margin : ℕ, ⋂ index : ℕ,
        {path | dist (path (times index)) center ≤ radius - 1 / (margin + 1 : ℝ)} := by
      ext path
      simp only [functionGood, mem_setOf_eq, mem_iUnion, mem_iInter]
    rw [representation]
    exact MeasurableSet.iUnion fun margin => MeasurableSet.iInter fun index =>
      measurableSet_le ((measurable_pi_apply (times index)).dist measurable_const) measurable_const
  have localMapMeasurable : Measurable
      (fun path : FiniteSupportPathSpace paths => UniformFun.toFun path.val) :=
    measurable_pi_lambda _ fun observed => (finiteSupportPathSpace_continuous_eval paths observed).measurable
  have globalMapMeasurable : Measurable
      (fun path : C(ℝ≥0, State) => fun observed : Icc (0 : ℝ) (horizon : ℝ) =>
        path ⟨observed.val, observed.property.1⟩) :=
    measurable_pi_lambda _ fun observed => (continuous_eval_const _).measurable
  have eventEquality := congrArg (fun law : Measure (Icc (0 : ℝ) (horizon : ℝ) → State) =>
    law functionGood) restriction
  dsimp only at eventEquality
  rw [Measure.map_apply localMapMeasurable functionGoodMeasurable,
    Measure.map_apply globalMapMeasurable functionGoodMeasurable] at eventEquality
  have limitEquality :
      (limit : Measure (FiniteSupportPathSpace paths))
        {path | dist path.val (UniformFun.ofFun (fun _ : Icc (0 : ℝ) (horizon : ℝ) => center)) < radius} =
      (limit : Measure (FiniteSupportPathSpace paths))
        ((fun path => UniformFun.toFun path.val) ⁻¹' functionGood) := by
    apply measure_congr
    filter_upwards [limitContinuous] with path pathContinuous
    apply propext
    simpa only [UniformFun.ofFun_toFun] using
      continuous_uniformRadius_lt_iff_dense (UniformFun.toFun path.val)
        pathContinuous times timesDense center radius
  have globalEquality :
      (globalLaw : Measure C(ℝ≥0, State))
        ((fun path => fun observed : Icc (0 : ℝ) (horizon : ℝ) =>
          path ⟨observed.val, observed.property.1⟩) ⁻¹' functionGood) =
      (globalLaw : Measure C(ℝ≥0, State))
        {path | (horizon : ℝ≥0∞) < continuousPathBallExit path center radius} := by
    congr 1
    ext path
    have restrictedContinuous : Continuous
        (fun time : Icc (0 : ℝ) (horizon : ℝ) => path ⟨time.val, time.property.1⟩) :=
      path.continuous.comp (continuous_subtype_val.subtype_mk fun time => time.property.1)
    letI : Nonempty (Icc (0 : ℝ) (horizon : ℝ)) := ⟨⟨0, le_rfl, horizon.property⟩⟩
    change (∃ margin : ℕ, ∀ index,
      dist (path ⟨(times index).val, (times index).property.1⟩) center ≤
        radius - 1 / (margin + 1 : ℝ)) ↔
      (horizon : ℝ≥0∞) < continuousPathBallExit path center radius
    rw [← continuous_uniformRadius_lt_iff_dense _ restrictedContinuous times timesDense,
      continuous_uniformRadius_lt_iff_forall _ restrictedContinuous,
      time_lt_continuousPathBallExit_iff]
    constructor
    · intro bound observed before
      exact bound ⟨observed.val, observed.property, by exact_mod_cast before⟩
    · intro bound observed
      exact bound ⟨observed.val, observed.property.1⟩ (by exact_mod_cast observed.property.2)
  rw [← globalEquality, ← eventEquality, ← limitEquality]
  apply ProbabilityMeasure.le_liminf_measure_open_of_tendsto convergence
  exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.continuous_uniformRadius_lt_iff_dense
#print axioms IGS.Sec31.DiscreteMarkov.continuous_uniformRadius_lt_iff_forall
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupport_weak_global_exit_tail
