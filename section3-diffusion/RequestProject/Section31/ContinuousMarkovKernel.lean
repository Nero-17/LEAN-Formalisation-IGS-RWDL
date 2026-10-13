import RequestProject.Section31.ContinuousMarkovPointMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.PiSystem
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Probability kernels of a positive unital C0 semigroup on a compact metric
space. Weak continuity implies Giry measurability by closed-set approximation
and a pi-system argument. The zero and composition laws follow from equality
of continuous-function integrals. No process or Hunt property is asserted. -/

namespace IGS.Sec31.ContinuousMarkov

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ProbabilityTheory
noncomputable section

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [SecondCountableTopology Space] [ambientMeasurable : MeasurableSpace Space] [BorelSpace Space]

/-- The topology of weak convergence supplies genuine measure-valued
measurability; measurability is not added as a hypothesis on the family. -/
theorem measurable_toMeasure_of_continuous {Parameter : Type*}
    [TopologicalSpace Parameter] [MeasurableSpace Parameter] [OpensMeasurableSpace Parameter]
    (laws : Parameter → ProbabilityMeasure Space) (lawsContinuous : Continuous laws) :
    Measurable (fun parameter => (laws parameter : Measure Space)) := by
  apply Measure.measurable_of_measurable_coe
  intro target targetMeasurable
  have evaluationMeasurable : ∀ (target : Set Space), MeasurableSet target →
      Measurable (fun parameter => (laws parameter : Measure Space) target) := by
    apply MeasurableSpace.induction_on_inter
      (C := fun target _ => Measurable (fun parameter => (laws parameter : Measure Space) target))
      (s := {target : Set Space | IsClosed target})
      (by
        have measurableBorel : ambientMeasurable = borel Space :=
          BorelSpace.measurable_eq
        exact measurableBorel.trans borel_eq_generateFrom_isClosed)
      isPiSystem_isClosed
    · simpa only [measure_empty] using
        (measurable_const : Measurable (fun _ : Parameter => (0 : ℝ≥0∞)))
    · intro target targetClosed
      change IsClosed target at targetClosed
      apply measurable_of_tendsto_metrizable
        (f := fun index parameter =>
          ∫⁻ location, targetClosed.apprSeq index location ∂(laws parameter))
      · intro index
        exact ((ProbabilityMeasure.continuous_lintegral_boundedContinuousFunction
          (targetClosed.apprSeq index)).comp lawsContinuous).measurable
      · apply tendsto_pi_nhds.mpr
        intro parameter
        exact HasOuterApproxClosed.tendsto_lintegral_apprSeq targetClosed
          (laws parameter : Measure Space)
    · intro target targetMeasurable induction
      have identity : (fun parameter => (laws parameter : Measure Space) targetᶜ) =
          fun parameter => 1 - (laws parameter : Measure Space) target := by
        funext parameter
        rw [measure_compl targetMeasurable (measure_ne_top _ _), measure_univ]
      rw [identity]
      exact measurable_const.sub induction
    · intro targets disjoint measurable induction
      have identity : (fun parameter => (laws parameter : Measure Space) (⋃ index, targets index)) =
          fun parameter => ∑' index, (laws parameter : Measure Space) (targets index) := by
        funext parameter
        exact measure_iUnion disjoint measurable
      rw [identity]
      exact Measurable.ennreal_tsum induction
  exact evaluationMeasurable target targetMeasurable

variable (semigroup : ℝ≥0 → C(Space, ℝ) →L[ℝ] C(Space, ℝ))
  (positive : ∀ time (function : C(Space, ℝ)), (∀ point, 0 ≤ function point) →
    ∀ point, 0 ≤ semigroup time function point)
  (preservesOne : ∀ time, semigroup time 1 = 1)

def semigroupPointProbability (time : ℝ≥0) (point : Space) : ProbabilityMeasure Space :=
  pointProbabilityMeasure (semigroup time) (positive time) (preservesOne time) point

theorem semigroupPointProbability_integral (time : ℝ≥0) (point : Space)
    (function : C(Space, ℝ)) :
    ∫ location, function location ∂(semigroupPointProbability semigroup positive preservesOne time point) =
      semigroup time function point :=
  pointProbabilityMeasure_integral (semigroup time) (positive time) (preservesOne time) point function

theorem semigroupPointProbability_continuous (time : ℝ≥0) :
    Continuous (semigroupPointProbability semigroup positive preservesOne time) :=
  pointProbabilityMeasure_continuous (semigroup time) (positive time) (preservesOne time)

theorem semigroupPointProbability_joint_continuous
    (jointContinuous : Continuous (fun point : C(Space, ℝ) × ℝ≥0 => semigroup point.2 point.1)) :
    Continuous (fun point : ℝ≥0 × Space =>
      semigroupPointProbability semigroup positive preservesOne point.1 point.2) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuousMap_continuous_integral.mpr
  intro function
  simp_rw [semigroupPointProbability_integral]
  have orbitContinuous : Continuous (fun time : ℝ≥0 => semigroup time function) :=
    jointContinuous.comp (continuous_const.prodMk continuous_id)
  exact continuous_eval.comp ((orbitContinuous.comp continuous_fst).prodMk continuous_snd)

def semigroupKernel (time : ℝ≥0) : Kernel Space Space where
  toFun point := (semigroupPointProbability semigroup positive preservesOne time point : Measure Space)
  measurable' := measurable_toMeasure_of_continuous _
    (semigroupPointProbability_continuous semigroup positive preservesOne time)

instance semigroupKernel_isMarkov (time : ℝ≥0) :
    IsMarkovKernel (semigroupKernel semigroup positive preservesOne time) where
  isProbabilityMeasure point :=
    (semigroupPointProbability semigroup positive preservesOne time point).property

theorem semigroupKernel_integral (time : ℝ≥0) (point : Space) (function : C(Space, ℝ)) :
    ∫ location, function location ∂(semigroupKernel semigroup positive preservesOne time point) =
      semigroup time function point :=
  semigroupPointProbability_integral semigroup positive preservesOne time point function

def semigroupTimeSpaceKernel
    (jointContinuous : Continuous (fun point : C(Space, ℝ) × ℝ≥0 => semigroup point.2 point.1)) :
    Kernel (ℝ≥0 × Space) Space where
  toFun point := (semigroupPointProbability semigroup positive preservesOne point.1 point.2 : Measure Space)
  measurable' := measurable_toMeasure_of_continuous _
    (semigroupPointProbability_joint_continuous semigroup positive preservesOne jointContinuous)

instance semigroupTimeSpaceKernel_isMarkov
    (jointContinuous : Continuous (fun point : C(Space, ℝ) × ℝ≥0 => semigroup point.2 point.1)) :
    IsMarkovKernel (semigroupTimeSpaceKernel semigroup positive preservesOne jointContinuous) where
  isProbabilityMeasure point :=
    (semigroupPointProbability semigroup positive preservesOne point.1 point.2).property

theorem semigroupKernel_zero (zeroLaw : semigroup 0 = ContinuousLinearMap.id ℝ C(Space, ℝ))
    (point : Space) :
    semigroupKernel semigroup positive preservesOne 0 point = Measure.dirac point := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  calc
    (∫ location, function location ∂(semigroupKernel semigroup positive preservesOne 0 point)) =
        semigroup 0 function.toContinuousMap point :=
      semigroupKernel_integral semigroup positive preservesOne 0 point function.toContinuousMap
    _ = function point := by rw [zeroLaw]; rfl
    _ = ∫ location, function location ∂(Measure.dirac point) := by rw [integral_dirac]

theorem semigroupPointProbability_zero
    (zeroLaw : semigroup 0 = ContinuousLinearMap.id ℝ C(Space, ℝ)) (point : Space) :
    semigroupPointProbability semigroup positive preservesOne 0 point =
      (⟨Measure.dirac point, inferInstance⟩ : ProbabilityMeasure Space) := by
  apply Subtype.ext
  exact semigroupKernel_zero semigroup positive preservesOne zeroLaw point

theorem semigroupKernel_add
    (additionLaw : ∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime))
    (firstTime secondTime : ℝ≥0) :
    semigroupKernel semigroup positive preservesOne (firstTime + secondTime) =
      semigroupKernel semigroup positive preservesOne secondTime ∘ₖ
        semigroupKernel semigroup positive preservesOne firstTime := by
  apply Kernel.ext
  intro point
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro function
  have compositionIntegral := Kernel.integral_comp
    (κ := semigroupKernel semigroup positive preservesOne firstTime)
    (η := semigroupKernel semigroup positive preservesOne secondTime) (a := point)
    (function.integrable _)
  calc
    (∫ location, function location
        ∂(semigroupKernel semigroup positive preservesOne (firstTime + secondTime) point)) =
        semigroup (firstTime + secondTime) function.toContinuousMap point :=
      semigroupKernel_integral semigroup positive preservesOne _ point function.toContinuousMap
    _ = semigroup firstTime (semigroup secondTime function.toContinuousMap) point := by
      rw [additionLaw]
      rfl
    _ = ∫ location, (semigroup secondTime function.toContinuousMap) location
        ∂(semigroupKernel semigroup positive preservesOne firstTime point) :=
      (semigroupKernel_integral semigroup positive preservesOne firstTime point
        (semigroup secondTime function.toContinuousMap)).symm
    _ = ∫ location, ∫ destination, function destination
        ∂(semigroupKernel semigroup positive preservesOne secondTime location)
        ∂(semigroupKernel semigroup positive preservesOne firstTime point) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun location =>
        (semigroupKernel_integral semigroup positive preservesOne secondTime location
          function.toContinuousMap).symm
    _ = ∫ location, function location
        ∂((semigroupKernel semigroup positive preservesOne secondTime ∘ₖ
          semigroupKernel semigroup positive preservesOne firstTime) point) := compositionIntegral.symm

theorem semigroupPointProbability_add_bind
    (additionLaw : ∀ firstTime secondTime, semigroup (firstTime + secondTime) =
      (semigroup firstTime).comp (semigroup secondTime))
    (firstTime secondTime : ℝ≥0) (point : Space) :
    (semigroupPointProbability semigroup positive preservesOne (firstTime + secondTime) point : Measure Space) =
      (semigroupPointProbability semigroup positive preservesOne firstTime point : Measure Space).bind
        (fun location => (semigroupPointProbability semigroup positive preservesOne secondTime location : Measure Space)) :=
  congrArg (fun kernel : Kernel Space Space => kernel point)
    (semigroupKernel_add semigroup positive preservesOne additionLaw firstTime secondTime)

end
end IGS.Sec31.ContinuousMarkov

#print axioms IGS.Sec31.ContinuousMarkov.measurable_toMeasure_of_continuous
#print axioms IGS.Sec31.ContinuousMarkov.semigroupPointProbability_joint_continuous
#print axioms IGS.Sec31.ContinuousMarkov.semigroupKernel_zero
#print axioms IGS.Sec31.ContinuousMarkov.semigroupKernel_add
#print axioms IGS.Sec31.ContinuousMarkov.semigroupPointProbability_add_bind
