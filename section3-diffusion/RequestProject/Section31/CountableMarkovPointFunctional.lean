import RequestProject.Section31.EIGSSemigroupSupBounds
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.LinearAlgebra.Countable
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Topology.Sequences

/-! A fixed-time common AE set for countably many continuous tests and its
bounded point functionals. This does not assert a measurable kernel, a
continuous output version, or simultaneous-time Chapman--Kolmogorov laws. -/

namespace IGS.Sec31.CountableMarkov
open MeasureTheory Filter Topology

set_option maxHeartbeats 2000000

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [CompactSpace X]
    [BorelSpace X]

section CountableTests
variable [SecondCountableTopology X] [T2Space X]

noncomputable def testGenerators : Option ℕ → C(X, ℝ)
  | none => 1
  | some index => TopologicalSpace.denseSeq C(X, ℝ) index

noncomputable def rationalTests : Submodule ℚ C(X, ℝ) :=
  Submodule.span ℚ (Set.range (testGenerators (X := X)))

instance rationalTests_countable : Countable (rationalTests (X := X)) := by
  unfold rationalTests
  infer_instance

theorem one_mem_rationalTests : (1 : C(X, ℝ)) ∈ rationalTests (X := X) := by
  exact Submodule.subset_span ⟨none, rfl⟩

theorem rationalTests_dense : Dense (rationalTests (X := X) : Set C(X, ℝ)) := by
  apply (TopologicalSpace.denseRange_denseSeq C(X, ℝ)).mono
  rintro values ⟨index, rfl⟩
  exact Submodule.subset_span ⟨some index, rfl⟩

end CountableTests

variable (measure : Measure X) [IsFiniteMeasure measure]
    (operator : C(X, ℝ) →L[ℝ] Lp ℝ 2 measure)
    (tests : Submodule ℚ C(X, ℝ))

/-- All point evaluations required to make one bounded rational-linear
functional are compatible at this point. -/
structure GoodPoint (point : X) : Prop where
  add : ∀ first second : tests,
    operator ((first + second : tests) : C(X, ℝ)) point =
      operator (first : C(X, ℝ)) point + operator (second : C(X, ℝ)) point
  smul : ∀ (scalar : ℚ) (values : tests),
    operator ((scalar • values : tests) : C(X, ℝ)) point =
      scalar • operator (values : C(X, ℝ)) point
  bound : ∀ values : tests,
    |operator (values : C(X, ℝ)) point| ≤ ‖(values : C(X, ℝ))‖
  positive : ∀ values : tests,
    (∀ location, 0 ≤ (values : C(X, ℝ)) location) →
      0 ≤ operator (values : C(X, ℝ)) point
  one : operator 1 point = 1

theorem ae_goodPoint [Countable tests]
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (positive : ∀ values : C(X, ℝ),
      (∀ location, 0 ≤ values location) → ∀ᵐ point ∂measure, 0 ≤ operator values point)
    (one : (operator 1 : X → ℝ) =ᵐ[measure] fun _ => 1) :
    ∀ᵐ point ∂measure, GoodPoint measure operator tests point := by
  have additions : ∀ first second : tests, ∀ᵐ point ∂measure,
      operator ((first + second : tests) : C(X, ℝ)) point =
        operator (first : C(X, ℝ)) point + operator (second : C(X, ℝ)) point := by
    intro first second
    simpa only [Submodule.coe_add, map_add, Pi.add_apply] using
      Lp.coeFn_add (operator (first : C(X, ℝ))) (operator (second : C(X, ℝ)))
  have scalars : ∀ (scalar : ℚ) (values : tests), ∀ᵐ point ∂measure,
      operator ((scalar • values : tests) : C(X, ℝ)) point =
        scalar • operator (values : C(X, ℝ)) point := by
    intro scalar values
    have identity : operator (scalar • (values : C(X, ℝ))) =
        scalar • operator (values : C(X, ℝ)) :=
      (operator.restrictScalars ℚ).map_smul scalar (values : C(X, ℝ))
    simpa only [Submodule.coe_smul, identity, Pi.smul_apply] using
      Lp.coeFn_smul scalar (operator (values : C(X, ℝ)))
  have positiveTests : ∀ values : tests, ∀ᵐ point ∂measure,
      (∀ location, 0 ≤ (values : C(X, ℝ)) location) →
        0 ≤ operator (values : C(X, ℝ)) point := by
    intro values
    by_cases inputPositive : ∀ location, 0 ≤ (values : C(X, ℝ)) location
    · exact (positive values inputPositive).mono fun _ outputPositive _ => outputPositive
    · exact Filter.Eventually.of_forall fun _ impossible => (inputPositive impossible).elim
  filter_upwards [ae_all_iff.mpr (fun first => ae_all_iff.mpr (additions first)),
    ae_all_iff.mpr (fun scalar => ae_all_iff.mpr (scalars scalar)),
    ae_all_iff.mpr (fun values : tests => supBound values),
    ae_all_iff.mpr positiveTests, one]
    with point addition scalar bound outputPositive constant
  exact ⟨addition, scalar, bound, outputPositive, constant⟩

noncomputable def pointRationalFunctional (point : X)
    (good : GoodPoint measure operator tests point) : tests →ₗ[ℚ] ℝ where
  toFun values := operator (values : C(X, ℝ)) point
  map_add' := good.add
  map_smul' := good.smul

theorem pointRationalFunctional_bound (point : X)
    (good : GoodPoint measure operator tests point) (values : tests) :
    ‖pointRationalFunctional measure operator tests point good values‖ ≤
      1 * ‖(values : C(X, ℝ))‖ := by
  simpa only [pointRationalFunctional, Real.norm_eq_abs, one_mul] using good.bound values

/-- The actual continuous extension of the good point's rational functional. -/
noncomputable def pointRealFunctional (point : X)
    (good : GoodPoint measure operator tests point) : C(X, ℝ) →L[ℝ] ℝ :=
  let rationalExtension :=
    (pointRationalFunctional measure operator tests point good).extendOfNorm tests.subtype
  rationalExtension.toLinearMap.toAddMonoidHom.toRealLinearMap rationalExtension.continuous

theorem pointRealFunctional_agrees (dense : Dense (tests : Set C(X, ℝ)))
    (point : X) (good : GoodPoint measure operator tests point) (values : tests) :
    pointRealFunctional measure operator tests point good values =
      operator (values : C(X, ℝ)) point := by
  exact LinearMap.extendOfNorm_eq
    (f := pointRationalFunctional measure operator tests point good) (e := tests.subtype)
    (by simpa using dense)
    ⟨1, pointRationalFunctional_bound measure operator tests point good⟩ values

theorem pointRealFunctional_bound (dense : Dense (tests : Set C(X, ℝ)))
    (point : X) (good : GoodPoint measure operator tests point) (values : C(X, ℝ)) :
    ‖pointRealFunctional measure operator tests point good values‖ ≤ ‖values‖ := by
  simpa only [one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := pointRationalFunctional measure operator tests point good) (e := tests.subtype)
    (by simpa using dense) 1 (pointRationalFunctional_bound measure operator tests point good) values

theorem pointRealFunctional_one (dense : Dense (tests : Set C(X, ℝ)))
    (oneMem : (1 : C(X, ℝ)) ∈ tests) (point : X)
    (good : GoodPoint measure operator tests point) :
    pointRealFunctional measure operator tests point good 1 = 1 := by
  rw [show (1 : C(X, ℝ)) = (⟨1, oneMem⟩ : tests).val from rfl,
    pointRealFunctional_agrees measure operator tests dense point good]
  exact good.one

theorem pointRealFunctional_positive (dense : Dense (tests : Set C(X, ℝ)))
    (oneMem : (1 : C(X, ℝ)) ∈ tests) (point : X)
    (good : GoodPoint measure operator tests point) (values : C(X, ℝ))
    (valuesNonnegative : ∀ location, 0 ≤ values location) :
    0 ≤ pointRealFunctional measure operator tests point good values := by
  have shiftedNorm : ‖‖values‖ • (1 : C(X, ℝ)) - values‖ ≤ ‖values‖ := by
    apply (ContinuousMap.norm_le _ (norm_nonneg values)).mpr
    intro location
    simp only [ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply,
      smul_eq_mul, mul_one, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith [values.apply_le_norm location, valuesNonnegative location, norm_nonneg values]
  have bound := pointRealFunctional_bound measure operator tests dense point good
    (‖values‖ • (1 : C(X, ℝ)) - values)
  rw [map_sub, map_smul, pointRealFunctional_one measure operator tests dense oneMem point good,
    smul_eq_mul, mul_one, Real.norm_eq_abs] at bound
  have signedBound := (le_abs_self
    (‖values‖ - pointRealFunctional measure operator tests point good values)).trans
      (bound.trans shiftedNorm)
  linarith

/-- For each continuous input separately, the point functional is an AE
representative of the actual L2 output. The AE set may depend on the input. -/
theorem ae_pointRealFunctional_agrees (dense : Dense (tests : Set C(X, ℝ)))
    (supBound : ∀ values : C(X, ℝ),
      ∀ᵐ point ∂measure, |operator values point| ≤ ‖values‖)
    (values : C(X, ℝ)) :
    ∀ᵐ point ∂measure, ∀ good : GoodPoint measure operator tests point,
      pointRealFunctional measure operator tests point good values = operator values point := by
  obtain ⟨approximation, approximationMem, approximationLimit⟩ :=
    mem_closure_iff_seq_limit.mp (dense values)
  have differenceBounds : ∀ index : ℕ, ∀ᵐ point ∂measure,
      |operator (approximation index) point - operator values point| ≤
        ‖approximation index - values‖ := by
    intro index
    have bound := supBound (approximation index - values)
    rw [map_sub] at bound
    filter_upwards [bound, Lp.coeFn_sub (operator (approximation index)) (operator values)]
      with point difference evaluation
    simpa only [evaluation, Pi.sub_apply] using difference
  filter_upwards [ae_all_iff.mpr differenceBounds] with point differences
  intro good
  have scalarLimit : Filter.Tendsto (fun index => operator (approximation index) point)
      Filter.atTop (nhds (operator values point)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _)
      (fun index => by simpa only [Real.norm_eq_abs] using differences index)
    exact tendsto_iff_norm_sub_tendsto_zero.mp approximationLimit
  have functionalLimit :=
    ((pointRealFunctional measure operator tests point good).continuous.tendsto values).comp approximationLimit
  change Filter.Tendsto
    (fun index => pointRealFunctional measure operator tests point good (approximation index))
    Filter.atTop (nhds (pointRealFunctional measure operator tests point good values)) at functionalLimit
  have agreement :
      (fun index => pointRealFunctional measure operator tests point good (approximation index)) =
        (fun index => operator (approximation index) point) := by
    funext index
    exact pointRealFunctional_agrees measure operator tests dense point good
      ⟨approximation index, approximationMem index⟩
  rw [agreement] at functionalLimit
  exact tendsto_nhds_unique functionalLimit scalarLimit

/-- This operator is the actual composition of the L2 operator and the
continuous-function inclusion. -/
noncomputable def continuousOperator (semigroup : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure) :
    C(X, ℝ) →L[ℝ] Lp ℝ 2 measure :=
  semigroup.comp (ContinuousMap.toLp 2 measure ℝ)

theorem ae_goodPoint_of_semigroup [Countable tests]
    (semigroup : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure)
    (preservesBounds : ∀ forcing : Lp ℝ 2 measure, ∀ lower upper : ℝ,
      (∀ᵐ point ∂measure, lower ≤ forcing point ∧ forcing point ≤ upper) →
      ∀ᵐ point ∂measure, lower ≤ semigroup forcing point ∧ semigroup forcing point ≤ upper)
    (positive : ∀ forcing : Lp ℝ 2 measure,
      (∀ᵐ point ∂measure, 0 ≤ forcing point) → ∀ᵐ point ∂measure, 0 ≤ semigroup forcing point)
    (oneFixed : semigroup (ContinuousMap.toLp 2 measure ℝ (1 : C(X, ℝ))) =
      ContinuousMap.toLp 2 measure ℝ (1 : C(X, ℝ))) :
    ∀ᵐ point ∂measure, GoodPoint measure (continuousOperator measure semigroup) tests point := by
  apply ae_goodPoint measure (continuousOperator measure semigroup) tests
  · exact LpMarkovBounds.continuous_input_sup_bound measure semigroup preservesBounds
  · intro values valuesNonnegative
    apply positive
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure values]
      with point evaluation
    change 0 ≤ ContinuousMap.toLp 2 measure ℝ values point
    rw [evaluation]
    exact valuesNonnegative point
  · change (semigroup (ContinuousMap.toLp 2 measure ℝ (1 : C(X, ℝ))) : X → ℝ)
      =ᵐ[measure] fun _ => 1
    rw [oneFixed]
    simpa only [ContinuousMap.one_apply] using
      ContinuousMap.coeFn_toLp (𝕜 := ℝ) (p := 2) measure (1 : C(X, ℝ))

end IGS.Sec31.CountableMarkov

#print axioms IGS.Sec31.CountableMarkov.rationalTests_dense
#print axioms IGS.Sec31.CountableMarkov.ae_goodPoint
#print axioms IGS.Sec31.CountableMarkov.pointRealFunctional_agrees
#print axioms IGS.Sec31.CountableMarkov.pointRealFunctional_bound
#print axioms IGS.Sec31.CountableMarkov.pointRealFunctional_one
#print axioms IGS.Sec31.CountableMarkov.pointRealFunctional_positive
#print axioms IGS.Sec31.CountableMarkov.ae_pointRealFunctional_agrees
#print axioms IGS.Sec31.CountableMarkov.ae_goodPoint_of_semigroup
