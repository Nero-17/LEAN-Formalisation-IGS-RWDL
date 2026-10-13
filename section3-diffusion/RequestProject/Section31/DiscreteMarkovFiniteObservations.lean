import RequestProject.Section31.DiscreteMarkovSubsampling
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Actual finite-prefix probabilities of the Ionescu--Tulcea path measure,
and their bounded measurable product-observation integrals. The backward
recursion removes the final transition first; no finite-dimensional law or
conditional-expectation identity is assumed. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped ProbabilityTheory BigOperators

noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type*} [MeasurableSpace X]

def finitePrefixProbability (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (count : ℕ) : ProbabilityMeasure (Finset.Iic count → X) :=
  ⟨(pathLaw kernel (initial : Measure X)).map (frestrictLe count),
    Measure.isProbabilityMeasure_map (measurable_frestrictLe count).aemeasurable⟩

def prefixProduct (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (history : Finset.Iic count → X) : ℝ :=
  (∏ index : Fin count, tests index.val
    (history ⟨index.val, Finset.mem_Iic.mpr (Nat.le_of_lt index.isLt)⟩)) *
    terminal (history ⟨count, Finset.mem_Iic.mpr le_rfl⟩)

/-- The genuine backward integration recursion for the given transition
kernel. A prefix of length count has tests at 0,...,count-1 and the terminal
test at count. -/
def backwardPrefix (kernel : Kernel X X) (tests : ℕ → X → ℝ) :
    ℕ → (X → ℝ) → X → ℝ
  | 0, terminal => terminal
  | count + 1, terminal => backwardPrefix kernel tests count
      (fun point => tests count point * ∫ target, terminal target ∂kernel point)

theorem kernel_integral_measurable (kernel : Kernel X X) (function : X → ℝ)
    (measurable : Measurable function) :
    Measurable (fun point => ∫ target, function target ∂kernel point) :=
  measurable.stronglyMeasurable.integral_kernel.measurable

theorem kernel_integral_norm_le (kernel : Kernel X X) [IsMarkovKernel kernel]
    (function : X → ℝ) (bound : ℝ) (bounded : ∀ point, ‖function point‖ ≤ bound)
    (point : X) : ‖∫ target, function target ∂kernel point‖ ≤ bound := by
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := kernel point) (Eventually.of_forall bounded))

theorem prefixProduct_measurable (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal) :
    Measurable (prefixProduct tests count terminal) := by
  apply Measurable.mul
  · apply Finset.measurable_prod
    intro index _
    exact (testsMeasurable index.val).comp (measurable_pi_apply _)
  · exact terminalMeasurable.comp (measurable_pi_apply _)

omit [MeasurableSpace X] in
theorem prefixProduct_norm_le (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (_terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound)
    (history : Finset.Iic count → X) :
    ‖prefixProduct tests count terminal history‖ ≤
      (∏ index : Fin count, bounds index.val) * terminalBound := by
  unfold prefixProduct
  rw [norm_mul, norm_prod]
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      (fun index _ => testsBounded index.val _)
  · exact terminalBounded _
  · exact norm_nonneg _
  · exact Finset.prod_nonneg (fun index _ => boundsNonnegative index.val)

theorem prefixProduct_integrable (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    Integrable (prefixProduct tests count terminal)
      (finitePrefixProbability kernel initial count : Measure _) := by
  exact Integrable.of_bound
    (prefixProduct_measurable tests count terminal testsMeasurable terminalMeasurable).aestronglyMeasurable
    ((∏ index : Fin count, bounds index.val) * terminalBound)
    (Eventually.of_forall (prefixProduct_norm_le tests count terminal bounds terminalBound
      boundsNonnegative terminalBoundNonnegative testsBounded terminalBounded))

omit [MeasurableSpace X] in
theorem prefixProduct_succ_on_path (tests : ℕ → X → ℝ) (count : ℕ)
    (terminal : X → ℝ) (path : ℕ → X) :
    prefixProduct tests (count + 1) terminal (frestrictLe (count + 1) path) =
      prefixProduct tests count (tests count) (frestrictLe count path) * terminal (path (count + 1)) := by
  unfold prefixProduct
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The actual joint endpoint law supplies the backward step. This is a
proved integral identity for the Ionescu--Tulcea law, not a Markov-property
premise. -/
theorem prefixProduct_integral_step (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    (∫ history, prefixProduct tests (count + 1) terminal history
      ∂(finitePrefixProbability kernel initial (count + 1) : Measure _)) =
      ∫ history, prefixProduct tests count
        (fun point => tests count point * ∫ target, terminal target ∂kernel point) history
        ∂(finitePrefixProbability kernel initial count : Measure _) := by
  let endpoint : Kernel (Finset.Iic count → X) X := kernel.comap
    (fun history => history ⟨count, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)
  let jointTest : (Finset.Iic count → X) × X → ℝ :=
    fun pair => prefixProduct tests count (tests count) pair.1 * terminal pair.2
  have jointMeasurable : Measurable jointTest :=
    ((prefixProduct_measurable tests count (tests count) testsMeasurable (testsMeasurable count)).comp
      measurable_fst).mul (terminalMeasurable.comp measurable_snd)
  have jointIntegrable : Integrable jointTest
      ((finitePrefixProbability kernel initial count : Measure _) ⊗ₘ endpoint) := by
    apply Integrable.of_bound jointMeasurable.aestronglyMeasurable
      (((∏ index : Fin count, bounds index.val) * bounds count) * terminalBound)
    apply Eventually.of_forall
    intro pair
    change ‖prefixProduct tests count (tests count) pair.1 * terminal pair.2‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul
    · exact prefixProduct_norm_le tests count (tests count) bounds (bounds count)
        boundsNonnegative (boundsNonnegative count) testsBounded (testsBounded count) pair.1
    · exact terminalBounded pair.2
    · exact norm_nonneg _
    · exact mul_nonneg (Finset.prod_nonneg (fun index _ => boundsNonnegative index.val))
        (boundsNonnegative count)
  have actualJoint :
      (pathLaw kernel (initial : Measure X)).map
        (fun path => (frestrictLe count path, path (count + 1))) =
      (finitePrefixProbability kernel initial count : Measure _) ⊗ₘ endpoint := by
    simpa only [pow_one] using pathLaw_history_endpoint_joint kernel (initial : Measure X) count 1
  have jointIntegral :
      (∫ path, jointTest (frestrictLe count path, path (count + 1))
        ∂pathLaw kernel (initial : Measure X)) =
      ∫ pair, jointTest pair ∂((finitePrefixProbability kernel initial count : Measure _) ⊗ₘ endpoint) := by
    rw [← actualJoint]
    exact (integral_map
      ((measurable_frestrictLe count).prodMk (measurable_pi_apply (count + 1))).aemeasurable
      jointMeasurable.aestronglyMeasurable).symm
  change (∫ history, prefixProduct tests (count + 1) terminal history
    ∂(pathLaw kernel (initial : Measure X)).map (frestrictLe (count + 1))) = _
  rw [integral_map (measurable_frestrictLe (count + 1)).aemeasurable
    (prefixProduct_measurable tests (count + 1) terminal testsMeasurable terminalMeasurable).aestronglyMeasurable]
  simp_rw [prefixProduct_succ_on_path]
  change (∫ path, jointTest (frestrictLe count path, path (count + 1))
    ∂pathLaw kernel (initial : Measure X)) = _
  rw [jointIntegral, Measure.integral_compProd jointIntegrable]
  simp_rw [jointTest, integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro history
  change prefixProduct tests count (tests count) history *
      (∫ target, terminal target ∂kernel (history ⟨count, Finset.mem_Iic.mpr le_rfl⟩)) = _
  unfold prefixProduct
  ring

/-- Every bounded measurable finite-prefix product has the actual backward
kernel-integral representation. -/
theorem finitePrefix_integral_backward (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    (∫ history, prefixProduct tests count terminal history
      ∂(finitePrefixProbability kernel initial count : Measure _)) =
      ∫ point, backwardPrefix kernel tests count terminal point ∂(initial : Measure X) := by
  induction count generalizing terminal terminalBound with
  | zero =>
    change (∫ history, prefixProduct tests 0 terminal history
      ∂(pathLaw kernel (initial : Measure X)).map (frestrictLe 0)) = _
    rw [integral_map (measurable_frestrictLe 0).aemeasurable
      (prefixProduct_measurable tests 0 terminal testsMeasurable terminalMeasurable).aestronglyMeasurable]
    simp only [prefixProduct, Fin.prod_univ_zero, one_mul, backwardPrefix, frestrictLe_apply]
    have zeroIntegral :
        (∫ point, terminal point ∂(pathLaw kernel (initial : Measure X)).map (fun path => path 0)) =
        ∫ path, terminal (path 0) ∂pathLaw kernel (initial : Measure X) :=
      integral_map (measurable_pi_apply 0).aemeasurable terminalMeasurable.aestronglyMeasurable
    rw [pathLaw_coordinate_zero] at zeroIntegral
    exact zeroIntegral.symm
  | succ count induction =>
    rw [prefixProduct_integral_step kernel initial tests count terminal bounds terminalBound
      testsMeasurable terminalMeasurable boundsNonnegative terminalBoundNonnegative testsBounded terminalBounded]
    change (∫ history, prefixProduct tests count
      (fun point => tests count point * ∫ target, terminal target ∂kernel point) history
      ∂(finitePrefixProbability kernel initial count : Measure _)) =
      ∫ point, backwardPrefix kernel tests count
        (fun location => tests count location * ∫ target, terminal target ∂kernel location) point
        ∂(initial : Measure X)
    apply induction (terminalBound := bounds count * terminalBound)
    · exact (testsMeasurable count).mul (kernel_integral_measurable kernel terminal terminalMeasurable)
    · exact mul_nonneg (boundsNonnegative count) terminalBoundNonnegative
    · intro point
      rw [norm_mul]
      exact mul_le_mul (testsBounded count point)
        (kernel_integral_norm_le kernel terminal terminalBound terminalBounded point)
        (norm_nonneg _) (boundsNonnegative count)

theorem pathLaw_prefix_integral_backward (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (tests : ℕ → X → ℝ) (count : ℕ) (terminal : X → ℝ)
    (bounds : ℕ → ℝ) (terminalBound : ℝ)
    (testsMeasurable : ∀ index, Measurable (tests index)) (terminalMeasurable : Measurable terminal)
    (boundsNonnegative : ∀ index, 0 ≤ bounds index) (terminalBoundNonnegative : 0 ≤ terminalBound)
    (testsBounded : ∀ index point, ‖tests index point‖ ≤ bounds index)
    (terminalBounded : ∀ point, ‖terminal point‖ ≤ terminalBound) :
    (∫ path, (∏ index : Fin count, tests index.val (path index.val)) * terminal (path count)
      ∂pathLaw kernel (initial : Measure X)) =
      ∫ point, backwardPrefix kernel tests count terminal point ∂(initial : Measure X) := by
  have representation := finitePrefix_integral_backward kernel initial tests count terminal bounds terminalBound
    testsMeasurable terminalMeasurable boundsNonnegative terminalBoundNonnegative testsBounded terminalBounded
  change (∫ history, prefixProduct tests count terminal history
    ∂(pathLaw kernel (initial : Measure X)).map (frestrictLe count)) = _ at representation
  rw [integral_map (measurable_frestrictLe count).aemeasurable
    (prefixProduct_measurable tests count terminal testsMeasurable terminalMeasurable).aestronglyMeasurable] at representation
  simpa only [prefixProduct, frestrictLe_apply] using representation

end
end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finitePrefixProbability
#print axioms IGS.Sec31.DiscreteMarkov.kernel_integral_measurable
#print axioms IGS.Sec31.DiscreteMarkov.prefixProduct_integrable
#print axioms IGS.Sec31.DiscreteMarkov.prefixProduct_integral_step
#print axioms IGS.Sec31.DiscreteMarkov.finitePrefix_integral_backward
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_prefix_integral_backward
