import RequestProject.Section31.FullDiscreteMarkovSubsampling
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Finite future blocks after bounded discrete stopping times under the actual
Ionescu--Tulcea law. The stopping property is expressed by finite-history
level events. No strong Markov identity is an assumption. -/

namespace IGS.Sec31.DiscreteMarkov

open MeasureTheory ProbabilityTheory Preorder Filter
open scoped BigOperators ProbabilityTheory Classical

noncomputable section
set_option maxHeartbeats 4000000

variable {X : Type} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

def futurePrefix (start count : ℕ) (path : ℕ → X) : Finset.Iic count → X :=
  fun index => path (start + index.val)

theorem futurePrefix_measurable (start count : ℕ) :
    Measurable (futurePrefix (X := X) start count) := by
  apply measurable_pi_lambda
  intro index
  exact measurable_pi_apply _

def futureBlockKernel (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) : Kernel (Finset.Iic start → X) (Finset.Iic count → X) :=
  (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
    (futurePrefix start count)

instance futureBlockKernel_isMarkov (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) : IsMarkovKernel (futureBlockKernel kernel start count) := by
  unfold futureBlockKernel
  exact Kernel.IsMarkovKernel.map _ (futurePrefix_measurable start count)

theorem traj_history_future_block_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) (initialHistory : Finset.Iic 0 → X) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
        (fun path => (frestrictLe start path, futurePrefix start count path)) =
      Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start initialHistory ⊗ₘ
        futureBlockKernel kernel start count := by
  have joint := Kernel.partialTraj_compProd_traj (κ := historyStep kernel)
    (X := fun _ : ℕ => X) (Nat.zero_le start) initialHistory
  calc
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
        (fun path => (frestrictLe start path, futurePrefix start count path)) =
        ((Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0 initialHistory).map
          (fun path => (frestrictLe start path, path))).map
          (Prod.map id (futurePrefix start count)) := by
      rw [Measure.map_map (f := fun path : ℕ → X => (frestrictLe start path, path))
        (g := Prod.map id (futurePrefix start count))
        (measurable_id.prodMap (futurePrefix_measurable start count)) (by fun_prop)]
      rfl
    _ = (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start initialHistory ⊗ₘ
        Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start).map
          (Prod.map id (futurePrefix start count)) := by rw [← joint]
    _ = _ := by
      unfold futureBlockKernel
      rw [Measure.compProd_map (futurePrefix_measurable start count)]

theorem traj_history_future_block_joint_kernel (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) 0).map
        (fun path => (frestrictLe start path, futurePrefix start count path)) =
      (Kernel.id ×ₖ futureBlockKernel kernel start count) ∘ₖ
        Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel) 0 start := by
  apply Kernel.ext
  intro initialHistory
  rw [Kernel.map_apply _ ((measurable_frestrictLe start).prodMk
      (futurePrefix_measurable start count)), Kernel.comp_apply,
    ← Measure.compProd_eq_comp_prod]
  exact traj_history_future_block_joint kernel start count initialHistory

theorem pathLaw_history_future_block_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : Measure X) [SFinite initial] (start count : ℕ) :
    (pathLaw kernel initial).map
        (fun path => (frestrictLe start path, futurePrefix start count path)) =
      (pathLaw kernel initial).map (frestrictLe start) ⊗ₘ
        futureBlockKernel kernel start count := by
  unfold pathLaw
  rw [Measure.map_comp _ _ ((measurable_frestrictLe start).prodMk
      (futurePrefix_measurable start count)), traj_history_future_block_joint_kernel,
    ← Measure.comp_assoc, ← Measure.compProd_eq_comp_prod,
    Measure.map_comp _ _ (measurable_frestrictLe start), Kernel.traj_map_frestrictLe]

theorem pathLaw_history_future_block_integral (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) (start count : ℕ)
    (function : (Finset.Iic start → X) × (Finset.Iic count → X) → ℝ) :
    (∫ path, function (frestrictLe start path, futurePrefix start count path)
      ∂pathLaw kernel (initial : Measure X)) =
      ∫ path, (∫ block, function (frestrictLe start path, block)
        ∂futureBlockKernel kernel start count (frestrictLe start path))
        ∂pathLaw kernel (initial : Measure X) := by
  have integrable : Integrable function
      ((pathLaw kernel (initial : Measure X)).map (frestrictLe start) ⊗ₘ
        futureBlockKernel kernel start count) := Integrable.of_finite
  have joint := pathLaw_history_future_block_joint kernel (initial : Measure X) start count
  calc
    (∫ path, function (frestrictLe start path, futurePrefix start count path)
        ∂pathLaw kernel (initial : Measure X)) =
        ∫ pair, function pair
          ∂((pathLaw kernel (initial : Measure X)).map (frestrictLe start) ⊗ₘ
            futureBlockKernel kernel start count) := by
      rw [← joint]
      exact (integral_map ((measurable_frestrictLe start).prodMk
        (futurePrefix_measurable start count)).aemeasurable
        (measurable_of_countable function).aestronglyMeasurable).symm
    _ = _ := by
      rw [Measure.integral_compProd integrable,
        integral_map (measurable_frestrictLe start).aemeasurable
          (measurable_of_countable _).aestronglyMeasurable]

def futureHistory (start count : ℕ) (history : Finset.Iic (start + count) → X) :
    Finset.Iic count → X :=
  fun index => history ⟨start + index.val,
    Finset.mem_Iic.mpr (Nat.add_le_add_left (Finset.mem_Iic.mp index.property) start)⟩

theorem futureHistory_measurable (start count : ℕ) :
    Measurable (futureHistory (X := X) start count) := by
  exact measurable_of_countable _

theorem traj_future_prefix_next_joint (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) (history : Finset.Iic start → X) :
    (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start history).map
        (fun path => (futurePrefix start count path, path (start + count + 1))) =
      futureBlockKernel kernel start count history ⊗ₘ historyStep kernel count := by
  have fullJoint :
      (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start history).map
          (fun path => (frestrictLe (start + count) path, path (start + count + 1))) =
        Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel)
          start (start + count) history ⊗ₘ historyStep kernel (start + count) := by
    exact (Kernel.partialTraj_compProd_eq_map_traj (κ := historyStep kernel)
      (X := fun _ : ℕ => X) (Nat.le_add_right start count) (x₀ := history)).symm
  have conditional : historyStep kernel (start + count) =
      (historyStep kernel count).comap (futureHistory start count)
        (futureHistory_measurable start count) := by
    apply Kernel.ext
    intro longerHistory
    rfl
  have prefixMarginal :
      (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel)
        start (start + count) history).map (futureHistory start count) =
        futureBlockKernel kernel start count history := by
    rw [← Kernel.traj_map_frestrictLe_apply, Measure.map_map
      (futureHistory_measurable start count) (measurable_frestrictLe (start + count))]
    change (Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start history).map
      (futurePrefix start count) = _
    exact (Kernel.map_apply _ (futurePrefix_measurable start count) history).symm
  calc
    _ = ((Kernel.traj (X := fun _ : ℕ => X) (historyStep kernel) start history).map
        (fun path => (frestrictLe (start + count) path, path (start + count + 1)))).map
        (Prod.map (futureHistory start count) id) := by
      rw [Measure.map_map ((futureHistory_measurable start count).prodMap measurable_id)
        ((measurable_frestrictLe (start + count)).prodMk (measurable_pi_apply _))]
      rfl
    _ = (Kernel.partialTraj (X := fun _ : ℕ => X) (historyStep kernel)
        start (start + count) history ⊗ₘ historyStep kernel (start + count)).map
        (Prod.map (futureHistory start count) id) := by rw [fullJoint]
    _ = _ := by
      rw [conditional, compProd_map_left_comap, prefixMarginal]

theorem futureBlockKernel_succ (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) (history : Finset.Iic start → X) :
    futureBlockKernel kernel start (count + 1) history =
      (futureBlockKernel kernel start count history ⊗ₘ historyStep kernel count).map
        (appendHistory count) := by
  have appendIdentity : appendHistory (X := X) count ∘
      (fun path => (futurePrefix start count path, path (start + count + 1))) =
      futurePrefix start (count + 1) := by
    funext path index
    by_cases before : index.val ≤ count
    · simp only [Function.comp_apply, appendHistory, dif_pos before, futurePrefix]
    · have last : index.val = count + 1 :=
        Nat.le_antisymm (Finset.mem_Iic.mp index.property)
          (Nat.succ_le_of_lt (Nat.lt_of_not_ge before))
      simp [appendHistory, futurePrefix, last, Nat.add_assoc]
  rw [← traj_future_prefix_next_joint, Measure.map_map (appendHistory_measurable count)
    ((futurePrefix_measurable start count).prodMk (measurable_pi_apply _)), appendIdentity]
  exact Kernel.map_apply _ (futurePrefix_measurable start (count + 1)) history

/-- The entire future block depends on the past only through the present state.
This is proved from the actual homogeneous IFT recurrence. -/
theorem futureBlockKernel_eq_dirac_prefix (kernel : Kernel X X) [IsMarkovKernel kernel]
    (start count : ℕ) (history : Finset.Iic start → X) :
    futureBlockKernel kernel start count history =
      (pathLaw kernel (Measure.dirac (history ⟨start, Finset.mem_Iic.mpr le_rfl⟩))).map
        (frestrictLe count) := by
  have homogeneous : ∀ count, futureBlockKernel kernel start count history =
      futureBlockKernel kernel 0 count
        (fun _ => history ⟨start, Finset.mem_Iic.mpr le_rfl⟩) := by
    intro count
    induction count with
    | zero =>
      have coordinateFactor (index : ℕ) : futurePrefix (X := X) index 0 =
          (fun point => fun _ : Finset.Iic 0 => point) ∘ (fun path : ℕ → X => path index) := by
        funext path entry
        have entryZero : entry.val = 0 := Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp entry.property)
        simp only [futurePrefix, Function.comp_apply, entryZero, Nat.add_zero]
      have coordinate (index : ℕ) (initialHistory : Finset.Iic index → X) :
          futureBlockKernel kernel index 0 initialHistory =
            Measure.dirac (fun _ : Finset.Iic 0 =>
              initialHistory ⟨index, Finset.mem_Iic.mpr le_rfl⟩) := by
        unfold futureBlockKernel
        rw [coordinateFactor, Kernel.map_comp_right _ (measurable_pi_apply _) (by fun_prop),
          traj_coordinate_at_start, Kernel.map_apply _ (by fun_prop),
          Kernel.deterministic_apply, Measure.map_dirac (by fun_prop)]
      rw [coordinate, coordinate]
    | succ count inductionHypothesis =>
      rw [futureBlockKernel_succ, futureBlockKernel_succ, inductionHypothesis]
  rw [homogeneous, pathLaw_dirac_eq_traj]
  rw [futureBlockKernel, Kernel.map_apply _ (futurePrefix_measurable 0 count)]
  have samePrefix : futurePrefix (X := X) 0 count = frestrictLe count := by
    funext path index
    simp only [futurePrefix, frestrictLe_apply, Nat.zero_add]
  rw [samePrefix]

theorem finite_observable_integrable {Y : Type} [Fintype Y]
    [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (measure : Measure (ℕ → X)) [IsFiniteMeasure measure]
    (projection : (ℕ → X) → Y) (measurable : Measurable projection) (function : Y → ℝ) :
    Integrable (fun path => function (projection path)) measure := by
  have integrable : Integrable function (measure.map projection) := Integrable.of_finite
  exact integrable.comp_measurable measurable

/-- A bounded stopping time, with its level events represented in the actual
finite coordinate histories. This is a stopping-property definition, not a
conditional distribution assumption. -/
structure BoundedHistoryStop (bound : ℕ) where
  time : (ℕ → X) → Fin (bound + 1)
  historyEvent : (index : Fin (bound + 1)) → Set (Finset.Iic index.val → X)
  level_iff : ∀ index path,
    time path = index ↔ frestrictLe index.val path ∈ historyEvent index

theorem BoundedHistoryStop.level_measurable {bound : ℕ}
    (stop : BoundedHistoryStop (X := X) bound) (index : Fin (bound + 1)) :
    MeasurableSet {path | stop.time path = index} := by
  have equality : {path | stop.time path = index} =
      (frestrictLe index.val) ⁻¹' stop.historyEvent index := by
    ext path
    exact stop.level_iff index path
  rw [equality]
  exact (Set.to_countable _).measurableSet.preimage (measurable_frestrictLe index.val)

theorem BoundedHistoryStop.indicator_sum {bound : ℕ}
    (stop : BoundedHistoryStop (X := X) bound)
    (function : (index : Fin (bound + 1)) → (Finset.Iic index.val → X) → ℝ)
    (path : ℕ → X) :
    (∑ index, (stop.historyEvent index).indicator (function index)
      (frestrictLe index.val path)) =
      function (stop.time path) (frestrictLe (stop.time path).val path) := by
  classical
  rw [Finset.sum_eq_single (stop.time path)]
  · exact Set.indicator_of_mem ((stop.level_iff (stop.time path) path).mp rfl) _
  · intro index _ different
    exact Set.indicator_of_notMem
      (fun belongs => different ((stop.level_iff index path).mpr belongs).symm) _
  · simp

theorem boundedStopping_future_block_integral (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) {bound : ℕ} (stop : BoundedHistoryStop (X := X) bound)
    (count : ℕ) (past : (index : Fin (bound + 1)) → (Finset.Iic index.val → X) → ℝ)
    (future : Fin (bound + 1) → (Finset.Iic count → X) → ℝ) :
    (∫ path, past (stop.time path) (frestrictLe (stop.time path).val path) *
      future (stop.time path) (futurePrefix (stop.time path).val count path)
      ∂pathLaw kernel (initial : Measure X)) =
      ∑ index, ∫ path, (stop.historyEvent index).indicator
        (fun history => past index history *
          ∫ block, future index block ∂futureBlockKernel kernel index.val count history)
        (frestrictLe index.val path) ∂pathLaw kernel (initial : Measure X) := by
  have split (path : ℕ → X) :
      past (stop.time path) (frestrictLe (stop.time path).val path) *
        future (stop.time path) (futurePrefix (stop.time path).val count path) =
      ∑ index, (stop.historyEvent index).indicator
        (fun history => past index history * future index (futurePrefix index.val count path))
        (frestrictLe index.val path) := by
    classical
    rw [Finset.sum_eq_single (stop.time path)]
    · rw [Set.indicator_of_mem ((stop.level_iff (stop.time path) path).mp rfl)]
    · intro index _ different
      exact Set.indicator_of_notMem
        (fun belongs => different ((stop.level_iff index path).mpr belongs).symm) _
    · simp
  have summandIntegrable (index : Fin (bound + 1)) : Integrable
      (fun path => (stop.historyEvent index).indicator
        (fun history => past index history * future index (futurePrefix index.val count path))
        (frestrictLe index.val path)) (pathLaw kernel (initial : Measure X)) := by
    exact finite_observable_integrable _
      (fun path => (frestrictLe index.val path, futurePrefix index.val count path))
      ((measurable_frestrictLe index.val).prodMk (futurePrefix_measurable index.val count))
      (fun pair => (stop.historyEvent index).indicator
        (fun history => past index history * future index pair.2) pair.1)
  calc
    _ = ∫ path, ∑ index, (stop.historyEvent index).indicator
        (fun history => past index history * future index (futurePrefix index.val count path))
        (frestrictLe index.val path) ∂pathLaw kernel (initial : Measure X) := by
      exact integral_congr_ae (Eventually.of_forall split)
    _ = ∑ index, ∫ path, (stop.historyEvent index).indicator
        (fun history => past index history * future index (futurePrefix index.val count path))
        (frestrictLe index.val path) ∂pathLaw kernel (initial : Measure X) := by
      exact integral_finset_sum _ (fun index _ => summandIntegrable index)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [pathLaw_history_future_block_integral kernel initial index.val count
        (fun pair => (stop.historyEvent index).indicator
          (fun history => past index history * future index pair.2) pair.1)]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro path
      by_cases belongs : frestrictLe index.val path ∈ stop.historyEvent index
      · simp only [Set.indicator_of_mem belongs]
        rw [integral_const_mul]
      · simp only [Set.indicator_of_notMem belongs, integral_zero]

theorem boundedStopping_dirac_future_block_integral (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) {bound : ℕ} (stop : BoundedHistoryStop (X := X) bound)
    (count : ℕ) (past : (index : Fin (bound + 1)) → (Finset.Iic index.val → X) → ℝ)
    (future : Fin (bound + 1) → (Finset.Iic count → X) → ℝ) :
    (∫ path, past (stop.time path) (frestrictLe (stop.time path).val path) *
      future (stop.time path) (futurePrefix (stop.time path).val count path)
      ∂pathLaw kernel (initial : Measure X)) =
      ∑ index, ∫ path, (stop.historyEvent index).indicator
        (fun history => past index history *
          ∫ continuation, future index (frestrictLe count continuation)
            ∂pathLaw kernel (Measure.dirac (history ⟨index.val, Finset.mem_Iic.mpr le_rfl⟩)))
        (frestrictLe index.val path) ∂pathLaw kernel (initial : Measure X) := by
  rw [boundedStopping_future_block_integral]
  apply Finset.sum_congr rfl
  intro index _
  apply integral_congr_ae
  apply Eventually.of_forall
  intro path
  dsimp only
  by_cases belongs : frestrictLe index.val path ∈ stop.historyEvent index
  · rw [Set.indicator_of_mem belongs, Set.indicator_of_mem belongs,
      futureBlockKernel_eq_dirac_prefix,
      integral_map (measurable_frestrictLe count).aemeasurable
        (measurable_of_countable (future index)).aestronglyMeasurable]
  · rw [Set.indicator_of_notMem belongs, Set.indicator_of_notMem belongs]

/-- Conditional upper bounds for an entire future block may be multiplied by
any nonnegative stopped-history weight. This is the form used for Laplace
iteration over repeated coarse-skeleton stopping times. -/
theorem boundedStopping_weighted_future_le (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) {bound : ℕ} (stop : BoundedHistoryStop (X := X) bound)
    (count : ℕ) (past : (index : Fin (bound + 1)) → (Finset.Iic index.val → X) → ℝ)
    (future : Fin (bound + 1) → (Finset.Iic count → X) → ℝ) (upper : ℝ)
    (pastNonnegative : ∀ index history, history ∈ stop.historyEvent index → 0 ≤ past index history)
    (conditionalUpper : ∀ index history, history ∈ stop.historyEvent index →
      (∫ continuation, future index (frestrictLe count continuation)
        ∂pathLaw kernel (Measure.dirac (history ⟨index.val, Finset.mem_Iic.mpr le_rfl⟩))) ≤ upper) :
    (∫ path, past (stop.time path) (frestrictLe (stop.time path).val path) *
      future (stop.time path) (futurePrefix (stop.time path).val count path)
      ∂pathLaw kernel (initial : Measure X)) ≤
      upper * ∫ path, past (stop.time path) (frestrictLe (stop.time path).val path)
        ∂pathLaw kernel (initial : Measure X) := by
  have sumPast :
      (∑ index, ∫ path, (stop.historyEvent index).indicator (past index)
        (frestrictLe index.val path) ∂pathLaw kernel (initial : Measure X)) =
      ∫ path, past (stop.time path) (frestrictLe (stop.time path).val path)
        ∂pathLaw kernel (initial : Measure X) := by
    rw [← integral_finset_sum _ (fun index _ => finite_observable_integrable _
      (frestrictLe index.val) (measurable_frestrictLe index.val)
      ((stop.historyEvent index).indicator (past index)))]
    exact integral_congr_ae (Eventually.of_forall (stop.indicator_sum past))
  rw [boundedStopping_dirac_future_block_integral, ← sumPast, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  rw [← integral_const_mul]
  apply integral_mono
  · exact finite_observable_integrable (X := X) (Y := Finset.Iic index.val → X)
      (pathLaw kernel (initial : Measure X))
      (frestrictLe (π := fun _ : ℕ => X) index.val)
      (measurable_frestrictLe index.val)
      ((stop.historyEvent index).indicator (fun history => past index history *
        ∫ continuation, future index (frestrictLe count continuation)
          ∂pathLaw kernel (Measure.dirac (history ⟨index.val, Finset.mem_Iic.mpr le_rfl⟩))))
  · exact finite_observable_integrable (X := X) (Y := Finset.Iic index.val → X)
      (pathLaw kernel (initial : Measure X))
      (frestrictLe (π := fun _ : ℕ => X) index.val)
      (measurable_frestrictLe index.val)
      (fun history => upper * (stop.historyEvent index).indicator (past index) history)
  · intro path
    by_cases belongs : frestrictLe index.val path ∈ stop.historyEvent index
    · simp only [Set.indicator_of_mem belongs]
      exact (mul_le_mul_of_nonneg_left (conditionalUpper index _ belongs)
        (pastNonnegative index _ belongs)).trans_eq (mul_comm _ _)
    · simp only [Set.indicator_of_notMem belongs, mul_zero]
      exact le_rfl

/-- A lower bound for a whole future-block event, valid after an actual bounded
stopping time and against every nonnegative stopped-history weight. -/
theorem boundedStopping_weighted_future_ge (kernel : Kernel X X) [IsMarkovKernel kernel]
    (initial : ProbabilityMeasure X) {bound : ℕ} (stop : BoundedHistoryStop (X := X) bound)
    (count : ℕ) (past : (index : Fin (bound + 1)) → (Finset.Iic index.val → X) → ℝ)
    (future : Fin (bound + 1) → (Finset.Iic count → X) → ℝ) (lower : ℝ)
    (pastNonnegative : ∀ index history, history ∈ stop.historyEvent index → 0 ≤ past index history)
    (conditionalLower : ∀ index history, history ∈ stop.historyEvent index →
      lower ≤ (∫ continuation, future index (frestrictLe count continuation)
        ∂pathLaw kernel (Measure.dirac (history ⟨index.val, Finset.mem_Iic.mpr le_rfl⟩)))) :
    lower * (∫ path, past (stop.time path) (frestrictLe (stop.time path).val path)
      ∂pathLaw kernel (initial : Measure X)) ≤
      ∫ path, past (stop.time path) (frestrictLe (stop.time path).val path) *
        future (stop.time path) (futurePrefix (stop.time path).val count path)
        ∂pathLaw kernel (initial : Measure X) := by
  have upper := boundedStopping_weighted_future_le kernel initial stop count past
    (fun index block => -future index block) (-lower) pastNonnegative (by
      intro index history belongs
      rw [integral_neg]
      exact neg_le_neg (conditionalLower index history belongs))
  simp only [mul_neg, integral_neg, neg_mul] at upper
  exact neg_le_neg_iff.mp upper

end

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_history_future_block_joint
#print axioms IGS.Sec31.DiscreteMarkov.pathLaw_history_future_block_integral
#print axioms IGS.Sec31.DiscreteMarkov.BoundedHistoryStop.level_measurable
#print axioms IGS.Sec31.DiscreteMarkov.BoundedHistoryStop.indicator_sum
#print axioms IGS.Sec31.DiscreteMarkov.boundedStopping_future_block_integral
#print axioms IGS.Sec31.DiscreteMarkov.futureBlockKernel_eq_dirac_prefix
#print axioms IGS.Sec31.DiscreteMarkov.boundedStopping_dirac_future_block_integral
#print axioms IGS.Sec31.DiscreteMarkov.boundedStopping_weighted_future_le
#print axioms IGS.Sec31.DiscreteMarkov.boundedStopping_weighted_future_ge
