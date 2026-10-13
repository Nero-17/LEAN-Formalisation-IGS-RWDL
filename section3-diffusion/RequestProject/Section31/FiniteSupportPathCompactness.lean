import RequestProject.Section31.FiniteSupportPathModulus
import Mathlib.Tactic

/-! Finite discretization in the common uniform path space. At each accuracy,
finitely many exceptional paths are allowed. The remaining paths share one
modulus bound. Thus finite-level step paths need not be continuous. -/

namespace IGS.Sec31.DiscreteMarkov

open Set Filter Metric
open scoped UniformConvergence Topology Classical

variable {Time State : Type*} [PseudoMetricSpace Time] [CompactSpace Time]
variable [MetricSpace State] [CompactSpace State]
variable {History : ℕ → Type*} [∀ level, Finite (History level)]
variable (paths : (level : ℕ) → History level → Time → State)

local instance compactStateBoundedForPathCompactness : BoundedSpace State :=
  ⟨Metric.isBounded_of_compactSpace⟩

theorem finiteSupportPath_totallyBounded_of_modulus_outside_finite
    (good : Set (FiniteSupportPathSpace paths))
    (modulus : ∀ error > (0 : ℝ), ∃ window > (0 : ℝ),
      ∃ exceptions : Set (FiniteSupportPathSpace paths), exceptions.Finite ∧
        ∀ path ∈ good, path ∉ exceptions →
          path ∈ finiteSupportPathModulusSet paths window error) :
    TotallyBounded good := by
  classical
  apply Metric.totallyBounded_of_finite_discretization
  intro tolerance tolerancePositive
  obtain ⟨window, windowPositive, exceptions, exceptionsFinite, tailModulus⟩ :=
    modulus (tolerance / 8) (by positivity)
  obtain ⟨timeGrid, _, timeGridFinite, timeGridCover⟩ :=
    @finite_cover_balls_of_compact Time _ _ isCompact_univ _ windowPositive
  obtain ⟨stateGrid, _, stateGridFinite, stateGridCover⟩ :=
    @finite_cover_balls_of_compact State _ _ isCompact_univ _
      (show 0 < tolerance / 8 by positivity)
  letI : Fintype exceptions := exceptionsFinite.fintype
  letI : Fintype timeGrid := timeGridFinite.fintype
  letI : Fintype stateGrid := stateGridFinite.fintype
  have stateApproximation : ∀ state : State,
      ∃ approximation ∈ stateGrid, dist state approximation < tolerance / 8 := by
    intro state
    obtain ⟨approximation, approximationMem, close⟩ :=
      Set.mem_iUnion₂.mp (stateGridCover (Set.mem_univ state))
    exact ⟨approximation, approximationMem, Metric.mem_ball.mp close⟩
  choose approximate approximateMem approximateClose using stateApproximation
  let gridCode (path : good) : timeGrid → stateGrid := fun time =>
    ⟨approximate (UniformFun.toFun path.val.val time.val),
      approximateMem (UniformFun.toFun path.val.val time.val)⟩
  let code (path : good) : exceptions ⊕ (timeGrid → stateGrid) :=
    if exceptional : path.val ∈ exceptions then Sum.inl ⟨path.val, exceptional⟩
    else Sum.inr (gridCode path)
  refine ⟨exceptions ⊕ (timeGrid → stateGrid), inferInstance, code, ?_⟩
  intro first second sameCode
  by_cases firstExceptional : first.val ∈ exceptions
  · have secondExceptional : second.val ∈ exceptions := by
      by_contra secondNotExceptional
      have impossible :
          (Sum.inl ⟨first.val, firstExceptional⟩ : exceptions ⊕ (timeGrid → stateGrid)) =
            Sum.inr (gridCode second) := by
        simpa only [code, dif_pos firstExceptional, dif_neg secondNotExceptional] using sameCode
      cases impossible
    have samePath : first.val = second.val := by
      have equality : (⟨first.val, firstExceptional⟩ : exceptions) =
          ⟨second.val, secondExceptional⟩ := by
        apply Sum.inl.inj
        simpa only [code, dif_pos firstExceptional, dif_pos secondExceptional] using sameCode
      exact congrArg (fun element : exceptions => element.val) equality
    simpa only [samePath, dist_self] using tolerancePositive
  · have secondNotExceptional : second.val ∉ exceptions := by
      intro secondExceptional
      have impossible :
          (Sum.inr (gridCode first) : exceptions ⊕ (timeGrid → stateGrid)) =
            Sum.inl ⟨second.val, secondExceptional⟩ := by
        simpa only [code, dif_neg firstExceptional, dif_pos secondExceptional] using sameCode
      cases impossible
    have sameGrid : gridCode first = gridCode second := by
      apply Sum.inr.inj
      simpa only [code, dif_neg firstExceptional, dif_neg secondNotExceptional] using sameCode
    apply lt_of_le_of_lt (b := tolerance / 2)
    · change dist first.val.val second.val.val ≤ tolerance / 2
      apply (UniformFun.dist_le (show 0 ≤ tolerance / 2 by positivity)).mpr
      intro time
      obtain ⟨nearTime, nearTimeMem, closeTime⟩ :=
        Set.mem_iUnion₂.mp (timeGridCover (Set.mem_univ time))
      have timeClose : dist time nearTime ≤ window :=
        (Metric.mem_ball.mp closeTime).le
      have firstClose := tailModulus first.val first.property firstExceptional
        time nearTime timeClose
      have secondClose := tailModulus second.val second.property secondNotExceptional
        time nearTime timeClose
      have sameApproximation :
          approximate (UniformFun.toFun first.val.val nearTime) =
            approximate (UniformFun.toFun second.val.val nearTime) :=
        congrArg (fun values : timeGrid → stateGrid =>
          (values ⟨nearTime, nearTimeMem⟩).val) sameGrid
      have gridClose : dist (UniformFun.toFun first.val.val nearTime)
          (UniformFun.toFun second.val.val nearTime) < tolerance / 4 := by
        calc
          dist (UniformFun.toFun first.val.val nearTime)
              (UniformFun.toFun second.val.val nearTime) ≤
            dist (UniformFun.toFun first.val.val nearTime)
                (approximate (UniformFun.toFun first.val.val nearTime)) +
              dist (UniformFun.toFun second.val.val nearTime)
                (approximate (UniformFun.toFun first.val.val nearTime)) :=
            dist_triangle_right _ _ _
          _ = dist (UniformFun.toFun first.val.val nearTime)
                (approximate (UniformFun.toFun first.val.val nearTime)) +
              dist (UniformFun.toFun second.val.val nearTime)
                (approximate (UniformFun.toFun second.val.val nearTime)) := by
            rw [sameApproximation]
          _ < tolerance / 4 := by
            have firstApprox := approximateClose (UniformFun.toFun first.val.val nearTime)
            have secondApprox := approximateClose (UniformFun.toFun second.val.val nearTime)
            linarith
      have triangle := dist_triangle4_right
        (UniformFun.toFun first.val.val time) (UniformFun.toFun second.val.val time)
        (UniformFun.toFun first.val.val nearTime) (UniformFun.toFun second.val.val nearTime)
      linarith
    · linarith

def finiteSupportGoodPathUnion (good : (level : ℕ) → Set (History level)) :
    Set (FiniteSupportPathSpace paths) :=
  ⋃ level, finitePathEmbedding paths level '' good level

theorem finiteSupportGoodPathUnion_totallyBounded
    (good : (level : ℕ) → Set (History level))
    (tailModulus : ∀ error > (0 : ℝ), ∃ threshold : ℕ, ∃ window > (0 : ℝ),
      ∀ level ≥ threshold, ∀ history ∈ good level,
        finitePathEmbedding paths level history ∈
          finiteSupportPathModulusSet paths window error) :
    TotallyBounded (finiteSupportGoodPathUnion paths good) := by
  classical
  apply finiteSupportPath_totallyBounded_of_modulus_outside_finite paths
  intro error errorPositive
  obtain ⟨threshold, window, windowPositive, bound⟩ := tailModulus error errorPositive
  let exceptions : Set (FiniteSupportPathSpace paths) :=
    ⋃ level : Fin threshold, Set.range (finitePathEmbedding paths level.val)
  have exceptionsFinite : exceptions.Finite :=
    Set.finite_iUnion fun (level : Fin threshold) =>
      finitePathEmbedding_range_finite paths level.val
  refine ⟨window, windowPositive, exceptions, exceptionsFinite, ?_⟩
  intro path pathGood pathNotExceptional
  obtain ⟨level, history, historyGood, rfl⟩ :=
    Set.mem_iUnion.mp pathGood
  have levelLarge : threshold ≤ level := by
    by_contra levelNotLarge
    have levelSmall : level < threshold := by omega
    apply pathNotExceptional
    exact Set.mem_iUnion.mpr ⟨⟨level, levelSmall⟩, Set.mem_range_self history⟩
  exact bound level levelLarge history historyGood

theorem finiteSupportGoodPathUnion_isCompact_closure
    (good : (level : ℕ) → Set (History level))
    (tailModulus : ∀ error > (0 : ℝ), ∃ threshold : ℕ, ∃ window > (0 : ℝ),
      ∀ level ≥ threshold, ∀ history ∈ good level,
        finitePathEmbedding paths level history ∈
          finiteSupportPathModulusSet paths window error) :
    IsCompact (closure (finiteSupportGoodPathUnion paths good)) :=
  (finiteSupportGoodPathUnion_totallyBounded paths good tailModulus).closure.isCompact_of_isClosed
    isClosed_closure

/-! At level n only constraints whose threshold is at most n are imposed.
In particular this definition does not require a fixed finite-level step
path to obey every vanishing modulus bound. -/

def finiteSupportModulusGoodHistory (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ)
    (level : ℕ) : Set (History level) :=
  {history | ∀ index, thresholds index ≤ level →
    finitePathEmbedding paths level history ∈
      finiteSupportPathModulusSet paths (windows index) (errors index)}

theorem finiteSupportModulusGoodHistory_union_totallyBounded
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0)) :
    TotallyBounded (finiteSupportGoodPathUnion paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors)) := by
  apply finiteSupportGoodPathUnion_totallyBounded paths
  intro error errorPositive
  obtain ⟨index, errorSmall⟩ :=
    (errorsVanish.eventually (gt_mem_nhds errorPositive)).exists
  refine ⟨thresholds index, windows index, windowsPositive index, ?_⟩
  intro level levelLarge history historyGood first second close
  exact (historyGood index levelLarge first second close).trans errorSmall.le

theorem finiteSupportModulusGoodHistory_union_isCompact_closure
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0)) :
    IsCompact (closure (finiteSupportGoodPathUnion paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors))) :=
  (finiteSupportModulusGoodHistory_union_totallyBounded paths thresholds windows errors
    windowsPositive errorsVanish).closure.isCompact_of_isClosed isClosed_closure

def finiteSupportGoodPathTail (good : (level : ℕ) → Set (History level)) (threshold : ℕ) :
    Set (FiniteSupportPathSpace paths) :=
  {path | ∃ level, threshold ≤ level ∧ path ∈ finitePathEmbedding paths level '' good level}

theorem finiteSupportGoodPathTail_subset_union
    (good : (level : ℕ) → Set (History level)) (threshold : ℕ) :
    finiteSupportGoodPathTail paths good threshold ⊆ finiteSupportGoodPathUnion paths good := by
  rintro path ⟨level, _, membership⟩
  exact Set.mem_iUnion.mpr ⟨level, membership⟩

theorem finiteSupportModulusGoodHistory_tail_isCompact_closure
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0)) (threshold : ℕ) :
    IsCompact (closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold)) :=
  (finiteSupportModulusGoodHistory_union_isCompact_closure paths thresholds windows errors
    windowsPositive errorsVanish).of_isClosed_subset isClosed_closure
      (closure_mono (finiteSupportGoodPathTail_subset_union paths _ threshold))

theorem finiteSupportModulusGoodHistory_tailClosure_subset_modulus
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ) (index threshold : ℕ)
    (thresholdLarge : thresholds index ≤ threshold) :
    closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold) ⊆
        finiteSupportPathModulusSet paths (windows index) (errors index) := by
  apply closure_minimal
  · rintro path ⟨level, levelLarge, history, historyGood, rfl⟩
    exact historyGood index (thresholdLarge.trans levelLarge)
  · exact finiteSupportPathModulusSet_isClosed paths (windows index) (errors index)

theorem finiteSupportModulusGoodHistory_tailIntersection_continuous
    (thresholds : ℕ → ℕ) (windows errors : ℕ → ℝ)
    (windowsPositive : ∀ index, 0 < windows index)
    (errorsVanish : Tendsto errors atTop (𝓝 0))
    (path : FiniteSupportPathSpace paths)
    (membership : path ∈ ⋂ threshold, closure (finiteSupportGoodPathTail paths
      (finiteSupportModulusGoodHistory paths thresholds windows errors) threshold)) :
    Continuous (UniformFun.toFun path.val) := by
  apply finiteSupportPath_continuous_of_vanishing_modulus paths path windows errors
    windowsPositive errorsVanish
  intro index
  exact finiteSupportModulusGoodHistory_tailClosure_subset_modulus paths thresholds windows errors
    index (thresholds index) le_rfl (Set.mem_iInter.mp membership (thresholds index))

end IGS.Sec31.DiscreteMarkov

#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportPath_totallyBounded_of_modulus_outside_finite
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportGoodPathUnion_totallyBounded
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportGoodPathUnion_isCompact_closure
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_union_totallyBounded
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_union_isCompact_closure
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_tail_isCompact_closure
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_tailClosure_subset_modulus
#print axioms IGS.Sec31.DiscreteMarkov.finiteSupportModulusGoodHistory_tailIntersection_continuous
