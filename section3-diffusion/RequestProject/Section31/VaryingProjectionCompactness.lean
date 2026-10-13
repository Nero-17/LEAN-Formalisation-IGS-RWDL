import RequestProject.Section31.VaryingCoreRecovery
import RequestProject.Section31.VaryingWeakLimits
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Compactness from actual finite-dimensional coordinates and vanishing
projection tails. The common subsequence is obtained from compact closed balls,
and the final limit from completeness; neither is an input assumption. -/

namespace IGS.Sec31

open Filter Topology

theorem bounded_coordinates_common_subsequence
    (Coordinates : ℕ → Type*) [∀ depth, NormedAddCommGroup (Coordinates depth)]
    [∀ depth, ProperSpace (Coordinates depth)]
    (coordinates : ∀ depth, ℕ → Coordinates depth)
    (bounded : ∀ depth, ∃ bound : ℝ, ∀ level, ‖coordinates depth level‖ ≤ bound) :
    ∃ limits : ∀ depth, Coordinates depth, ∃ selection : ℕ → ℕ,
      StrictMono selection ∧ ∀ depth,
        Tendsto (fun index => coordinates depth (selection index)) atTop (nhds (limits depth)) := by
  choose bounds coordinateBounds using bounded
  have compactProduct : IsCompact {values : ∀ depth, Coordinates depth |
      ∀ depth, values depth ∈ Metric.closedBall 0 (bounds depth)} :=
    isCompact_pi_infinite (fun depth => isCompact_closedBall 0 (bounds depth))
  obtain ⟨limits, _, selection, selectionStrict, convergence⟩ := compactProduct.tendsto_subseq
    (x := fun level depth => coordinates depth level) (fun level depth => by
      simpa only [Metric.mem_closedBall, dist_zero_right] using coordinateBounds depth level)
  refine ⟨limits, selection, selectionStrict, ?_⟩
  intro depth
  exact (continuous_apply depth).tendsto limits |>.comp convergence

namespace VaryingHilbertCore

variable {Core Hilbert : Type*} [AddCommGroup Core] [Module ℝ Core]
    [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    {LevelHilbert : ℕ → Type*} [∀ level, NormedAddCommGroup (LevelHilbert level)]
    [∀ level, InnerProductSpace ℝ (LevelHilbert level)]

def reindex (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (selection : ℕ → ℕ) (selectionTendsto : Tendsto selection atTop atTop) :
    VaryingHilbertCore Core Hilbert (fun index => LevelHilbert (selection index)) where
  embed := core.embed
  restrict := fun index => core.restrict (selection index)
  dense := core.dense
  norm_converges := fun element => (core.norm_converges element).comp selectionTendsto

theorem strong_reindex (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (selection : ℕ → ℕ) (selectionTendsto : Tendsto selection atTop atTop)
    {sequence : ∀ level, LevelHilbert level} {limit : Hilbert}
    (convergence : core.Strong sequence limit) :
    (core.reindex selection selectionTendsto).Strong (fun index => sequence (selection index)) limit := by
  intro tolerance positive
  obtain ⟨element, limitClose, sequenceClose⟩ := convergence tolerance positive
  exact ⟨element, limitClose, selectionTendsto.eventually sequenceClose⟩

theorem weak_strong_subsequence_limit_eq (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (selection : ℕ → ℕ) (selectionTendsto : Tendsto selection atTop atTop)
    (sequence : ∀ level, LevelHilbert level) (weakLimit strongLimit : Hilbert)
    (weakConvergence : core.Weak sequence weakLimit)
    (strongConvergence : (core.reindex selection selectionTendsto).Strong
      (fun index => sequence (selection index)) strongLimit) : weakLimit = strongLimit := by
  have differenceZero : ‖weakLimit - strongLimit‖ ≤ 0 := by
    apply norm_le_of_inner_bound_on_denseRange core.embed core.dense (weakLimit - strongLimit) 0 le_rfl
    intro element
    have weakPairing := (weakConvergence _ _ (core.strong_restrict element)).comp selectionTendsto
    have strongPairing := (core.reindex selection selectionTendsto).strong_inner_tendsto strongConvergence
      ((core.reindex selection selectionTendsto).strong_restrict element)
    have equality := tendsto_nhds_unique weakPairing strongPairing
    change inner ℝ weakLimit (core.embed element) = inner ℝ strongLimit (core.embed element) at equality
    simpa only [inner_sub_left, equality, sub_self, zero_mul] using (le_rfl : (0 : ℝ) ≤ 0)
  exact sub_eq_zero.1 (norm_eq_zero.1 (le_antisymm differenceZero (norm_nonneg _)))

theorem strong_linear_rows_of_coordinates_tendsto {Index : Type*} [Fintype Index] [DecidableEq Index]
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (native : ∀ level, (Index → ℝ) →ₗ[ℝ] LevelHilbert level)
    (limit : (Index → ℝ) →ₗ[ℝ] Hilbert)
    (fixedConvergence : ∀ values, core.Strong (fun level => native level values) (limit values))
    (coordinates : ℕ → Index → ℝ) (values : Index → ℝ)
    (coordinateConvergence : Tendsto coordinates atTop (nhds values)) :
    core.Strong (fun level => native level (coordinates level)) (limit values) := by
  apply core.strong_of_norm_sub_tendsto_zero _ (fun level => native level values) _ (fixedConvergence values)
  have errorTendsto : Tendsto (fun level => ∑ index,
      |coordinates level index - values index| * ‖native level (Pi.single index 1)‖) atTop (nhds 0) := by
    have entryTendsto : ∀ index, Tendsto (fun level =>
        |coordinates level index - values index| * ‖native level (Pi.single index 1)‖) atTop (nhds 0) := by
      intro index
      have coefficientTendsto := (((continuous_apply index).tendsto values).comp coordinateConvergence).sub_const (values index)
      simpa only [sub_self, abs_zero, zero_mul] using coefficientTendsto.abs.mul
        (core.strong_norm_tendsto (fixedConvergence (Pi.single index 1)))
    simpa using tendsto_finset_sum Finset.univ (fun index _ => entryTendsto index)
  apply squeeze_zero (fun _ => norm_nonneg _) _ errorTendsto
  intro level
  have reconstruction :
      (∑ index, (coordinates level index - values index) • (Pi.single index (1 : ℝ) : Index → ℝ)) =
        coordinates level - values := by
    ext index
    simp [Finset.sum_apply, Pi.single_apply]
  rw [← map_sub, ← reconstruction, map_sum]
  calc
    _ ≤ ∑ index, ‖native level ((coordinates level index - values index) • (Pi.single index (1 : ℝ) : Index → ℝ))‖ :=
      norm_sum_le _ _
    _ = _ := by simp only [map_smul, norm_smul, Real.norm_eq_abs]

theorem exists_strong_limit_of_projection_tails [CompleteSpace Hilbert]
    (core : VaryingHilbertCore Core Hilbert LevelHilbert)
    (sequence : ∀ level, LevelHilbert level)
    (projections : ℕ → ∀ level, LevelHilbert level) (limits : ℕ → Hilbert)
    (errors : ℕ → ℝ)
    (projectionConvergence : ∀ depth, core.Strong (projections depth) (limits depth))
    (tailBounds : ∀ depth, ∀ᶠ level in atTop, ‖sequence level - projections depth level‖ ≤ errors depth)
    (errorsTendsto : Tendsto errors atTop (nhds 0)) :
    ∃ limit : Hilbert, Tendsto limits atTop (nhds limit) ∧ core.Strong sequence limit ∧
      ∀ depth, ‖limits depth - limit‖ ≤ errors depth := by
  have pairBound : ∀ first second, ‖limits first - limits second‖ ≤ errors first + errors second := by
    intro first second
    apply le_of_tendsto (core.strong_norm_sub_tendsto (projectionConvergence first) (projectionConvergence second))
    filter_upwards [tailBounds first, tailBounds second] with level firstBound secondBound
    calc
      ‖projections first level - projections second level‖ ≤
          ‖projections first level - sequence level‖ + ‖sequence level - projections second level‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ errors first + errors second := by
        rw [norm_sub_rev (projections first level) (sequence level)]
        exact add_le_add firstBound secondBound
  have limitsCauchy : CauchySeq limits := by
    apply Metric.cauchySeq_iff.2
    intro tolerance positive
    obtain ⟨threshold, errorsSmall⟩ := eventually_atTop.1
      (errorsTendsto.eventually (gt_mem_nhds (half_pos positive)))
    refine ⟨threshold, ?_⟩
    intro first firstAfter second secondAfter
    rw [dist_eq_norm]
    exact (pairBound first second).trans_lt (by linarith [errorsSmall first firstAfter, errorsSmall second secondAfter])
  obtain ⟨limit, limitsTendsto⟩ := cauchySeq_tendsto_of_complete limitsCauchy
  have limitBounds : ∀ depth, ‖limits depth - limit‖ ≤ errors depth := by
    intro depth
    have distanceTendsto := ((tendsto_const_nhds (x := limits depth)).sub limitsTendsto).norm
    exact le_of_tendsto_of_tendsto distanceTendsto
      (by simpa only [add_zero] using errorsTendsto.const_add (errors depth))
      (Filter.Eventually.of_forall (pairBound depth))
  refine ⟨limit, limitsTendsto, ?_, limitBounds⟩
  intro tolerance positive
  obtain ⟨depth, errorSmall⟩ := (errorsTendsto.eventually (gt_mem_nhds (by positivity : 0 < tolerance / 3))).exists
  obtain ⟨element, limitClose, projectionClose⟩ := projectionConvergence depth (tolerance / 3) (by positivity)
  refine ⟨element, ?_, ?_⟩
  · exact (norm_sub_le_norm_sub_add_norm_sub (core.embed element) (limits depth) limit).trans_lt
      (by linarith [limitBounds depth])
  · filter_upwards [projectionClose, tailBounds depth] with level projectionClose tailBound
    exact (norm_sub_le_norm_sub_add_norm_sub (sequence level) (projections depth level) (core.restrict level element)).trans_lt
      (by linarith)

end VaryingHilbertCore
end IGS.Sec31

#print axioms IGS.Sec31.bounded_coordinates_common_subsequence
#print axioms IGS.Sec31.VaryingHilbertCore.reindex
#print axioms IGS.Sec31.VaryingHilbertCore.strong_reindex
#print axioms IGS.Sec31.VaryingHilbertCore.weak_strong_subsequence_limit_eq
#print axioms IGS.Sec31.VaryingHilbertCore.strong_linear_rows_of_coordinates_tendsto
#print axioms IGS.Sec31.VaryingHilbertCore.exists_strong_limit_of_projection_tails

